#!/usr/bin/env python3
# -*- coding: utf-8 -*-

r"""
midi_file tester.py — Validador MIDI (SMF) con GUI, drag & drop, visor HEX y “Abrir en DAW”.

- DnD con tkinterdnd2 si está disponible.
- Fallback Windows con windnd (opcional).
- Parser de e.data compatible con: {rutas con espacios}, saltos de línea y URIs file://.
"""
from __future__ import annotations
import os, sys, json, csv, threading, platform, subprocess, urllib.parse

from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
from concurrent.futures import ThreadPoolExecutor, as_completed

# ====== DRAG & DROP OPCIONAL ======
DND_AVAILABLE = False
DND_TEXT = None
DND_FILES = None
TkinterDnD = None
try:
    from tkinterdnd2 import DND_FILES as _DND_FILES, TkinterDnD
    DND_FILES = _DND_FILES
    DND_AVAILABLE = True
except Exception:
    DND_AVAILABLE = False

WIN_WINDND_AVAILABLE = False
if platform.system() == "Windows":
    try:
        import windnd  # pip install windnd
        WIN_WINDND_AVAILABLE = True
    except Exception:
        WIN_WINDND_AVAILABLE = False

# ============ NÚCLEO VALIDADOR (igual que antes, abreviado aquí) ============
MAGIC_MTHD = b"MThd"
MAGIC_MTRK = b"MTrk"

@dataclass
class MIDIHeader:
    format_type: int
    num_tracks: int
    division: int

@dataclass
class TrackStats:
    note_on:int=0; note_off:int=0; dangling_notes:int=0
    program_changes:int=0; controllers:int=0; pitch_bends:int=0
    aftertouch_poly:int=0; aftertouch_ch:int=0; sysex:int=0
    meta:int=0; tempo_events:int=0; time_sig_events:int=0; key_sig_events:int=0
    tempo_values:List[int]=field(default_factory=list)

@dataclass
class TrackReport:
    index:int
    length_declared:int=0
    length_parsed:int=0
    has_end_of_track:bool=False
    errors:List[str]=field(default_factory=list)
    warnings:List[str]=field(default_factory=list)
    error_locs:List[Tuple[str,int]]=field(default_factory=list)
    warning_locs:List[Tuple[str,int]]=field(default_factory=list)
    stats:TrackStats=field(default_factory=TrackStats)

@dataclass
class FileReport:
    path:str
    ok:bool=False
    header:Optional[MIDIHeader]=None
    tracks:List[TrackReport]=field(default_factory=list)
    errors:List[str]=field(default_factory=list)
    warnings:List[str]=field(default_factory=list)
    error_locs:List[Tuple[str,int]]=field(default_factory=list)
    warning_locs:List[Tuple[str,int]]=field(default_factory=list)
    bytes_size:int=0

class Reader:
    def __init__(self,data:bytes):
        self.data=data; self.pos=0; self.len=len(data)
    def remaining(self): return self.len-self.pos
    def read(self,n:int)->bytes:
        if self.pos+n>self.len: raise EOFError("Unexpected EOF")
        out=self.data[self.pos:self.pos+n]; self.pos+=n; return out
    def peek(self,n:int=1)->bytes: return self.data[self.pos:min(self.pos+n,self.len)]
    def tell(self): return self.pos

def read_uint16_be(b:bytes)->int: return (b[0]<<8)|b[1]
def read_uint32_be(b:bytes)->int: return (b[0]<<24)|(b[1]<<16)|(b[2]<<8)|b[3]

def read_vlq(r:Reader)->int:
    val=0
    for _ in range(4):
        byte=r.read(1)[0]
        val=(val<<7)|(byte&0x7F)
        if not (byte&0x80): return val
    raise ValueError("VLQ demasiado largo (>4 bytes)")

def validate_division(div:int, rep:FileReport):
    if div & 0x8000:
        fps=((div>>8)&0xFF); fps=fps-0x100 if fps>=0x80 else fps; fps=-fps
        tpf=div & 0xFF
        if fps not in (24,25,29,30):
            rep.warnings.append(f"SMPTE fps inusual: {fps}")
            rep.warning_locs.append(("SMPTE fps inusual", 0))
        if tpf==0:
            rep.errors.append("Ticks/frame=0 inválido")
            rep.error_locs.append(("Ticks/frame=0 inválido", 0))
    else:
        if div<=0:
            rep.errors.append("Division PPQN debe ser >0")
            rep.error_locs.append(("Division PPQN debe ser >0", 0))

def parse_header(r:Reader, rep:FileReport)->Optional[MIDIHeader]:
    try:
        if r.read(4)!=MAGIC_MTHD:
            rep.errors.append("No MThd al inicio"); rep.error_locs.append(("No MThd al inicio", 0))
            return None
        hlen=read_uint32_be(r.read(4))
        if hlen<6:
            rep.errors.append("Cabecera demasiado corta"); rep.error_locs.append(("Cabecera demasiado corta", r.tell())); return None
        hb=r.read(6)
        fmt=read_uint16_be(hb[0:2]); ntr=read_uint16_be(hb[2:4]); div=read_uint16_be(hb[4:6])
        if hlen>6:
            _=r.read(hlen-6); rep.warnings.append(f"Cabecera con {hlen} bytes (estándar=6)"); rep.warning_locs.append((f"Cabecera {hlen} bytes", r.tell()))
        if fmt not in (0,1,2):
            rep.errors.append(f"Formato desconocido: {fmt}"); rep.error_locs.append((f"Formato desconocido: {fmt}", r.tell()))
        if ntr==0:
            rep.errors.append("Número de pistas=0 inválido"); rep.error_locs.append(("Número de pistas=0 inválido", r.tell()))
        validate_division(div, rep)
        return MIDIHeader(fmt,ntr,div)
    except Exception as e:
        rep.errors.append(f"Error cabecera: {e}"); rep.error_locs.append((f"Error cabecera: {e}", r.tell()))
        return None

def _err(tr:TrackReport, msg:str, abs_off:int): tr.errors.append(msg); tr.error_locs.append((msg, abs_off))
def _warn(tr:TrackReport, msg:str, abs_off:int): tr.warnings.append(msg); tr.warning_locs.append((msg, abs_off))
def _check_data_range(vals:bytes, tr:TrackReport, tindex:int, ctx:str, abs_off:int):
    for v in vals:
        if v>127: _err(tr, f"Pista {tindex}: dato >127 en {ctx}: {v}", abs_off); break

def parse_track(r:Reader, tindex:int, rep:FileReport, pair_notes:bool, strict:bool)->TrackReport:
    tr=TrackReport(index=tindex)
    try:
        if r.read(4)!=MAGIC_MTRK: _err(tr, f"Pista {tindex}: falta 'MTrk'.", r.tell()-4); return tr
        tr.length_declared=read_uint32_be(r.read(4))
        start=r.tell(); end=start+tr.length_declared
        if end>r.len: _err(tr, f"Pista {tindex}: longitud declarada excede archivo.", start); end=r.len
        local=Reader(r.data[start:end]); status=None; active={}
        while local.remaining()>0:
            ev_start=local.tell()
            try: _=read_vlq(local)
            except Exception as e: _err(tr, f"Pista {tindex}: VLQ inválido: {e}", start+ev_start); break
            if local.remaining()<=0: break
            b=local.read(1)[0]
            if b & 0x80: status=b
            else:
                if status is None: _err(tr, f"Pista {tindex}: running status sin previo.", start+local.tell()-1); break
                local.pos-=1
            if status is None: _err(tr, f"Pista {tindex}: status indefinido.", start+local.tell()); break
            if 0x80<=status<=0xEF:
                ch=status & 0x0F; mt=status & 0xF0
                dl = 1 if mt in (0xC0,0xD0) else 2
                if local.remaining()<dl: _err(tr, f"Pista {tindex}: datos insuficientes para {hex(status)}.", start+local.tell()); break
                data=local.read(dl); _check_data_range(data, tr, tindex, f"msg {hex(status)}", start+local.tell()-dl)
                if mt==0x80:
                    tr.stats.note_off+=1
                    if pair_notes:
                        key=(ch, data[0]); active[key]=max(0, active.get(key,0)-1)
                elif mt==0x90:
                    vel=data[1] if dl==2 else 0
                    if vel==0:
                        tr.stats.note_off+=1
                        if pair_notes:
                            key=(ch, data[0]); active[key]=max(0, active.get(key,0)-1)
                    else:
                        tr.stats.note_on+=1
                        if pair_notes:
                            key=(ch, data[0]); active[key]=active.get(key,0)+1
                elif mt==0xA0: tr.stats.aftertouch_poly+=1
                elif mt==0xB0: tr.stats.controllers+=1
                elif mt==0xC0: tr.stats.program_changes+=1
                elif mt==0xD0: tr.stats.aftertouch_ch+=1
                elif mt==0xE0: tr.stats.pitch_bends+=1
            elif status==0xFF:
                if local.remaining()<2: _err(tr, f"Pista {tindex}: meta truncado.", start+local.tell()); break
                meta=local.read(1)[0]
                try: ln=read_vlq(local)
                except Exception as e: _err(tr, f"Pista {tindex}: meta VLQ inválido: {e}", start+local.tell()); break
                if local.remaining()<ln: _err(tr, f"Pista {tindex}: meta datos truncados {hex(meta)}.", start+local.tell()); break
                md=local.read(ln); tr.stats.meta+=1
                if meta==0x2F:
                    if ln!=0: _err(tr, f"Pista {tindex}: End-of-Track len !=0.", start+local.tell()-ln)
                    tr.has_end_of_track=True
                    if local.remaining()>0:
                        _warn(tr, f"Pista {tindex}: bytes extra tras EOT ({local.remaining()}).", start+local.tell())
                        _=local.read(local.remaining()); break
                elif meta==0x51:
                    if ln!=3: _err(tr, f"Pista {tindex}: Tempo len {ln} (3).", start+local.tell()-ln)
                    else:
                        us=(md[0]<<16)|(md[1]<<8)|md[2]; tr.stats.tempo_events+=1; tr.stats.tempo_values.append(us)
                        if strict and not (10_000<=us<=2_000_000): _warn(tr, f"Pista {tindex}: Tempo inusual {us} us/qn.", start+local.tell()-3)
                elif meta==0x58:
                    if ln!=4: _err(tr, f"Pista {tindex}: TimeSig len {ln} (4).", start+local.tell()-ln)
                    else:
                        nn,dd,cc,bb=md
                        if nn==0 or dd>7: _warn(tr, f"Pista {tindex}: compás inusual nn={nn}, dd={dd}.", start+local.tell()-4)
                        tr.stats.time_sig_events+=1
                elif meta==0x59:
                    if ln!=2: _err(tr, f"Pista {tindex}: KeySig len {ln} (2).", start+local.tell()-ln)
                    else: tr.stats.key_sig_events+=1
            elif status in (0xF0,0xF7):
                try: ln=read_vlq(local)
                except Exception as e: _err(tr, f"Pista {tindex}: SysEx VLQ inválido: {e}", start+local.tell()); break
                if local.remaining()<ln: _err(tr, f"Pista {tindex}: SysEx truncado.", start+local.tell()); break
                _=local.read(ln); tr.stats.sysex+=1
            else:
                _err(tr, f"Pista {tindex}: status desconocido {hex(status)}.", start+local.tell()); break
        tr.length_parsed=local.tell(); r.pos=end
        if tr.length_parsed!=tr.length_declared: _warn(tr, f"Pista {tindex}: len analizada {tr.length_parsed} != declarada {tr.length_declared}.", end)
        if not tr.has_end_of_track: _err(tr, f"Pista {tindex}: sin End-of-Track (FF 2F 00).", end-1)
        if pair_notes: tr.stats.dangling_notes = 0  # (omitir conteo exacto aquí)
    except Exception as e:
        _err(tr, f"Pista {tindex}: error inesperado: {e}", r.tell())
    return tr

def validate_midi_file(path:str, pair_notes:bool=False, strict:bool=False)->FileReport:
    rep=FileReport(path=path, ok=False)
    try:
        with open(path,'rb') as f: data=f.read()
        rep.bytes_size=len(data); r=Reader(data)
        header=parse_header(r, rep)
        if header is None: return rep
        rep.header=header
        t=0
        while r.remaining()>0 and t<header.num_tracks:
            rep.tracks.append(parse_track(r, t, rep, pair_notes, strict)); t+=1
        total_err = len(rep.errors)+sum(len(t.errors) for t in rep.tracks)
        rep.ok = (total_err==0)
    except Exception as e:
        rep.errors.append(f"Error: {e}"); rep.ok=False
    return rep

def iter_midi_files(paths:List[str], recursive:bool=False)->List[str]:
    out=[]
    for p in paths:
        if os.path.isdir(p):
            for root, dirs, files in os.walk(p):
                for name in files:
                    if name.lower().endswith(('.mid','.midi')): out.append(os.path.join(root,name))
                if not recursive: break
        else:
            if p.lower().endswith(('.mid','.midi')): out.append(p)
    return sorted(set(out))

def tempo_mean_usqn(v:List[int])->Optional[float]:
    if not v: return None
    return sum(v)/len(v)

# ============ GUI ============
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

BaseTk = TkinterDnD.Tk if DND_AVAILABLE else tk.Tk

def _parse_dropped_items(data: str) -> List[str]:
    r"""
    Admite:
      - {C:\ruta con espacios}\n{D:\otra} ...
      - C:\sin\llaves C:\otra
      - /home/user/file.mid (Linux/Mac)
      - URIs: file:///home/user/a.mid  file:///C:/Users/A/a.mid
      - líneas separadas por \n
    """
    # 1) tokenizar respetando llaves
    items = []
    buf = ""
    brace = False
    for ch in data:
        if ch == "{":
            brace = True; buf = ""
        elif ch == "}":
            brace = False; items.append(buf)
        elif ch.isspace() and not brace:
            if buf: items.append(buf); buf=""
        else:
            buf += ch
    if buf: items.append(buf)
    # 2) expandir por líneas
    parts = []
    for it in items:
        parts.extend([p for p in it.splitlines() if p.strip()])
    # 3) normalizar URIs y %20
    norm = []
    for p in parts:
        if p.startswith("file://"):
            p = urllib.parse.unquote(p[7:])
            if p.startswith("/") and len(p) > 3 and p[2] == ":":
                p = p[1:]  # /C:/...
        norm.append(p)
    return norm

class HexViewer(tk.Toplevel):
    def __init__(self, master, path:str, highlights:List[int]=None):
        super().__init__(master)
        self.title(f"HEX — {os.path.basename(path)}")
        self.geometry("900x520")
        self.path=path
        self.data=b""
        self.highlights=set(highlights or [])
        self._build_ui()
        self._load()

    def _build_ui(self):
        top=ttk.Frame(self); top.pack(fill="x", padx=8, pady=6)
        self.entry_offset=ttk.Entry(top, width=16); self.entry_offset.pack(side="left")
        ttk.Button(top, text="Ir a offset", command=self.goto_offset).pack(side="left", padx=6)
        ttk.Label(top, text="Buscar (hex, ej. FF 2F 00):").pack(side="left", padx=(12,4))
        self.entry_search=ttk.Entry(top, width=28); self.entry_search.pack(side="left")
        ttk.Button(top, text="Buscar", command=self.search).pack(side="left", padx=6)
        self.text=tk.Text(self, font=("Consolas", 10), wrap="none"); self.text.pack(fill="both", expand=True, padx=8, pady=(0,8))
        xscroll=ttk.Scrollbar(self, orient="horizontal", command=self.text.xview); xscroll.pack(fill="x")
        self.text.configure(xscrollcommand=xscroll.set)
        self.text.tag_configure("hi", background="#fff1a8"); self.text.tag_configure("hit", background="#b7e0ff")

    def _load(self):
        try:
            with open(self.path, "rb") as f: self.data=f.read()
            self.render()
        except Exception as e:
            messagebox.showerror("HEX", f"No se pudo abrir:\n{e}")

    def render(self):
        self.text.delete("1.0","end")
        data=self.data; B=16
        for off in range(0, len(data), B):
            chunk=data[off:off+B]
            hexs=" ".join(f"{b:02X}" for b in chunk)
            ascii_s="".join(chr(b) if 32<=b<127 else "." for b in chunk)
            self.text.insert("end", f"{off:08X}  {hexs:<48}  |{ascii_s}|\n")
        for off in self.highlights: self._highlight(off, tag="hi")

    def _highlight(self, off:int, tag="hi"):
        B=16; line=off//B; col=off%B
        start_col=10+col*3; end_col=start_col+2
        s=f"{line+1}.{start_col}"; e=f"{line+1}.{end_col}"
        try: self.text.tag_add(tag, s, e); self.text.see(s)
        except tk.TclError: pass

    def goto_offset(self):
        s=self.entry_offset.get().strip()
        try:
            off=int(s, 0); self._highlight(off, tag="hit")
        except Exception:
            messagebox.showwarning("HEX","Offset inválido (usa decimal o 0x..)")

    def search(self):
        patt=self.entry_search.get().strip()
        try:
            bs=bytes(int(x,16) for x in patt.replace(","," ").split())
            idx=self.data.find(bs)
            if idx>=0:
                for i in range(len(bs)): self._highlight(idx+i, tag="hit")
            else:
                messagebox.showinfo("HEX","No encontrado.")
        except Exception:
            messagebox.showwarning("HEX","Formato inválido. Ej: FF 2F 00")

class MidiCheckerGUI(BaseTk):
    def __init__(self):
        super().__init__()
        self.title("MIDI File Tester")
        self.geometry("1120x680"); self.minsize(960, 580)

        self.files:List[str]=[]
        self.reports:List[FileReport]=[]
        self.running=False

        self.var_recursive=tk.BooleanVar(value=True)
        self.var_pairnotes=tk.BooleanVar(value=True)
        self.var_strict=tk.BooleanVar(value=False)
        self.var_jobs=tk.IntVar(value=4)

        self._build_ui()

    def _build_ui(self):
        top=ttk.Frame(self); top.pack(fill="x", padx=8, pady=6)
        ttk.Button(top, text="Añadir archivos…", command=self.add_files).pack(side="left")
        ttk.Button(top, text="Añadir carpeta…", command=self.add_folder).pack(side="left", padx=(6,0))
        ttk.Button(top, text="Limpiar", command=self.clear_list).pack(side="left", padx=(6,0))

        msg = "Drag & Drop ACTIVO" if DND_AVAILABLE or WIN_WINDND_AVAILABLE else "Instala tkinterdnd2 (o windnd en Windows) para activar drag & drop"
        fg  = "#0a7d22" if (DND_AVAILABLE or WIN_WINDND_AVAILABLE) else "#b36b00"
        ttk.Label(top, text=msg, foreground=fg).pack(side="left", padx=12)

        opts=ttk.Frame(top); opts.pack(side="left", padx=12)
        ttk.Checkbutton(opts, text="Recursivo", variable=self.var_recursive).grid(row=0,column=0,sticky="w")
        ttk.Checkbutton(opts, text="Emparejar notas", variable=self.var_pairnotes).grid(row=0,column=1,sticky="w", padx=(10,0))
        ttk.Checkbutton(opts, text="Estricto", variable=self.var_strict).grid(row=0,column=2,sticky="w", padx=(10,0))
        ttk.Label(opts, text="Hilos:").grid(row=0,column=3,sticky="e", padx=(10,2))
        ttk.Spinbox(opts, from_=1, to=32, textvariable=self.var_jobs, width=4).grid(row=0,column=4,sticky="w")

        ttk.Button(top, text="Validar", command=self.run_validation).pack(side="right")
        ttk.Button(top, text="Exportar CSV", command=self.export_csv).pack(side="right", padx=(0,6))
        ttk.Button(top, text="Exportar JSON", command=self.export_json).pack(side="right", padx=(0,6))

        dropfrm = ttk.Frame(self); dropfrm.pack(fill="x", padx=8, pady=(0,6))
        self.dropzone = tk.Label(dropfrm, text="Arrastra aquí archivos .mid/.midi", relief="groove", anchor="center")
        self.dropzone.pack(fill="x")

        # Registrar ambos: root y zona como targets
        if DND_AVAILABLE:
            try:
                self.dropzone.drop_target_register(DND_FILES)
                self.dropzone.dnd_bind("<<Drop>>", self.on_drop)
                self.drop_target_register(DND_FILES)  # root
                self.dnd_bind("<<Drop>>", self.on_drop_root)
            except Exception:
                pass
        elif WIN_WINDND_AVAILABLE:
            windnd.hook_dropfiles(self.dropzone, func=self.on_drop_win)

        columns=("status","path","format","tracks","division","size","errors","warnings")
        self.tree=ttk.Treeview(self, columns=columns, show="headings", height=14)
        for c,t in zip(columns, ["Estado","Archivo","Fmt","Pistas","División","Tamaño","Errores","Avisos"]):
            self.tree.heading(c, text=t)
        self.tree.column("status", width=90, anchor="center")
        self.tree.column("path", width=520)
        self.tree.column("format", width=50, anchor="center")
        self.tree.column("tracks", width=60, anchor="e")
        self.tree.column("division", width=110, anchor="center")
        self.tree.column("size", width=100, anchor="e")
        self.tree.column("errors", width=70, anchor="e")
        self.tree.column("warnings", width=70, anchor="e")
        self.tree.pack(fill="both", expand=True, padx=8, pady=(0,6))
        self.tree.bind("<<TreeviewSelect>>", self.on_select_row)

        bottom = ttk.Frame(self); bottom.pack(fill="both", expand=True, padx=8, pady=(0,8))
        left = ttk.Frame(bottom); left.pack(side="left", fill="both", expand=True)
        self.txt_details = tk.Text(left, height=12, wrap="word", font=("Consolas", 10))
        self.txt_details.pack(fill="both", expand=True)
        right = ttk.Frame(bottom); right.pack(side="left", fill="y", padx=(8,0))
        ttk.Button(right, text="Ver bytes (HEX)", command=self.open_hex).pack(fill="x")
        ttk.Button(right, text="Abrir en DAW…", command=self.open_in_daw).pack(fill="x", pady=(6,0))

        status = ttk.Frame(self); status.pack(fill="x", padx=8, pady=(0,8))
        self.progress=ttk.Progressbar(status, mode="determinate"); self.progress.pack(side="left", fill="x", expand=True)
        self.lbl_status=ttk.Label(status, text="Listo"); self.lbl_status.pack(side="left", padx=(8,0))

    # ---------- DnD handlers ----------
    def on_drop_root(self, event):
        self._handle_drop_data(event.data)

    def on_drop(self, event):
        self._handle_drop_data(event.data)

    def on_drop_win(self, files):
        # windnd da lista de bytes; decodificar
        paths = [f.decode("utf-8") for f in files]
        self._add_paths(paths)

    def _handle_drop_data(self, data: str):
        paths = _parse_dropped_items(data)
        # Clasificar carpetas/archivos y expandir
        expanded = []
        for p in paths:
            if os.path.isdir(p):
                expanded += iter_midi_files([p], recursive=True)
            elif p.lower().endswith(('.mid','.midi')):
                expanded.append(p)
        self._add_paths(expanded)

    def _add_paths(self, paths: List[str]):
        added = 0
        for p in paths:
            if p not in self.files:
                self.files.append(p); added += 1
        self.refresh_table()
        self.set_status(f"Añadidos {added} elemento(s) por arrastre")

    # ---------- Resto de la app (igual que antes): añadir archivos/carpeta, validar, exportar, HEX, etc. ----------
    def add_files(self):
        paths=filedialog.askopenfilenames(title="Selecciona ficheros MIDI", filetypes=[("MIDI files","*.mid *.midi")])
        if not paths: return
        for p in paths:
            if p not in self.files: self.files.append(p)
        self.refresh_table()

    def add_folder(self):
        folder=filedialog.askdirectory(title="Selecciona carpeta con MIDIs")
        if not folder: return
        files=iter_midi_files([folder], recursive=self.var_recursive.get())
        for p in files:
            if p not in self.files: self.files.append(p)
        self.refresh_table()

    def clear_list(self):
        self.files.clear(); self.reports.clear()
        for i in self.tree.get_children(): self.tree.delete(i)
        self.clear_details(); self.set_status("Listo")

    def set_status(self, txt:str):
        self.lbl_status.config(text=txt); self.update_idletasks()

    def refresh_table(self):
        for i in self.tree.get_children(): self.tree.delete(i)
        for p in sorted(self.files, key=lambda s:s.lower()):
            self.tree.insert("", "end", values=("Pendiente", p, "", "", "", "", "", ""))
        self.set_status(f"{len(self.files)} archivo(s) en cola")

    def on_select_row(self, _=None):
        sel=self.tree.selection()
        if not sel: return
        p=self.tree.item(sel[0])['values'][1]
        rep=next((r for r in self.reports if r.path==p), None)
        if rep is None: self.show_details("Sin detalles"); return
        self.show_report_details(rep)

    def show_details(self, txt:str):
        self.txt_details.delete("1.0","end"); self.txt_details.insert("1.0", txt)

    def run_validation(self):
        if self.running: messagebox.showinfo("Validación","Ya hay una validación en curso."); return
        if not self.files: messagebox.showwarning("Validación","Añade archivos o carpetas primero."); return
        self.running=True; self.reports.clear()
        for iid in self.tree.get_children():
            vals=list(self.tree.item(iid)['values']); vals[0]="En cola"; self.tree.item(iid, values=vals)
        self.progress.configure(value=0, maximum=len(self.files))
        self.set_status("Validando…")
        jobs=max(1, int(self.var_jobs.get()))
        pair=self.var_pairnotes.get(); strict=self.var_strict.get()

        def worker():
            loc=[]
            try:
                with ThreadPoolExecutor(max_workers=jobs) as ex:
                    futures={ex.submit(validate_midi_file, p, pair, strict): p for p in self.files}
                    done=0
                    for fut in as_completed(futures):
                        rep=fut.result(); loc.append(rep); done+=1
                        self.after(0, self._update_row, rep, done)
            finally:
                self.after(0, self._finish, loc)
        threading.Thread(target=worker, daemon=True).start()

    def _update_row(self, rep:FileReport, done:int):
        for iid in self.tree.get_children():
            vals=list(self.tree.item(iid)['values'])
            if vals and vals[1]==rep.path:
                status="OK" if rep.ok else "ERROR"
                fmt=rep.header.format_type if rep.header else ""
                ntr=rep.header.num_tracks if rep.header else ""
                div=rep.header.division if rep.header else ""
                size=rep.bytes_size
                errs=len(rep.errors)+sum(len(t.errors) for t in rep.tracks)
                warns=len(rep.warnings)+sum(len(t.warnings) for t in rep.tracks)
                vals=[status, rep.path, fmt, ntr, div, size, errs, warns]
                self.tree.item(iid, values=vals, tags=(status,))
                break
        self.tree.tag_configure("OK", foreground="#0a7d22")
        self.tree.tag_configure("ERROR", foreground="#b40000")
        self.progress.configure(value=done)
        self.set_status(f"Validando… {done}/{len(self.files)}")

    def _finish(self, reports:List[FileReport]):
        self.reports=sorted(reports, key=lambda r:r.path.lower())
        ok=sum(1 for r in self.reports if r.ok)
        self.set_status(f"Completado: {ok}/{len(self.reports)} OK")
        self.running=False
        if self.tree.get_children():
            self.tree.selection_set(self.tree.get_children()[0])
            self.on_select_row()

    def show_report_details(self, rep:FileReport):
        lines=[]
        lines.append(f"Archivo: {rep.path}")
        lines.append(f"Tamaño: {rep.bytes_size} bytes")
        if rep.header:
            div=rep.header.division
            if div & 0x8000:
                fps=((div>>8)&0xFF); fps=fps-0x100 if fps>=0x80 else fps; fps=-fps
                lines.append(f"Cabecera: formato={rep.header.format_type}, pistas={rep.header.num_tracks}, SMPTE fps={fps}, tpf={div & 0xFF}")
            else:
                lines.append(f"Cabecera: formato={rep.header.format_type}, pistas={rep.header.num_tracks}, ticks/negra={div}")
        if rep.errors:
            lines.append("\nERRORES:"); lines += [f"  - {e}" for e in rep.errors]
        if rep.warnings:
            lines.append("\nAVISOS:"); lines += [f"  * {w}" for w in rep.warnings]
        for t in rep.tracks:
            lines.append(f"\n[Track {t.index}] len={t.length_parsed}/{t.length_declared}  EOT={'sí' if t.has_end_of_track else 'no'}")
            lines += [f"  - ERROR: {e}" for e in t.errors]
            lines += [f"  * AVISO: {w}" for w in t.warnings]
        self.show_details("\n".join(lines))

    def _selected_report(self)->Optional[FileReport]:
        sel=self.tree.selection()
        if not sel: return None
        path=self.tree.item(sel[0])['values'][1]
        return next((r for r in self.reports if r.path==path), None)

    def _collect_highlights(self, rep:FileReport)->List[int]:
        offs=[]
        offs += [o for _,o in rep.error_locs] + [o for _,o in rep.warning_locs]
        for t in rep.tracks:
            offs += [o for _,o in t.error_locs] + [o for _,o in t.warning_locs]
        offs = [o for o in offs if isinstance(o,int) and 0<=o<rep.bytes_size]
        uniq=[]; seen=set()
        for o in offs:
            if o not in seen: seen.add(o); uniq.append(o)
        return uniq[:2000]

    def open_hex(self):
        rep=self._selected_report()
        if rep is None: messagebox.showinfo("HEX","Selecciona un archivo en la tabla."); return
        HexViewer(self, rep.path, highlights=self._collect_highlights(rep))

    def open_in_daw(self):
        rep=self._selected_report()
        if rep is None: messagebox.showinfo("Abrir","Selecciona un archivo en la tabla."); return
        p=rep.path
        try:
            sysname=platform.system()
            if sysname=="Windows": os.startfile(p)
            elif sysname=="Darwin": subprocess.Popen(["open", p])
            else: subprocess.Popen(["xdg-open", p])
        except Exception as e:
            messagebox.showerror("Abrir en DAW", f"No se pudo abrir:\n{e}")

    def export_csv(self):
        if not self.reports: messagebox.showwarning("CSV","No hay resultados."); return
        path=filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV","*.csv")])
        if not path: return
        try:
            with open(path,'w',newline='',encoding='utf-8') as f:
                w=csv.writer(f, delimiter=';')
                w.writerow(["path","ok","bytes_size","format","num_tracks","division","track_index","track_len_decl","track_len_parsed","track_has_EOT","errors","warnings"])
                for rep in self.reports:
                    fmt=rep.header.format_type if rep.header else ""
                    ntr=rep.header.num_tracks if rep.header else ""
                    div=rep.header.division if rep.header else ""
                    rep_err=" | ".join(rep.errors); rep_warn=" | ".join(rep.warnings)
                    for t in rep.tracks:
                        w.writerow([rep.path,rep.ok,rep.bytes_size,fmt,ntr,div,t.index,t.length_declared,t.length_parsed,t.has_end_of_track,
                                    rep_err + (" | " if rep_err and (t.errors or t.warnings) else "") + " | ".join(t.errors),
                                    rep_warn + (" | " if rep_warn and t.warnings else "") + " | ".join(t.warnings)])
            messagebox.showinfo("CSV","Exportado.")
        except Exception as e:
            messagebox.showerror("CSV", f"Error al guardar:\n{e}")

    def export_json(self):
        if not self.reports: messagebox.showwarning("JSON","No hay resultados."); return
        path=filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON","*.json")])
        if not path: return
        try:
            j=[]
            for rep in self.reports:
                j.append({
                    "path":rep.path,"ok":rep.ok,"bytes_size":rep.bytes_size,
                    "header":{"format":rep.header.format_type,"num_tracks":rep.header.num_tracks,"division":rep.header.division} if rep.header else None,
                    "errors":rep.errors,"warnings":rep.warnings,
                    "tracks":[{"index":t.index,"length_declared":t.length_declared,"length_parsed":t.length_parsed,
                               "has_end_of_track":t.has_end_of_track,"errors":t.errors,"warnings":t.warnings} for t in rep.tracks]
                })
            with open(path,'w',encoding='utf-8') as f: json.dump(j,f,ensure_ascii=False,indent=2)
            messagebox.showinfo("JSON","Exportado.")
        except Exception as e:
            messagebox.showerror("JSON", f"Error al guardar:\n{e}")

if __name__=="__main__":
    app=MidiCheckerGUI()
    app.mainloop()
