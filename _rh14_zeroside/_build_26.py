# -*- coding: utf-8 -*-
"""Generic md -> docx builder (pandoc + OMML, then academic layout).

Usage: python _build_26.py <src.md> <out.docx>
"""
import subprocess
import sys
import zipfile
from pathlib import Path

from docx import Document
from docx.enum.table import WD_ALIGN_VERTICAL
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml import OxmlElement
from docx.oxml.ns import qn
from docx.shared import Cm, Pt, RGBColor

BASE = Path(r"C:\proj2\_rh14_zeroside")
SRC = Path(sys.argv[1])
OUT = Path(sys.argv[2])
TMP = BASE / ("_tmp_" + OUT.stem + ".md")
PANDOC = r"C:\Program Files\Pandoc\pandoc.exe"
M_NS = "http://schemas.openxmlformats.org/officeDocument/2006/math"
BODY_PT = 10.5
CN = "宋体"
HEI = "黑体"
EN = "Times New Roman"


def run_pandoc(md, out):
    argv = [PANDOC, str(md), "-o", str(out),
            "--from", "markdown+tex_math_single_backslash+tex_math_dollars",
            "--to", "docx"]
    r = subprocess.run(argv, capture_output=True, text=True, encoding="utf-8")
    if r.returncode != 0:
        print("PANDOC STDOUT:", r.stdout)
        print("PANDOC STDERR:", r.stderr)
        raise SystemExit("pandoc failed")
    return r.stderr


def count_math(docx):
    with zipfile.ZipFile(docx) as z:
        xml = z.read("word/document.xml").decode("utf-8")
    return xml.count("<m:oMath")


def set_rfonts(rpr, ascii_f, ea_f):
    rf = rpr.find(qn("w:rFonts"))
    if rf is None:
        rf = OxmlElement("w:rFonts")
        rpr.insert(0, rf)
    for k in ("w:ascii", "w:hAnsi", "w:cs"):
        rf.set(qn(k), ascii_f)
    rf.set(qn("w:eastAsia"), ea_f)


def style_font(style, ascii_f, ea_f, size, bold=False):
    style.font.size = Pt(size)
    style.font.bold = bold
    style.font.italic = False
    try:
        style.font.color.rgb = RGBColor(0, 0, 0)
    except Exception:
        pass
    set_rfonts(style.element.get_or_add_rPr(), ascii_f, ea_f)


def style_par(style, align, line, before, after, first_chars=0, keep_next=False):
    pf = style.paragraph_format
    pf.alignment = align
    pf.line_spacing = line
    pf.space_before = Pt(before)
    pf.space_after = Pt(after)
    pf.keep_with_next = keep_next
    pPr = style.element.get_or_add_pPr()
    ind = pPr.get_or_add_ind()
    ind.set(qn("w:left"), "0")
    ind.set(qn("w:right"), "0")
    if first_chars:
        ind.set(qn("w:firstLineChars"), str(first_chars))
        ind.set(qn("w:firstLine"), str(int(BODY_PT * 20 * first_chars / 100)))
    else:
        ind.set(qn("w:firstLineChars"), "0")
        ind.set(qn("w:firstLine"), "0")


def get_style(doc, names):
    for n in names:
        try:
            return doc.styles[n]
        except KeyError:
            continue
    return None


def has_display_math(p):
    tag = "{%s}oMathPara" % M_NS
    for el in p._p.iter():
        if el.tag == tag:
            return True
    return False


# ---------------------------------------------------------------- build
run_pandoc(SRC, OUT)
n_math = count_math(OUT)
print("math objects after pass 1:", n_math)

if n_math == 0:
    txt = SRC.read_text(encoding="utf-8")
    txt = txt.replace("\\[", "$$").replace("\\]", "$$")
    txt = txt.replace("\\(", "$").replace("\\)", "$")
    TMP.write_text(txt, encoding="utf-8", newline="\n")
    run_pandoc(TMP, OUT)
    print("math objects after pass 2:", count_math(OUT))

doc = Document(str(OUT))

# ---------------------------------------------------------------- page
for sec in doc.sections:
    sec.page_width = Cm(21.0)
    sec.page_height = Cm(29.7)
    sec.top_margin = Cm(2.5)
    sec.bottom_margin = Cm(2.5)
    sec.left_margin = Cm(2.5)
    sec.right_margin = Cm(2.5)
    sec.header_distance = Cm(1.5)
    sec.footer_distance = Cm(1.5)

# ---------------------------------------------------------------- styles
for name in ("Normal", "Body Text", "First Paragraph"):
    st = get_style(doc, [name])
    if st is not None:
        style_font(st, EN, CN, BODY_PT)
        style_par(st, WD_ALIGN_PARAGRAPH.JUSTIFY, 1.5, 0, 0, first_chars=200)

for name, size, before, after in (("Heading 1", 12, 12, 6),
                                  ("Heading 2", 10.5, 8, 4),
                                  ("Heading 3", 10.5, 6, 3),
                                  ("Heading 4", 10.5, 6, 3)):
    st = get_style(doc, [name])
    if st is not None:
        style_font(st, EN, HEI, size, bold=True)
        style_par(st, WD_ALIGN_PARAGRAPH.LEFT, 1.0, before, after,
                  first_chars=0, keep_next=True)

st = get_style(doc, ["Title"])
if st is not None:
    style_font(st, EN, HEI, 18, bold=True)
    style_par(st, WD_ALIGN_PARAGRAPH.CENTER, 1.0, 0, 18, first_chars=0)

st = get_style(doc, ["Caption"])
if st is not None:
    style_font(st, EN, HEI, 9, bold=True)
    style_par(st, WD_ALIGN_PARAGRAPH.CENTER, 1.0, 4, 3, first_chars=0)

for name in ("Source Code", "SourceCode"):
    st = get_style(doc, [name])
    if st is not None:
        style_font(st, "Consolas", CN, 8.5)
        style_par(st, WD_ALIGN_PARAGRAPH.LEFT, 1.0, 3, 3, first_chars=0)

for name in ("Verbatim Char", "VerbatimChar"):
    st = get_style(doc, [name])
    if st is not None:
        style_font(st, "Consolas", CN, 8.5)

for name in ("Block Text", "Block Quote", "Quote"):
    st = get_style(doc, [name])
    if st is not None:
        style_font(st, EN, CN, 9.5)
        style_par(st, WD_ALIGN_PARAGRAPH.JUSTIFY, 1.2, 4, 4, first_chars=0)
        pPr = st.element.get_or_add_pPr()
        ind = pPr.get_or_add_ind()
        ind.set(qn("w:left"), "340")

# ---------------------------------------------------------------- body paragraphs
title_done = False
for p in doc.paragraphs:
    nm = p.style.name
    if nm.startswith("Heading"):
        if nm == "Heading 1" and not title_done:
            title_done = True
            p.alignment = WD_ALIGN_PARAGRAPH.CENTER
            p.paragraph_format.space_before = Pt(0)
            p.paragraph_format.space_after = Pt(18)
            for r in p.runs:
                r.font.size = Pt(18)
                r.font.name = EN
                set_rfonts(r._element.get_or_add_rPr(), EN, HEI)
        continue
    if nm in ("Source Code", "SourceCode"):
        continue
    if has_display_math(p):
        p.alignment = WD_ALIGN_PARAGRAPH.CENTER
        pf = p.paragraph_format
        pf.first_line_indent = Pt(0)
        pf.left_indent = Pt(0)
        pf.right_indent = Pt(0)
        pf.space_before = Pt(6)
        pf.space_after = Pt(6)
        pf.line_spacing = 1.0
        continue

# ---------------------------------------------------------------- tables
def header_texts(t):
    return [c.text.strip() for c in t.rows[0].cells]


def widths_for(hdr, ncol):
    joined = "|".join(hdr)
    if ncol == 3 and hdr and hdr[0] == "项":
        return [3.2, 6.4, 6.4]
    if ncol == 5 and hdr and hdr[0] == "段":
        return [1.1, 1.9, 3.4, 4.9, 4.7]
    if ncol == 5 and hdr and hdr[0] == "Stage":
        return [1.3, 1.7, 3.3, 4.9, 4.8]
    if ncol == 3 and hdr and hdr[0] == "Item":
        return [3.2, 6.4, 6.4]
    if ncol == 2:
        return [4.6, 11.4]
    return [16.0 / ncol] * ncol


def set_borders(tblPr, first_row):
    old = tblPr.find(qn("w:tblBorders"))
    if old is not None:
        tblPr.remove(old)
    borders = OxmlElement("w:tblBorders")
    spec = (("top", "8", "single", "000000"),
            ("left", "0", "none", None),
            ("bottom", "8", "single", "000000"),
            ("right", "0", "none", None),
            ("insideH", "4", "single", "D0D0D0"),
            ("insideV", "0", "none", None))
    for edge, sz, val, color in spec:
        e = OxmlElement("w:" + edge)
        e.set(qn("w:val"), val)
        if val != "none":
            e.set(qn("w:sz"), sz)
            e.set(qn("w:space"), "0")
            e.set(qn("w:color"), color)
        borders.append(e)
    anchor = None
    for tag in ("w:shd", "w:tblLayout", "w:tblCellMar", "w:tblLook"):
        anchor = tblPr.find(qn(tag))
        if anchor is not None:
            break
    if anchor is not None:
        anchor.addprevious(borders)
    else:
        tblPr.append(borders)

    for cell in first_row.cells:
        tcPr = cell._tc.get_or_add_tcPr()
        bt = OxmlElement("w:tcBorders")
        b = OxmlElement("w:bottom")
        b.set(qn("w:val"), "single")
        b.set(qn("w:sz"), "4")
        b.set(qn("w:space"), "0")
        b.set(qn("w:color"), "000000")
        bt.append(b)
        tcPr.append(bt)


def set_cell_margins(tblPr):
    old = tblPr.find(qn("w:tblCellMar"))
    if old is not None:
        tblPr.remove(old)
    mar = OxmlElement("w:tblCellMar")
    for side, w in (("top", 40), ("left", 108), ("bottom", 40), ("right", 108)):
        e = OxmlElement("w:" + side)
        e.set(qn("w:w"), str(w))
        e.set(qn("w:type"), "dxa")
        mar.append(e)
    anchor = tblPr.find(qn("w:tblLook"))
    if anchor is not None:
        anchor.addprevious(mar)
    else:
        tblPr.append(mar)


for t in doc.tables:
    ncol = len(t.columns)
    hdr = header_texts(t)
    ws = widths_for(hdr, ncol)
    nrows = len(t.rows)
    fsize = 8.5 if nrows > 25 else 9.0

    t.autofit = False
    tblPr = t._tbl.tblPr
    tblW = tblPr.find(qn("w:tblW"))
    if tblW is None:
        tblW = OxmlElement("w:tblW")
        tblPr.append(tblW)
    tblW.set(qn("w:type"), "pct")
    tblW.set(qn("w:w"), "5000")

    for i, w in enumerate(ws):
        if i < ncol:
            t.columns[i].width = Cm(w)

    set_borders(tblPr, t.rows[0])
    set_cell_margins(tblPr)

    for ri, row in enumerate(t.rows):
        trPr = row._tr.get_or_add_trPr()
        cs = OxmlElement("w:cantSplit")
        trPr.append(cs)
        if ri == 0:
            th = OxmlElement("w:tblHeader")
            trPr.append(th)
        for ci, cell in enumerate(row.cells):
            cell.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
            for p in cell.paragraphs:
                pf = p.paragraph_format
                pf.first_line_indent = Pt(0)
                pf.left_indent = Pt(0)
                pf.right_indent = Pt(0)
                pf.line_spacing = 1.0
                pf.space_before = Pt(0)
                pf.space_after = Pt(0)
                p.alignment = (WD_ALIGN_PARAGRAPH.CENTER
                               if (ri == 0 or ci == 0)
                               else WD_ALIGN_PARAGRAPH.LEFT)
                for r in p.runs:
                    r.font.size = Pt(fsize)
                    r.font.bold = (ri == 0)
                    r.font.color.rgb = RGBColor(0, 0, 0)
                    set_rfonts(r._element.get_or_add_rPr(), EN, CN)

# ---------------------------------------------------------------- footer page number
for sec in doc.sections:
    f = sec.footer
    par = f.paragraphs[0] if f.paragraphs else f.add_paragraph()
    par.alignment = WD_ALIGN_PARAGRAPH.CENTER
    par.paragraph_format.first_line_indent = Pt(0)
    for r in list(par.runs):
        r._r.getparent().remove(r._r)
    run = par.add_run()
    run.font.size = Pt(9)
    run.font.name = EN
    set_rfonts(run._element.get_or_add_rPr(), EN, CN)
    fld_begin = OxmlElement("w:fldChar")
    fld_begin.set(qn("w:fldCharType"), "begin")
    instr = OxmlElement("w:instrText")
    instr.set(qn("xml:space"), "preserve")
    instr.text = " PAGE "
    fld_sep = OxmlElement("w:fldChar")
    fld_sep.set(qn("w:fldCharType"), "separate")
    txt = OxmlElement("w:t")
    txt.text = "1"
    fld_end = OxmlElement("w:fldChar")
    fld_end.set(qn("w:fldCharType"), "end")
    for el in (fld_begin, instr, fld_sep, txt, fld_end):
        run._r.append(el)

doc.save(str(OUT))
print("tables:", len(doc.tables))
print("paragraphs:", len(doc.paragraphs))
print("saved:", OUT, OUT.stat().st_size, "bytes")
