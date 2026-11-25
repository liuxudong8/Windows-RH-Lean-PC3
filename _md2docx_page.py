# -*- coding: utf-8 -*-
"""把一页纸 md 转成单页 docx（A4，窄边距，8.5pt）。用法：python _md2docx_page.py <src.md> <dst.docx>"""
import sys
import re
from docx import Document
from docx.shared import Pt, Cm
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml.ns import qn

SRC = (sys.argv[1] if len(sys.argv)>1 else r"C:\proj2\_partner\03_RH14审计一页纸.md")
DST = (sys.argv[2] if len(sys.argv)>2 else r"C:\proj2\_partner\03_RH14审计一页纸.docx")

doc = Document()
sec = doc.sections[0]
sec.page_width, sec.page_height = Cm(21.0), Cm(29.7)
for a in ("top_margin", "bottom_margin", "left_margin", "right_margin"):
    setattr(sec, a, Cm(1.4))

st = doc.styles["Normal"]
st.font.name = "宋体"
st.font.size = Pt(8.5)
st.element.rPr.rFonts.set(qn("w:eastAsia"), "宋体")
st.paragraph_format.space_after = Pt(1)
st.paragraph_format.line_spacing = 1.0

def para(text, bold=False, size=None, align=None, space_before=0):
    p = doc.add_paragraph()
    p.paragraph_format.space_before = Pt(space_before)
    if align:
        p.alignment = align
    r = p.add_run(text)
    r.bold = bold
    if size:
        r.font.size = Pt(size)
    return p

def rich(text, size=9.5):
    """把 `code` 渲染成分等宽、把 **bold** 渲染成粗体。"""
    p = doc.add_paragraph()
    p.paragraph_format.space_before = Pt(0)
    for tok in re.split(r"(`[^`]*`|\*\*[^*]*\*\*)", text):
        if not tok:
            continue
        if tok.startswith("`") and tok.endswith("`"):
            r = p.add_run(tok[1:-1])
            r.font.name = "Consolas"
            r.font.size = Pt(size - 1)
            r.element.rPr.rFonts.set(qn("w:eastAsia"), "Consolas")
        elif tok.startswith("**") and tok.endswith("**"):
            r = p.add_run(tok[2:-2])
            r.bold = True
            r.font.size = Pt(size)
        else:
            r = p.add_run(tok)
            r.font.size = Pt(size)
    return p

lines = open(SRC, encoding="utf-8").read().split("\n")
i = 0
while i < len(lines):
    s = lines[i].rstrip()
    if not s or set(s) <= {"-"}:
        i += 1
        continue
    if s.startswith("# "):
        para(s[2:], bold=True, size=13, align=WD_ALIGN_PARAGRAPH.CENTER)
    elif s.startswith("## "):
        para(s[3:], bold=True, size=10, space_before=3)
    elif s.startswith("|"):
        rows = []
        while i < len(lines) and lines[i].startswith("|"):
            cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
            if not set("".join(cells)) <= {"-", ":"}:
                rows.append(cells)
            i += 1
        if rows:
            t = doc.add_table(rows=len(rows), cols=len(rows[0]))
            t.style = "Table Grid"
            for r_i, cells in enumerate(rows):
                for c_i, c in enumerate(cells):
                    cell = t.cell(r_i, c_i)
                    cell.text = ""
                    p = cell.paragraphs[0]
                    p.paragraph_format.space_after = Pt(0)
                    run = p.add_run(c.strip("`"))
                    run.font.size = Pt(7.5)
                    run.bold = r_i == 0
            para("", size=4)
        continue
    else:
        rich(s)
    i += 1

doc.save(DST)
print("saved:", DST)


