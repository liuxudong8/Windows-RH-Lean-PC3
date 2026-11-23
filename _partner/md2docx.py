# -*- coding: utf-8 -*-
"""极简 markdown -> docx（支持 #/##/### 标题、表格、无序/有序列表、引用、代码块、粗体与行内代码）"""
import re, sys, os
from docx import Document
from docx.shared import Pt, RGBColor, Cm
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml.ns import qn

BOLD = re.compile(r"\*\*(.+?)\*\*")
CODE = re.compile(r"`([^`]+)`")


def set_cn_font(doc):
    style = doc.styles["Normal"]
    style.font.name = "Calibri"
    style.font.size = Pt(10.5)
    style.element.rPr.rFonts.set(qn("w:eastAsia"), "宋体")


def add_runs(p, text, size=None, color=None):
    """按 **粗体** 与 `code` 切分写入 run"""
    pos = 0
    tokens = []
    for m in BOLD.finditer(text):
        if m.start() > pos:
            tokens.append((text[pos:m.start()], False, False))
        tokens.append((m.group(1), True, False))
        pos = m.end()
    if pos < len(text):
        tokens.append((text[pos:], False, False))
    # 行内代码在非粗体片段里再切一次
    final = []
    for seg, bold, _ in tokens:
        if bold:
            final.append((seg, True, False))
            continue
        p2 = 0
        for m in CODE.finditer(seg):
            if m.start() > p2:
                final.append((seg[p2:m.start()], False, False))
            final.append((m.group(1), False, True))
            p2 = m.end()
        if p2 < len(seg):
            final.append((seg[p2:], False, False))
    for seg, bold, code in final:
        if not seg:
            continue
        r = p.add_run(seg)
        r.bold = bold
        if code:
            r.font.name = "Consolas"
            r.font.size = Pt(9)
    if size:
        for r in p.runs:
            r.font.size = size
    if color:
        for r in p.runs:
            r.font.color.rgb = color


def is_table_sep(line):
    return bool(re.match(r"^\|[\s:|-]+\|$", line.strip())) and "-" in line


def split_row(line):
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|"):
        s = s[:-1]
    return [c.strip() for c in s.split("|")]


def convert(md_path, docx_path):
    with open(md_path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    doc = Document()
    set_cn_font(doc)
    for s in doc.sections:
        s.left_margin = Cm(2.2); s.right_margin = Cm(2.2)
        s.top_margin = Cm(2.0); s.bottom_margin = Cm(2.0)

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        s = line.strip()

        # 代码块
        if s.startswith("```"):
            i += 1
            buf = []
            while i < n and not lines[i].strip().startswith("```"):
                buf.append(lines[i]); i += 1
            i += 1
            p = doc.add_paragraph()
            r = p.add_run("\n".join(buf))
            r.font.name = "Consolas"; r.font.size = Pt(9)
            p.paragraph_format.space_before = Pt(4)
            p.paragraph_format.space_after = Pt(4)
            continue

        # 表格
        if s.startswith("|") and i + 1 < n and is_table_sep(lines[i + 1]):
            header = split_row(lines[i])
            i += 2
            rows = []
            while i < n and lines[i].strip().startswith("|"):
                rows.append(split_row(lines[i])); i += 1
            t = doc.add_table(rows=1, cols=len(header))
            t.style = "Table Grid"
            for j, h in enumerate(header):
                cell = t.rows[0].cells[j]
                cell.text = ""
                p = cell.paragraphs[0]
                add_runs(p, h, size=Pt(9.5))
                for r in p.runs:
                    r.bold = True
            for row in rows:
                cells = t.add_row().cells
                for j in range(min(len(row), len(header))):
                    cells[j].text = ""
                    add_runs(cells[j].paragraphs[0], row[j], size=Pt(9.5))
            doc.add_paragraph()
            continue

        if not s:
            i += 1
            continue

        if s.startswith("---") and set(s) <= {"-"}:
            i += 1
            continue

        # 标题
        m = re.match(r"^(#{1,4})\s+(.*)$", s)
        if m:
            level = len(m.group(1))
            text = m.group(2)
            if level == 1:
                p = doc.add_paragraph()
                p.alignment = WD_ALIGN_PARAGRAPH.CENTER
                add_runs(p, text, size=Pt(20), color=RGBColor(0x1F, 0x38, 0x64))
                for r in p.runs:
                    r.bold = True
            elif level == 2:
                p = doc.add_paragraph()
                add_runs(p, text, size=Pt(14), color=RGBColor(0x1F, 0x38, 0x64))
                for r in p.runs:
                    r.bold = True
            else:
                p = doc.add_paragraph()
                add_runs(p, text, size=Pt(11.5), color=RGBColor(0x2E, 0x5C, 0x8A))
                for r in p.runs:
                    r.bold = True
            p.paragraph_format.space_before = Pt(10)
            p.paragraph_format.space_after = Pt(4)
            i += 1
            continue

        # 引用
        if s.startswith(">"):
            p = doc.add_paragraph()
            add_runs(p, s.lstrip("> ").strip(), size=Pt(9.5))
            for r in p.runs:
                r.italic = True
            p.paragraph_format.left_indent = Cm(0.6)
            i += 1
            continue

        # 无序列表
        mb = re.match(r"^[-*]\s+(.*)$", s)
        if mb:
            p = doc.add_paragraph(style="List Bullet")
            add_runs(p, mb.group(1))
            i += 1
            continue

        # 有序列表
        mo = re.match(r"^(\d+)\.\s+(.*)$", s)
        if mo:
            p = doc.add_paragraph(style="List Number")
            add_runs(p, mo.group(2))
            i += 1
            continue

        # 普通段落
        p = doc.add_paragraph()
        add_runs(p, s)
        p.paragraph_format.space_after = Pt(6)
        i += 1

    doc.save(docx_path)
    return os.path.getsize(docx_path)


if __name__ == "__main__":
    for src in sys.argv[1:]:
        dst = os.path.splitext(src)[0] + ".docx"
        size = convert(src, dst)
        print("OK", os.path.basename(dst), size, "B")
