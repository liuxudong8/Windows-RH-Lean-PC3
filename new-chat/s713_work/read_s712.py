# -*- coding: utf-8 -*-
import docx

p = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.12-fourierCos真定义与fourierCos_scale缩放律真证.docx"
d = docx.Document(p)
print("paras:", len(d.paragraphs), "tables:", len(d.tables))
for i, para in enumerate(d.paragraphs[:80]):
    st = para.style.name if para.style else "?"
    txt = para.text.strip()
    omath = len(para._p.findall(".//{http://schemas.openxmlformats.org/officeDocument/2006/math}oMath"))
    if txt or omath:
        print(i, "|", st, "| oMath:", omath, "|", txt[:90])
