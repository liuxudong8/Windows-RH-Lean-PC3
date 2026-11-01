# -*- coding: utf-8 -*-
import docx

p = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S7.12-fourierCos真定义与fourierCos_scale缩放律真证.docx"
d = docx.Document(p)
import re
for i, para in enumerate(d.paragraphs):
    xml = para._p.xml
    has_math = "oMath" in xml
    has_para = "oMathPara" in xml
    txt = para.text.strip()
    if has_math or has_para:
        print(i, "| oMathPara:", has_para, "|", txt[:120])
print("---table---")
for t in d.tables:
    for r in t.rows[:15]:
        print(" | ".join(c.text.strip()[:40] for c in r.cells))
