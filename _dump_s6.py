import zipfile, re, html, sys, io

path = r"C:\Users\shtcl\Doubao\chats\2026-10-16\document\d1\路2攻防XLII-S6-λ_eff≤1卡点解除-λ≤1-2最优核族的0.6725严格化判定.docx"
kw = sys.argv[1:] or ["C_MT", "cot"]

z = zipfile.ZipFile(path)
xml = z.read("word/document.xml").decode("utf-8", "ignore")
paras = xml.split("</w:p>")
texts = []
for p in paras:
    parts = re.findall(r"<(?:w|m):t[^>]*>(.*?)</(?:w|m):t>", p, flags=re.S)
    s = "".join(parts)
    s = html.unescape(s)
    s = re.sub(r"\s+", " ", s).strip()
    texts.append(s)

printed = set()
for i, s in enumerate(texts):
    if any(k in s for k in kw):
        for j in range(max(0, i - 2), min(len(texts), i + 3)):
            if j in printed:
                continue
            printed.add(j)
            t = texts[j]
            if t:
                print(f"[{j}] {t}")
        print("-" * 70)
