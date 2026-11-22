# -*- coding: utf-8 -*-
import os, re, json, collections

SRC = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
toks = json.load(open(r"C:\proj2\_alpoge\lean_tokens.json", encoding="utf-8"))
skip = {"LeAn", "Lean", "PAGE"}
toks = [t for t in toks if t not in skip and not t.endswith(".lean") and not re.match(r"^III\.", t)]
print("tokens to test:", len(toks))

# 文件名核对
files = [l.strip() for l in open(r"C:\proj2\_alpoge\cited_filenames.txt", encoding="utf-8") if l.strip()]
index = {}
for root, dirs, fs in os.walk(SRC):
    for fn in fs:
        if fn.endswith(".lean"):
            index.setdefault(fn, []).append(os.path.join(root, fn))
miss_files = [f for f in files if f not in index]
print("CITED_FILENAMES", len(files), "MISSING", len(miss_files), miss_files[:10])

# 一次性扫全库
alt = "|".join(re.escape(t) for t in sorted(toks, key=len, reverse=True))
pat = re.compile(r"(?<![A-Za-z0-9_'.])(" + alt + r")(?![A-Za-z0-9_'])")
found = collections.Counter()
firsthit = {}
nfiles = 0
for root, dirs, fs in os.walk(SRC):
    for fn in fs:
        if not fn.endswith(".lean"):
            continue
        p = os.path.join(root, fn)
        try:
            body = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        nfiles += 1
        for m in pat.finditer(body):
            t = m.group(1)
            found[t] += 1
            if t not in firsthit:
                line = body.count("\n", 0, m.start()) + 1
                firsthit[t] = f"{os.path.relpath(p, SRC)}:{line}"
print("scanned files", nfiles)
nf = [t for t in toks if t not in found]
print("TOKENS_FOUND", len(toks) - len(nf), "/", len(toks))
print("NOT_FOUND:", nf)
json.dump({"counts": dict(found), "first": firsthit, "notfound": nf},
          open(r"C:\proj2\_alpoge\token_check.json", "w"), ensure_ascii=False, indent=1)
