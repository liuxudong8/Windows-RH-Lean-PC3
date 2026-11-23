# -*- coding: utf-8 -*-
"""列出 ExceptionalDirichletZeroUniqueZeroFreeRegion 的传递闭包文件（本地模块）。"""
import os, re, collections

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
IMP = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)")

graph = collections.defaultdict(set)
ml = collections.defaultdict(list)
path = {}

for dp, _, fs in os.walk(ROOT):
    for fn in fs:
        if not fn.endswith(".lean"):
            continue
        fp = os.path.join(dp, fn)
        rel = os.path.relpath(fp, ROOT).replace(os.sep, "/")[:-5].replace("/", ".")
        path[rel] = fp
        with open(fp, encoding="utf-8", errors="ignore") as f:
            for line in f:
                m = IMP.match(line)
                if not m:
                    continue
                d = m.group(1)
                if d == "Mathlib" or d.startswith("Mathlib."):
                    ml[rel].append(d)
                else:
                    graph[rel].add(d)

t = ("Development.AbelianVarietyTheory.Proofs.GlobalInterpolation."
     "ExceptionalDirichletZeroUniqueZeroFreeRegion")

seen, st = set(), [t]
while st:
    m = st.pop()
    if m in seen:
        continue
    seen.add(m)
    st.extend([d for d in graph[m] if d not in seen])

order = sorted(seen)
for m in order:
    fp = path.get(m)
    sz = os.path.getsize(fp) if fp else -1
    print("%8d  %-4s  %s" % (sz, "ML" if ml.get(m) else "--", m))
print("total", len(seen))
if t in path:
    print("ROOTFILE", path[t])
