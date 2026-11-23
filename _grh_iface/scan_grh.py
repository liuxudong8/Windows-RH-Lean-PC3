# -*- coding: utf-8 -*-
"""在 RH_14 归档树中定位 GRH / Dirichlet-L / 零点计数 的语句入口。
单次遍历全树，用组合正则，输出 JSON + 可读摘要。"""
import os, re, json, collections, time

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
OUT = r"C:\proj2\_grh_iface"
KEY = "grh_full"

PAT = re.compile(
    r"(?P<grh_full>GeneralizedRiemannHypothesis)"
    r"|(?P<rh>\bRiemannHypothesis\b)"
    r"|(?P<grh_abbr>\bGRH\b)"
    r"|(?P<dchar>DirichletCharacter|Dirichlet\.Character)"
    r"|(?P<chi_field>IsChiField|\bchC\b|\bChiField\b)"
    r"|(?P<data_params>DataParams)"
    r"|(?P<zero_count>zeroCount|zerosUpTo|ZerosUpTo|CountingFunction|countZeros|zerosIn|ZeroCount)"
    r"|(?P<rvm>von\s?Mangoldt|RvM|argCount)"
    r"|(?P<dlfun>dirichletL|DirichletL|\bLFunction\b)"
    r"|(?P<legendre>Legendre|legendre)"
    r"|(?P<conductor>\bconductor\b)"
    r"|(?P<zero_free>zeroFree|ZeroFree|zero_free|ZeroZone)"
    r"|(?P<growth>GrowthBound|GrowthSizeBound|SizeWindow)"
)

MAX_PER_KEY = 600

hits = collections.defaultdict(list)
counts = collections.Counter()
filecounts = collections.Counter()
nfiles = 0
nlines = 0
t0 = time.time()

for dirpath, _, filenames in os.walk(ROOT):
    for fn in filenames:
        if not fn.endswith(".lean"):
            continue
        nfiles += 1
        fp = os.path.join(dirpath, fn)
        rel = os.path.relpath(fp, ROOT).replace("\\", "/")
        try:
            with open(fp, "r", encoding="utf-8", errors="ignore") as f:
                for ln, line in enumerate(f, 1):
                    nlines += 1
                    if ("Hypothesis" not in line and "GRH" not in line and "dirichlet" not in line
                            and "Dirichlet" not in line and "ChiField" not in line and "chC" not in line
                            and "DataParams" not in line and "zero" not in line and "Zero" not in line
                            and "RvM" not in line and "Mangoldt" not in line and "Legendre" not in line
                            and "legendre" not in line and "conductor" not in line and "Growth" not in line
                            and "Window" not in line):
                        continue
                    m = PAT.search(line)
                    if not m:
                        continue
                    k = m.lastgroup
                    counts[k] += 1
                    filecounts[(k, rel)] += 1
                    if len(hits[k]) < MAX_PER_KEY:
                        hits[k].append([rel, ln, line.strip()[:220]])
        except Exception as e:
            hits["error"].append([rel, 0, str(e)[:120]])

with open(os.path.join(OUT, "scan_hits.json"), "w", encoding="utf-8") as f:
    json.dump({"files": nfiles, "lines": nlines, "secs": round(time.time() - t0, 1),
               "counts": counts, "hits": hits}, f, ensure_ascii=False, indent=1)

with open(os.path.join(OUT, "scan_summary.txt"), "w", encoding="utf-8") as f:
    f.write("FILES %d  LINES %d  SECS %.1f\n\n" % (nfiles, nlines, time.time() - t0))
    for k in sorted(counts, key=lambda x: -counts[x]):
        f.write("== %s : %d hits in %d files ==\n" % (k, counts[k], sum(1 for (kk, _) in filecounts if kk == k)))
        top = sorted([(c, r) for (kk, r), c in filecounts.items() if kk == k], reverse=True)[:12]
        for c, r in top:
            f.write("   %5d  %s\n" % (c, r))
        f.write("\n")

print("DONE files=%d lines=%d secs=%.1f" % (nfiles, nlines, time.time() - t0))
for k in sorted(counts, key=lambda x: -counts[x]):
    print("%-12s %6d" % (k, counts[k]))
