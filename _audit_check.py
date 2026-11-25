import re, os

ROOT = r"C:\proj2"
SKIP_DIRS = {".lake", ".git", "node_modules", ".idea", "archive"}
f = os.path.join(ROOT, r"OrderPreservingBijection\Exceptional\PrimeCountAsymptoticInProgressions.lean")
src = open(f, encoding="utf-8").read()

for name in ["PrimeCountAsymptoticInProgressions", "ShortIntervalImpliesProgressions", "SizeR", "MuConst"]:
    pat = re.compile(r"(?<![A-Za-z0-9_'!.])(" + re.escape(name) + r")(?![A-Za-z0-9_'!])")
    print(f"{name:40s} 本文件命中 = {len(pat.findall(src))}")

print("\n--- 全库计数（仅这几个名字，逐个扫）---")
texts = []
for dp, dns, fns in os.walk(ROOT):
    dns[:] = [d for d in dns if d not in SKIP_DIRS]
    for fn in fns:
        if fn.endswith(".lean") and not fn.startswith("_probe"):
            try:
                texts.append((os.path.relpath(os.path.join(dp, fn), ROOT), open(os.path.join(dp, fn), encoding="utf-8").read()))
            except Exception:
                pass
for name in ["PrimeCountAsymptoticInProgressions", "ShortIntervalImpliesProgressions", "SizeR"]:
    pat = re.compile(r"(?<![A-Za-z0-9_'!.])(" + re.escape(name) + r")(?![A-Za-z0-9_'!])")
    tot = 0; where = []
    for rel, t in texts:
        c = len(pat.findall(t))
        if c:
            tot += c; where.append((rel, c))
    print(f"{name:40s} 全库 = {tot}   {where}")
