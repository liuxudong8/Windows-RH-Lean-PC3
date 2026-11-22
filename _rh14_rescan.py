# -*- coding: utf-8 -*-
"""对完整 175,187 个 .lean 重跑静态审计，并统计声明总数。"""
import os, re, collections, json

SRC = r"F:\F\BSD_GRH_RH\RH_14\lean\src"

decl_re = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque|example)\b")
kw = ["axiom", "constant", "opaque", "unsafe", "sorry", "admit", "native_decide",
      "partial def", "partial_def", "implemented_by", "extern"]

files = 0
lines = 0
cnt = collections.Counter()
decls = collections.Counter()
hits = {k: [] for k in kw}
for root, dirs, fs in os.walk(SRC):
    for fn in fs:
        if not fn.endswith(".lean"):
            continue
        p = os.path.join(root, fn)
        files += 1
        try:
            body = open(p, encoding="utf-8", errors="ignore").read()
        except Exception as e:
            print("ERR", p, e)
            continue
        n = body.count("\n")
        lines += n
        for i, line in enumerate(body.split("\n"), 1):
            s = line.lstrip()
            if s.startswith("--") or s.startswith("/-"):
                continue
            m = decl_re.match(line)
            if m:
                decls[m.group(1)] += 1
            for k in kw:
                if k in ("axiom", "constant", "opaque", "unsafe", "partial def"):
                    if not m or m.group(1) not in ("axiom", "opaque"):
                        if k in ("axiom", "constant", "opaque"):
                            if not (m and m.group(1) == k):
                                continue
                    pass
                if re.search(r"(?<![A-Za-z0-9_'])(" + k.replace(" ", r"\s+") + r")(?![A-Za-z0-9_'])", line):
                    cnt[k] += 1
                    if len(hits[k]) < 40:
                        hits[k].append(f"{os.path.relpath(p, SRC)}:{i}: {s[:110]}")

print("FILES", files)
print("LINES", lines)
print("DECLS", dict(decls), "TOTAL", sum(decls.values()))
print("KW_COUNTS", dict(cnt))
for k in kw:
    if hits[k]:
        print("\n== " + k + " ==")
        for h in hits[k][:12]:
            print("  ", h)
