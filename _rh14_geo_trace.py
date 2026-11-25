# -*- coding: utf-8 -*-
"""追踪 GlobalTheory.Published.GeometricLemma 的消费链，并核对是否进 287 槽。"""
import os, re

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
ROOTFILE = os.path.join(ROOT, "Development", "AutomorphicArithmetic", "ThetaCorrespondence",
                        "ThetaPairLifts", "ThirdPlaceSeries", "EveryCharacterOfLiteratureOfVWin.lean")

DECL = re.compile(r"^[ \t]*(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|instance|class)\s+([^\s:({\[]+)")

def line_of(t, pos):
    return t.count("\n", 0, pos) + 1

def root_body():
    t = open(ROOTFILE, encoding="utf-8", errors="ignore").read()
    L = t.split("\n")
    # 定位 root theorem 起的证明体
    idx = next(i for i, s in enumerate(L)
               if s.lstrip().startswith("theorem") and "every_character_of_literature_of_vWin" in s)
    body = "\n".join(L[idx: idx + 40])
    names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", body))
    return idx + 1, body, names

def consumers():
    hits = {}
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            try:
                t = open(p, encoding="utf-8", errors="ignore").read()
            except Exception:
                continue
            if "GeometricLemma" not in t:
                continue
            pos = 0
            decls = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(t)]
            for m in re.finditer(r"GeometricLemma", t):
                ln = line_of(t, m.start())
                seg = t[max(0, m.start() - 120): m.start() + 120].replace("\n", " ")
                d = None
                for st, kind, nm in decls:
                    if st < m.start():
                        d = (kind, nm, line_of(t, st))
                    else:
                        break
                hits.setdefault((os.path.relpath(p, ROOT).replace(os.sep, "/"), ln), (d, seg.strip()[:200]))
    return hits

def main():
    rl, body, rootnames = root_body()
    print("=== root 定位：EveryCharacterOfLiteratureOfVWin.lean:%d ===" % rl)
    for i, s in enumerate(body.split("\n")[:14], rl):
        print("%5d | %s" % (i, s[:200]))
    print()
    print("=== GeometricLemma 出现点（decl 上下文 + 片段）===")
    hits = consumers()
    for (rel, ln), (d, seg) in sorted(hits.items()):
        ctx = "%s %s @%s" % d if d else "?"
        print("%-70s :%-5d [%s]  %s" % (rel, ln, ctx, seg))
    print()
    print("=== 与 root 体的交集 ===")
    declnames = {d[1] for d, _ in hits.values() if d}
    inter = declnames & rootnames
    print("消费方 decl 名：", sorted(declnames)[:40], "…共", len(declnames))
    print("与 root 体直接同名的：", sorted(inter))

if __name__ == "__main__":
    main()
