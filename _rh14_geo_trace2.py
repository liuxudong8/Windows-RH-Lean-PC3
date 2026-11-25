# -*- coding: utf-8 -*-
"""精确追踪：Published.GeometricLemma（类型）与 siegelEisensteinSimplePole（字段/定理）。"""
import os, re

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
ROOTFILE = os.path.join(ROOT, "Development", "AutomorphicArithmetic", "ThetaCorrespondence",
                        "ThetaPairLifts", "ThirdPlaceSeries", "EveryCharacterOfLiteratureOfVWin.lean")

DECL = re.compile(r"^[ \t]*(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|instance|class)\s+([^\s:({\[]+)")
GEOTYPE = re.compile(r"GeometricLemma(?![A-Za-z0-9_'])")
FIELD = re.compile(r"siegelEisensteinSimplePole")

def root_names():
    L = open(ROOTFILE, encoding="utf-8", errors="ignore").read().split("\n")
    idx = next(i for i, s in enumerate(L)
               if s.lstrip().startswith("theorem") and "every_character_of_literature_of_vWin" in s)
    body = "\n".join(L[idx: idx + 4])
    return idx + 1, set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body))

def main():
    rl, rnames = root_names()
    print("root @", rl, " body token 数:", len(rnames))
    for pat, tag in ((GEOTYPE, "GEOTYPE"), (FIELD, "FIELD")):
        print("\n=== %s ===" % tag)
        for dp, dn, fn in os.walk(ROOT):
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                try:
                    t = open(p, encoding="utf-8", errors="ignore").read()
                except Exception:
                    continue
                if pat.pattern.split("(?")[0].split("(")[0] not in t and not pat.search(t):
                    continue
                decls = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(t)]
                for m in pat.finditer(t):
                    ln = t.count("\n", 0, m.start()) + 1
                    d = None
                    for st, kind, nm in decls:
                        if st < m.start():
                            d = (kind, nm)
                        else:
                            break
                    seg = t[max(0, m.start() - 100): m.start() + 140].replace("\n", " ")
                    inroot = "  <ROOT-BODY>" if (d and d[1] in rnames) else ""
                    print("%-64s :%-5d %-28s%s | %s" % (
                        os.path.relpath(p, ROOT).replace(os.sep, "/"), ln,
                        (d[1] if d else "?"), inroot, seg.strip()[:150]))

if __name__ == "__main__":
    main()
