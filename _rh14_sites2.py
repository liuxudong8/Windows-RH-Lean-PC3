# -*- coding: utf-8 -*-
"""第 2 条（收尾）：只对真真空命题抓「承载名字」的消费点，并打印两处待查定义体。"""
import os, re

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
NAMES = ["trivialClassCondition", "TrivialRankCondition", "UnusedSlot55",
         "NoCondition", "TrivialCondition", "UnusedSlot72"]
KEYS = ("theorem", "lemma", "→", ":=", "have", "def ", "abbrev", ":")

def body(rel, ln, span=3):
    p = os.path.join(ROOT, rel.replace("/", os.sep))
    L = open(p, encoding="utf-8", errors="ignore").read().split("\n")
    return "\n      ".join(L[ln - 1: ln - 1 + span])

def main():
    print("=== 待查定义体 ===")
    print("[SettingHypotheses]", body("Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnramifiedNoJump.lean", 132))
    print("[SetHyp]", body("Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean", 327))
    print()
    print("=== 承载消费点（只看签名 / 结构字段 / 目标）===")
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, ROOT).replace(os.sep, "/")
            try:
                t = open(p, encoding="utf-8", errors="ignore").read()
            except Exception:
                continue
            for i, s in enumerate(t.split("\n"), 1):
                if not any(n in s for n in NAMES):
                    continue
                if re.search(r"\bdef\b|\babbrev\b", s) and ":= True" in s:
                    continue                      # 定义本体，跳过
                if s.strip().startswith(("--", "/-", "*")):
                    continue
                if not any(k in s for k in KEYS):
                    continue
                print("%-72s :%-5d %s" % (rel, i, s.strip()[:230]))

if __name__ == "__main__":
    main()
