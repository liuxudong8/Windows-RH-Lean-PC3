# -*- coding: utf-8 -*-
"""计算选定模块的传递 import 闭包大小（只看本地模块，Mathlib 单独计）。"""
import os, re, json, sys, collections

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
OUT = r"C:\proj2\_grh_iface"

IMP = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)")

targets = [
    "Statements",
    "Main",
    "Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime",
    "Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis",
    "Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible",
    "Formalism.LandauZeroFreeBounds.NoZeroComplex",
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder",
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0ZeroFreeRegionBound",
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiPowerSavingBound",
    "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiSqrtLogBound",
    "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion",
    "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus",
    "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaDirichletZerosRightHalf",
    "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow",
    "GroundTheory.GlobalFields.TateThesis.HeckeLFunction",
]

mod2file = {}
graph = collections.defaultdict(set)
mathlib_dep = collections.defaultdict(set)
nfiles = 0

for dirpath, _, filenames in os.walk(ROOT):
    for fn in filenames:
        if not fn.endswith(".lean"):
            continue
        fp = os.path.join(dirpath, fn)
        rel = os.path.relpath(fp, ROOT).replace("\\", "/")[:-5].replace("/", ".")
        mod2file[rel] = rel
        nfiles += 1
        deps = graph[rel]
        mldeps = mathlib_dep[rel]
        try:
            with open(fp, "r", encoding="utf-8", errors="ignore") as f:
                for line in f:
                    m = IMP.match(line)
                    if not m:
                        continue
                    d = m.group(1)
                    if d == "Mathlib" or d.startswith("Mathlib."):
                        mldeps.add(d)
                    else:
                        deps.add(d)
        except Exception:
            pass

def closure(root):
    seen = set()
    stack = [root]
    missing = set()
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        if m not in graph:
            missing.add(m)
            continue
        for d in graph[m]:
            if d not in seen:
                stack.append(d)
    ml = set()
    for m in seen:
        ml |= mathlib_dep.get(m, set())
    return seen, missing, ml

lines = []
data = {}
for t in targets:
    c, miss, ml = closure(t)
    data[t] = {"closure": len(c), "missing": sorted(miss)[:20], "mathlib_roots": len(ml),
               "mathlib_names": sorted(ml)[:15]}
    lines.append("%-95s closure=%6d  mathlib_imports=%4d  missing=%d" % (t, len(c), len(ml), len(miss)))

with open(os.path.join(OUT, "closures.json"), "w", encoding="utf-8") as f:
    json.dump({"files": nfiles, "mods": len(graph), "targets": data}, f, ensure_ascii=False, indent=1)
with open(os.path.join(OUT, "closures.txt"), "w", encoding="utf-8") as f:
    f.write("local modules: %d\n\n" % len(graph))
    f.write("\n".join(lines))
print("\n".join(lines))
