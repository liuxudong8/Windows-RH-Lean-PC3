# -*- coding: utf-8 -*-
import os, hashlib, json, sys, unicodedata

BASE = r"F:\F\BSD_GRH_RH\RH_14"
TAR = os.path.join(BASE, "lean.tar.gz")
SRC = os.path.join(BASE, "lean", "src")

PAPER_SHA = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"

# 1) hash
h = hashlib.sha256()
with open(TAR, "rb") as f:
    while True:
        b = f.read(1 << 24)
        if not b:
            break
        h.update(b)
digest = h.hexdigest()
print("SIZE", os.path.getsize(TAR))
print("SHA256", digest)
print("MATCH", digest == PAPER_SHA)

# 2) the 29 cited source files
cites = [
 ("1","Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean"),
 ("2","Formalism/ProductFormula/StatementOCCM.lean"),
 ("3","Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean"),
 ("4","Formalism/StatementCM.lean"),
 ("5","Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean"),
 ("6","Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean"),
 ("7","Formalism/RankGapBounds/MeanBoundSecondForm.lean"),
 ("8","Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean"),
 ("9","Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean"),
 ("10","Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean"),
 ("11","Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean"),
 ("12","Supplements/Kernels/MainTheorems.lean"),
 ("13","Development/AutomorphicArithmetic/AdelicQuotients/ThetaLiftLinear.lean"),
 ("14","Formalism/ThetaLiftIndependence/Statement.lean"),
 ("15","Formalism/SharpRestriction/GrowthBounds/CoarseMultiplicity/KeyMinorDvd.lean"),
 ("16","Development/AutomorphicSpectrum/Proofs/GeometryProofs/ChowlaSelbergPeriodStatement.lean"),
 ("17","Formalism/BehrendSets/StatementE.lean"),
 ("18","Formalism/ThickAverageLoss/PartnersToFactorsAt.lean"),
 ("19","Formalism/SharpRestriction/GlobalTheoremInputs.lean"),
 ("20","Formalism/CorankShare/StatementFR.lean"),
 ("21","Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementAB.lean"),
 ("22","Formalism/LocalRingCardinality/DataParams2.lean"),
 ("23","Formalism/SharpRestriction/GlobalSchurBounds/FlipTwoThree.lean"),
 ("24","Formalism/SharpRestriction/GlobalSchurBounds/IntegrableOfContinuousCircleMeasure.lean"),
 ("25","Formalism/HarderNarasimhan/StatementPl.lean"),
 ("26","Formalism/LocalRingCardinality/Params.lean"),
 ("27","Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean"),
 ("28","Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean"),
 ("29","Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean"),
]
miss = []
sizes = {}
for num, rel in cites:
    p = os.path.join(SRC, rel)
    ok = os.path.exists(p)
    sizes[num] = (ok, os.path.getsize(p) if ok else None)
    if not ok:
        miss.append((num, rel))
print("CITES_OK", sum(1 for v in sizes.values() if v[0]), "/", len(cites))
for num, rel in miss:
    print("  MISSING", num, rel)
print("CITE_SIZES", json.dumps({k: v[1] for k, v in sizes.items()}))

# 3) line count over all .lean under src
tot_lines = 0
tot_files = 0
maxf = ("", 0)
for root, dirs, files in os.walk(SRC):
    for fn in files:
        if not fn.endswith(".lean"):
            continue
        p = os.path.join(root, fn)
        tot_files += 1
        try:
            with open(p, "rb") as f:
                n = f.read().count(b"\n")
        except Exception as e:
            print("ERR", p, e); continue
        tot_lines += n
        if n > maxf[1]:
            maxf = (p, n)
print("LEAN_FILES", tot_files)
print("TOTAL_LINES", tot_lines)
print("BIGGEST", maxf[1], maxf[0])
