# -*- coding: utf-8 -*-
"""从 nonempty_hyps_definite_side_of_closed_bound 做 decl 级前向可达性，找 theta_tower_compatibility。"""
import os, re, sys
from collections import deque

ROOT = r"F:\F\BSD_GRH_RH\RH_14\lean\src"
SEED = "nonempty_hyps_definite_side_of_closed_bound"
TARGETS = ["theta_tower_compatibility", "doublingMethod", "HeckeFormAnisotropicOfRallisBottom",
           "RallisInnerProductBottomNormEq", "RealFunctionalsSeparateOfHypothesis"]
DEPTH = 4

DECL = re.compile(r"^([ \t]*)(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+|scoped\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|opaque)\s+([A-Za-z_][A-Za-z0-9_.']*)")
STOP = re.compile(r"^[ \t]*(end|namespace|section|open|variable|import|attribute|set_option|@)\b")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def short(n):
    return n.split(".")[-1]

def build_index():
    idx = {}
    files = []
    for dp, dn, fn in os.walk(ROOT):
        for f in fn:
            if f.endswith(".lean"):
                files.append(os.path.join(dp, f))
    print("[index] files:", len(files), flush=True)
    for p in files:
        try:
            t = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        L = t.split("\n")
        for i, s in enumerate(L):
            m = DECL.match(s)
            if not m:
                continue
            nm = m.group(3)
            idx.setdefault(short(nm), []).append((p, i))
    print("[index] decls:", sum(len(v) for v in idx.values()), "names:", len(idx), flush=True)
    return idx

def body_of(p, i):
    L = open(p, encoding="utf-8", errors="ignore").read().split("\n")
    out = [L[i]]
    j = i + 1
    while j < len(L):
        s = L[j]
        if DECL.match(s) or STOP.match(s):
            break
        out.append(s)
        j += 1
    return "\n".join(out), L[i]

def main():
    idx = build_index()
    seen = {SEED}
    q = deque([(SEED, ())])
    hit = []
    while q:
        name, path = q.popleft()
        if len(path) >= DEPTH:
            continue
        for p, i in idx.get(name, [])[:2]:
            body, head = body_of(p, i)
            toks = set(IDENT.findall(body))
            for t in TARGETS:
                if t in toks or t in body:
                    hit.append((t, path + (name,), os.path.relpath(p, ROOT).replace(os.sep, "/"), i + 1))
            for t in toks:
                if t in idx and t not in seen and not t.startswith(("Nat", "Int", "List", "Option", "Set", "Finset", "Real")):
                    if short(t) in idx:
                        seen.add(short(t))
                        q.append((short(t), path + (name,)))
    print("\n=== 命中 ===")
    if not hit:
        print("深度 %d 内未命中任何目标的声明名。" % DEPTH)
    for t, path, rel, ln in hit:
        print("TARGET=%s\n  %s:%d\n  path: %s" % (t, rel, ln, " -> ".join(path)))
    print("\n=== 已展开 decl 数:", len(seen))

if __name__ == "__main__":
    main()
