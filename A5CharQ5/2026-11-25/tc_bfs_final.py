# -*- coding: utf-8 -*-
"""因子表 → 自动生成词 → 邻对受限 BFS（真实引理词路径）。"""
from collections import deque

RULES = [
    ("baa", "aaabb"),          # 0 b_a2_comm
    ("aab", "bbaaa"),          # 1 a2_b_comm
    ("aabaa", "bb"),           # 2 a2_b_a2_eq_b2
    ("baab", "aaa"),           # 3 b_a2_b_eq_a3
    ("aba", "aaaabbaaaa"),     # 4 a_b_a_eq_a4_b2_a4
    ("bbaabb", "baaab"),       # 5 b2_a2_b2_eq_b_a3_b
    ("bbbb", "b"),             # 6 pB_pow_four
    ("baaaab", "aaabaaa"),     # 7 hbab4
    ("bba", "aabaaa"),         # 8 hba
]

def word_of(factors):
    out = []
    for c, k in factors:
        out.append(c * k)
    return "".join(out)

def rewrites(w, cap):
    out = []
    for idx, (l, r) in enumerate(RULES):
        for d, (pat, rep) in ((1, (l, r)), (-1, (r, l))):
            start = 0
            while True:
                p = w.find(pat, start)
                if p < 0:
                    break
                nw = w[:p] + rep + w[p+len(pat):]
                if len(nw) <= cap:
                    out.append((p, idx, d, nw))
                start = p + 1
    return out

def bfs(start, goal, max_depth, cap, seen_limit=400000):
    if start == goal:
        return []
    q = deque([(start, [])])
    seen = {start}
    while q:
        w, path = q.popleft()
        if len(path) >= max_depth:
            continue
        for pos, ridx, d, nw in rewrites(w, cap):
            if nw in seen:
                continue
            seen.add(nw)
            np = path + [(w, pos, ridx, d, nw)]
            if nw == goal:
                return np
            q.append((nw, np))
            if len(seen) > seen_limit:
                return None
    return None

def fmt_path(start, goal, path):
    w = start
    for (w0, pos, ridx, d, nw) in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        print(f"      {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'})", flush=True)
        w = nw
    print(f"      goal={goal}  reached={w == goal}", flush=True)

A = ('a', 1)
A2, A3, A4 = ('a',2), ('a',3), ('a',4)
B = ('b', 1)
B2 = ('b', 2)

# ---- a_11 外链 RHS 因子表 ----
a11 = {
    "R0":  [A,B,A,B,A,B,B],
    "R1":  [A,B,A,B,A3,B,A2],
    "R2":  [A,B,A,B,B,A2,B2,A2],
    "R3":  [A,B,A3,B,A4,B2,A2],
    "R4":  [A,B,A3,B,A,B,A4],
    "R5":  [A,B,B,A2,B2,A,B,A4],
    "R6":  [A3,B,A4,B2,A,B,A4],
    "R7":  [A3,B,A,B,A3,B,A4],
    "R8":  [B,A2,B2,A,B,A3,B,A4],
    "R9":  [B,A4,B,A3,B,A3,B,A4],
    "R10": [B,A4,B,B,A2,B2,A3,B,A4],
    "R11": [B,A4,B2,A4,B2,A4],
    "R12": [B,A,B,A,B2,A4],
}
# ---- b_11 外链 RHS 因子表 ----
b11 = {
    "R0":  [B,B,A,B,A,B,B],
    "R1":  [A2,B,A3,B,A,B2],
    "R2":  [A2,B,A3,B,A3,B,A2],
    "R3":  [A2,B2,A2,B2,A3,B,A2],
    "R4":  [A2,B2,A4,B2,A2],
    "R5":  [A4,B,A,B2,A2],
    "R6":  [A4,B,A3,B,A4],
    "R7":  [A4,B2,A2,B2,A4],
    "R8":  [A4,B2,A4,B,A],
    "R9":  [A,B,A,B,A],
}
# ---- b_7 外链 RHS 因子表 ----
b7 = {
    "R0":  [B,A,B,A,B],
    "R1":  [B,A4,B2,A4,B],
    "R2":  [B,A2,B2,A3,B,A4,B],
    "R3":  [A3,B,A3,B,A4,B],
    "R4":  [A,B,B,A,B,A4,B],
    "R5":  [A,B,B,A,A2,B2,A3],
    "R6":  [A,B,B,A4,B,A3],
    "R7":  [A,B,B,A2,B2,A],
    "R8":  [A,B,A3,B,A],
    "R9":  [A,B,A,B2,A4],
}

def chain(name, tab, keys, max_depth=5, cap=26):
    print(f"==== {name}", flush=True)
    ws = {k: word_of(tab[k]) for k in keys}
    for k in keys:
        print(f"  {k}: {ws[k]} ({len(ws[k])})", flush=True)
    for i in range(len(keys) - 1):
        k0, k1 = keys[i], keys[i+1]
        print(f"  -- {k0}->{k1}: {ws[k0]} -> {ws[k1]}", flush=True)
        p = bfs(ws[k0], ws[k1], max_depth=max_depth, cap=cap)
        if p is None:
            print("     NO PATH", flush=True)
        else:
            print(f"     steps={len(p)}", flush=True)
            fmt_path(ws[k0], ws[k1], p)

chain("a_11", a11, ["R0","R1","R2","R3","R4","R5","R6","R7","R8","R9","R10","R11","R12"])
chain("b_11", b11, ["R0","R1","R2","R3","R4","R5","R6","R7","R8","R9"])
chain("b_7", b7, ["R0","R1","R2","R3","R4"])
print("==== b_7 tail R4->R9 (整段重设计)", flush=True)
ws4, ws9 = word_of(b7["R4"]), word_of(b7["R9"])
print(f"  R4={ws4}  R9={ws9}", flush=True)
p = bfs(ws4, ws9, max_depth=7, cap=28)
if p is None:
    print("  NO PATH", flush=True)
else:
    print(f"  steps={len(p)}", flush=True)
    fmt_path(ws4, ws9, p)
