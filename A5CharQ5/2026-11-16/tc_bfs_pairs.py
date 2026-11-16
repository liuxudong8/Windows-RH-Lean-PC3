# -*- coding: utf-8 -*-
"""受限 BFS：为每个相邻 RHS 对找引理词路径（短词限深，防爆炸）。"""
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

def bfs(start, goal, max_depth, cap, seen_limit=300000):
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
        print(f"      {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'})")
        w = nw
    print(f"      goal={goal}  reached={w == goal}")

PAIRS = [
    ("b11 R0->R1", "bbababb", "aabaaababbb"),
    ("b11 R7->R8", "aaaabbaabbaaaa", "aaaabbaaaabba"),
    ("b11 R8->R9", "aaaabbaaaabba", "ababa"),
    ("b7 tail",   "abbaabaaaab", "abaabbaaaa"),
    ("a11 R3->R4(Bi)", "abaaabaaaabbaa", "abaaababaaaa"),
    ("a11 R4->R5(Ci)", "abaaababaaaa", "abbaabbaabaaaa"),
    ("a11 R5->R6(Di)", "abbaabbaabaaaa", "aaabaaaaaabbaabaaaa"),
    ("a11 R6->R7(Di2)", "aaabaaaaaabbaabaaaa", "aaabaaabaaabaaaa"),
    ("a11 R7->R8(Bi2)", "aaabaaabaaabaaaa", "bbaabbaabaaaabaaaa"),
    ("a11 R8->R9(Ci2)", "bbaabbaabaaaabaaaa", "baaaabaaabaaabaaaa"),
    ("a11 R9->R10(Gi)", "baaaabaaabaaabaaaa", "baaaabbbaaabbaaabaaaa"),
    ("a11 R10->R11(Ai)", "baaaabbbaaabbaaabaaaa", "baaaabbbaaaaabbaaaa"),
    ("a11 R11->R12(Ai2)", "baaaabbbaaaaabbaaaa", "baabaabbaaaa"),
]

for name, start, goal in PAIRS:
    print(f"==== {name}  {start}({len(start)}) -> {goal}({len(goal)})", flush=True)
    p = bfs(start, goal, max_depth=4, cap=26)
    if p is None:
        print("      NO PATH within depth4/cap26", flush=True)
    else:
        print(f"      steps={len(p)}", flush=True)
        fmt_path(start, goal, p)
