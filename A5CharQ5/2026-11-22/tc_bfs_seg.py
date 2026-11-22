# -*- coding: utf-8 -*-
"""段级 BFS：对 a_11 / b_11 / b_7 的每个坏段，从段 L0 词到段 R 词搜最短引理路径。"""
from collections import deque

RULES = [
    ("baa", "aaabb"),          # 0 b a^2 <-> a^3 b^2
    ("aab", "bbaaa"),          # 1 a^2 b <-> b^2 a^3
    ("aabaa", "bb"),           # 2 a^2 b a^2 <-> b^2
    ("baab", "aaa"),           # 3 b a^2 b <-> a^3
    ("aba", "aaaabbaaaa"),     # 4 a b a <-> a^4 b^2 a^4
    ("bbaabb", "baaab"),       # 5 b^2 a^2 b^2 <-> b a^3 b
    ("bbbb", "b"),             # 6 b^4 <-> b
    ("baaaab", "aaabaaa"),     # 7 b a^4 b <-> a^3 b a^3
    ("bba", "aabaaa"),         # 8 b^2 a <-> a^2 b a^3
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

def bfs(start, goal, max_depth=25, cap=60):
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
    return None, len(seen)

def show_path(path, start, goal):
    w = start
    print("start:", start, "len", len(start))
    for (w0, pos, ridx, d, nw) in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        print(f"  {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'})")
    print("goal:", goal, "len", len(goal))
    print("steps:", len(path))
    print()

SEGS = [
    ("a11-B",  "abaaabaaaabbbbaa", "abaaababaaaa"),
    ("a11-C",  "abaaababaaaa", "abbaabbaabaaaa"),
    ("a11-D",  "abbaabbaabaaaa", "aaabaaaaaabbaabaaaa"),
    ("a11-D2", "aaabaaaaaabbaabaaaa", "aaabaaabaaabaaaa"),
    ("a11-B2", "aaabaaabaaabaaaa", "bbaabbaabaaaabaaaa"),
    ("a11-C2", "bbaabbaabaaaabaaaa", "baaaabaaabaaabaaaa"),
    ("a11-G",  "baaaabaaabaaabaaaa", "baaaabbbaaabbaaabaaaa"),
    ("a11-A",  "baaaabbbaaabbaaabaaaa", "baaaabbbaaaaabbaaaa"),
    ("a11-A2", "baaaabbbaaaaabbaaaa", "baabaabbaaaa"),
    ("b11-s1", "bbababb", "aabaaababbb"),
    ("b11-s2", "aabaaababbb", "aabaaabaaabaa"),
    ("b11-s3", "aabaaabaaabaa", "aabbaabbaaabaa"),
    ("b11-s4", "aabbaabbaaabaa", "aabbaaaabbaa"),
    ("b11-s5", "aabbaaaabbaa", "aaaababbaa"),
    ("b11-s6", "aaaababbaa", "aaaabaaabaaaa"),
    ("b11-s7", "aaaabaaabaaaa", "aaaabbaabbaaaa"),
    ("b11-s8", "aaaabbaabbaaaa", "aaaabbaaaabba"),
    ("b11-s9", "aaaabbaaaabba", "ababa"),
    ("b7-tail","abbaabaaaab", "abaabbaaaa"),
]

for name, start, goal in SEGS:
    p = bfs(start, goal, max_depth=20, cap=60)
    if p is None:
        print(f"==== {name}: NO PATH (start={start}, goal={goal})")
    else:
        print(f"==== {name}")
        show_path(p, start, goal)
