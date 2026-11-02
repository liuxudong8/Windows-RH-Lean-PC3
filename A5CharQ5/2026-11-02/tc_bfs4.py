# -*- coding: utf-8 -*-
"""BFS v4：词级 BFS（规则双向，词不规范化，按词去重，词长上限）。
目标 = 精确词匹配。规则均为群恒等式，故保持元素不变——只找字面路径。
"""
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
    print("start:", w)
    for (w0, pos, ridx, d, nw) in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        print(f"  {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'}: {l}->{r})")
    print("goal:", goal)
    print("steps:", len(path))

def main():
    cases = [
        ("coset_a_11", "abababb", "bababbaaaa"),
        ("coset_b_7", "babab", "ababbaaaa"),
        ("coset_b_8", "bbabb", "aabbaa"),
        ("coset_b_11", "bbababb", "ababa"),
    ]
    for name, start, goal in cases:
        print(f"==== {name}: {start} -> {goal}")
        p = bfs(start, goal, max_depth=18, cap=50)
        if p is None:
            print("  NO PATH")
        else:
            show_path(p, start, goal)
            print()

if __name__ == "__main__":
    main()
