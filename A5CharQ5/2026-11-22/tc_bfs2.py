# -*- coding: utf-8 -*-
"""改进 BFS：按群元素去重（状态有限），规则含新发现恒等式，双向。
词 = 'a'/'b' 序列（幂展开）。规范化：aaaaa->'', bbb->''。
"""
from collections import deque
import itertools

def comp(p, q):
    return tuple(p[q[i] - 1] for i in range(len(p)))

def mulp(*ps):
    r = tuple(range(1, 7))
    for p in ps:
        r = comp(p, r)
    return r

def powp(p, k):
    r = tuple(range(1, 7))
    for _ in range(k % 60):
        r = comp(p, r)
    return r

# a = (1 2 3 4 5) fixed 6; b: 3-cycle with (a^2 b)^2 = 1
A = (2, 3, 4, 5, 1, 6)
for B in itertools.permutations(range(1, 7)):
    if powp(B, 3) == tuple(range(1, 7)) and powp(mulp(powp(A, 2), B), 2) == tuple(range(1, 7)):
        break
ONE = tuple(range(1, 7))

def elem(w):
    r = ONE
    for c in w:
        r = mulp(r, A if c == 'a' else B)
    return r

def normalize(w):
    while True:
        nw = w.replace("aaaaa", "").replace("bbb", "")
        if nw == w:
            return nw
        w = nw

RULES = [
    ("baa", "aaabb"),
    ("aab", "bbaaa"),
    ("aabaa", "bb"),
    ("baab", "aaa"),
    ("aba", "aaaabbaaaa"),
    ("bbaabb", "baaab"),
    ("bbbb", "b"),
    ("baaaab", "aaabaaa"),   # b a^4 b <-> a^3 b a^3
    ("bba", "aabaaa"),       # b^2 a <-> a^2 b a^3
]

def rewrites(w):
    out = []
    for idx, (l, r) in enumerate(RULES):
        for d, (pat, rep) in ((1, (l, r)), (-1, (r, l))):
            start = 0
            while True:
                p = w.find(pat, start)
                if p < 0:
                    break
                out.append((p, idx, d, normalize(w[:p] + rep + w[p+len(pat):])))
                start = p + 1
    return out

def bfs(start, goal, max_depth=30):
    start, goal = normalize(start), normalize(goal)
    q = deque([(start, [])])
    seen = {elem(start)}
    while q:
        w, path = q.popleft()
        if len(path) >= max_depth:
            continue
        for pos, ridx, d, nw in rewrites(w):
            if elem(nw) in seen:
                continue
            seen.add(elem(nw))
            np = path + [(w, pos, ridx, d, nw)]
            if nw == goal:
                return np
            q.append((nw, np))
    return None

def show_path(path, start, goal):
    w = normalize(start)
    print("start:", w, " (", elem(w), ")")
    for (w0, pos, ridx, d, nw) in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        print(f"  [{w0[:pos]}|{pat}|{w0[pos+len(pat):]}] -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'}: {l}->{r})")
    print("goal:", w)

def main():
    cases = [
        ("coset_a_11", "abaababbb", "bababbbaaaa"),
        ("coset_b_7", "babab", "ababbbaaaa"),
        ("coset_b_8", "bbabb", "aabb aa"),
        ("coset_b_11", "bbababb", "ababa"),
    ]
    for name, start, goal in cases:
        start = normalize(start.replace(" ", ""))
        goal = normalize(goal.replace(" ", ""))
        print(f"==== {name}: {start} -> {goal}")
        p = bfs(start, goal)
        if p is None:
            print("  NO PATH")
        else:
            show_path(p, start, goal)
            print()

if __name__ == "__main__":
    main()
