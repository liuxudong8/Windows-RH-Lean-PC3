# -*- coding: utf-8 -*-
"""BFS v3：按群元素去重（≤60 状态必然终止），目标按元素匹配。
词不规范化（避免破坏结构），仅加长度上限。输出完整规则路径。
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

A = (2, 3, 4, 5, 1, 6)
ONE = tuple(range(1, 7))
B = None
for cand in itertools.permutations(range(1, 7)):
    # 阶恰为 3（非恒等）且 (a²b)² = 1
    if cand != ONE and powp(cand, 3) == ONE and powp(mulp(powp(A, 2), cand), 2) == ONE:
        B = cand
        break

def elem(w):
    r = ONE
    for c in w:
        r = mulp(r, A if c == 'a' else B)
    return r

RULES = [
    ("baa", "aaabb"),          # 0 b a^2 -> a^3 b^2
    ("aab", "bbaaa"),          # 1 a^2 b -> b^2 a^3
    ("aabaa", "bb"),           # 2 a^2 b a^2 -> b^2
    ("baab", "aaa"),           # 3 b a^2 b -> a^3
    ("aba", "aaaabbaaaa"),     # 4 a b a -> a^4 b^2 a^4
    ("bbaabb", "baaab"),       # 5 b^2 a^2 b^2 -> b a^3 b
    ("bbbb", "b"),             # 6 b^4 -> b
    ("baaaab", "aaabaaa"),     # 7 b a^4 b -> a^3 b a^3
    ("bba", "aabaaa"),         # 8 b^2 a -> a^2 b a^3
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

def bfs(start, goal, max_depth=30, cap=90):
    q = deque([(start, [])])
    seen = {elem(start)}
    gelem = elem(goal)
    while q:
        w, path = q.popleft()
        if len(path) >= max_depth:
            continue
        for pos, ridx, d, nw in rewrites(w, cap):
            if elem(nw) in seen:
                continue
            seen.add(elem(nw))
            np = path + [(w, pos, ridx, d, nw)]
            if elem(nw) == gelem:
                return np
            q.append((nw, np))
    return None

def show_path(path, start, goal):
    w = start
    print("start:", w)
    for (w0, pos, ridx, d, nw) in path:
        l, r = RULES[ridx]
        pat = l if d == 1 else r
        rep = r if d == 1 else l
        print(f"  {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'}: {l}->{r})")
    print("goal:", goal, " (reached elem", elem(goal), ")")
    print("steps:", len(path))

def main():
    cases = [
        ("coset_a_11", "abaababbb", "bababbbaaaa"),
        ("coset_b_7", "babab", "ababbbaaaa"),
        ("coset_b_8", "bbabb", "aabbaa"),
        ("coset_b_11", "bbababb", "ababa"),
    ]
    for name, start, goal in cases:
        print(f"==== {name}: {start} -> {goal}")
        p = bfs(start, goal)
        if p is None:
            print("  NO PATH")
        else:
            show_path(p, start, goal)
            print()

if __name__ == "__main__":
    main()
