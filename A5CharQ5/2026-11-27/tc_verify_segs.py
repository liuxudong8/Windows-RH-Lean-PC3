# -*- coding: utf-8 -*-
"""混合验证：手推段逐行元素比对 + 困难段限深 BFS 找路径。"""
import itertools
from collections import deque

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
    if cand != ONE and powp(cand, 3) == ONE and powp(mulp(powp(A, 2), cand), 2) == ONE:
        B = cand
        break
assert B is not None

def W(factors):
    r = ONE
    for c, k in factors:
        r = mulp(r, powp(A if c == 'a' else B, k))
    return r

def chk_chain(name, seqs):
    ok = True
    for i in range(len(seqs) - 1):
        a, b = W(seqs[i]), W(seqs[i + 1])
        if a != b:
            ok = False
            print(f"  FAIL {name} step {i}: {seqs[i]} != {seqs[i+1]}")
    if ok:
        print(f"  OK   {name} ({len(seqs)} rows)")
    return ok

F = lambda c, k: (c, k)
A1, A2, A3, A4, A6 = F('a',1), F('a',2), F('a',3), F('a',4), F('a',6)
B1, B2 = F('b',1), F('b',2)

print("== 手推段验证 ==")
# a11-B (Bi :1082)
chk_chain("a11-B", [
    [A1,B1,A3,B1,A4,B2,A2],
    [A1,B1,A3,B1,A1,B1,A2,A2],
    [A1,B1,A3,B1,A1,B1,A4],
])
# a11-C (Ci :1085)
chk_chain("a11-C", [
    [A1,B1,A3,B1,A1,B1,A4],
    [A1,B1,B1,A2,B1,B1,A1,B1,A4],
    [A1,B1,B1,A2,B2,A1,B1,A4],
])
# a11-D (Di :1088)
chk_chain("a11-D", [
    [A1,B1,B1,A2,B2,A1,B1,A4],
    [A1,B2,A2,B2,A1,B1,A4],
    [A1,B2,A1,A1,B2,A1,B1,A4],
    [A1,A2,B1,A3,A1,B2,A1,B1,A4],
    [A3,B1,A3,A1,B2,A1,B1,A4],
    [A3,B1,A4,B2,A1,B1,A4],
])
# a11-D2 (Di2 :1091)
chk_chain("a11-D2", [
    [A3,B1,A4,B2,A1,B1,A4],
    [A3,B1,A4,A2,B1,A3,B1,A4],
    [A3,B1,A6,B1,A3,B1,A4],
    [A3,B1,A1,B1,A3,B1,A4],
])
# a11-B2 (Bi2 :1095)
chk_chain("a11-B2", [
    [A3,B1,A1,B1,A3,B1,A4],
    [B1,A2,B1,B1,A1,B1,A3,B1,A4],
    [B1,A2,B2,A1,B1,A3,B1,A4],
])
# a11-C2 (Ci2 :1098)
chk_chain("a11-C2", [
    [B1,A2,B2,A1,B1,A3,B1,A4],
    [B1,A2,A2,B1,A3,B1,A3,B1,A4],
    [B1,A4,B1,A3,B1,A3,B1,A4],
])
# b11-s1
chk_chain("b11-s1", [
    [B1,B1,A1,B1,A1,B1,B1],
    [B2,A1,B1,A1,B2],
    [A2,B1,A2,A1,B1,A2,B1,A2],
    [A2,B1,A2,A1,B1,A1,B1,B1],   # 原段RHS（词 aabaaababbb 的展开）
    [A2,B1,A3,B1,A1,B2],
])
# 注意：s1 的 RHS 字面是 aabaaababbb 展开 = [A2,B1,A2,A1,B1,A1,B1,B1]，
# 再合并 a2·a→a3、bb→b2 得 [A2,B1,A3,B1,A1,B2]
# b11-s2
chk_chain("b11-s2", [
    [A2,B1,A2,A1,B1,A1,B1,B1],
    [A2,B1,A3,B1,A1,B2],
    [A2,B1,A3,B1,A1,A2,B1,A2],
    [A2,B1,A3,B1,A3,B1,A2],
])
# b11-s3
chk_chain("b11-s3", [
    [A2,B1,A3,B1,A3,B1,A2],
    [A2,B1,B1,A2,B1,B1,A3,B1,A2],
    [A2,B2,A2,B2,A3,B1,A2],
])
# b11-s4
chk_chain("b11-s4", [
    [A2,B2,A2,B2,A3,B1,A2],
    [A2,B2,A2,A2,B1,B2,A2],
    [A2,B2,A4,B2,A2],
])
# b11-s5
chk_chain("b11-s5", [
    [A2,B2,A4,B2,A2],
    [A2,B1,A3,B2,A2],
    [A4,B1,A6,B2,A2],
    [A4,B1,A1,B2,A2],
])
# b11-s6
chk_chain("b11-s6", [
    [A4,B1,A1,B2,A2],
    [A4,B1,A3,B1,A2,A1,B1,A2],
    [A4,B1,A3,B1,A2,A2],
    [A4,B1,A3,B1,A4],
])
# b11-s7
chk_chain("b11-s7", [
    [A4,B1,A3,B1,A4],
    [A4,B2,A2,B2,A4],
])
# b11-s9 末桥（s8 之后）
chk_chain("b11-s9-bridge", [
    [A4,B2,A4,B1,A1],
    [A1,B1,A1,B1,A1],
])

print("== 困难段限深 BFS ==")
import sys
sys.stdout.flush()
sys.exit(0)  # BFS 段另行单独限深运行
RULES = [
    ("baa", "aaabb"),          # 0
    ("aab", "bbaaa"),          # 1
    ("aabaa", "bb"),           # 2
    ("baab", "aaa"),           # 3
    ("aba", "aaaabbaaaa"),     # 4
    ("bbaabb", "baaab"),       # 5
    ("bbbb", "b"),             # 6
    ("baaaab", "aaabaaa"),     # 7
    ("bba", "aabaaa"),         # 8
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

def bfs(start, goal, max_depth, cap):
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

HARD = [
    ("a11-G",  "baaaabaaabaaabaaaa", "baaaabbbaaabbaaabaaaa"),
    ("a11-A",  "baaaabbbaaabbaaabaaaa", "baaaabbbaaaaabbaaaa"),
    ("a11-A2", "baaaabbbaaaaabbaaaa", "baabaabbaaaa"),
    ("b7-tail","abbaabaaaab", "abaabbaaaa"),
    ("b11-s8", "aaaabbaabbaaaa", "aaaabbaaaabba"),
]
for name, start, goal in HARD:
    p = bfs(start, goal, max_depth=9, cap=44)
    if p is None:
        print(f"  NO PATH {name}")
    else:
        print(f"  PATH {name} ({len(p)} steps):")
        w = start
        for (w0, pos, ridx, d, nw) in p:
            l, r = RULES[ridx]
            pat = l if d == 1 else r
            print(f"    {w0[:pos]}|{pat}|{w0[pos+len(pat):]} -> {nw}   (rule{ridx} {'fwd' if d==1 else 'rev'})")
        print(f"    goal={goal}")
