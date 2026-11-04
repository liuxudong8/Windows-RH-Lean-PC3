# -*- coding: utf-8 -*-
"""单步调试：B 选择 + b_8 路径验证"""
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
    if cand != ONE and powp(cand, 3) == ONE and powp(mulp(powp(A, 2), cand), 2) == ONE:
        B = cand
        break
print("B =", B)
print("order(B) =", min(k for k in range(1, 7) if powp(B, k) == ONE))
print("(A^2 B)^2 =", powp(mulp(powp(A, 2), B), 2))

def elem(w):
    r = ONE
    for c in w:
        r = mulp(r, A if c == 'a' else B)
    return r

RULES = [
    ("baa", "aaabb"),
    ("aab", "bbaaa"),
    ("aabaa", "bb"),
    ("baab", "aaa"),
    ("aba", "aaaabbaaaa"),
    ("bbaabb", "baaab"),
    ("bbbb", "b"),
    ("baaaab", "aaabaaa"),
    ("bba", "aabaaa"),
]

w = "bbabb"
print("start elem:", elem(w))
print("goal elem:", elem("aabbaa"))
print("equal?", elem(w) == elem("aabbaa"))
for idx, (l, r) in enumerate(RULES):
    for d, (pat, rep) in ((1, (l, r)), (-1, (r, l))):
        start = 0
        while True:
            p = w.find(pat, start)
            if p < 0:
                break
            nw = w[:p] + rep + w[p+len(pat):]
            print(f"  rule{idx} {'fwd' if d==1 else 'rev'} pos {p}: {pat}->{rep} => {nw} (elem {elem(nw)})")
            start = p + 1

# 手算路径
w2 = "aabaaabb"
print()
print("step2 from aabaaabb:")
for idx, (l, r) in enumerate(RULES):
    for d, (pat, rep) in ((1, (l, r)), (-1, (r, l))):
        start = 0
        while True:
            p = w2.find(pat, start)
            if p < 0:
                break
            nw = w2[:p] + rep + w2[p+len(pat):]
            print(f"  rule{idx} {'fwd' if d==1 else 'rev'} pos {p}: {pat}->{rep} => {nw} (elem {elem(nw)})")
            start = p + 1
