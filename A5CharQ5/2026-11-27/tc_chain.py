# -*- coding: utf-8 -*-
"""逐步验证 4 条坏引理的候选 Lean calc 链（每行中间等式数值背书）。
群 = S6 置换：a=(1 2 3 4 5)(6), b = 3-cycle 且 (a^2 b)^2=1。
"""
import itertools

def comp(p, q):
    return tuple(p[q[i] - 1] for i in range(len(p)))

def mul(*ps):
    r = tuple(range(1, len(ps[0]) + 1))
    for p in ps:
        r = comp(p, r)
    return r

def pow(p, k):
    r = tuple(range(1, len(p) + 1))
    for _ in range(k % 60):
        r = comp(p, r)
    return r

def find_b():
    a = (2, 3, 4, 5, 1, 6)
    n = 6
    for b in itertools.permutations(range(1, n + 1)):
        if pow(b, 3) != tuple(range(1, 7)):
            continue
        if pow(mul(pow(a, 2), b), 2) == tuple(range(1, 7)):
            return a, b

a, b = find_b()
pA, pB = a, b
ONE = tuple(range(1, 7))

def W(seq):
    """seq: list of ('a',k)/('b',k)"""
    r = ONE
    for c, k in seq:
        r = mul(r, pow(pA if c == 'a' else pB, k))
    return r

# ---- 关键恒等式 ----
checks = []

# hbab4: pB*pA^4*pB = pA^3*pB*pA^3
checks.append(("hbab4", mul(pB, pow(pA,4), pB), mul(pow(pA,3), pB, pow(pA,3))))

# hba: pB^2*pA = pA^2*pB*pA^3
checks.append(("hba", mul(pow(pB,2), pA), mul(pow(pA,2), pB, pow(pA,3))))

# hbab2: pB^2*pA*pB^2 = pA^2*pB^2*pA^2   (b_8 目标，k=2)
checks.append(("hbab2", mul(pow(pB,2), pA, pow(pB,2)), mul(pow(pA,2), pow(pB,2), pow(pA,2))))

# ---- coset_b_8 候选链：pB^2*pA*pB^2 = pA^2*pB^2*pA^2 ----
#  pB^2*pA = pA^2*pB*pA^3 (hba)  →  pA^2*pB*pA^3*pB^2 → pA^2*pB*(pA^3*pB^2) → pA^2*pB*(pB*pA^2) → pA^2*pB^2*pA^2
b8 = []
b8.append(("b8.1", W([('b',2),('a',1),('b',2)]), mul(pow(pA,2), pB, pow(pA,3), pow(pB,2))))
b8.append(("b8.2", b8[-1][2], mul(pow(pA,2), pB, mul(pow(pA,3), pow(pB,2)))))
b8.append(("b8.3", b8[-1][2], mul(pow(pA,2), pB, mul(pB, pow(pA,2)))))
b8.append(("b8.4", b8[-1][2], mul(pow(pA,2), pow(pB,2), pow(pA,2))))

# ---- coset_b_11 候选：pB^2*pA*pB*pA*pB^2 = pA*pB*pA*pB*pA ----
b11 = []
# 用反向 Ci（b² → a²·b·a²）展开两处 b²，然后 Di（a³ → b·a²·b），再…
b11.append(("b11.1", W([('b',2),('a',1),('b',1),('a',1),('b',2)]),
                   mul(pow(pA,2), pB, pow(pA,2), pA, pB, pA, pow(pA,2), pB, pow(pA,2))))
b11.append(("b11.2", b11[-1][2], W([('a',2),('b',1),('a',1),('b',1),('a',1),('b',1),('a',2),('b',1),('a',2)])))
b11.append(("b11.3", b11[-1][2], W([('a',2),('b',1),('a',1),('b',1),('a',1),('b',1),('a',1),('b',1),('a',2)])))

# ---- coset_b_7 候选链：pB*pA*pB*pA*pB = pA*pB*pA*pB^2*pA^4 ----
#  F: pA*pB*pA = pA^4*pB^2*pA^4；hbab4: pB*pA^4*pB = pA^3*pB*pA^3
b7 = []
b7.append(("b7.1", W([('b',1),('a',1),('b',1),('a',1),('b',1)]),
                   mul(pB, pow(pA,4), pow(pB,2), pow(pA,4), pB)))
b7.append(("b7.2", b7[-1][2], mul(pow(pA,3), pB, pow(pA,3), pow(pB,2), pow(pA,4), pB)))
b7.append(("b7.3", b7[-1][2], mul(pow(pA,3), pB, pow(pA,3), mul(pow(pB,2), pow(pA,4), pB))))
# 目标 RHS: pA*pB*pA*pB^2*pA^4
b7.append(("b7.goal", b7[-1][2], W([('a',1),('b',1),('a',1),('b',2),('a',4)])))
# 也许需要中间再走：pA^3*pB*pA^3*pB^2*pA^4*pB 与目标不等就找更短路径

# ---- coset_a_11 候选：pA*pB*pA*pB*pA*pB^2 = pB*pA*pB*pA*pB^2*pA^4 ----
# 沿用已编译段到 pA*pB*pA^3*pB*pA^4*pB^2*pA^2，然后：
a11 = []
a11.append(("a11.pre", W([('a',1),('b',1),('a',3),('b',1),('a',4),('b',2),('a',2)]),
                    mul(pA, pB, pow(pA,3), pB, pA, pB, pow(pA,4))))   # Bi 位置 5
a11.append(("a11.2", a11[-1][2], W([('a',1),('b',1),('b',1),('a',2),('b',2),('a',1),('b',1),('a',4)])))
a11.append(("a11.goal", a11[-1][2], W([('b',1),('a',1),('b',1),('a',1),('b',2),('a',4)])))

for name, x, y in checks + b8 + b7 + b11 + a11:
    tag = "OK " if x == y else "FAIL"
    print(f"{tag} {name}")

print()
print("b_7: 中间串 1 与目标:")
print("  ", b7[2][2] == b7[3][2])
