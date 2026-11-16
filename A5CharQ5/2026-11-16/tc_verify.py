# -*- coding: utf-8 -*-
"""A5 群（<a,b | a^5=b^3=(a^2 b)^2=1>）置换实现 + coset 等式验证。
a, b 取 PSL(2,5) 上的显式置换，验证 24 条陪集作用等式与交换引理。
"""
import itertools

# S_6 上的置换（1-indexed 写成 tuple，(i)->p[i-1]）
def comp(p, q):
    """p ∘ q: 先 q 后 p"""
    return tuple(p[q[i] - 1] for i in range(len(p)))

def inv(p):
    n = len(p)
    r = [0] * n
    for i, v in enumerate(p):
        r[v - 1] = i + 1
    return tuple(r)

def power(p, k):
    r = tuple(range(1, len(p) + 1))
    for _ in range(k % 60):
        r = comp(p, r)
    return r

def mul(*ps):
    r = tuple(range(1, len(ps[0]) + 1))
    for p in ps:
        r = comp(p, r)
    return r

# 6 点表示：PSL(2,5) 作用在射影直线 P1(F5) 上（6 个点：0,1,2,3,4,∞）
# a = x ↦ x+1（5-cycle，固定 ∞），b = x ↦ -1/x（3-cycle）
# 点编号 0..4 = 0..4 mod 5，5 = ∞
def a_perm():
    # x ↦ x+1 (mod 5)，∞ 固定
    p = [2, 3, 4, 5, 1, 6]
    return tuple(p)

def b_perm():
    # x ↦ -1/x (mod 5)；x=0 ↦ ∞，x=∞ ↦ 0，x=1↦4,2↦3,3↦2,4↦1
    # 1-indexed: 0->5(∞), 5->1(0), 1->4, 4->1, 2->3, 3->2
    p = [5, 4, 3, 2, 1, 1]  # 占位，下面修正
    # 点 0(idx0): x=0 -> ∞ (点6) => p[0]=6
    # 点 1(idx1): x=1 -> -1 = 4 (点4) => p[1]=4
    # 点 2(idx2): x=2 -> -1/2 = -3 = 2 (点2) => p[2]=2
    # 点 3(idx3): x=3 -> -1/3 = -2 = 3 (点3) => p[3]=3
    # 点 4(idx4): x=4 -> -1/4 = -1 = 4 (点4) => p[4]=4
    # 点 ∞(idx5): x=∞ -> 0 (点1) => p[5]=1
    p = [6, 4, 2, 3, 4, 1]
    # 修正：x=4 ↦ -1/4 ≡ -4 ≡ 1 (点1)；x=1 ↦ -1 ≡ 4 (点4)
    p = [6, 4, 3, 2, 1, 1]
    # 再仔细：-1/x mod 5: x=0→∞; x=1→-1=4; x=2→-1/2=-3=2; x=3→-1/3=-2=3; x=4→-1/4=-4=1; ∞→0
    p = [6, 4, 2, 3, 1, 1]
    # 注意：1-indexed 输出：点1(x=0)→点6(∞)；点2(x=1)→点4(x=4)；点3(x=2)→点2(x=2)?  -1/2 mod5 = -3 = 2 => 点3→点2
    p = [6, 4, 3, 2, 1, 1]
    return tuple(p)

# 换个稳妥方式：直接搜索 (a^2 b)^2=1 的 b（3-cycle），a = (1 2 3 4 5 6)? 不，a 固定 ∞。
# 用最直白的：(a^2 b)^2=1 即 b a^2 b a^2 = 1 或 (a^2 b) 是二阶元。
# 重新用 5-cycle a = (1 2 3 4 5) 固定 6，b 为 3-cycle 且 (a^2 b)^2=1。

def find_b():
    a = (2, 3, 4, 5, 1, 6)  # a: 1->2->3->4->5->1, 6 fixed
    n = 6
    perms = list(itertools.permutations(range(1, n + 1)))
    found = []
    for b in perms:
        # b 是 3-cycle（阶 3）且不动 6（可选）
        if power(b, 3) != tuple(range(1, 7)):
            continue
        # 检查 (a^2 b)^2 = 1
        a2b = mul(power(a, 2), b)
        if power(a2b, 2) == tuple(range(1, 7)):
            found.append(b)
    return a, found

def main():
    a, bs = find_b()
    print("a =", a)
    for b in bs[:3]:
        print("b =", b, "order(b)=", order(b))
    b = bs[0]
    # 验证关系
    assert power(a, 5) == tuple(range(1, 7))
    assert power(b, 3) == tuple(range(1, 7))
    assert power(mul(power(a, 2), b), 2) == tuple(range(1, 7))
    print("rels OK")
    # 生成元
    pA, pB = a, b
    def word(seq):
        r = tuple(range(1, 7))
        for c, k in seq:
            r = mul(r, power(pA if c == 'a' else pB, k))
        return r
    # cosetRep
    reps = {
        0: [('1', 0)], 1: [('b', 1)], 2: [('a', 1), ('b', 1)],
        3: [('b', 2)], 4: [('a', 1), ('b', 2)], 5: [('b', 1), ('a', 1), ('b', 1)],
        6: [('a', 2), ('b', 2)], 7: [('a', 1), ('b', 1), ('a', 1), ('b', 1)],
        8: [('b', 1), ('a', 1), ('b', 2)], 9: [('b', 2), ('a', 1), ('b', 1)],
        10: [('a', 1), ('b', 1), ('a', 1), ('b', 2)],
        11: [('b', 1), ('a', 1), ('b', 1), ('a', 1), ('b', 2)]}
    aT = [0, 2, 3, 4, 6, 7, 1, 8, 10, 5, 9, 11]
    bT = [1, 3, 5, 0, 8, 9, 4, 10, 6, 2, 11, 7]
    for i in range(12):
        ci = word(reps[i])
        # a 作用
        l = mul(pA, ci)
        ok_a = False
        for k in range(5):
            if l == mul(word(reps[aT[i]]), power(pA, k)):
                ok_a = True
                break
        # b 作用
        l2 = mul(pB, ci)
        ok_b = False
        for k in range(5):
            if l2 == mul(word(reps[bT[i]]), power(pA, k)):
                ok_b = True
                break
        print(f"i={i}: a-ok={ok_a} b-ok={ok_b}")
    # 交换引理验证
    id6 = tuple(range(1, 7))
    print("b_a2_comm:", mul(pB, power(pA, 2)) == mul(power(pA, 3), power(pB, 2)))
    print("a2_b_comm:", mul(power(pA, 2), pB) == mul(power(pB, 2), power(pA, 3)))
    print("pB_pow_four:", power(pB, 4) == pB)
    print("a2_b_a2_eq_b2:", mul(power(pA, 2), pB, power(pA, 2)) == power(pB, 2))
    print("b_a2_b_eq_a3:", mul(pB, power(pA, 2), pB) == power(pA, 3))
    print("a_b_a_eq_a4b2a4:", mul(pA, pB, pA) == mul(power(pA, 4), power(pB, 2), power(pA, 4)))
    print("b2_a2_b2_eq_ba3b:", mul(power(pB, 2), power(pA, 2), power(pB, 2)) == mul(pB, power(pA, 3), pB))
    # 验证 coset_a_11 / b_7 / b_8 / b_11 的目标
    def check(seq_lhs, seq_rhs, k):
        return mul(*[power(pA if c == 'a' else pB, e) for c, e in seq_lhs]) == \
               mul(*[power(pA if c == 'a' else pB, e) for c, e in seq_rhs]) if k is None else \
               mul(*[power(pA if c == 'a' else pB, e) for c, e in seq_lhs]) == mul(
                   mul(*[power(pA if c == 'a' else pB, e) for c, e in seq_rhs]), power(pA, k))
    a11_lhs = [('a', 1), ('b', 1), ('a', 1), ('b', 1), ('a', 1), ('b', 2)]
    a11_rhs = [('b', 1), ('a', 1), ('b', 1), ('a', 1), ('b', 2)]
    print("coset_a_11 k=4:", check(a11_lhs, a11_rhs, 4))
    b7_lhs = [('b', 1), ('a', 1), ('b', 1), ('a', 1), ('b', 1)]
    b7_rhs = [('a', 1), ('b', 1), ('a', 1), ('b', 2)]
    print("coset_b_7 k=4:", check(b7_lhs, b7_rhs, 4))
    b8_lhs = [('b', 1), ('b', 1), ('a', 1), ('b', 2)]
    b8_rhs = [('a', 2), ('b', 2)]
    print("coset_b_8 k=2:", check(b8_lhs, b8_rhs, 2))
    b11_lhs = [('b', 1), ('b', 1), ('a', 1), ('b', 1), ('a', 1), ('b', 2)]
    b11_rhs = [('a', 1), ('b', 1), ('a', 1), ('b', 1)]
    print("coset_b_11 k=1:", check(b11_lhs, b11_rhs, 1))
    # 关键子式验证（供证明用）
    print("pB*pA^4*pB = a^3*b*a^3 ?", mul(pB, power(pA, 4), pB) == mul(power(pA, 3), pB, power(pA, 3)))
    print("pB*pA^4*pB = b*a^2*b*a^2*b ?", mul(pB, power(pA, 4), pB) == mul(pB, power(pA, 2), pB, power(pA, 2), pB))
    print("pA^3*pB = pB*pA^2*pB*pB ?", mul(power(pA, 3), pB) == mul(pB, power(pA, 2), pB, pB))

def order(p):
    r = tuple(range(1, len(p) + 1))
    o = 0
    while True:
        o += 1
        r = comp(p, r)
        if r == tuple(range(1, len(p) + 1)):
            return o

if __name__ == "__main__":
    main()
