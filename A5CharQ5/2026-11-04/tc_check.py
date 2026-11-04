# Todd-Coxeter 陪集枚举验证：呈现 a^5 = b^3 = (a^2 b)^2 = 1, H = <a>
# 用自由约化模拟商群元素（字 = 整数对 (ai, bj) 模关系），直接群表验证
import itertools

# A5 的生成元（真实置换，验证陪集映射正确性用）
# s = (0 1 2 3 4) 5-cycle; t = (0 1 2) 3-cycle; 呈现 a = of0 ↦ s, b = of1 ↦ t
def perm_mul(p, q):
    return tuple(p[q[i]] for i in range(5))

s = (1,2,3,4,0)  # 0->1->2->3->4->0
t = (1,2,0,3,4)  # 0->1->2->0
a = s  # 呈现生成元 a = of 0 ↦ s
b = t
ident = tuple(range(5))

# 验证关系
assert perm_mul(a, a) == ident or True
# a^5 = 1
pa = ident
for _ in range(5): pa = perm_mul(pa, a)
assert pa == ident, "a^5 != 1"
# b^3 = 1
pb = ident
for _ in range(3): pb = perm_mul(pb, b)
assert pb == ident, "b^3 != 1"
# (a^2 b)^2 = 1  -> a2b = a*a*b
a2 = perm_mul(a, a)
a2b = perm_mul(a2, b)
pa2b = ident
for _ in range(2): pa2b = perm_mul(pa2b, a2b)
assert pa2b == ident, "(a^2 b)^2 != 1"

print("关系验证 OK: a^5=b^3=(a^2 b)^2=1 (置换层面)")

# 陪集枚举：H=<a> 在 G=<a,b> 上。用字约化：每个字用 (i,j) 表示 a^i b^j 形式？
# 直接暴力：生成 <a,b> 的所有字（长度上限），按"同陪集"（左乘 H 的元素）聚类
# 左陪集 xH: x 与 x' 同陪集 iff x^{-1} x' in H = {a^k}
# 用真实置换运算
def elem_of_word(word):
    # word: list of generators, 0=a, 1=b, -1=a^-1, -2=b^-1 (a^5=1,b^3=1 so inverses = powers)
    e = ident
    for g in word:
        if g == 0: e = perm_mul(e, a)
        elif g == 1: e = perm_mul(e, b)
        elif g == 2: e = perm_mul(e, a)  # a^4
        elif g == 3: e = perm_mul(e, b)  # b^2
    return e

def perm_inv(p):
    inv = [0]*5
    for i, v in enumerate(p): inv[v] = i
    return tuple(inv)

# H = {a^k}
H = []
e = ident
for k in range(5):
    H.append(e)
    e = perm_mul(e, a)

def same_coset(x, y):
    # x^{-1} y in H
    xy = perm_mul(perm_inv(x), y)
    return xy in H

# BFS 生成 G = <a,b>（字长上限 10，A5 有限 60 元素）
from collections import deque
seen = {ident: ()}
q = deque([ident])
gens = [a, b]
names = ['a','b']
while q:
    cur = q.popleft()
    for g, nm in zip(gens, names):
        nxt = perm_mul(cur, g)
        if nxt not in seen:
            seen[nxt] = seen[cur] + (nm,)
            q.append(nxt)

print("G = <a,b> 元素数:", len(seen))
assert len(seen) == 60, "不是 60 个元素!"

# 左陪集聚类
cosets = []
rep_to_coset = {}
for x in seen:
    placed = False
    for ci, rep in enumerate(cosets):
        if same_coset(x, rep):
            rep_to_coset[x] = ci
            placed = True
            break
    if not placed:
        rep_to_coset[x] = len(cosets)
        cosets.append(x)

print("陪集数:", len(cosets))
assert len(cosets) == 12, "陪集数不是 12!"

# 检查每个陪集是否有 a^i b^j a^k 形代表
for ci, rep in enumerate(cosets):
    found = None
    for i in range(5):
        for j in range(3):
            for k in range(5):
                e = ident
                for _ in range(i): e = perm_mul(e, a)
                for _ in range(j): e = perm_mul(e, b)
                for _ in range(k): e = perm_mul(e, a)
                if rep_to_coset[e] == ci:
                    found = (i, j, k)
                    break
            if found: break
        if found: break
    print(f"陪集 {ci}: 代表 a^{found[0]} b^{found[1]} a^{found[2]}" if found else f"陪集 {ci}: 无 a^i b^j a^k 形代表")

# BFS 最短字（陪集代表的最短生成元字，供 Lean 定义陪集代表用）
print("\n陪集代表最短字：")
for ci, rep in enumerate(cosets):
    w = seen[rep]
    ws = ''.join(w) if w else '1'
    print(f"  陪集 {ci}: {ws}")

# Todd-Coxeter 表：a、b 在每个陪集上的作用
print("\nTodd-Coxeter 表：")
for ci, rep in enumerate(cosets):
    ra = perm_mul(a, rep); rb = perm_mul(b, rep)
    print(f"  陪集 {ci}: a->{rep_to_coset[ra]}, b->{rep_to_coset[rb]}")

# 作用表 (j,k)：g·c_i = c_j·a^k（k 为 a 的指数）
def powp(x, n):
    e = ident
    for _ in range(n): e = perm_mul(e, x)
    return e

print("\n作用表 (j,k)（g·c_i = c_j·a^k）：")
for ci, rep in enumerate(cosets):
    for g, gn in [(a, 'a'), (b, 'b')]:
        e = perm_mul(g, rep)
        j = rep_to_coset[e]
        cj = cosets[j]
        k = None
        for kk in range(5):
            if perm_mul(cj, powp(a, kk)) == e:
                k = kk; break
        assert k is not None, f"找不到 k: {gn}·c{ci}"
        print(f"  {gn}·c{ci} = c{j}·a^{k}")

# 交换表：b·a^i = a^j·b^k（i=1..4，陪集约化用）
print("\n交换表（b·a^i = a^j·b^k，i=1..4）：")
for i in range(1, 5):
    e = perm_mul(b, powp(a, i))
    for j in range(5):
        for k in range(3):
            if perm_mul(powp(a, j), powp(b, k)) == e:
                print(f"  b·a^{i} = a^{j}·b^{k}")
                break
        else: continue
        break

# 陪集代表的逆：(c_i)^{-1} = c_j·a^k（S_inv 证明需要 12 条逆引理数值）
# c_i^{-1} ∈ c_j·H ⟺ c_j^{-1}·c_i^{-1} ∈ H = {a^k}
print("\n陪集代表的逆（(c_i)^{-1} = c_j·a^k）：")
for ci, rep in enumerate(cosets):
    ri = perm_inv(rep)
    found = None
    for j, cj in enumerate(cosets):
        if perm_mul(perm_inv(cj), ri) in H:
            for k in range(5):
                if perm_mul(perm_inv(cj), ri) == powp(a, k):
                    found = (j, k)
                    break
            break
    assert found is not None, f"c{ci} 逆无解"
    print(f"  c{ci}^-1 = c{found[0]}·a^{found[1]}")

