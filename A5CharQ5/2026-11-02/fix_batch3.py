# fix_batch3：b_11 段7（双 b·b 合并）+ 段8（尾部 a⁴ 拆分 + show 模式 + pow_add 方向）
path = r"C:\proj2\A5CharQ5\A5Defs.lean"
with open(path, encoding="utf-8") as f:
    s = f.read()

reps = []

# J. 段7 行3：show pB*pB 改 rw [← pow_two, ← pow_two]
old = """    rw [show pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 4
        = pA ^ 4 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 4 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]"""
new = """    rw [show pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 4
        = pA ^ 4 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 4 by group]
    rw [← pow_two, ← pow_two]"""
assert s.count(old) == 1, f"J count={s.count(old)}"
s = s.replace(old, new)

# K. 段8 整段重写
old = """  -- 8：b²·a³ → a²·b（位置 8，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并
  _ = pA ^ 4 * pB ^ 2 * pA ^ 4 * pB * pA := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * pB ^ 2 * (pA ^ 3 * pA)
        = (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pA by group]
    rw [← a2_b_comm]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pA
        = pA ^ 4 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pA by group]
    rw [show pA ^ 3 * pA = pA ^ 4 by rw [← pow_succ]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]"""
new = """  -- 8：b²·a³ → a²·b（位置 8，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并
  _ = pA ^ 4 * pB ^ 2 * pA ^ 4 * pB * pA := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * pB ^ 2 * (pA ^ 3 * pA)
        = (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pA by group]
    rw [← a2_b_comm]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pA
        = (pA ^ 3 * pA) * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pA by group]
    rw [show pA ^ 3 * pA = pA ^ 4 by rw [← pow_succ]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]"""
assert s.count(old) == 1, f"K count={s.count(old)}"
s = s.replace(old, new)

with open(path, "w", encoding="utf-8", newline="") as f:
    f.write(s)
print("all batch3 replacements applied")
