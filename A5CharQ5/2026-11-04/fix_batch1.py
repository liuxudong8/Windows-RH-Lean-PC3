# 批量修正编译错误根因
# 1) nth_rewrite_lhs -> nth_rewrite（本 mathlib 版本无 nth_rewrite_lhs）
# 2) 拆幂/拆 b² 的 rw 双侧改写 -> nth_rewrite 1 只动 LHS
# 3) a_11 Di bb 段：先合并 (pB·pB)->b² 再 nth_rewrite 1 [← a2_b_a2_eq_b2]
# 4) b_11 段 1：先合并 bb->b² 再 nth_rewrite 1
# 5) b_8 末行：group 不展开幂 -> 显式拆幂
path = r"C:\proj2\A5CharQ5\A5Defs.lean"
with open(path, encoding="utf-8") as f:
    s = f.read()

reps = []

# A. a_11 段 3（Di bb）：行 2-3 修正
old_a = """    rw [show pA * pB * pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4
        = pA * (pB * pB) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4 by group]
    rw [← a2_b_a2_eq_b2]
    rw [show pA * (pA ^ 2 * pB * pA ^ 2) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4"""
new_a = """    rw [show pA * pB * pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4
        = pA * (pB * pB) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4 by group]
    rw [show pA * (pB * pB) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4
        = pA * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4 by
          rw [← pow_two]]
    nth_rewrite 1 [← a2_b_a2_eq_b2]
    rw [show pA * (pA ^ 2 * pB * pA ^ 2) * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 4"""
assert s.count(old_a) == 1, f"A count={s.count(old_a)}"
s = s.replace(old_a, new_a)

# B. a_11 段 4 行 1：拆 a⁴ 双侧 -> nth_rewrite 1
old_b = """  -- Di：a³·b² → b·a²（位置 5）＋幂拆合
  _ = pA ^ 3 * pB * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    rw [show pA ^ 4 = pA * pA ^ 3 by rw [pow_succ']]"""
new_b = """  -- Di：a³·b² → b·a²（位置 5）＋幂拆合
  _ = pA ^ 3 * pB * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [show pA ^ 4 = pA * pA ^ 3 by rw [pow_succ']]"""
assert s.count(old_b) == 1, f"B count={s.count(old_b)}"
s = s.replace(old_b, new_b)

# C. a_11 段 5 行 1：nth_rewrite_lhs -> nth_rewrite
old_c = """  _ = pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite_lhs 1 [← b_a2_b_eq_a3]"""
new_c = """  _ = pB * pA ^ 2 * pB ^ 2 * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [← b_a2_b_eq_a3]"""
assert s.count(old_c) == 1, f"C count={s.count(old_c)}"
s = s.replace(old_c, new_c)

# D. b_7 段 1 行 1：拆 a⁴ 双侧 -> nth_rewrite 1
old_d = """  _ = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB := by
    rw [show pA ^ 4 = pA ^ 2 * pA ^ 2 by rw [← pow_add]]"""
new_d = """  _ = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 2 * pA ^ 2 by rw [← pow_add]]"""
assert s.count(old_d) == 1, f"D count={s.count(old_d)}"
s = s.replace(old_d, new_d)

# E. b_8 末行：group 不展开幂 -> 显式拆幂
old_e = """  _ = pA * pA * pB * pB * pA * pA := by
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 = pA * pA * pB * pB * pA * pA by group]"""
new_e = """  _ = pA * pA * pB * pB * pA * pA := by
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2
        = (pA * pA) * pB ^ 2 * (pA * pA) by
          rw [pow_two]]
    rw [show (pA * pA) * pB ^ 2 * (pA * pA)
        = (pA * pA) * (pB * pB) * (pA * pA) by
          rw [pow_two]]
    rw [show (pA * pA) * (pB * pB) * (pA * pA)
        = pA * pA * pB * pB * pA * pA by group]"""
assert s.count(old_e) == 1, f"E count={s.count(old_e)}"
s = s.replace(old_e, new_e)

# F. b_11 段 1：先合并 bb->b² 再 nth_rewrite 1
old_f = """  -- 1：bb → a²·b·a²（位置 0，rule2 反向；最左 bb 块）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2 := by
    nth_rewrite_lhs 1 [← a2_b_a2_eq_b2]
    rw [show (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA * pB * pB
        = pA ^ 2 * pB * (pA ^ 2 * pA) * pB * pA * (pB * pB) by group]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]"""
new_f = """  -- 1：bb → a²·b·a²（位置 0，rule2 反向；先合并最左 bb）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2 := by
    rw [show pB * pB * pA * pB * pA * pB * pB
        = pB ^ 2 * pA * pB * pA * pB ^ 2 by
          rw [← pow_two]]
    nth_rewrite 1 [← a2_b_a2_eq_b2]
    rw [show (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA * pB ^ 2
        = pA ^ 2 * pB * (pA ^ 2 * pA) * pB * pA * pB ^ 2 by group]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]"""
assert s.count(old_f) == 1, f"F count={s.count(old_f)}"
s = s.replace(old_f, new_f)

# G. b_11 段 3 行 1：nth_rewrite_lhs -> nth_rewrite
old_g = """  _ = pA ^ 2 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 2 := by
    nth_rewrite_lhs 1 [← b_a2_b_eq_a3]"""
new_g = """  _ = pA ^ 2 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 2 := by
    nth_rewrite 1 [← b_a2_b_eq_a3]"""
assert s.count(old_g) == 1, f"G count={s.count(old_g)}"
s = s.replace(old_g, new_g)

# H. b_11 段 5 行 1：nth_rewrite_lhs -> nth_rewrite
old_h = """  _ = pA ^ 4 * pB * pA * pB ^ 2 * pA ^ 2 := by
    nth_rewrite_lhs 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]"""
new_h = """  _ = pA ^ 4 * pB * pA * pB ^ 2 * pA ^ 2 := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]"""
assert s.count(old_h) == 1, f"H count={s.count(old_h)}"
s = s.replace(old_h, new_h)

# I. b_11 段 8 行 1：nth_rewrite_lhs -> nth_rewrite
old_i = """  _ = pA ^ 4 * pB ^ 2 * pA ^ 4 * pB * pA := by
    nth_rewrite_lhs 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]"""
new_i = """  _ = pA ^ 4 * pB ^ 2 * pA ^ 4 * pB * pA := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]"""
assert s.count(old_i) == 1, f"I count={s.count(old_i)}"
s = s.replace(old_i, new_i)

with open(path, "w", encoding="utf-8", newline="") as f:
    f.write(s)
print("all 9 replacements applied")
