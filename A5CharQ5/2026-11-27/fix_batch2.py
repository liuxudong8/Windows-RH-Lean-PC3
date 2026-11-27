# fix_batch2：第二批修正
# a_11：段4（pow_succ' 方向+show模式）、段6/3（pow_add 方向）、段7（nth_rewrite+平铺）
# b_7：段1 行1（show 包整 LHS）、段2（拆 b²）、段3（拆 a³×2）
# b_11：段1（←pow_two ×2）、段4（show 括块）、段4/5/6（pow_add 方向）
path = r"C:\proj2\A5CharQ5\A5Defs.lean"
with open(path, encoding="utf-8") as f:
    s = f.read()

reps = []

# A. a_11 :1108 pow_add -> ← pow_add（a_11 段3 行6）
old = """    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
  -- Di：a³·b² → b·a²（位置 5）＋幂拆合
  _ = pA ^ 3 * pB * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [show pA ^ 4 = pA * pA ^ 3 by rw [pow_succ']]
    rw [show pA ^ 3 * pB * (pA * pA ^ 3) * pB ^ 2 * pA * pB * pA ^ 4
        = pA ^ 3 * pB * pA * (pA ^ 3 * pB ^ 2) * pA * pB * pA ^ 4 by group]"""
new = """    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- Di：a³·b² → b·a²（位置 5）＋幂拆合
  _ = pA ^ 3 * pB * pA * pB * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [pow_succ']]
    rw [show pA ^ 3 * pB * (pA ^ 3 * pA) * pB ^ 2 * pA * pB * pA ^ 4
        = pA ^ 3 * pB * pA * (pA ^ 3 * pB ^ 2) * pA * pB * pA ^ 4 by group]"""
assert s.count(old) == 1, f"A count={s.count(old)}"
s = s.replace(old, new)

# B. a_11 :1129 pow_add -> ← pow_add（段6 行3）
old = """        = pB * (pA ^ 2 * pA ^ 2) * pB * (pA ^ 2 * pA) * pB * pA ^ 3 * pB * pA ^ 4 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
  -- Gi：a³ → b·a²·b（位置 6）＋b·b 合并
  _ = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite_lhs 1 [← b_a2_b_eq_a3]
    rw [show pB * pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB * pB) * pA ^ 3 * pB * pA ^ 4 by group]
    rw [show pA ^ 2 * pB * pB = pA ^ 2 * pB ^ 2 by rw [← pow_two]]"""
new = """        = pB * (pA ^ 2 * pA ^ 2) * pB * (pA ^ 2 * pA) * pB * pA ^ 3 * pB * pA ^ 4 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
  -- Gi：a³ → b·a²·b（位置 6）＋b·b 合并
  _ = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 := by
    nth_rewrite 1 [← b_a2_b_eq_a3]
    rw [show pB * pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB * pB) * pA ^ 3 * pB * pA ^ 4 by group]
    rw [show pA ^ 2 * pB * pB = pA ^ 2 * pB ^ 2 by rw [← pow_two]]
    rw [show pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB ^ 2) * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 by group]"""
assert s.count(old) == 1, f"B count={s.count(old)}"
s = s.replace(old, new)

# C. b_7 段1 行1：show 包整 LHS
old = """  _ = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB := by
    nth_rewrite 1 [show pA ^ 4 = pA ^ 2 * pA ^ 2 by rw [← pow_add]]
    rw [show pB * (pA ^ 2 * pA ^ 2) * pB ^ 2 * pA ^ 4 * pB
        = pB * pA ^ 2 * (pA ^ 2 * pB ^ 2) * pA ^ 4 * pB by group]"""
new = """  _ = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB := by
    rw [show pB * pA ^ 4 * pB ^ 2 * pA ^ 4 * pB
        = pB * (pA ^ 2 * pA ^ 2) * pB ^ 2 * pA ^ 4 * pB by
          rw [← pow_add]]
    rw [show pB * (pA ^ 2 * pA ^ 2) * pB ^ 2 * pA ^ 4 * pB
        = pB * pA ^ 2 * (pA ^ 2 * pB ^ 2) * pA ^ 4 * pB by group]"""
assert s.count(old) == 1, f"C count={s.count(old)}"
s = s.replace(old, new)

# D. b_7 段2：拆 b² + show 改模式
old = """  _ = pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 4 * pB := by
    rw [show pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB
        = (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 4 * pB by group]
    rw [b_a2_b_eq_a3]"""
new = """  _ = pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 4 * pB := by
    rw [show pB ^ 2 = pB * pB by rw [pow_two]]
    rw [show pB * pA ^ 2 * (pB * pB) * pA ^ 3 * pB * pA ^ 4 * pB
        = (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 4 * pB by group]
    rw [b_a2_b_eq_a3]"""
assert s.count(old) == 1, f"D count={s.count(old)}"
s = s.replace(old, new)

# E. b_7 段3：拆 a³×2 + show 改模式
old = """  _ = pA * pB * pB * pA * pB * pA ^ 4 * pB := by
    rw [show pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 4 * pB
        = pA * (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA ^ 4 * pB by group]
    rw [a2_b_a2_eq_b2]"""
new = """  _ = pA * pB * pB * pA * pB * pA ^ 4 * pB := by
    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ]]
    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ]]
    rw [show (pA * pA ^ 2) * pB * (pA * pA ^ 2) * pB * pA ^ 4 * pB
        = pA * (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA ^ 4 * pB by group]
    rw [a2_b_a2_eq_b2]"""
assert s.count(old) == 1, f"E count={s.count(old)}"
s = s.replace(old, new)

# F. b_11 段1：← pow_two ×2
old = """  -- 1：bb → a²·b·a²（位置 0，rule2 反向；先合并最左 bb）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2 := by
    rw [show pB * pB * pA * pB * pA * pB * pB
        = pB ^ 2 * pA * pB * pA * pB ^ 2 by
          rw [← pow_two]]"""
new = """  -- 1：bb → a²·b·a²（位置 0，rule2 反向；先合并最左 bb）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2 := by
    rw [show pB * pB * pA * pB * pA * pB * pB
        = pB ^ 2 * pA * pB * pA * pB ^ 2 by
          rw [← pow_two, ← pow_two]]"""
assert s.count(old) == 1, f"F count={s.count(old)}"
s = s.replace(old, new)

# G. b_11 段4：行1 前加 show 括块
old = """  _ = pA ^ 2 * pB ^ 2 * pA ^ 4 * pB ^ 2 * pA ^ 2 := by
    rw [← a2_b_comm]
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pB * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]"""
new = """  _ = pA ^ 2 * pB ^ 2 * pA ^ 4 * pB ^ 2 * pA ^ 2 := by
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pB * pA ^ 2 by group]
    rw [← a2_b_comm]
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pB * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]"""
assert s.count(old) == 1, f"G count={s.count(old)}"
s = s.replace(old, new)

# H. b_11 段5 行5：pow_add -> ← pow_add
old = """        = (pA ^ 2 * pA ^ 2) * pB * pA * pB ^ 2 * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
  -- 6：bb → a²·b·a²（位置 6，rule2 反向；b² 单块）＋幂合并"""
new = """        = (pA ^ 2 * pA ^ 2) * pB * pA * pB ^ 2 * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- 6：bb → a²·b·a²（位置 6，rule2 反向；b² 单块）＋幂合并"""
assert s.count(old) == 1, f"H count={s.count(old)}"
s = s.replace(old, new)

# I. b_11 段6 行4：pow_add -> ← pow_add
old = """        = pA ^ 4 * pB * (pA * pA ^ 2) * pB * (pA ^ 2 * pA ^ 2) by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]"""
new = """        = pA ^ 4 * pB * (pA * pA ^ 2) * pB * (pA ^ 2 * pA ^ 2) by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]"""
assert s.count(old) == 1, f"I count={s.count(old)}"
s = s.replace(old, new)

with open(path, "w", encoding="utf-8", newline="") as f:
    f.write(s)
print("all 9 batch2 replacements applied")
