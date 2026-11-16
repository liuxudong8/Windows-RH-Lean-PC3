# fix_batch4：第四批修正
path = r"C:\proj2\A5CharQ5\A5Defs.lean"
with open(path, encoding="utf-8") as f:
    s = f.read()

# 1. a_11 段4 行1-2：pow_succ' 正向给 a·a³，show 模式同步
old = """    nth_rewrite 1 [show pA ^ 4 = pA ^ 3 * pA by rw [pow_succ']]
    rw [show pA ^ 3 * pB * (pA ^ 3 * pA) * pB ^ 2 * pA * pB * pA ^ 4
        = pA ^ 3 * pB * pA * (pA ^ 3 * pB ^ 2) * pA * pB * pA ^ 4 by group]"""
new = """    nth_rewrite 1 [show pA ^ 4 = pA * pA ^ 3 by rw [pow_succ']]
    rw [show pA ^ 3 * pB * (pA * pA ^ 3) * pB ^ 2 * pA * pB * pA ^ 4
        = pA ^ 3 * pB * pA * (pA ^ 3 * pB ^ 2) * pA * pB * pA ^ 4 by group]"""
assert s.count(old) == 1, f"1 count={s.count(old)}"
s = s.replace(old, new)

# 2. a_11 段7 行3：先重组再合并 b·b
old = """    rw [show pA ^ 2 * pB * pB = pA ^ 2 * pB ^ 2 by rw [← pow_two]]
    rw [show pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB ^ 2) * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 by group]"""
new = """    rw [show (pA ^ 2 * pB) * pB = pA ^ 2 * (pB * pB) by rw [← mul_assoc]]
    rw [show pA ^ 2 * (pB * pB) = pA ^ 2 * pB ^ 2 by rw [← pow_two]]
    rw [show pB * pA ^ 4 * pB * pB * (pA ^ 2 * pB ^ 2) * pA ^ 3 * pB * pA ^ 4
        = pB * pA ^ 4 * pB * pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 by group]"""
assert s.count(old) == 1, f"2 count={s.count(old)}"
s = s.replace(old, new)

# 3. a_11 段8 行4：双 b·b 合并 + a⁴ 合并
old = """    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- Ai：a⁴·b²·a⁴ → a·b·a（位置 1-10）
  _ = pB * pA * pB * pA * pB ^ 2 * pA ^ 4 := by"""
new = """    rw [← pow_two, ← pow_two]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- Ai：a⁴·b²·a⁴ → a·b·a（位置 1-10）
  _ = pB * pA * pB * pA * pB ^ 2 * pA ^ 4 := by"""
assert s.count(old) == 1, f"3 count={s.count(old)}"
s = s.replace(old, new)

# 4. b_7 段1 行5-8：group 重写（去 mul_assoc show）
old = """    rw [show pA ^ 2 * (pB * pB) = (pA ^ 2 * pB) * pB by rw [mul_assoc]]
    rw [show pB * pA ^ 2 * ((pA ^ 2 * pB) * pB) * pA ^ 4 * pB
        = pB * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 4 * pB by group]
    rw [a2_b_comm]
    rw [show pB * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pB * pA ^ 4 * pB
        = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB by group]"""
new = """    rw [show pB * pA ^ 2 * (pA ^ 2 * (pB * pB)) * pA ^ 4 * pB
        = pB * pA ^ 2 * ((pA ^ 2 * pB) * pB) * pA ^ 4 * pB by group]
    rw [show pB * pA ^ 2 * ((pA ^ 2 * pB) * pB) * pA ^ 4 * pB
        = pB * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 4 * pB by group]
    rw [a2_b_comm]
    rw [show pB * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pB * pA ^ 4 * pB
        = pB * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 4 * pB by group]"""
assert s.count(old) == 1, f"4 count={s.count(old)}"
s = s.replace(old, new)

# 5. b_7 段3 行1-2：pow_succ -> pow_succ'
old = """    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ]]
    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ]]"""
new = """    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ']]
    rw [show pA ^ 3 = pA * pA ^ 2 by rw [pow_succ']]"""
assert s.count(old) == 1, f"5 count={s.count(old)}"
s = s.replace(old, new)

# 6. b_11 段1 行1：group 重组尾部 + 双合并
old = """    rw [show pB * pB * pA * pB * pA * pB * pB
        = pB ^ 2 * pA * pB * pA * pB ^ 2 by
          rw [← pow_two, ← pow_two]]"""
new = """    rw [show pB * pB * pA * pB * pA * pB * pB
        = pB * pB * pA * pB * pA * (pB * pB) by group]
    rw [show pB * pB * pA * pB * pA * (pB * pB)
        = pB ^ 2 * pA * pB * pA * pB ^ 2 by
          rw [← pow_two, ← pow_two]]"""
assert s.count(old) == 1, f"6 count={s.count(old)}"
s = s.replace(old, new)

# 7. b_11 段2 行1：show 包完整 LHS
old = """  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 2 := by
    rw [← a2_b_a2_eq_b2]"""
new = """  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 2 := by
    rw [show pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2
        = pA ^ 2 * pB * pA ^ 3 * pB * pA * (pA ^ 2 * pB * pA ^ 2) by
          rw [← a2_b_a2_eq_b2]]"""
assert s.count(old) == 1, f"7 count={s.count(old)}"
s = s.replace(old, new)

# 8. b_11 段4 行5：重组尾部 + b² 合并 + a⁴ 合并
old = """    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 5：b²·a³ → a²·b（位置 2，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并"""
new = """    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
    rw [show pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * (pB * pB) * pA ^ 2 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [← pow_add]]
  -- 5：b²·a³ → a²·b（位置 2，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并"""
assert s.count(old) == 1, f"8 count={s.count(old)}"
s = s.replace(old, new)

# 9. b_11 段7 行3：show 包完整 LHS
old = """    rw [← pow_two, ← pow_two]
  -- 8：b²·a³ → a²·b（位置 8，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并"""
new = """    rw [show pA ^ 4 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 4
        = pA ^ 4 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 4 by
          rw [← pow_two, ← pow_two]]
  -- 8：b²·a³ → a²·b（位置 8，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并"""
assert s.count(old) == 1, f"9 count={s.count(old)}"
s = s.replace(old, new)

# 10. b_11 段9：删冗余 show 行
old = """  _ = pA * pB * pA * pB * pA := by
    rw [← a_b_a_eq_a4_b2_a4]
    rw [show (pA * pB * pA) * pB * pA
        = pA * pB * pA * pB * pA by group]
lemma pA_mul_coset"""
new = """  _ = pA * pB * pA * pB * pA := by
    rw [← a_b_a_eq_a4_b2_a4]
lemma pA_mul_coset"""
assert s.count(old) == 1, f"10 count={s.count(old)}"
s = s.replace(old, new)

with open(path, "w", encoding="utf-8", newline="") as f:
    f.write(s)
print("all 10 batch4 replacements applied")
