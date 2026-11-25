# 用行号定位整段替换 coset_b_11（:1248 起，到下一个 lemma 前）
path = r"C:\proj2\A5CharQ5\A5Defs.lean"
with open(path, encoding="utf-8") as f:
    lines = f.readlines()

start = next(i for i, l in enumerate(lines) if "lemma coset_b_11" in l)
end = next(i for i, l in enumerate(lines[start + 1:], start + 1)
           if l.startswith("lemma ") and "coset_b_11" not in l)

print("start line:", start + 1, repr(lines[start].strip()))
print("end line:", end + 1, repr(lines[end].strip()))

new_block = r'''lemma coset_b_11 : ∃ k : Fin 5, pB * cosetRep 11 = cosetRep 7 * pA ^ k.val := by
  use (1 : Fin 5)
  change pB * (pB * pA * pB * pA * pB * pB) = pA * pB * pA * pB * pA
  calc pB * (pB * pA * pB * pA * pB * pB)
      = pB * pB * pA * pB * pA * pB * pB := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- 1：bb → a²·b·a²（位置 0，rule2 反向；最左 bb 块）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA * pB ^ 2 := by
    nth_rewrite_lhs 1 [← a2_b_a2_eq_b2]
    rw [show (pA ^ 2 * pB * pA ^ 2) * pA * pB * pA * pB * pB
        = pA ^ 2 * pB * (pA ^ 2 * pA) * pB * pA * (pB * pB) by group]
    rw [show pA ^ 2 * pA = pA ^ 3 by rw [← pow_succ]]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 2：bb → a²·b·a²（位置 8，rule2 反向；尾部 b² 单块）＋幂合并
  _ = pA ^ 2 * pB * pA ^ 3 * pB * pA ^ 3 * pB * pA ^ 2 := by
    rw [← a2_b_a2_eq_b2]
    rw [show pA ^ 2 * pB * pA ^ 3 * pB * pA * (pA ^ 2 * pB * pA ^ 2)
        = pA ^ 2 * pB * pA ^ 3 * pB * (pA * pA ^ 2) * pB * pA ^ 2 by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
  -- 3：aaa → b·a²·b（位置 3，rule3 反向；首 a³ 单块）＋幂合并
  _ = pA ^ 2 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 3 * pB * pA ^ 2 := by
    nth_rewrite_lhs 1 [← b_a2_b_eq_a3]
    rw [show pA ^ 2 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 3 * pB * pA ^ 2
        = pA ^ 2 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 3 * pB * pA ^ 2 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 4：b²·a³ → a²·b（位置 6，rule1 反向；b²·a³ 单块）＋幂合并
  _ = pA ^ 2 * pB ^ 2 * pA ^ 4 * pB ^ 2 * pA ^ 2 := by
    rw [← a2_b_comm]
    rw [show pA ^ 2 * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pB * pA ^ 2
        = pA ^ 2 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pB * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 5：b²·a³ → a²·b（位置 2，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并
  _ = pA ^ 4 * pB * pA * pB ^ 2 * pA ^ 2 := by
    nth_rewrite_lhs 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    rw [show pA ^ 2 * pB ^ 2 * (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2
        = pA ^ 2 * (pB ^ 2 * pA ^ 3) * pA * pB ^ 2 * pA ^ 2 by group]
    rw [← a2_b_comm]
    rw [show pA ^ 2 * (pA ^ 2 * pB) * pA * pB ^ 2 * pA ^ 2
        = (pA ^ 2 * pA ^ 2) * pB * pA * pB ^ 2 * pA ^ 2 by group]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
  -- 6：bb → a²·b·a²（位置 6，rule2 反向；b² 单块）＋幂合并
  _ = pA ^ 4 * pB * pA ^ 3 * pB * pA ^ 4 := by
    rw [← a2_b_a2_eq_b2]
    rw [show pA ^ 4 * pB * pA * (pA ^ 2 * pB * pA ^ 2) * pA ^ 2
        = pA ^ 4 * pB * (pA * pA ^ 2) * pB * (pA ^ 2 * pA ^ 2) by group]
    rw [show pA * pA ^ 2 = pA ^ 3 by rw [← pow_succ']]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
  -- 7：aaa → b·a²·b（位置 5，rule3 反向；a³ 单块）＋幂合并
  _ = pA ^ 4 * pB ^ 2 * pA ^ 2 * pB ^ 2 * pA ^ 4 := by
    rw [← b_a2_b_eq_a3]
    rw [show pA ^ 4 * pB * (pB * pA ^ 2 * pB) * pB * pA ^ 4
        = pA ^ 4 * (pB * pB) * pA ^ 2 * (pB * pB) * pA ^ 4 by group]
    rw [show pB * pB = pB ^ 2 by rw [← pow_two]]
  -- 8：b²·a³ → a²·b（位置 8，rule1 反向；拆 a⁴ 只动 LHS）＋幂合并
  _ = pA ^ 4 * pB ^ 2 * pA ^ 4 * pB * pA := by
    nth_rewrite_lhs 1 [show pA ^ 4 = pA ^ 3 * pA by rw [← pow_succ]]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * pB ^ 2 * (pA ^ 3 * pA)
        = (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pB ^ 2 * pA ^ 3) * pA by group]
    rw [← a2_b_comm]
    rw [show (pA ^ 3 * pA) * pB ^ 2 * pA ^ 2 * (pA ^ 2 * pB) * pA
        = pA ^ 4 * pB ^ 2 * (pA ^ 2 * pA ^ 2) * pB * pA by group]
    rw [show pA ^ 3 * pA = pA ^ 4 by rw [← pow_succ]]
    rw [show pA ^ 2 * pA ^ 2 = pA ^ 4 by rw [pow_add]]
  -- 9：a⁴·b²·a⁴ → a·b·a（位置 0-9，rule4 反向；跨三因子）
  _ = pA * pB * pA * pB * pA := by
    rw [← a_b_a_eq_a4_b2_a4]
    rw [show (pA * pB * pA) * pB * pA
        = pA * pB * pA * pB * pA by group]
'''

lines[start:end] = [new_block]
with open(path, "w", encoding="utf-8", newline="") as f:
    f.writelines(lines)
print("replaced ok")
