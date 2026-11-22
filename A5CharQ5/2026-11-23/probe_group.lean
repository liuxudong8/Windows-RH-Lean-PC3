import A5CharQ5.A5Defs

-- 探针1：group 后 rw ← pow_two 能否闭合 a^2*b*(b*a^2) = a^2*b^2*a^2
example : pA ^ 2 * pB * (pB * pA ^ 2) = pA ^ 2 * pB ^ 2 * pA ^ 2 := by
  group
  rw [← pow_two]

-- 探针2：group 能否把 a^2*b*a^3*(b*b) 的尾 (b*b) 露出来 → b^2
example : pA ^ 2 * pB * pA ^ 3 * (pB * pB) = pA ^ 2 * pB * pA ^ 3 * pB ^ 2 := by
  group
  rw [← pow_two]

-- 探针3：hba 完整链（b_8 新链）group 兜底
example : pB ^ 2 * pA * pB * pB = pA ^ 2 * pB ^ 2 * pA ^ 2 := by
  rw [hba]
  group
  rw [← pow_two, ← pow_two]

-- 探针4：b_a2_comm 反向 a^3*b^2 -> b*a^2 后 group 兜底
example : pA ^ 2 * pB * pA ^ 3 * pB * pB = pA ^ 2 * pB * (pB * pA ^ 2) := by
  rw [show pA ^ 3 * pB ^ 2 = pB * pA ^ 2 by rw [b_a2_comm]]
  group

-- 探针5：a_11 一处坏行 :1060 的目标（数学 = 上一步）
example : pA * pB * pA ^ 3 * pB * pA ^ 4 * pB ^ 2 * pA ^ 2 = pA * pB * pA ^ 3 * pB * pA * pB * pA ^ 4 := by
  rw [show pA ^ 4 * pB ^ 2 * pA ^ 2 = pA * pB * pA ^ 4 by
        rw [← a2_b_a2_eq_b2, show pA ^ 6 = pA by
          rw [← pow_add, show pA ^ 5 = 1 by rw [pA_pow_five], mul_one]]]
  group
