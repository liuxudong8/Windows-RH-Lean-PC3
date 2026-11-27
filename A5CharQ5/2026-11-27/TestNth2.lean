import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Monoid.Basic

-- 测试 b_7/b_8/b_11 修复所需的 rw 关键模式
-- 环境：C:\proj2 为 lake 项目根，mathlib 在 ./mathlib4-master

-- ============ 测试 1：rw [← mul_assoc] 在长链中的命中位置 ============
-- 目的：确认 rw [← mul_assoc] 命中最左最深的 (a*b)*c 节点（即 L2）
-- 源：((((pB*pA)*pB)*pA)*pB)（5 因子，左结合）
-- 期望：命中 L2 = (pB*pA)*pB → pB*(pA*pB)，得到 ((pB*(pA*pB))*pA)*pB = pB*(pA*pB)*pA*pB
example (x : Type) [Monoid x] (pA pB : x) : pB*pA*pB*pA*pB = pB*(pA*pB)*pA*pB := by
  rw [← mul_assoc]
  rfl

-- ============ 测试 2：两次 ← mul_assoc 得到 pB*(pA*pB*pA)*pB ============
example (x : Type) [Monoid x] (pA pB : x) : pB*pA*pB*pA*pB = pB*(pA*pB*pA)*pB := by
  rw [← mul_assoc, ← mul_assoc]
  rfl

-- ============ 测试 3：simpa [mul_assoc] 闭合括号化差异（因子序相同） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pB*(pA^4*pB^2*pA^4)*pB = pB*pA^4*pB^2*pA^4*pB := by
  simpa [mul_assoc]

-- ============ 测试 4：show + rw 幂拆解（pA^4 = pA^2*pA^2，匹配第一个 pA^4） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^4*pB^2*pA^4*pB = pB*pA^2*pA^2*pB^2*pA^4*pB := by
  rw [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
  rfl

-- ============ 测试 5：rw [← mul_assoc] 命中 L2 = (pB*pA^2)*pA^2 → (pB*pA^2)*(pA^2*pB^2) ============
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pA^2*pB^2*pA^4*pB = (pB*pA^2)*(pA^2*pB^2)*pA^4*pB := by
  rw [← mul_assoc]
  rfl

-- ============ 测试 6：show pA^2*pB^2 = pB^2*pA^3*pB（拆 b² + A 规则） ============
example (x : Type) [Monoid x] (pA pB : x)
    (hA : pA^2*pB = pB^2*pA^3) :
    (pB*pA^2)*(pA^2*pB^2)*pA^4*pB = (pB*pA^2)*(pB^2*pA^3*pB)*pA^4*pB := by
  rw [show pA^2*pB^2 = pB^2*pA^3*pB by
      rw [pow_two, mul_assoc, hA]]

-- ============ 测试 7：rw [pow_two] 匹配 pB^2 原子（任意深度） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pA^2*pB^2*pA^3*pB*pA^4*pB = pB*pA^2*pB*pB*pA^3*pB*pA^4*pB := by
  rw [pow_two]

-- ============ 测试 8：rw [← pow_succ] 匹配 pB*pB^2 → pB^3（任意深度） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pB*pB^2*pA^3*pB*pA^3*pB*pA^4*pB = pB^3*pA^3*pB*pA^3*pB*pA^4*pB := by
  rw [← pow_succ]

-- ============ 测试 9：rw [pB_pow_three] + simp ============
example (x : Type) [Monoid x] (pA pB : x) (hB : pB^3 = 1) :
    pB^3*pA^3*pB*pA^3*pB*pA^4*pB = pA^3*pB*pA^3*pB*pA^4*pB := by
  rw [hB]
  simp

-- ============ 测试 10：rw [show pA^6 = pA ...]（pow_succ' + pA_pow_five） ============
example (x : Type) [Monoid x] (pA pB : x) (hA5 : pA^5 = 1) :
    pA*pB^2*pA^6*pB*pA^4*pB = pA*pB^2*pA*pB*pA^4*pB := by
  rw [show pA^6 = pA by
      rw [pow_succ', hA5]
      simp]

-- ============ 测试 11：rw [← pow_add] 匹配 pA^3*pA^3 → pA^6（直接子项） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB^2*(pA^3*pA^3)*pB*pA^4*pB = pA*pB^2*pA^6*pB*pA^4*pB := by
  rw [← pow_add]

-- ============ 测试 12：rw [← mul_assoc] 于 (pA*pB^2)*pA^3 → (pA*pB^2)*(pA^3*pA^3) ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB^2*pA^3*pA^3*pB*pA^4*pB = pA*pB^2*(pA^3*pA^3)*pB*pA^4*pB := by
  rw [← mul_assoc]
  rfl

-- ============ 测试 13：show pA^4*pB = pA^2*(pA^2*pB) ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pB*pA^4*pB = pA*pB*pB*pA*pB*pA^2*(pA^2*pB) := by
  rw [show pA^4*pB = pA^2*(pA^2*pB) by
      rw [show pA^4 = pA^2*pA^2 by rw [← pow_add]]
      simpa [mul_assoc]]

-- ============ 测试 14：simpa 重组隔离子项（因子序相同） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pB*pA^2*pB^2*pA^3 = pA*pB*pB*pA*(pB*pA^2*pB^2*pA^3) := by
  simpa [mul_assoc]

-- ============ 测试 15：rw [pow_two] 于括号子项内部 ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*(pB*pA^2*pB^2*pA^3) = pA*pB*pB*pA*(pB*pA^2*pB*pB*pA^3) := by
  rw [pow_two]

-- ============ 测试 16：rw [← mul_assoc] 于括号子项内部（命中 L2 = (pB*pA^2)*pB） ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*(pB*pA^2*pB*pB*pA^3) = pA*pB*pB*pA*(pB*(pA^2*pB)*pB*pA^3) := by
  rw [← mul_assoc]
  rfl

-- ============ 测试 17：pA*(pA^3*pB*pA^3) 中合并 pA*pA^3 ============
-- 源：(pA*pB*pB*pA)*(pA^3*pB*pA^3)，目标：(pA*pB*pB)*(pA*pA^3)*pB*pA^3
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*(pA^3*pB*pA^3) = pA*pB*pB*pA*pA^3*pB*pA^3 := by
  simpa [mul_assoc]

-- ============ 测试 18：pA*pB*pB*pA*pA^3*pB*pA^3 = pA*pB*pB*pA^4*pB*pA^3 ============
-- 需要 pA*pA^3 合并，但 pA*pA^3 不是直接子项。用 show 匹配 (pA*pB*pB*pA)*pA^3 不行。
-- 方案：先 simpa 全左结合，再 rw [← pow_succ] 需要 pA*pA^3 子项 —— 这里验证失败预期？
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pA^3*pB*pA^3 = pA*pB*pB*pA^4*pB*pA^3 := by
  rw [show (pA*pB*pB*pA)*pA^3 = pA*pB*pB*pA^4 by
      rw [← mul_assoc]  -- (pA*pB*pB*pA)*pA^3 → ？ (a*b)*c 于 L4=(pA*pB*pB*pA)*pA^3 需 a*b = pA*pB*pB*pA → a=pA*pB*pB, b=pA → pA*pB*pB*(pA*pA^3)？不对，← mul_assoc 匹配 (a*b)*c 最左最深，这里子项内只有这一个三元节点
      ]
  -- 上面 rw 的 show 无法直接完成；改用嵌套 calc：
  sorry

-- ============ 测试 19：用 calc 子链完成测试 18 的变换 ============
example (x : Type) [Monoid x] (pA pB : x) :
    pA*pB*pB*pA*pA^3*pB*pA^3 = pA*pB*pB*pA^4*pB*pA^3 := by
  calc pA*pB*pB*pA*pA^3*pB*pA^3
      = pA*pB*pB*(pA*pA^3)*pB*pA^3 := by
          -- 树：((((((pA*pB)*pB)*pA)*pA^3)*pB)*pA^3)
          -- 需要 ((pA*pB*pB)*pA)*pA^3 → (pA*pB*pB)*(pA*pA^3)：命中 L4 = (((pA*pB)*pB)*pA)*pA^3
          -- rw [← mul_assoc] 命中 L2=(pA*pB)*pB 最先，失败预期 —— 改用 nth_rewrite？
          nth_rewrite 3 [← mul_assoc]
          rfl
  _ = pA*pB*pB*pA^4*pB*pA^3 := by
      rw [← pow_succ]  -- pA*pA^3 → pA^(3+1) = pA^4
      rfl

-- ============ 测试 20：b8 第 5 步 —— pA^3*pB^2 → pB*pA^2（Bi，← b_a2_comm） ============
example (x : Type) [Monoid x] (pA pB : x) (hBi : pA^3*pB^2 = pB*pA^2) :
    pA^2*pB*(pA^3*pB^2) = pA^2*pB*(pB*pA^2) := by
  rw [hBi]

-- ============ 测试 21：b11 的 Ci@8：pB^2 → pA^2*pB*pA^2（nth_rewrite 只替换第二个 pB^2） ============
example (x : Type) [Monoid x] (pA pB : x) (hCi : pB^2 = pA^2*pB*pA^2) :
    pA^2*pB*pA^3*pB*pA^3*pB*pA^2 = pA^2*pB*pA^3*pB*(pA^2*pB*pA^2)*pA^3*pB*pA^2 := by
  nth_rewrite 1 [hCi]
  rfl

-- ============ 测试 22：simpa [mul_assoc, pow_two] 之类？先不用 ============

end
