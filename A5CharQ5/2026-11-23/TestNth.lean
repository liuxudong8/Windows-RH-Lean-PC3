import Mathlib

-- 测试 nth_rewrite 匹配顺序：目标是 ((a*b)*c)*d，mul_assoc 可匹配根（三元）和子项 ((a*b)*c)（三元）
-- 若 nth_rewrite 1 = 根、nth_rewrite 2 = 子项，则：
--   nth_rewrite 2 [mul_assoc] 应把子项 ((a*b)*c) 重绑为 a*(b*c)，得到 (a*(b*c))*d
example (x : Type) [Monoid x] (a b c d : x) : a * b * c * d = a * (b * c) * d := by
  nth_rewrite 2 [mul_assoc]
  -- 若成功，目标变成 (a*(b*c))*d = a*(b*c)*d，同树，rfl 闭合
  rfl

-- 对照：nth_rewrite 1 [mul_assoc] 匹配根 → ((a*b)*c)*d 变 (a*b)*(c*d)，目标不同
example (x : Type) [Monoid x] (a b c d : x) : a * b * (c * d) = a * b * c * d := by
  nth_rewrite 1 [mul_assoc]
  rfl

-- 反向（← mul_assoc）测试：((a*b)*c)*d → (a*(b*c))*d 需要匹配子项
example (x : Type) [Monoid x] (a b c d : x) : a * (b * c) * d = a * b * c * d := by
  nth_rewrite 2 [← mul_assoc]
  rfl
