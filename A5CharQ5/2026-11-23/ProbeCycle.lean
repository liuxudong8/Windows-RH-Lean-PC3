import A5CharQ5.A5Defs

/-- multiset 每项 ≥ 2 时，`2 * card ≤ sum`。 -/
lemma two_mul_card_le_sum (t : Multiset ℕ) (h : ∀ a ∈ t, 2 ≤ a) : 2 * t.card ≤ t.sum := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 2 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, 2 ≤ b := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    have := ih hs
    rw [Multiset.card_cons, Multiset.sum_cons]
    omega

/-- A₅ 中元素的 cycleType 基数 ≤ 2。 -/
lemma G_cycleType_card_le_two (g : G) : g.val.cycleType.card ≤ 2 := by
  have h2 : ∀ a ∈ g.val.cycleType, 2 ≤ a :=
    fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha
  have h := two_mul_card_le_sum g.val.cycleType h2
  have h5 : g.val.cycleType.sum ≤ 5 := by
    have := Equiv.Perm.sum_cycleType_le g.val
    simpa using this
  omega

/-- A₅ 中元素满足 `Even (sum + card)`（符号为 +1 的等价形式）。 -/
lemma G_even_sum_add_card (g : G) : Even (g.val.cycleType.sum + g.val.cycleType.card) := by
  have hsign : g.val.sign = 1 := (MonoidHom.mem_ker).mp g.property
  have hn : (-1 : ℤˣ) ^ (g.val.cycleType.sum + g.val.cycleType.card) = 1 := by
    rw [← Equiv.Perm.sign_of_cycleType]
    exact hsign
  have hz : ((-1 : ℤ) ^ (g.val.cycleType.sum + g.val.cycleType.card) = 1) := by
    have hv := congrArg (fun u : ℤˣ => (u : ℤ)) hn
    simpa using hv
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hz

/-- **第 1 步**：A₅ 元素的 cycleType 只有四种 —— ∅、{3}、{5}、{2,2}。
    对应 A₅ 的四个共轭类 1、3A、5A/5B、2A。 -/
theorem G_cycleType_cases (g : G) :
    g.val.cycleType = 0 ∨ g.val.cycleType = {3} ∨
    g.val.cycleType = {5} ∨ g.val.cycleType = {2, 2} := by
  have hc : g.val.cycleType.card ≤ 2 := G_cycleType_card_le_two g
  have he : Even (g.val.cycleType.sum + g.val.cycleType.card) := G_even_sum_add_card g
  have h5 : g.val.cycleType.sum ≤ 5 := by
    have := Equiv.Perm.sum_cycleType_le g.val
    simpa using this
  have h2 : ∀ a ∈ g.val.cycleType, 2 ≤ a :=
    fun a ha => Equiv.Perm.two_le_of_mem_cycleType ha
  have hc3 : g.val.cycleType.card = 0 ∨ g.val.cycleType.card = 1 ∨
      g.val.cycleType.card = 2 := by omega
  rcases hc3 with h0 | h1 | h2c
  · left
    exact Multiset.card_eq_zero.mp h0
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h1
    have hmem : a ∈ g.val.cycleType := by rw [ha]; exact Multiset.mem_singleton.mpr rfl
    have ha2 : 2 ≤ a := h2 a hmem
    have hasum : a ≤ g.val.cycleType.sum := by rw [ha]; simp
    have ha5 : a ≤ 5 := le_trans hasum h5
    have hea : Even (a + 1) := by
      have h := he
      rw [ha, Multiset.sum_singleton, Multiset.card_singleton] at h
      simpa using h
    obtain ⟨k, hk⟩ := hea
    have : a = 3 ∨ a = 5 := by omega
    rcases this with rfl | rfl
    · right; left; exact ha
    · right; right; left; exact ha
  · obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp h2c
    have hmemx : x ∈ g.val.cycleType := by rw [hxy]; simp
    have hmemy : y ∈ g.val.cycleType := by rw [hxy]; simp
    have hx2 : 2 ≤ x := h2 x hmemx
    have hy2 : 2 ≤ y := h2 y hmemy
    have hsum : x + y ≤ 5 := by
      rw [hxy] at h5
      simpa using h5
    have hex : Even (x + y + 2) := by
      have h := he
      rw [hxy] at h
      simpa using h
    obtain ⟨k, hk⟩ := hex
    have hxy2 : x = 2 ∧ y = 2 := by omega
    right; right; right
    rw [hxy, hxy2.1, hxy2.2]
