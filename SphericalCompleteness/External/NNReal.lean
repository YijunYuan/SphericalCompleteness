import Mathlib.Data.NNReal.Defs

lemma NNReal.exists_add_one_div_pow_two_lt
(a b : NNReal) (h : a < b) : ∃ n : ℕ, a + 1 / 2 ^ n < b := by
  let c : NNReal := ⟨b - a, by
    simpa only [sub_nonneg, NNReal.coe_le_coe] using le_of_lt h
    ⟩
  have hc : c > 0 := by
    unfold c
    refine NNReal.coe_pos.mp ?_
    simpa only [NNReal.coe_mk, sub_pos, NNReal.coe_lt_coe]
  rcases NNReal.exists_nat_pos_inv_lt hc with ⟨N, hN1, hN2⟩
  use N
  simp only [gt_iff_lt, one_div, c] at *
  field_simp at hN2
  replace hN2 : 1 < N * (b.val - a.val) := hN2
  field_simp
  suffices hh : 1 < 2 ^ N * (b.val - a.val) by
    nth_rw 1 [mul_sub, lt_sub_iff_add_lt, add_comm] at hh
    have : 2 ^ N * a.val + 1 = ↑(2 ^ N * a + 1) := rfl
    rw [this] at hh
    have : 2 ^ N * b.val = ↑(2 ^ N * b) := rfl
    nth_rw 1 [this, mul_comm] at hh
    exact NNReal.coe_lt_coe.mp hh
  refine lt_trans hN2 ?_
  refine mul_lt_mul_of_lt_of_le_of_pos_of_nonneg ?_ (le_refl _) hc <| pow_nonneg zero_le_two N
  suffices _ : N < 2 ^ N by norm_cast
  exact Nat.lt_two_pow_self
