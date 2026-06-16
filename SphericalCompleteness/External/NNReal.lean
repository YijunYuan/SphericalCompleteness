/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Auxiliary `NNReal` lemmas

Supporting lemmas on nonnegative reals.
-/

lemma NNReal.exists_add_one_div_pow_two_lt
(a b : NNReal) (h : a < b) : ∃ n : ℕ, a + 1 / 2 ^ n < b := by
  have hba : 0 < b - a := tsub_pos_of_lt h
  have htend : Filter.Tendsto (fun n : ℕ => (1 / 2 : NNReal) ^ n) Filter.atTop (nhds 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  obtain ⟨n, hn⟩ := (htend.eventually (eventually_lt_nhds hba)).exists
  refine ⟨n, ?_⟩
  rw [div_pow, one_pow] at hn
  exact lt_tsub_iff_left.mp hn
