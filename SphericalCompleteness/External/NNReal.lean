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
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (tsub_pos_of_lt h) (by norm_num : (1 / 2 : NNReal) < 1)
  exact ⟨n, lt_tsub_iff_left.mp (by rwa [div_pow, one_pow] at hn)⟩
