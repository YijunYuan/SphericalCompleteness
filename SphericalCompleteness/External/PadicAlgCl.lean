import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Base

open PadicAlgCl
open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

lemma exists_rat_pow_p_norm_between (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : ∃ c : ℚ,
  a < ‖(p : (PadicAlgCl p))‖ ^ (c : ℝ) ∧
  ‖(p : (PadicAlgCl p))‖ ^ (c : ℝ) < b := by
  let a' := a + (b - a) / 2
  have ha' : 0 < a' := by
    unfold a'; linarith
  have ha'b : a' < b := by
    unfold a'; linarith
  have : (p : PadicAlgCl p) = ((p : ℚ_[p]): PadicAlgCl p) := rfl
  have := this ▸ PadicAlgCl.norm_extends p (p : ℚ_[p])
  repeat rw [this]
  rw [Padic.norm_p]
  have : Real.logb ((↑p)⁻¹) b < Real.logb ((↑p)⁻¹) a' := by
    simp
    refine Real.logb_lt_logb ?_ ha' ha'b
    simpa only [Nat.one_lt_cast] using hp.out.one_lt
  rcases exists_rat_btwn this with ⟨c, hc1, hc2⟩
  use c
  constructor
  · simp only [Real.logb_inv_base] at hc2
    replace hc2 : Real.logb (↑p) a' < -↑c := lt_neg_of_lt_neg hc2
    apply (Real.logb_lt_iff_lt_rpow
      (by simpa only [Nat.one_lt_cast] using hp.out.one_lt) ha').1 at hc2
    rw [Real.rpow_neg_eq_inv_rpow] at hc2
    refine lt_trans ?_ hc2
    simpa [a']
  · simp only [Real.logb_inv_base] at hc1
    replace hc1 : Real.logb (↑p) b > -↑c := neg_lt_of_neg_lt hc1
    simp only [gt_iff_lt] at hc1
    rw [Real.lt_logb_iff_rpow_lt
      (by simpa only [Nat.one_lt_cast] using hp.out.one_lt) (lt_trans ha' ha'b)] at hc1
    rwa [Real.rpow_neg_eq_inv_rpow] at hc1

noncomputable instance instDenselyNormedFieldPadicAlgCl : DenselyNormedField (PadicAlgCl p) where
  lt_norm_lt a b ha hab := by
    rcases exists_rat_pow_p_norm_between p a b ha hab with ⟨r, hr1, hr2⟩
    let f : Polynomial (PadicAlgCl p) := X ^ r.den - Polynomial.C ((p : PadicAlgCl p) ^ r.num)
    have hf : f.degree ≠ 0 := by
      have := @Polynomial.degree_eq_of_le_of_coeff_ne_zero _ r.den _ f ?_ ?_
      · simp [this]
      · unfold f
        rw [sub_eq_add_neg]
        refine le_trans (Polynomial.degree_add_le _ _) ?_
        simpa using le_trans degree_C_le Nat.WithBot.coe_nonneg
      · simp [f, Polynomial.coeff_C]
    rcases IsAlgClosed.exists_root f hf with ⟨z, hz⟩
    have hz' : z ^ r.den - (p : PadicAlgCl p) ^ r.num = 0 := by
      rw [← hz]
      simp only [f, eval_sub, eval_pow, eval_X, eval_C]
    replace hz' : ‖z‖ ^ r.den = ‖(p : PadicAlgCl p)‖ ^ r.num := by
      apply eq_of_sub_eq_zero at hz'
      repeat rw [← norm_pow]
      simp only [hz', norm_zpow]
    replace hz' : ‖z‖ = ‖(p : PadicAlgCl p)‖ ^ (↑r : ℝ) := by
      rw [← Rat.num_div_den r]
      simp
      apply_fun (fun x => x ^ (r.den : ℝ)⁻¹) at hz'
      repeat rw [← Real.rpow_natCast] at hz'
      rw [Real.rpow_rpow_inv (norm_nonneg z) (by simp)] at hz'
      rw [hz', Real.rpow_inv_eq (zpow_nonneg (norm_nonneg _) r.num)
        (Real.rpow_nonneg (norm_nonneg _) _) (by simp)]
      simp [← Real.rpow_mul (norm_nonneg _)]
    exact ⟨z, hz' ▸ ⟨hr1, hr2⟩⟩
