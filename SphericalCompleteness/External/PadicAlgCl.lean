/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Analysis.Normed.Field.Approximation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Bases

/-!
# Algebraic closure of the `p`-adics

Auxiliary results on the algebraic closure of the `p`-adic numbers.
-/

@[expose] public section

open PadicAlgCl
open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Between any two nonnegative reals `a < b` there is a rational power of `‖p‖` (the `p`-adic norm
of the prime `p` in `PadicAlgCl p`). This is the density input that makes `PadicAlgCl p` a densely
normed field: the norm attains values `‖p‖ ^ (c : ℝ)` for `c : ℚ`, which are dense in `ℝ≥0`. -/
private lemma exists_rat_pow_p_norm_between (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : ∃ c : ℚ,
    a < ‖(p : (PadicAlgCl p))‖ ^ (c : ℝ) ∧
    ‖(p : (PadicAlgCl p))‖ ^ (c : ℝ) < b := by
  let a' := a + (b - a) / 2
  have ha' : 0 < a' := by unfold a'; linarith
  have ha'b : a' < b := by unfold a'; linarith
  have : (p : PadicAlgCl p) = ((p : ℚ_[p]): PadicAlgCl p) := rfl
  replace := this ▸ PadicAlgCl.norm_extends p (p : ℚ_[p])
  repeat rw [this]
  rw [Padic.norm_p]
  have : Real.logb ((↑p)⁻¹) b < Real.logb ((↑p)⁻¹) a' := by
    simp only [Real.logb_inv_base, neg_lt_neg_iff]
    refine Real.logb_lt_logb ?_ ha' ha'b
    simpa only [Nat.one_lt_cast] using hp.out.one_lt
  rcases exists_rat_btwn this with ⟨c, hc1, hc2⟩
  refine ⟨c, ?_, ?_⟩
  · simp only [Real.logb_inv_base] at hc2
    replace hc2 : Real.logb (↑p) a' < -↑c := lt_neg_of_lt_neg hc2
    apply (Real.logb_lt_iff_lt_rpow
      (by simpa only [Nat.one_lt_cast] using hp.out.one_lt) ha').1 at hc2
    rw [Real.rpow_neg_eq_inv_rpow] at hc2
    exact lt_trans (by simpa [a']) hc2
  · simp only [Real.logb_inv_base] at hc1
    replace hc1 : Real.logb (↑p) b > -↑c := neg_lt_of_neg_lt hc1
    simp only [gt_iff_lt] at hc1
    rw [Real.lt_logb_iff_rpow_lt
      (by simpa only [Nat.one_lt_cast] using hp.out.one_lt) (lt_trans ha' ha'b)] at hc1
    rwa [Real.rpow_neg_eq_inv_rpow] at hc1

/--
`PadicAlgCl p` is a densely normed field.

This instance supplies `DenselyNormedField (PadicAlgCl p)`, i.e. it asserts that the norm on
`PadicAlgCl p` is nontrivial and that for any `r : ℝ` and any `x : PadicAlgCl p` with `r < ‖x‖`,
there exists `y : PadicAlgCl p` with `r < ‖y‖` and `‖y‖ < ‖x‖`. Equivalently, the values of the
norm are order-dense in `ℝ≥0`.

The instance is marked `noncomputable` because it relies on classical choice/analysis facts rather
than an algorithm.
-/
noncomputable instance instDenselyNormedFieldPadicAlgCl : DenselyNormedField (PadicAlgCl p) where
  lt_norm_lt a b ha hab := by
    rcases exists_rat_pow_p_norm_between p a b ha hab with ⟨r, hr1, hr2⟩
    let f : Polynomial (PadicAlgCl p) := X ^ r.den - Polynomial.C ((p : PadicAlgCl p) ^ r.num)
    have hf : f.degree ≠ 0 := by simp [f, Polynomial.degree_X_pow_sub_C r.den_pos]
    rcases IsAlgClosed.exists_root f hf with ⟨z, hz⟩
    have hz' : z ^ r.den - (p : PadicAlgCl p) ^ r.num = 0 := by
      rw [← hz]; simp only [f, eval_sub, eval_pow, eval_X, eval_C]
    replace hz' : ‖z‖ ^ r.den = ‖(p : PadicAlgCl p)‖ ^ r.num := by
      apply eq_of_sub_eq_zero at hz'
      repeat rw [← norm_pow]
      simp only [hz', norm_zpow]
    replace hz' : ‖z‖ = ‖(p : PadicAlgCl p)‖ ^ (↑r : ℝ) := by
      rw [← Rat.num_div_den r]
      simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      apply_fun (fun x ↦ x ^ (r.den : ℝ)⁻¹) at hz'
      repeat rw [← Real.rpow_natCast] at hz'
      rw [Real.rpow_rpow_inv (norm_nonneg z) (by simp)] at hz'
      rw [hz', Real.rpow_inv_eq (zpow_nonneg (norm_nonneg _) r.num)
        (Real.rpow_nonneg (norm_nonneg _) _) (by simp)]
      simp [← Real.rpow_mul (norm_nonneg _)]
    exact ⟨z, hz' ▸ ⟨hr1, hr2⟩⟩

open Classical in
/--
`PadicAlgCl p` is a separable topological space.

This instance provides `TopologicalSpace.SeparableSpace (PadicAlgCl p)`, i.e. it asserts the
existence of a countable dense subset of `PadicAlgCl p` with respect to its given topology.
Such an instance is often used to enable results and constructions that require separability
(e.g. working with dense sequences or applying theorems stated for separable spaces).
-/
instance instSeparableSpacePadicAlgCl : TopologicalSpace.SeparableSpace (PadicAlgCl p) where
  exists_countable_dense := by
    refine ⟨{z : PadicAlgCl p | IsAlgebraic ℚ z}, Algebraic.countable ℚ (PadicAlgCl p),
      Metric.dense_iff.mpr <| fun α ε hε ↦ ?_⟩
    rcases (PadicAlgCl.isAlgebraic p).isAlgebraic α with ⟨f', hfne', hfz'⟩
    set f := f' * C (f'.leadingCoeff)⁻¹ with hf_def
    have hf : Monic f := monic_mul_leadingCoeff_inv hfne'
    have hfz : aeval α f = 0 := by rw [hf_def, aeval_mul, hfz', zero_mul]
    have hdense : DenseRange (algebraMap ℚ ℚ_[p]) := by
      have : (algebraMap ℚ ℚ_[p] : ℚ → ℚ_[p]) = Rat.cast := by ext q; simp [Rat.cast_def]
      rw [this]; exact Padic.denseRange_ratCast p
    set n := f.natDegree with hn
    have hnpos : 0 < n := natDegree_pos_of_monic_of_aeval_eq_zero hf hfz
    set M := max ‖α‖ 1 with hM
    have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    set δ := (ε / M) ^ (n : ℝ) / (n + 1) with hδ_def
    have hδpos : 0 < δ :=
      div_pos (Real.rpow_pos_of_pos (div_pos hε hMpos) _) (by positivity)
    rcases exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hdense hf hδpos
      with ⟨g, hgm, hdeg, hgcoeff⟩
    rcases exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hδpos (f := f) (g := g.map (algebraMap ℚ ℚ_[p])) hfz hf (hgm.map _)
      (by rw [natDegree_map_eq_of_injective (algebraMap ℚ ℚ_[p]).injective]; omega)
      (fun i ↦ by simpa using hgcoeff i) (IsAlgClosed.splits _) with ⟨β, hβroot, hβnorm⟩
    refine ⟨β, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm, dist_eq_norm]
      refine hβnorm.trans_le ?_
      rw [← hn, ← hM, show ((↑n + 1) * δ) = (ε / M) ^ (n : ℝ) by rw [hδ_def]; field_simp,
        ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by positivity : (n : ℝ) ≠ 0),
        Real.rpow_one, div_mul_cancel₀ _ (ne_of_gt hMpos)]
    · simp only [Set.mem_setOf_eq]
      rw [mem_aroots] at hβroot
      refine ⟨g, hgm.ne_zero, ?_⟩
      have hβ := hβroot.2
      rwa [aeval_map_algebraMap] at hβ
