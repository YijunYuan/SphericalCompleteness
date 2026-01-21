import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Bases
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Cardinal

import SphericalCompleteness.External.ContinuityOfRoots

open PadicAlgCl
open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

lemma exists_rat_pow_p_norm_between (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : ∃ c : ℚ,
  a < ‖(p : (PadicAlgCl p))‖ ^ (c : ℝ) ∧
  ‖(p : (PadicAlgCl p))‖ ^ (c : ℝ) < b := by
  let a' := a + (b - a) / 2
  have ha' : 0 < a' := by unfold a'; linarith
  have ha'b : a' < b := by unfold a'; linarith
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
    exact lt_trans (by simpa [a']) hc2
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

theorem QAlg_in_QpAlgCl_is_countable (p : ℕ) [hp : Fact (Nat.Prime p)] :
  {z : PadicAlgCl p | IsAlgebraic ℚ z}.Countable := by
  let S := {z : PadicAlgCl p | IsAlgebraic ℚ z}
  have : S ⊆ ⋃ (f : {g : ℚ[X] // g ≠ 0}), {z : PadicAlgCl p | aeval z f.val = 0} := by
    intro z hz
    simp
    rcases hz with ⟨f, hfne, hfz⟩
    use f
  replace := le_trans (Cardinal.mk_le_mk_of_subset this) <| Cardinal.mk_iUnion_le
    (fun (f : { g : ℚ[X] // g ≠ 0 }) ↦ {z : PadicAlgCl p | (aeval z) f.val = 0})
  suffices hfinal : Cardinal.mk S ≤ Cardinal.aleph0 by
    exact Cardinal.le_aleph0_iff_subtype_countable.mp hfinal
  refine le_trans this <| le_trans (Cardinal.mul_le_max _ _) <| max_le (max_le ?_ ?_) (le_refl _)
  · exact le_trans (Cardinal.mk_subtype_le _) <| by simp
  · refine ciSup_le' <| fun f => ?_
    simp
    refine Set.Finite.countable ?_
    have t : ((Polynomial.map (algebraMap ℚ ℚ_[p])) f.val).toAlgCl ≠ 0 := by
      simpa using f.prop
    simpa using Polynomial.finite_setOf_isRoot t

open Classical in
instance instSeparableSpacePadicAlgCl : TopologicalSpace.SeparableSpace (PadicAlgCl p) where
  exists_countable_dense := by
    use {z : PadicAlgCl p | IsAlgebraic ℚ z}
    refine ⟨QAlg_in_QpAlgCl_is_countable p, Metric.dense_iff.mpr <| fun α ε hε => ?_⟩
    rcases (PadicAlgCl.isAlgebraic p).isAlgebraic α with ⟨f', hfne', hfz'⟩
    let f := f' * C (f'.leadingCoeff)⁻¹
    have hf : Monic f := monic_mul_leadingCoeff_inv hfne'
    have hfz : aeval α f = 0 := by
      rw [aeval_mul, hfz', aeval_C]
      simp
    rcases continuity_of_roots f hf α hfz (by linarith : 0 < ε / 2) with ⟨δ, hδpos, hδ⟩
    let fun_g : Fin (f.natDegree + 1) → ℚ := fun i =>
      if hi : i = f.natDegree then 1
      else (Padic.rat_dense p (f.coeff i) hδpos).choose
    let g' := Polynomial.ofFn _ fun_g
    let g := (Polynomial.map (algebraMap ℚ ℚ_[p])) g'
    have hgg : ∀ i, (hi : i ≤ f.natDegree) →  g.coeff i = fun_g ⟨i,
      Order.lt_add_one_iff.mpr hi⟩ := by
      intro i hi
      simpa [g, g'] using ofFn_coeff_eq_val_of_lt fun_g (Order.lt_add_one_iff.mpr hi)
    have hfg : f.natDegree = g.natDegree := by
      have := Polynomial.ofFn_natDegree_lt (by simp) fun_g
      rw [Nat.lt_add_one_iff] at this
      simp [g]
      refine Eq.symm <| eq_of_le_of_not_lt this ?_
      by_contra hc
      have this' := hgg f.natDegree <| le_refl _
      simp [g, Polynomial.coeff_eq_zero_of_natDegree_lt hc, fun_g] at this'
    have hg : Monic g := by
      unfold Monic leadingCoeff
      rw [hgg g.natDegree (hfg ▸ (le_refl _))]
      simp [fun_g, hfg]
    replace hfg : f.degree = g.degree := by
      rw [Polynomial.degree_eq_natDegree hf.ne_zero, Polynomial.degree_eq_natDegree hg.ne_zero, hfg]
    have hfgδ : (f - g).stdGaussNorm ≤ δ := by
      rw [le_gaussNorm_iff_coeff_le]
      · intro i
        simp
        if hi : i > f.natDegree then
          rw [coeff_eq_zero_of_natDegree_lt hi]
          rw [coeff_eq_zero_of_natDegree_lt <| Polynomial.natDegree_eq_of_degree_eq hfg ▸ hi]
          simpa using le_of_lt hδpos
        else
        simp at hi
        rw [hgg i hi]
        unfold fun_g
        if hii : i = f.natDegree then
          simpa [hii, hf] using le_of_lt hδpos
        else
          simpa [hii] using le_of_lt (Padic.rat_dense p (f.coeff i) hδpos).choose_spec
      · exact le_of_lt hδpos
    rcases hδ g hg hfg hfgδ with ⟨β, hβg, hβα⟩
    use β
    constructor
    · simpa [dist_comm, dist_eq_norm] using lt_of_le_of_lt hβα <| by linarith
    · simp
      use g'
      constructor
      · have : g ≠ 0 := Monic.ne_zero hg
        contrapose this
        simpa [g]
      · simpa [g] using hβg
