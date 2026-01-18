import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.GaussNorm

open Polynomial

instance {𝕜 : Type u_1} : FunLike (𝕜 → ℝ) 𝕜 ℝ where
  coe := fun f => f
  coe_injective' := fun _ _ stupid => stupid

noncomputable abbrev Polynomial.toAlgCl {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :=
  (Polynomial.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) f

lemma toAlgCl_natdeg_eq {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :
  (f.toAlgCl).natDegree = f.natDegree := by
  unfold toAlgCl
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap 𝕜 (AlgebraicClosure 𝕜)).injective]

abbrev Polynomial.stdGaussNorm {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] (f : Polynomial 𝕜) :=
(Polynomial.gaussNorm hn.norm 1) f

lemma one_le_stdGaussNorm_of_monic {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) (hf : Monic f) :
  1 ≤ f.stdGaussNorm := by
  unfold stdGaussNorm gaussNorm
  have : f.support.Nonempty := by
    refine support_nonempty.mpr ?_
    exact Monic.ne_zero hf
  simp [this]
  use f.natDegree
  simpa [hf] using le_of_eq norm_one.symm

lemma pos_deg_of_monic_of_root {𝕜 : Type u_1} [Field 𝕜]
(f : 𝕜[X]) (hf : Monic f) (α : AlgebraicClosure 𝕜) (hfz : eval α f.toAlgCl = 0) :
  0 < f.natDegree := by
  refine (Monic.natDegree_pos hf).mpr ?_
  by_contra hc
  simp [hc] at hfz

theorem ttt.extracted_1_4 {𝕜 : Type*} [hn : NontriviallyNormedField 𝕜]
  (f g : 𝕜[X]) (hf : f.Monic) (hg : g.Monic) (hfg : f.degree = g.degree) (α : AlgebraicClosure 𝕜)
  (hfz : eval α f.toAlgCl = 0) :
  (g - f).natDegree ≤ f.natDegree - 1 := by
  rw [Nat.le_sub_one_iff_lt]
  · refine lt_of_le_of_ne ?_ ?_
    · rw [sub_eq_add_neg]
      refine le_trans (natDegree_add_le _ _) ?_
      simp
      apply natDegree_le_iff_degree_le.2
      simp [← hfg]
    · by_contra hc
      have hc' := hc
      apply_fun (g - f).coeff at hc
      rw [Polynomial.coeff_sub] at hc
      nth_rw 1 [hc'] at hc
      rw [hc'] at hc
      replace hfg := natDegree_eq_of_degree_eq hfg
      nth_rw 1 [hfg] at hc
      nth_rw 2 [← hc'] at hc
      simp [hf, hg] at hc
      replace hc := leadingCoeff_eq_zero.1 hc.symm
      simp [hc] at hc'
      simp [eq_one_of_monic_natDegree_zero hf (id (Eq.symm hc'))] at hfz
  · exact pos_deg_of_monic_of_root f hf α hfz

theorem spectralNorm_le_gaussNorm {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
[IsUltrametricDist 𝕜]
  (f : 𝕜[X]) (hf : f.Monic) (α : AlgebraicClosure 𝕜)
  (hfz : eval α f.toAlgCl = 0) :
  spectralNorm 𝕜 (AlgebraicClosure 𝕜) α ≤ f.stdGaussNorm := by
  if hx : ¬ 1 ≤ spectralNorm 𝕜 (AlgebraicClosure 𝕜) α then
    simp at hx
    exact le_of_lt <| lt_of_lt_of_le hx (one_le_stdGaussNorm_of_monic f hf)
  else
  simp at hx
  suffices hh : (spectralNorm 𝕜 (AlgebraicClosure 𝕜) α) ^ f.natDegree ≤
    f.stdGaussNorm * (spectralNorm 𝕜 (AlgebraicClosure 𝕜) α) ^ (f.natDegree - 1) by
    have := one_le_stdGaussNorm_of_monic f hf
    if hα : spectralNorm 𝕜 (AlgebraicClosure 𝕜) α = 0 then
      simp [hα]; linarith
    else
    have : f.natDegree = f.natDegree -1 + 1 := by
      refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
      exact pos_deg_of_monic_of_root f hf α hfz
    nth_rw 1 [this, pow_succ'] at hh
    rwa [mul_le_mul_iff_of_pos_right] at hh
    exact pow_pos (lt_of_le_of_ne (spectralNorm_nonneg α)
      (fun a ↦ hα (id (Eq.symm a)))) (f.natDegree - 1)
  have t := pos_deg_of_monic_of_root f hf α hfz
  rw [eval_eq_sum_range, Finset.sum_range_succ_comm] at hfz
  simp [hf] at hfz
  rw [add_eq_zero_iff_eq_neg, ← Finset.sum_neg_distrib] at hfz
  apply_fun spectralNorm 𝕜 (AlgebraicClosure 𝕜) at hfz
  have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
  rw [this α t] at hfz
  rw [hfz]
  refine le_trans (IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean
    isNonarchimedean_spectralNorm <| Finset.Aesop.range_nonempty <| Nat.ne_zero_of_lt t) ?_
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro i hi
  rw [spectralNorm_neg <| Algebra.IsAlgebraic.isAlgebraic _]
  refine le_trans (spectralNorm_mul
    (Algebra.IsAlgebraic.isAlgebraic _) (Algebra.IsAlgebraic.isAlgebraic _)) ?_
  apply mul_le_mul ?_ ?_ (spectralNorm_nonneg (α ^ i)) ?_
  · rw [spectralNorm_extends]
    if hff : f.coeff i = 0 then
      simp [hff]
      have := one_le_stdGaussNorm_of_monic f hf; linarith
    else
    unfold Polynomial.stdGaussNorm Polynomial.gaussNorm
    simp [support_nonempty.mpr <| Monic.ne_zero hf]
    use i
    simp [hff]
    exact le_refl _
  · have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
    if hi' : i = 0 then
      simpa [hi', spectralNorm_one] using one_le_pow₀ hx
    else
    rw [this α (Nat.one_le_iff_ne_zero.2 hi')]
    exact pow_le_pow_right₀ hx <| (Nat.le_sub_one_iff_lt t).mpr hi
  · have := one_le_stdGaussNorm_of_monic f hf; linarith

theorem spectralNorm_eval_le_gaussNorm_sub {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
[IsUltrametricDist 𝕜]
(f g : Polynomial 𝕜) (hf : Monic f) (hg : Monic g) (hfg : f.degree = g.degree)
(α : AlgebraicClosure 𝕜)
(hfz : f.toAlgCl.IsRoot α)
: spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (g.toAlgCl.eval α)
  ≤ (f - g).stdGaussNorm * f.stdGaussNorm ^ (f.natDegree - 1)
:= by
  have : g.toAlgCl.eval α = (g - f).toAlgCl.eval α + f.toAlgCl.eval α := by simp
  unfold Polynomial.IsRoot at hfz
  rw [hfz, add_zero] at this
  nth_rw 2 [Polynomial.eval_eq_sum_range] at this
  rw [this]
  refine le_trans
    (IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean isNonarchimedean_spectralNorm
    (by simp : (Finset.range ((g - f).toAlgCl.natDegree + 1)).Nonempty)) ?_
  simp only [Finset.sup'_le_iff, Finset.mem_range]
  intro i hi
  refine le_trans (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _) ?_) ?_
  · exact IsAlgebraic.pow (Algebra.IsAlgebraic.isAlgebraic α) i
  · apply mul_le_mul ?_ ?_ (spectralNorm_nonneg _) ?_
    · have : (g - f).toAlgCl.coeff i = algebraMap 𝕜 (AlgebraicClosure 𝕜) ((g - f).coeff i) := by
        unfold toAlgCl
        simp
      rw [this, spectralNorm_extends]
      unfold Polynomial.stdGaussNorm Polynomial.gaussNorm
      if hp : (f - g).support.Nonempty then
        simp only [hp, ↓reduceDIte, one_pow, mul_one]
        rw [Finset.le_sup'_iff]
        if hi : i ∈ (f - g).support then
          use i
          simp [hi, norm_sub_rev]
          exact le_refl _
        else
          have : (g - f).coeff i = 0 := by
            refine notMem_support_iff.mp ?_
            contrapose hi
            rw [mem_support_iff] at *
            simp only [coeff_sub, ne_eq] at *
            grind only
          simp only [mem_support_iff, ne_eq, this, norm_zero]
          exact ⟨hp.choose, ⟨mem_support_iff.mp hp.choose_spec, norm_nonneg _⟩⟩
      else
        simp at hp
        simp [sub_eq_zero.1 hp] at *
    · if hi' : i = 0 then
        simpa [hi', spectralNorm_one] using one_le_pow₀ <| one_le_stdGaussNorm_of_monic f hf
      else
      have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
      rw [this α (Nat.one_le_iff_ne_zero.2 hi')]
      refine le_trans (?_ : spectralNorm 𝕜 (AlgebraicClosure 𝕜) α ^ i ≤ f.stdGaussNorm ^ i) ?_
      · apply pow_le_pow_left₀ (spectralNorm_nonneg α)
        exact spectralNorm_le_gaussNorm f hf α hfz
      · refine pow_le_pow_right₀ ?_ ?_
        · exact one_le_stdGaussNorm_of_monic _ hf
        · rw [Nat.lt_add_one_iff] at hi
          refine le_trans hi ?_
          rw [toAlgCl_natdeg_eq]
          exact ttt.extracted_1_4 f g hf hg hfg α hfz
    · unfold stdGaussNorm gaussNorm
      by_cases hp : (f - g).support.Nonempty <;>
      simp only [hp, ↓reduceDIte, le_refl, one_pow, mul_one]
      rw [Finset.le_sup'_iff]
      exact ⟨hp.choose, ⟨hp.choose_spec, norm_nonneg _⟩⟩
