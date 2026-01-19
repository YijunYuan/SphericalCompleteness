import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Algebra.Polynomial.Splits

open Polynomial

noncomputable abbrev Polynomial.toAlgCl {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :=
  (Polynomial.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) f

lemma toAlgCl_natdeg_eq {𝕜 : Type u_1} [Field 𝕜] (f : Polynomial 𝕜) :
  (f.toAlgCl).natDegree = f.natDegree := by
  unfold toAlgCl
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap 𝕜 (AlgebraicClosure 𝕜)).injective]

abbrev Polynomial.stdGaussNorm {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] (f : Polynomial 𝕜) :=
(@gaussNorm _ _ _ {coe := fun f => f, coe_injective' := fun _ _ stupid => stupid} hn.norm 1) f

lemma stdGaussNorm_nonneg {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) : 0 ≤ f.stdGaussNorm := by
  unfold stdGaussNorm gaussNorm
  by_cases hp : f.support.Nonempty <;>
  simp only [hp, ↓reduceDIte, le_refl, one_pow, mul_one]
  rw [Finset.le_sup'_iff]
  exact ⟨hp.choose, ⟨hp.choose_spec, norm_nonneg _⟩⟩

lemma stdGaussNorm_eq_zero_iff {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) :
  f.stdGaussNorm = 0 ↔ f = 0 := by
  constructor
  · intro h
    unfold stdGaussNorm gaussNorm at h
    if hh : f.support.Nonempty then
      simp [hh] at h
      have := (Finset.sup'_le_iff hh _).1 <| le_of_eq h
      replace : ∀ b ∈ f.support, f.coeff b = 0 :=
        fun b hb => norm_eq_zero.mp <| eq_of_le_of_ge (this b hb) (norm_nonneg _)
      refine support_eq_empty.mp ?_
      by_contra hc
      have t := Finset.nonempty_iff_ne_empty.2 hc
      exact Polynomial.mem_support_iff.1 t.choose_spec <| this t.choose t.choose_spec
    else
    have := Polynomial.nonempty_support_iff.not.1 hh
    contrapose this; exact this
  · intro h
    simp [h]

lemma le_gaussNorm_iff_coeff_le {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) {r : ℝ} (hr : 0 ≤ r) :
  f.stdGaussNorm ≤ r ↔ ∀ i : ℕ, ‖f.coeff i‖ ≤ r := by
  unfold stdGaussNorm gaussNorm
  if h : f.support.Nonempty then
    simp [h]
    refine ⟨fun hh i => ?_, fun hh i hi ↦ hh i⟩
    if ht : f.coeff i = 0 then simpa [ht]
    else exact hh i ht
  else
  simp [h, hr]
  intro i
  suffices tt : f.coeff i = 0 by simpa [tt]
  exact notMem_support_iff.mp <| forall_not_of_not_exists h i

lemma gaussNorm_pos_iff {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) :
  0 < f.stdGaussNorm ↔ f ≠ 0 := by
  refine iff_not_comm.mp ?_
  simpa [← stdGaussNorm_eq_zero_iff] using
    ⟨fun h => ge_of_eq (id (Eq.symm h)), fun h => eq_of_le_of_ge h (stdGaussNorm_nonneg f)⟩

lemma one_le_stdGaussNorm_of_monic {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜]
(f : Polynomial 𝕜) (hf : Monic f) :
  1 ≤ f.stdGaussNorm := by
  unfold stdGaussNorm gaussNorm
  have : f.support.Nonempty := by
    refine support_nonempty.mpr ?_
    exact Monic.ne_zero hf
  simp [this]
  use f.natDegree
  simp [hf]

lemma pos_deg_of_monic_of_root {𝕜 : Type u_1} [Field 𝕜]
(f : 𝕜[X]) (hf : Monic f) (α : AlgebraicClosure 𝕜) (hfz : eval α f.toAlgCl = 0) :
  0 < f.natDegree := by
  refine (Monic.natDegree_pos hf).mpr ?_
  by_contra hc
  simp [hc] at hfz

lemma natDegree_sub_monic_le_natDegree_sub_one {𝕜 : Type*} [hn : NontriviallyNormedField 𝕜]
  (f g : 𝕜[X]) (hf : f.Monic) (hg : g.Monic) (hfg : f.degree = g.degree) (α : AlgebraicClosure 𝕜)
  (hfz : eval α f.toAlgCl = 0) :
  (g - f).natDegree ≤ f.natDegree - 1 := by
  rw [Nat.le_sub_one_iff_lt <| pos_deg_of_monic_of_root f hf α hfz]
  refine lt_of_le_of_ne ?_ ?_
  · rw [sub_eq_add_neg]
    refine le_trans (natDegree_add_le _ _) ?_
    simp [natDegree_le_iff_degree_le, ← hfg]
  · by_contra hc
    have hc' := hc
    apply_fun (g - f).coeff at hc
    rw [Polynomial.coeff_sub, hc'] at hc
    nth_rw 1 [natDegree_eq_of_degree_eq hfg] at hc
    nth_rw 2 [← hc'] at hc
    simp [hf, hg] at hc
    simp [leadingCoeff_eq_zero.1 hc.symm] at hc'
    simp [eq_one_of_monic_natDegree_zero hf (id (Eq.symm hc'))] at hfz

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
    have : f.natDegree = f.natDegree - 1 + 1 :=
      (Nat.sub_eq_iff_eq_add <| pos_deg_of_monic_of_root f hf α hfz).mp rfl
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
  apply mul_le_mul ?_ ?_ (spectralNorm_nonneg (α ^ i)) <| stdGaussNorm_nonneg f
  · rw [spectralNorm_extends]
    if hff : f.coeff i = 0 then
      simpa [hff] using stdGaussNorm_nonneg f
    else
    unfold Polynomial.stdGaussNorm Polynomial.gaussNorm
    simp [support_nonempty.mpr <| Monic.ne_zero hf]
    use i
  · have : IsPowMul (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) := isPowMul_spectralNorm
    if hi' : i = 0 then
      simpa [hi', spectralNorm_one] using one_le_pow₀ hx
    else
    rw [this α (Nat.one_le_iff_ne_zero.2 hi')]
    exact pow_le_pow_right₀ hx <| (Nat.le_sub_one_iff_lt t).mpr hi

open Classical in
lemma Finset.prod.multiplicative_mor {ι : Type*}
{M : Type*} [CommMonoid M] (s : Finset ι) (f : ι → M)
{β : Type*} [CommMonoid β] (g : M → β)
(hg1 : g 1 = 1) (hgmul : ∀ x y : M, g (x * y) = g x * g y) :
  g (∏ i ∈ s, f i) = ∏ i ∈ s, g (f i) := by
  induction' s using Finset.induction_on with a s ha ih
  · simpa
  · nth_rw 2 [Finset.prod_insert ha]
    rw [← ih, ← hgmul, ← Finset.prod_insert ha]

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
        simp
      rw [this, spectralNorm_extends]
      unfold Polynomial.stdGaussNorm Polynomial.gaussNorm
      if hp : (f - g).support.Nonempty then
        simp only [hp, ↓reduceDIte, one_pow, mul_one]
        rw [Finset.le_sup'_iff]
        if hi : i ∈ (f - g).support then
          use i
          simp [hi, norm_sub_rev]
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
          exact natDegree_sub_monic_le_natDegree_sub_one f g hf hg hfg α hfz
    · exact stdGaussNorm_nonneg (f - g)

open Classical in
theorem continuity_of_roots₀ {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [IsUltrametricDist 𝕜]
(f g : Polynomial 𝕜) (hf : Monic f) (hg : Monic g) (hfg : f.degree = g.degree)
(α : AlgebraicClosure 𝕜) (hα : f.toAlgCl.IsRoot α) :
∃ β : AlgebraicClosure 𝕜,
  g.toAlgCl.IsRoot β ∧
  spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (α - β)
    ≤ (f - g).stdGaussNorm ^ (1 / (f.natDegree : ℝ)) * f.stdGaussNorm := by
  if hfg' : f = g then
    use α
    simp [← hfg']
    constructor
    · simpa using hα
    · apply mul_nonneg
      · exact Real.zero_rpow_nonneg (↑f.natDegree)⁻¹
      · exact stdGaussNorm_nonneg f
  else
  by_contra hc
  push_neg at hc
  have : IsAlgClosed (AlgebraicClosure 𝕜) := IsAlgClosure.isAlgClosed 𝕜
  have := Polynomial.aeval_eq_prod_aroots_sub_of_monic_of_splits hg (this.factors g.toAlgCl) α
  have t : (aeval α) g = g.toAlgCl.eval α := by
    simp [aeval, toAlgCl]
  rw [t, Multiset.prod_eq_prod_toEnumFinset] at this
  apply_fun (spectralNorm 𝕜 (AlgebraicClosure 𝕜)) at this
  rw [Finset.prod.multiplicative_mor _ _ (spectralNorm 𝕜 (AlgebraicClosure 𝕜))] at this
  · have this' : ∀ s ∈ (Multiset.map (fun a ↦ α - a) (g.aroots (AlgebraicClosure 𝕜))).toEnumFinset,
      (f - g).stdGaussNorm ^ (1 / (↑f.natDegree : ℝ)) * f.stdGaussNorm <
      spectralNorm 𝕜 (AlgebraicClosure 𝕜) s.1 := by
      intro s hs
      replace hs := Multiset.mem_of_mem_toEnumFinset hs
      rcases Multiset.mem_map.1 hs with ⟨z, hz⟩
      rw [← hz.2]
      exact hc z (isRoot_of_mem_roots hz.1)
    replace this' := Finset.prod_lt_prod_of_nonempty ?_ this' ?_
    · rw [← this] at this'
      simp at this'
      rw [IsAlgClosed.card_aroots_eq_natDegree, mul_pow] at this'
      rw [← natDegree_eq_of_degree_eq hfg, ← Real.rpow_natCast, Real.rpow_inv_rpow] at this'
      · have := spectralNorm_eval_le_gaussNorm_sub f g hf hg hfg α hα
        simp at this
        replace := lt_of_lt_of_le this' this
        have t := (gaussNorm_pos_iff (f - g)).2 <| sub_ne_zero_of_ne hfg'
        replace := (mul_lt_mul_iff_right₀ t).1 this
        rw [pow_lt_pow_iff_right₀] at this
        · omega
        · have t := one_le_stdGaussNorm_of_monic f hf
          refine lt_of_le_of_ne t ?_
          by_contra hc
          rw [← hc] at this
          simp only [one_pow, lt_self_iff_false] at this
      · exact stdGaussNorm_nonneg (f - g)
      · simp at hα
        simpa using Nat.ne_zero_of_lt <| Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hf hα
    · intro _ _
      apply mul_pos
      · apply Real.rpow_pos_of_pos
        replace hfg' : f - g ≠ 0 := sub_ne_zero_of_ne hfg'
        exact (gaussNorm_pos_iff (f - g)).mpr hfg'
      · have := one_le_stdGaussNorm_of_monic f hf; linarith
    · suffices hw : (g.aroots (AlgebraicClosure 𝕜)).toFinset.Nonempty by
        rcases hw with ⟨a, ha⟩
        use (α - a,0)
        simp
        refine Multiset.count_pos.mpr <| Multiset.mem_map.mpr ?_
        use a
        simp at ha
        simp [ha]
      simp at hα
      have := Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hf hα
      rw [natDegree_eq_of_degree_eq hfg] at this
      replace : g.toAlgCl.degree ≠ 0 := by
        simpa using ne_of_gt <| natDegree_pos_iff_degree_pos.1 this
      rcases IsAlgClosed.exists_root _ this with ⟨a, ha⟩
      use a
      simp at ha
      simpa [ha] using Polynomial.Monic.ne_zero_of_ne (zero_ne_one' 𝕜) hg
  · exact spectralNorm_one
  · exact fun x y => spectralAlgNorm_mul x y

theorem continuity_of_roots {𝕜 : Type u_1} [hn : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [IsUltrametricDist 𝕜]
  (f : Polynomial 𝕜) (hf : Monic f) (α : AlgebraicClosure 𝕜) (hα : aeval α f = 0)
  {ε : ℝ} (hε : 0 < ε) :
∃ δ : ℝ, 0 < δ ∧
  ∀ g : Polynomial 𝕜, Monic g →
  f.degree = g.degree →
  (f - g).stdGaussNorm ≤ δ →
  ∃ β : AlgebraicClosure 𝕜,
    aeval β g = 0 ∧
    spectralAlgNorm 𝕜 (AlgebraicClosure 𝕜) (α - β) ≤ ε := by
  use (ε / f.stdGaussNorm) ^ (f.natDegree : ℝ)
  constructor
  · refine Real.rpow_pos_of_pos (div_pos hε ?_) ↑f.natDegree
    have := one_le_stdGaussNorm_of_monic f hf
    linarith
  · intro g hg hfg hfgs
    rcases continuity_of_roots₀ f g hf hg hfg α (by simpa using hα) with ⟨β, hβroot, hβnorm⟩
    use β
    constructor
    · simpa using hβroot
    · refine le_trans hβnorm ?_
      suffices hh : (f - g).stdGaussNorm ^ (1 / (↑f.natDegree : ℝ)) ≤ ε / f.stdGaussNorm by
        refine (le_div_iff₀ ?_).mp hh
        have t := one_le_stdGaussNorm_of_monic f hf
        linarith
      simp
      rw [Real.rpow_inv_le_iff_of_pos]
      · exact hfgs
      · exact stdGaussNorm_nonneg (f - g)
      · exact div_nonneg (le_of_lt hε) (stdGaussNorm_nonneg f)
      · simpa using pos_deg_of_monic_of_root f hf α (by simpa using hα)
