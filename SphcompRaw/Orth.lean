import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Field.Ultra

import SphcompRaw.Basic

open Metric
open Filter


noncomputable def ndist (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x y : {z : E // z ≠ 0}) :=
(Metric.infDist x.val (𝕜 ∙ y.val)) / ‖x.val‖

def orth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x y : E) := Metric.infDist x (𝕜 ∙ y) = ‖x‖

noncomputable def orth' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x : E) (F : Subspace 𝕜 E) := Metric.infDist x F = ‖x‖

lemma orth'_iff (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] (x : E) (F : Subspace 𝕜 E) :
  orth' 𝕜 x F ↔ ∀ y ∈ F, orth 𝕜 x y := by
  unfold orth orth'
  constructor
  · intro h y hy
    refine eq_of_le_of_not_lt ?_ ?_
    · have := (@Metric.le_infDist E _
        (↑(Submodule.span 𝕜 {y}) : Set E) x (infDist x ↑(Submodule.span 𝕜 {y}))
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1 (le_refl _) (zero_mem _)
      simpa only [ge_iff_le, dist_zero_right] using this
    · by_contra hc
      rcases (@Metric.infDist_lt_iff E _
        (↑(Submodule.span 𝕜 {y}) : Set E) x ‖x‖
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1 hc with ⟨y',hy'⟩
      have := (@Metric.le_infDist E _ ↑F x ‖x‖ (Submodule.nonempty F)).1 (by simp only [h,
        le_refl]) (by aesop : y' ∈ F)
      replace hy' := hy'.2
      linarith
  · intro h
    refine eq_of_le_of_not_lt ?_ ?_
    · have := @Metric.infDist_le_dist_of_mem E _ ↑F x 0 (zero_mem _)
      simpa only [ge_iff_le, dist_zero_right] using this
    · by_contra hc
      rcases (@Metric.infDist_lt_iff E _
        ↑F x ‖x‖ (Submodule.nonempty F)).1 hc with ⟨y,hy⟩
      specialize h y hy.1
      have := h ▸ (@Metric.le_infDist E _ ↑(Submodule.span 𝕜 {y})
        x (infDist x ↑(Submodule.span 𝕜 {y}))
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1
        (le_refl _) (Submodule.mem_span_singleton_self y)
      replace hy := hy.2
      linarith

theorem orth'_scale (𝕜 : Type*) [inst : NontriviallyNormedField 𝕜] {E : Type u_2}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) (F : Subspace 𝕜 E)
  (hxF : orth' 𝕜 x F) (a : E) (ha : a ∈ Submodule.span 𝕜 {x}) : orth' 𝕜 a F := by
  unfold orth' at *
  refine eq_of_le_of_not_lt ?_ ?_
  · have := @Metric.infDist_le_dist_of_mem E _ ↑F a 0 (zero_mem _)
    simpa only [ge_iff_le, dist_zero_right] using this
  · by_contra hc
    rcases (@Metric.infDist_lt_iff E _
      ↑F a ‖a‖ (Submodule.nonempty F)).1 hc with ⟨z,hz⟩
    rcases Submodule.mem_span_singleton.1 ha with ⟨s, hs⟩
    rw [← hs] at hz
    have hnz : s ≠ 0 := by
      intro hs'
      simp only [SetLike.mem_coe, hs', zero_smul, dist_zero, norm_zero] at hz
      replace hz := hz.2
      have := norm_nonneg z
      linarith
    nth_rw 2 [((inv_smul_eq_iff₀ hnz).mp rfl : z = s • (s⁻¹ • z))] at hz
    simp only [SetLike.mem_coe, dist_eq_norm, ← smul_sub, norm_smul] at hz
    rw [mul_lt_mul_iff_right₀ (norm_pos_iff.mpr hnz), ← dist_eq_norm, ← hxF] at hz
    exact (Metric.notMem_of_dist_lt_infDist hz.2) <| Submodule.smul_mem F s⁻¹ hz.1


noncomputable def bsngsndg (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] (x : E) (F : Subspace 𝕜 E) (hxF : orth' 𝕜 x F) :
(Submodule.span 𝕜 {x}) × F≃ₛₗᵢ[RingHom.id 𝕜] (Submodule.span 𝕜 {x}) + F where
  toFun z := ⟨z.1.val + z.2.val, by
    simp only [Submodule.add_eq_sup]
    exact Submodule.add_mem_sup z.1.prop z.2.prop
    ⟩
  map_add' := by
    simp only [Submodule.add_eq_sup, Prod.fst_add, Submodule.coe_add, Prod.snd_add,
      AddMemClass.mk_add_mk, Subtype.mk.injEq, Prod.forall, Subtype.forall]
    intros
    exact add_add_add_comm _ _ _ _
  map_smul' := by
    intro m a
    simp only [Submodule.add_eq_sup, Prod.smul_fst, SetLike.val_smul, Prod.smul_snd,
      RingHom.id_apply, SetLike.mk_smul_mk, smul_add]
  norm_map' := by
    simp only [Submodule.add_eq_sup, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      AddSubgroupClass.coe_norm, Prod.forall, Prod.norm_mk, Subtype.forall]
    intro a ha b hab
    if hh : a = 0 ∨ b = 0 then
      cases hh with
      |inl hh => simp only [hh, zero_add, norm_zero, norm_nonneg, sup_of_le_right]
      |inr hh => simp only [hh, add_zero, norm_zero, norm_nonneg, sup_of_le_left]
    else
      refine eq_of_le_of_not_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      by_contra hc
      if h : ‖b‖ ≤ ‖a‖ then
        simp only [h, sup_of_le_left] at hc
        have : dist a (-b) = ‖a + b‖ := by simp only [dist_eq_norm, sub_neg_eq_add]
        rw [← this, ← orth'_scale 𝕜 x F hxF a ha] at hc
        exact (notMem_of_dist_lt_infDist hc) <| neg_mem hab
      else
        simp only [not_le] at h
        simp only [sup_of_le_right <| le_of_lt h] at hc
        have := IsUltrametricDist.norm_add_le_max (a + b) (-a)
        simp only [add_neg_cancel_comm, norm_neg, le_sup_iff] at this
        replace this := this.resolve_right <| not_le_of_gt h
        linarith
  invFun := by
    rw [Submodule.add_eq_sup]
    intro z
    exact (⟨(Submodule.mem_sup.mp z.prop).choose,
            (Submodule.mem_sup.mp z.prop).choose_spec.1⟩,
           ⟨(Submodule.mem_sup.mp z.prop).choose_spec.2.choose,
            (Submodule.mem_sup.mp z.prop).choose_spec.2.choose_spec.1⟩)
  left_inv := by
    intro t
    simp only [Submodule.add_eq_sup, eq_mpr_eq_cast, cast_eq]
    have := (Submodule.mem_sup.mp (Subtype.prop ⟨↑t.1 + (↑t.2 : E),
      id (Submodule.add_mem_sup (Subtype.prop t.1) (Subtype.prop t.2))⟩))
    have this' := this.choose_spec.2.choose_spec.2
    simp only at this'
    refine Prod.ext_iff.mpr ?_
    have h1 : this.choose - t.1 ∈ Submodule.span 𝕜 {x} :=
      (Submodule.sub_mem_iff_left (Submodule.span 𝕜 {x}) t.1.prop).mpr this.choose_spec.1
    have h2 : this.choose_spec.2.choose - t.2 ∈ F :=
      (Submodule.sub_mem_iff_left F t.2.prop).mpr this.choose_spec.2.choose_spec.1
    have h3 : this.choose - t.1 = - (this.choose_spec.2.choose - t.2) := by
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this', add_comm]
    have h1' : this.choose - t.1 ∈ (↑(Submodule.span 𝕜 {x}) : Set E) ∩ ↑F := by
      simp only [Set.mem_inter_iff, SetLike.mem_coe, h1, true_and]
      simp only [h3, neg_sub]
      exact sub_mem_comm_iff.mp h2
    have h2' : this.choose_spec.2.choose - t.2 ∈ (↑(Submodule.span 𝕜 {x}) : Set E) ∩ ↑F := by
      simp only [Set.mem_inter_iff, SetLike.mem_coe, h2, and_true]
      rw [← neg_eq_iff_eq_neg] at h3
      rw [← h3]
      exact Submodule.neg_mem (Submodule.span 𝕜 {x}) h1
    have hh : (↑(Submodule.span 𝕜 {x}) : Set E) ∩ ↑F = {0} := by
      ext w
      simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hw1, hw2⟩
        replace hxF : orth' 𝕜 w F := orth'_scale 𝕜 x F hxF w hw1
        unfold orth' at hxF
        simpa only [hxF, dist_self, norm_le_zero_iff] using
          @Metric.infDist_le_dist_of_mem E _ F w w hw2
      · intro h
        simp only [h, zero_mem, and_self]
    simp only [hh, Set.mem_singleton_iff, sub_eq_zero] at h1' h2'
    simp only [h2', and_true]
    exact SetLike.coe_eq_coe.mp h1'
  right_inv := by
    intro t
    simp only [Submodule.add_eq_sup, eq_mpr_eq_cast, cast_eq,
      (Submodule.mem_sup.mp t.prop).choose_spec.2.choose_spec.2, Subtype.coe_eta]

theorem exists_orth_vec (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(F : Subspace 𝕜 E) [SphericallyCompleteSpace F]
[FiniteDimensional 𝕜 E]
(hF : Module.finrank 𝕜 F < Module.finrank 𝕜 E) :
∃ x : E, orth' 𝕜 x F := by
  replace hF : (↑(Module.finrank 𝕜 ↥F) : Cardinal.{u_2}) < ↑(Module.finrank 𝕜 E) :=
    Nat.cast_lt.mpr hF
  repeat rw [Module.finrank_eq_rank'] at hF
  rcases Submodule.exists_smul_notMem_of_rank_lt hF with ⟨a, ha⟩
  specialize ha 1 one_ne_zero
  simp only [one_smul] at ha
  suffices h : ∃ z : E, z ∈ F ∧ ‖a - z‖ = infDist a F by
    rcases h with ⟨z, hz⟩
    use a - z
    unfold orth'
    rw [hz.2]
    refine eq_of_le_of_ge ?_ ?_
    · rw [Metric.le_infDist <| Submodule.nonempty F]
      intro w hw
      rw [dist_eq_norm, (by simp only [sub_sub_sub_cancel_right] : a - w = (a - z) - (w - z)),
        ← dist_eq_norm]
      exact infDist_le_dist_of_mem <| sub_mem hw hz.1
    · rw [Metric.le_infDist <| Submodule.nonempty F]
      intro w hw
      rw [dist_eq_norm, (sub_sub a z w : a - z - w = a - (z + w)),
        ← dist_eq_norm]
      exact infDist_le_dist_of_mem <| add_mem hz.1 hw

  sorry
