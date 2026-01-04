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

import SphericalCompleteness.Basic

open Metric
open Filter

namespace SphericallyCompleteSpace

abbrev Orthogonal (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x y : E) := Metric.infDist x (𝕜 ∙ y) = ‖x‖

abbrev 𝒪rthogonal (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x : E) (F : Subspace 𝕜 E) := Metric.infDist x F = ‖x‖

abbrev 𝕆rthogonal (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(F1 : Subspace 𝕜 E) (F2 : Subspace 𝕜 E) := ∀ x ∈ F1, 𝒪rthogonal 𝕜 x F2

lemma 𝒪rthogonal_iff (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x : E) (F : Subspace 𝕜 E) :
  𝒪rthogonal 𝕜 x F ↔ ∀ y ∈ F, Orthogonal 𝕜 x y := by
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
      refine lt_iff_not_ge.1 hy'.2 <| (@Metric.le_infDist E _ ↑F x ‖x‖ (Submodule.nonempty F)).1
        (by simp only [h, le_refl]) (by aesop : y' ∈ F)
  · intro h
    refine eq_of_le_of_not_lt ?_ ?_
    · have := @Metric.infDist_le_dist_of_mem E _ ↑F x 0 (zero_mem _)
      simpa only [ge_iff_le, dist_zero_right] using this
    · by_contra hc
      rcases (@Metric.infDist_lt_iff E _
        ↑F x ‖x‖ (Submodule.nonempty F)).1 hc with ⟨y,hy⟩
      refine lt_iff_not_ge.1 hy.2 ?_
      exact (h y hy.1) ▸ (@Metric.le_infDist E _ ↑(Submodule.span 𝕜 {y})
        x (infDist x ↑(Submodule.span 𝕜 {y}))
        (Submodule.nonempty (Submodule.span 𝕜 {y}))).1
        (le_refl _) (Submodule.mem_span_singleton_self y)

theorem 𝒪rthogonal_scale (𝕜 : Type*) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(x : E) (F : Subspace 𝕜 E)
  (hxF : 𝒪rthogonal 𝕜 x F) (a : E) (ha : a ∈ Submodule.span 𝕜 {x}) : 𝒪rthogonal 𝕜 a F := by
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
      exact lt_iff_not_ge.1 hz.2 <| norm_nonneg z
    nth_rw 2 [((inv_smul_eq_iff₀ hnz).mp rfl : z = s • (s⁻¹ • z))] at hz
    simp only [SetLike.mem_coe, dist_eq_norm, ← smul_sub, norm_smul] at hz
    rw [mul_lt_mul_iff_right₀ (norm_pos_iff.mpr hnz), ← dist_eq_norm, ← hxF] at hz
    exact (Metric.notMem_of_dist_lt_infDist hz.2) <| Submodule.smul_mem F s⁻¹ hz.1


noncomputable def direct_prod_iso_sum_of_orth (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] (x : E) (F : Subspace 𝕜 E) (hxF : 𝒪rthogonal 𝕜 x F) :
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
        rw [← this, ← 𝒪rthogonal_scale 𝕜 x F hxF a ha] at hc
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
    have h1 := (Submodule.sub_mem_iff_left (Submodule.span 𝕜 {x}) t.1.prop).mpr this.choose_spec.1
    have h2 := (Submodule.sub_mem_iff_left F t.2.prop).mpr this.choose_spec.2.choose_spec.1
    have h3 : this.choose - t.1 = - (this.choose_spec.2.choose - t.2) := by
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this', add_comm]
    have h1' : this.choose - t.1 ∈ (↑(Submodule.span 𝕜 {x}) : Set E) ∩ ↑F := by
      simp only [Set.mem_inter_iff, SetLike.mem_coe, h1, true_and]
      simpa only [h3, neg_sub] using sub_mem_comm_iff.mp h2
    have h2' : this.choose_spec.2.choose - t.2 ∈ (↑(Submodule.span 𝕜 {x}) : Set E) ∩ ↑F := by
      simp only [Set.mem_inter_iff, SetLike.mem_coe, h2, and_true]
      rw [← neg_eq_iff_eq_neg.2 h3]
      exact Submodule.neg_mem (Submodule.span 𝕜 {x}) h1
    have hh : (↑(Submodule.span 𝕜 {x}) : Set E) ∩ ↑F = {0} := by
      ext w
      simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hw1, hw2⟩
        replace hxF : 𝒪rthogonal 𝕜 w F := 𝒪rthogonal_scale 𝕜 x F hxF w hw1
        simpa only [hxF, dist_self, norm_le_zero_iff] using
          @Metric.infDist_le_dist_of_mem E _ F w w hw2
      · intro h
        simp only [h, zero_mem, and_self]
    simp only [hh, Set.mem_singleton_iff, sub_eq_zero] at h1' h2'
    simpa only [h2', and_true] using SetLike.coe_eq_coe.mp h1'
  right_inv := by
    intro t
    simp only [Submodule.add_eq_sup, eq_mpr_eq_cast, cast_eq,
      (Submodule.mem_sup.mp t.prop).choose_spec.2.choose_spec.2, Subtype.coe_eta]

private lemma res_ball (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E]
(F : Subspace 𝕜 E) [SphericallyCompleteSpace F]
[FiniteDimensional 𝕜 E] (a : E) :
∀ s > infDist a F, ∃ z : F, (closedBall a s) ∩ ↑F = ((fun x : F => (x : E)) '' closedBall z s) := by
  intro s hs
  rcases (Metric.infDist_lt_iff (Submodule.nonempty F)).1 hs with ⟨y, hy⟩
  use ⟨y, hy.1⟩
  ext x
  simp only [Set.mem_inter_iff, mem_closedBall, SetLike.mem_coe, Set.mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · refine fun h => ⟨h.2, ?_⟩
    rcases (le_sup_iff.1 <| iud.dist_triangle_max x a y) with hxy | hay
    · exact le_trans hxy h.1
    · exact le_of_lt <| lt_of_le_of_lt hay hy.2
  · rintro ⟨w, hw⟩
    simp only [w, and_true]
    rw [dist_comm] at hy
    rcases (le_sup_iff.1 <| iud.dist_triangle_max x y a) with hxy | hay
    · exact le_trans hxy hw
    · exact le_of_lt <| lt_of_le_of_lt hay hy.2

theorem exists_orth_vec (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E]
(F : Subspace 𝕜 E) [sF : SphericallyCompleteSpace F]
[FiniteDimensional 𝕜 E]
(hF : Module.finrank 𝕜 F < Module.finrank 𝕜 E) :
∃ (x : E), x ≠ 0 ∧ 𝒪rthogonal 𝕜 x F := by
  replace hF : (↑(Module.finrank 𝕜 ↥F) : Cardinal.{u_2}) < ↑(Module.finrank 𝕜 E) :=
    Nat.cast_lt.mpr hF
  repeat rw [Module.finrank_eq_rank'] at hF
  rcases Submodule.exists_smul_notMem_of_rank_lt hF with ⟨a, ha⟩
  specialize ha 1 one_ne_zero
  simp only [one_smul] at ha
  suffices h : ∃ z : E, z ∈ F ∧ ‖a - z‖ = infDist a F ∧ (a - z) ≠ 0 by
    rcases h with ⟨z, hz⟩
    use a - z
    simp only [𝒪rthogonal, hz.2.1]
    refine ⟨fun hc => ((sub_eq_zero.1 hc) ▸ ha) hz.1, eq_of_le_of_ge ?_ ?_⟩
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
  have := @sF.isSphericallyComplete (fun i => (res_ball 𝕜 F a (infDist a F + 1 / (i + 1))
    (by simp only [one_div, gt_iff_lt, lt_add_iff_pos_right, inv_pos, Nat.cast_add_one_pos]
      )).choose) (fun i => ⟨infDist a F + 1 / (i + 1), by
    refine add_nonneg infDist_nonneg ?_
    simp only [one_div, inv_nonneg]
    linarith
    ⟩) (by
    refine antitone_nat_of_succ_le <| fun n => ?_
    simp only [Nat.cast_add, Nat.cast_one, one_div, NNReal.coe_mk, Set.le_eq_subset]
    intro x hx
    have := (res_ball 𝕜 F a (infDist a F + 1 / (n + 1 + 1)) (by simp; linarith)).choose_spec
    simp only [one_div] at this
    have h1 : ↑x ∈ closedBall a (infDist a ↑F + (↑n + 1 + 1 : ℝ)⁻¹) ∩ ↑F := by
      rw [this, Set.mem_image]
      use x
    replace h1 : ↑x ∈ closedBall a (infDist a ↑F + (↑n + 1 : ℝ)⁻¹) ∩ ↑F := by
      refine ⟨?_ , x.prop⟩
      simp only [Set.mem_inter_iff, mem_closedBall, Subtype.coe_prop, and_true] at h1
      simp only [mem_closedBall] at *
      refine le_trans h1 ?_
      simp only [add_le_add_iff_left]; field_simp; linarith
    replace := (res_ball 𝕜 F a (infDist a F + 1 / (n + 1)) (by simp; linarith)).choose_spec
    simp only [one_div] at this
    rw [this] at h1
    simpa only [mem_closedBall, ge_iff_le, Set.mem_image, SetLike.coe_eq_coe, exists_eq_right] using
      h1
    )
  simp only [one_div, NNReal.coe_mk, Set.nonempty_iInter, Subtype.exists] at this
  rcases this with ⟨z, hz, hfin⟩
  use z
  simp only [hz, true_and]
  replace hfin : ∀ i : ℕ, z ∈ closedBall a (infDist a ↑F + 1 / (↑i + 1)) := by
    intro i
    specialize hfin i
    have : z ∈ ((fun x : F => (x : E)) '' closedBall ((res_ball 𝕜 F a (infDist a F + 1 / (i + 1))
    (by simp only [one_div, gt_iff_lt, lt_add_iff_pos_right, inv_pos,
      Nat.cast_add_one_pos])).choose) (infDist a ↑F + 1 / (i + 1))) := by
      simp only [mem_closedBall, one_div, Set.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right] at *
      use hz
    rw [← (res_ball 𝕜 F a (infDist a F + 1 / (i + 1))
      (by simp only [one_div, gt_iff_lt, lt_add_iff_pos_right,
        inv_pos, Nat.cast_add_one_pos])).choose_spec] at this
    exact Set.mem_of_mem_inter_left this
  refine ⟨eq_of_le_of_ge ?_ ?_ , fun hc => ha <| (sub_eq_zero.1 hc) ▸ hz⟩
  · simp only [one_div, mem_closedBall, dist_comm, dist_eq_norm] at hfin
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    specialize hfin (⌈1 / ε⌉₊ + 1)
    refine le_trans hfin ?_
    simp only [one_div, Nat.cast_add, Nat.cast_one, add_le_add_iff_left]
    field_simp
    rw [mul_add,mul_add, add_assoc]
    have : ε * ↑⌈1 / ε⌉₊ ≥ 1 := by
      simpa only [one_div, ge_iff_le] using (inv_le_iff_one_le_mul₀' hε).mp <| Nat.le_ceil (ε⁻¹)
    linarith
  · rw [← dist_eq_norm]
    exact infDist_le_dist_of_mem hz

end SphericallyCompleteSpace
