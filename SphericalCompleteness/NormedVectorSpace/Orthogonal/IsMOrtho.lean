/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.Basic

/-!
# Orthogonality: orthogonal decomposition and existence of orthogonal vectors

Building on the definition of metric orthogonality `x ⟂ₘ F`, this file constructs the isometric
direct-sum decomposition `(𝕜 ∙ x) × F ≃ₛₗᵢ (𝕜 ∙ x) + F` attached to a vector orthogonal to a
subspace, and proves that in a finite-dimensional ultrametric normed space a spherically complete
subspace of strictly smaller dimension always admits a nonzero vector orthogonal to it.
-/

@[expose] public section

open Metric
open Filter

namespace SphericallyCompleteSpace

namespace IsMOrtho

/-- Metric orthogonality to `F` passes from `x` to every scalar multiple of `x`: any element of
the line `𝕜 ∙ x` is again metrically orthogonal to `F`. -/
private lemma of_mem_span_singleton (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (x : E) (F : Subspace 𝕜 E)
    (hxF : x ⟂ₘ F) (a : E) (ha : a ∈ Submodule.span 𝕜 {x}) : a ⟂ₘ F := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
  exact smul r hxF

/--
Constructs a `𝕜`-linear isometric equivalence between the direct product
`(Submodule.span 𝕜 {x}) × F` and the (internal) sum `(Submodule.span 𝕜 {x}) + F`,
under the hypothesis that `x` is `M`-orthogonal to the subspace `F` (`hxF : x ⟂ₘ F`).

Intuitively, when `x` is orthogonal to `F` in the ultrametric sense, every element of the sum
admits a decomposition into a component in the span of `x` and a component in `F` that is
compatible with the norm, yielding an isometry.

This is stated as an isometric linear equivalence (`≃ₛₗᵢ[RingHom.id 𝕜]`), i.e. a linear
equivalence that preserves norms.
-/
noncomputable def directProdIsoSum (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (x : E) (F : Subspace 𝕜 E) (hxF : x ⟂ₘ F) :
    (Submodule.span 𝕜 {x}) × F ≃ₛₗᵢ[RingHom.id 𝕜] (Submodule.span 𝕜 {x}) + F := by
  let f : (Submodule.span 𝕜 {x}) × F →ₗᵢ[𝕜] (Submodule.span 𝕜 {x}) + F :=
    { toLinearMap := ((Submodule.span 𝕜 {x}).subtype.coprod F.subtype).codRestrict _
        (fun z ↦ Submodule.add_mem_sup z.1.property z.2.property)
      norm_map' := by
        intro z
        change ‖(z.1 : E) + (z.2 : E)‖ = max ‖(z.1 : E)‖ ‖(z.2 : E)‖
        have h := (iff_forall_isVOrtho (z.1 : E) F).mp
          (of_mem_span_singleton 𝕜 x F hxF z.1 z.1.property) z.2 z.2.property
        simpa only [one_smul] using IsVOrtho.iff_norm_add_eq_max.mp h 1 1 }
  exact LinearIsometryEquiv.ofSurjective f (by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩)

end IsMOrtho

universe u

section
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E]
  (F : Subspace 𝕜 E) [sF : SphericallyCompleteSpace F] [FiniteDimensional 𝕜 E]

omit sF [FiniteDimensional 𝕜 E] in
/-- For any radius `s` strictly above the distance from `a` to `F`, the slice of the closed ball
`closedBall a s` lying in `F` is itself a closed ball of `F`: it equals the image of
`closedBall z s` for a suitable center `z ∈ F`. This lets a nested family of balls around `a` be
transported into `F`, where spherical completeness of `F` can be applied. -/
private lemma exists_image_closedBall_eq_closedBall_inter (a : E) :
    ∀ s > infDist a F, ∃ z : F,
      (closedBall a s) ∩ ↑F = ((fun x : F ↦ (x : E)) '' closedBall z s) := by
  intro s hs
  rcases (Metric.infDist_lt_iff (Submodule.nonempty F)).1 hs with ⟨y, hy⟩
  use ⟨y, hy.1⟩
  ext x
  simp only [Set.mem_inter_iff, mem_closedBall, SetLike.mem_coe, Set.mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · refine fun h ↦ ⟨h.2, ?_⟩
    rcases (le_sup_iff.1 <| iud.dist_triangle_max x a y) with hxy | hay
    · exact le_trans hxy h.1
    · exact le_of_lt <| lt_of_le_of_lt hay hy.2
  · rintro ⟨w, hw⟩
    simp only [w, and_true]
    rw [dist_comm] at hy
    rcases (le_sup_iff.1 <| iud.dist_triangle_max x y a) with hxy | hay
    · exact le_trans hxy hw
    · exact le_of_lt <| lt_of_le_of_lt hay hy.2

/--
Given a finite-dimensional ultrametric normed space `E` over a nontrivially normed field `𝕜`,
and a subspace `F` which is spherically complete, if `F` has strictly smaller `finrank` than `E`,
then there exists a nonzero vector `x : E` that is `M`-orthogonal to `F` (notation `x ⟂ₘ F`).

This is the inductive step that lets one build an orthogonal complement one dimension at a time:
as long as `F` does not exhaust `E`, spherical completeness of `F` guarantees a best approximation
of any vector outside `F`, and the corresponding residual is a nonzero vector realizing its full
norm as its distance to `F`.
-/
theorem exists_isMOrtho_vec_of_finrank_lt
    (hF : Module.finrank 𝕜 F < Module.finrank 𝕜 E) :
    ∃ (x : E), x ≠ 0 ∧ (x ⟂ₘ F) := by
  replace hF : (↑(Module.finrank 𝕜 ↥F) : Cardinal.{u}) < ↑(Module.finrank 𝕜 E) :=
    Nat.cast_lt.mpr hF
  repeat rw [Module.finrank_eq_rank'] at hF
  rcases Submodule.exists_smul_notMem_of_rank_lt hF with ⟨a, ha⟩
  specialize ha 1 one_ne_zero
  simp only [one_smul] at ha
  suffices h : ∃ z : E, z ∈ F ∧ ‖a - z‖ = infDist a F ∧ (a - z) ≠ 0 by
    rcases h with ⟨z, hz⟩
    use a - z
    simp only [IsMOrtho, hz.2.1]
    refine ⟨fun hc ↦ ((sub_eq_zero.1 hc) ▸ ha) hz.1, eq_of_le_of_ge ?_ ?_⟩
    · rw [Metric.le_infDist <| Submodule.nonempty F]
      intro w hw
      rw [dist_eq_norm, (by simp only [sub_sub_sub_cancel_right] : a - w = (a - z) - (w - z)),
        ← dist_eq_norm]
      exact infDist_le_dist_of_mem <| sub_mem hw hz.1
    · rw [Metric.le_infDist <| Submodule.nonempty F]
      intro w hw
      rw [dist_eq_norm, (sub_sub a z w : a - z - w = a - (z + w)), ← dist_eq_norm]
      exact infDist_le_dist_of_mem <| add_mem hz.1 hw
  have := @sF.nonempty_iInter_of_antitone
    (fun i ↦ (exists_image_closedBall_eq_closedBall_inter 𝕜 F a (infDist a F + 1 / (i + 1))
    (by simp only [one_div, gt_iff_lt, lt_add_iff_pos_right, inv_pos, Nat.cast_add_one_pos]
      )).choose) (fun i ↦ ⟨infDist a F + 1 / (i + 1), by
    refine add_nonneg infDist_nonneg ?_
    simp only [one_div, inv_nonneg]
    linarith
    ⟩) (by
    refine antitone_nat_of_succ_le <| fun n ↦ ?_
    simp only [Nat.cast_add, Nat.cast_one, one_div]
    intro x hx
    have := (exists_image_closedBall_eq_closedBall_inter 𝕜 F a (infDist a F + 1 / (n + 1 + 1))
      (by simp; linarith)).choose_spec
    simp only [one_div] at this
    have h1 : ↑x ∈ closedBall a (infDist a ↑F + (↑n + 1 + 1 : ℝ)⁻¹) ∩ ↑F := by
      rw [this, Set.mem_image]
      exact ⟨x, hx, rfl⟩
    replace h1 : ↑x ∈ closedBall a (infDist a ↑F + (↑n + 1 : ℝ)⁻¹) ∩ ↑F := by
      refine ⟨?_, x.prop⟩
      simp only [Set.mem_inter_iff, mem_closedBall, Subtype.coe_prop, and_true] at h1
      simp only [mem_closedBall] at *
      refine le_trans h1 ?_
      simp only [add_le_add_iff_left]; field_simp; linarith
    replace := (exists_image_closedBall_eq_closedBall_inter 𝕜 F a (infDist a F + 1 / (n + 1))
      (by simp; linarith)).choose_spec
    simp only [one_div] at this
    rw [this] at h1
    obtain ⟨y, hyball, hyx⟩ := h1
    have hyeqx : y = x := SetLike.coe_eq_coe.mp hyx
    rw [mem_closedBall] at hyball
    subst hyeqx
    rwa [mem_closedBall]
    )
  simp only [one_div, Set.nonempty_iInter, Subtype.exists] at this
  rcases this with ⟨z, hz, hfin⟩
  use z
  simp only [hz, true_and]
  replace hfin : ∀ i : ℕ, z ∈ closedBall a (infDist a ↑F + 1 / (↑i + 1)) := by
    intro i
    have : z ∈ ((fun x : F ↦ (x : E)) '' closedBall
    ((exists_image_closedBall_eq_closedBall_inter 𝕜 F a (infDist a F + 1 / (i + 1))
    (by simp only [one_div, gt_iff_lt, lt_add_iff_pos_right, inv_pos,
      Nat.cast_add_one_pos])).choose) (infDist a ↑F + 1 / (i + 1))) := by
      simp only [mem_closedBall, one_div, Set.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right] at *
      exact ⟨hz, hfin i⟩
    rw [← (exists_image_closedBall_eq_closedBall_inter 𝕜 F a (infDist a F + 1 / (i + 1))
      (by simp only [one_div, gt_iff_lt, lt_add_iff_pos_right,
        inv_pos, Nat.cast_add_one_pos])).choose_spec] at this
    exact Set.mem_of_mem_inter_left this
  refine ⟨eq_of_le_of_ge ?_ ?_, fun hc ↦ ha <| (sub_eq_zero.1 hc) ▸ hz⟩
  · simp only [one_div, mem_closedBall, dist_comm, dist_eq_norm] at hfin
    refine le_of_forall_pos_le_add (fun ε hε ↦ le_trans (hfin (⌈1 / ε⌉₊ + 1)) ?_)
    simp only [one_div, Nat.cast_add, Nat.cast_one, add_le_add_iff_left]
    field_simp
    rw [mul_add, mul_add, add_assoc]
    have : ε * ↑⌈1 / ε⌉₊ ≥ 1 := by
      simpa only [one_div, ge_iff_le] using (inv_le_iff_one_le_mul₀' hε).mp <| Nat.le_ceil (ε⁻¹)
    linarith
  · simpa [← dist_eq_norm] using infDist_le_dist_of_mem hz

end

end SphericallyCompleteSpace
