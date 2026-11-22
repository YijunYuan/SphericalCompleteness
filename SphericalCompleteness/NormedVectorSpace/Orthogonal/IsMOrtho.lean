/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import SphericalCompleteness.Metric.Basic
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
  obtain ⟨z, hz⟩ := Metric.exists_dist_le_of_sphericallyComplete (F : Set E) F.nonempty a
  refine ⟨a - z, fun h ↦ ha ((sub_eq_zero.mp h) ▸ z.prop), ?_⟩
  by_contra h
  obtain ⟨w, hw, hlt⟩ := IsMOrtho.not_iff_exists_dist_lt_norm.mp h
  have hle := hz ⟨z + w, F.add_mem z.prop hw⟩
  simp only [dist_eq_norm, sub_sub] at hle hlt
  exact (not_lt_of_ge hle) hlt

end

end SphericallyCompleteSpace
