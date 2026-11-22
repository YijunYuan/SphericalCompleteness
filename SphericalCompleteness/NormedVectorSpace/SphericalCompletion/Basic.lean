/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Metric.Seminormed.SphericalCompletion
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Defs
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.LpQuotient

/-!
# Spherical completion: basic results

This file records the fundamental properties of the *spherical completion* of an ultrametric
normed `𝕜`-vector space `E`, organised around the class
`SphericallyCompleteSpace.IsSphericalCompletion ι`, indexed by a linear isometry
`ι : E →ₗᵢ[𝕜] F`, which asserts that `ι` realises the spherically complete space `F` as a *minimal*
spherically complete extension of `E` (no proper spherically complete submodule of `F` contains the
image of `E`).

The bundled-distance construction supplies spherically complete immediate linear extensions
of seminormed spaces. Immediacy gives minimality: every ambient point has a nearest point in
a spherically complete intermediate submodule. The completion of a separated source is again
separated.

## Main statements

* `SphericallyCompleteSpace.IsSphericalCompletion.exists_isSphericalCompletion`: every ultrametric
  normed `𝕜`-vector space admits a spherical completion, i.e. an embedding `ι : E →ₗᵢ[𝕜] E₀` with
  `IsSphericalCompletion ι`.
* `SphericallyCompleteSpace.IsSphericalCompletion.embedding_isImmediate`: any embedding realising a
  spherical completion of `E` is an immediate extension.
* `SphericallyCompleteSpace.IsSphericalCompletion.unique`: any two spherical completions of `E` have
  linearly isometric codomains, via an equivalence compatible with the two embeddings.
* `SphericallyCompleteSpace.IsSphericalCompletion.weak_universal_property`: linear isometries out
  of `E` into a spherically complete space factor through any spherical-completion embedding of `E`.
* `SphericallyCompleteSpace.iff_maximallyComplete`: `E` is spherically complete if and only if it
  is maximally complete.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

open IsImmediate

namespace IsSphericalCompletion

/-- Any spherically complete immediate linear extension is minimal among spherically
complete intermediate submodules. This criterion also applies to seminormed spaces. -/
theorem of_isImmediate_nnMetric {𝕜 : Type*} [NormedField 𝕜]
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [IsUltrametricDist E] [IsUltrametricDist F]
    [SphericallyCompleteSpace F] (f : E →ₗᵢ[𝕜] F) (hi : (nnMetric F).IsImmediate f) :
    IsSphericalCompletion f where
  minimal_of_sphericallyComplete D hD hle := by
    have : ((nnMetric F).comap ((↑) : D → F)).IsSphericallyComplete :=
      (sphericallyCompleteSpace_iff D).mp hD
    exact PseudoMetric.IsImmediate.eq_top_of_isSphericallyComplete (nnMetric F)
      (i := f.toLinearMap) hi D hle

/-- The bundled-distance definition is equivalent to the normed-space minimality class
together with injectivity of the embedding. The latter is automatic for a separated source. -/
theorem isLinearSphericalCompletion_iff {𝕜 : Type*} [NormedField 𝕜]
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [IsUltrametricDist E] [IsUltrametricDist F]
    (f : E →ₗᵢ[𝕜] F) : (nnMetric E).IsLinearSphericalCompletion (nnMetric F) f.toLinearMap ↔
      Function.Injective f ∧ IsSphericalCompletion f := by
  constructor
  · intro h
    have : SphericallyCompleteSpace F := (sphericallyCompleteSpace_iff F).mpr h.complete
    exact ⟨h.injective, of_isImmediate_nnMetric f h.immediate⟩
  · rintro ⟨hinj, hf⟩
    apply (PseudoMetric.isLinearSphericalCompletion_iff_minimal (nnMetric F) (nnMetric E)
      f.toLinearMap hinj f.isometry.nndist_eq).mpr
    intro D hD hc
    exact hf.minimal_of_sphericallyComplete D ((sphericallyCompleteSpace_iff D).mpr hc) hD

/--
The maximal immediate-extension submodule of `E` chosen inside a spherically complete ambient
space `E₀` (via `exists_maximal_immediateExtensionSubmodule`) is a spherical completion of `E`,
with canonical embedding `maximalImmediateExtensionEmbedding f`.

The maximal submodule is spherically complete and immediate over the original image.
Minimality follows from the nearest-point criterion for spherically complete intermediate
submodules.
-/
instance instIsSphericalCompletionOfMaximalImmediateExtensionSubmodule
    {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    IsSphericalCompletion (maximalImmediateExtensionEmbedding f) := by
  let M := (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose
  have hm : (nnMetric E₀).IsImmediateSubmodule f.range M := by
    have hm : M ∈ immediateExtensionSubmodules E E₀ f :=
      (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose_spec.1
    rwa [immediateExtensionSubmodules_eq_nnMetric] at hm
  obtain ⟨hM, hi⟩ := (nnMetric E₀).isImmediateSubmodule_iff.mp hm
  apply of_isImmediate_nnMetric
  exact hi.comp (f := f.toLinearMap.rangeRestrict)
    (fun y hy ↦ (hy (f.toLinearMap.surjective_rangeRestrict y)).elim)

/-- Every ultrametric seminormed space over a normed field has a spherical completion.
The embedding is injective, including on vectors with seminorm zero. -/
theorem exists_isSphericalCompletion_seminormed (𝕜 : Type*) [NormedField 𝕜]
    (E : Type u) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    ∃ (F : Type u) (_ : SeminormedAddCommGroup F) (_ : NormedSpace 𝕜 F) (_ : IsUltrametricDist F)
      (ι : E →ₗᵢ[𝕜] F), Function.Injective ι ∧ IsSphericalCompletion ι := by
  obtain ⟨F, _, _, _, i, _, hinj, hi⟩ := Metric.exists_seminormed_linearSphericalCompletion 𝕜 E
  exact ⟨F, inferInstance, inferInstance, inferInstance, i, hinj, of_isImmediate_nnMetric i hi⟩

/--
Every ultrametric normed `𝕜`-vector space `E` admits a spherical completion: there is a type `E₀`
carrying an ultrametric normed `𝕜`-vector-space structure together with a linear isometry
`ι : E →ₗᵢ[𝕜] E₀` for which `IsSphericalCompletion ι` holds. Since that class `extends
SphericallyCompleteSpace`, `E₀` is in particular spherically complete.

The arbitrary-value linear extension is spherically complete and immediate for the
nonnegative-real distance. This distance defines a genuine norm because the source is separated.
-/
theorem exists_isSphericalCompletion (𝕜 : Type*) [NormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    ∃ E₀ : Type u,
      ∃ _ : NormedAddCommGroup E₀,
      ∃ _ : NormedSpace 𝕜 E₀,
      ∃ _ : IsUltrametricDist E₀,
      ∃ ι : E →ₗᵢ[𝕜] E₀,
        IsSphericalCompletion ι := by
  obtain ⟨F, _, _, _, i, _, hi⟩ := Metric.exists_normed_linearSphericalCompletion 𝕜 E
  exact ⟨F, inferInstance, inferInstance, inferInstance, i, of_isImmediate_nnMetric i hi⟩

/--
Any embedding `ι : E →ₗᵢ[𝕜] F` realising `F` as a spherical completion of `E` (i.e. carrying an
`IsSphericalCompletion ι` instance) is an *immediate* extension.

Minimality identifies an injective norm-preserving map with a bundled-distance linear
spherical completion, hence its image is immediate.
-/
theorem embedding_isImmediate {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {ι : E →ₗᵢ[𝕜] F} (hF : IsSphericalCompletion ι) :
    IsImmediate ι := by
  exact (isImmediate_iff_nnMetric ι).mpr
    (((isLinearSphericalCompletion_iff ι).mpr ⟨ι.injective, hF⟩).immediate)

/--
Uniqueness of the spherical completion (immediate-extension form).

If `ι₁ : E →ₗᵢ[𝕜] F₁` realises `F₁` as a spherical completion of `E` and `f : E →ₗᵢ[𝕜] F₂` is an
immediate extension into a spherically complete space `F₂`, then there is a linear isometric
equivalence `T : F₂ ≃ₗᵢ[𝕜] F₁` intertwining the two embeddings, i.e. `T.comp f = ι₁`.

Extend `f` along its own immediacy to a linear isometry `T : F₂ →ₗᵢ[𝕜] F₁` with `T.comp f = ι₁`.
The range of `T` is spherically complete and contains the range of `ι₁`, so minimality of the
spherical completion `F₁` forces `T` to be surjective, hence a linear isometric equivalence; the
intertwining identity survives the upgrade since the underlying map is unchanged.
-/
theorem exists_linearIsometryEquiv_of_isImmediate
    {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    {ι₁ : E →ₗᵢ[𝕜] F₁} (hF₁ : IsSphericalCompletion ι₁)
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [IsUltrametricDist F₂]
    [SphericallyCompleteSpace F₂]
    {f : E →ₗᵢ[𝕜] F₂} (hf : IsImmediate f) :
    ∃ T : F₂ ≃ₗᵢ[𝕜] F₁, T.toLinearIsometry.comp f = ι₁ := by
  rcases IsImmediate.exists_linearIsometry_comp_eq f hf ι₁ with ⟨T, hT⟩
  have hmin := hF₁.minimal_of_sphericallyComplete (LinearMap.range T.toLinearMap)
    (of_isometryEquiv (Isometry.isometryEquivOnRange T.isometry))
  rw [← hT] at hmin
  let e : F₂ ≃ₗᵢ[𝕜] F₁ := LinearIsometryEquiv.ofSurjective T (LinearMap.range_eq_top.mp
    (hmin (by apply LinearMap.range_comp_le_range)))
  have he : e.toLinearIsometry = T := LinearIsometry.ext fun x ↦ Eq.refl (e.toLinearIsometry x)
  exact ⟨e, by simpa [he] using hT⟩

/-- Two injective spherical completions of a seminormed space are linearly isometrically
equivalent over their common source. -/
theorem unique_of_injective {𝕜 : Type*} [NormedField 𝕜]
    {E F₁ F₂ : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F₁]
    [SeminormedAddCommGroup F₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂]
    [IsUltrametricDist E] [IsUltrametricDist F₁] [IsUltrametricDist F₂]
    {ι₁ : E →ₗᵢ[𝕜] F₁} {ι₂ : E →ₗᵢ[𝕜] F₂}
    (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂)
    (hF₁ : IsSphericalCompletion ι₁) (hF₂ : IsSphericalCompletion ι₂) :
    ∃ g : F₁ ≃ₗᵢ[𝕜] F₂, g.toLinearIsometry.comp ι₁ = ι₂ := by
  have hi := (isLinearSphericalCompletion_iff ι₁).mpr ⟨h₁, hF₁⟩
  have hj := (isLinearSphericalCompletion_iff ι₂).mpr ⟨h₂, hF₂⟩
  obtain ⟨g, hcomp, hd⟩ := hi.unique (nnMetric F₁) (nnMetric F₂) hj
  let T : F₁ ≃ₗᵢ[𝕜] F₂ := ⟨g, fun x ↦ by
    simpa only [nnMetric_apply, map_zero, nndist_zero_right, coe_nnNorm] using
      congrArg NNReal.toReal (hd x 0)⟩
  exact ⟨T, LinearIsometry.ext fun x ↦ LinearMap.congr_fun hcomp x⟩

/--
Uniqueness of the spherical completion.

Any two spherical completions of the same space `E`, given by embeddings `ι₁ : E →ₗᵢ[𝕜] F₁` and
`ι₂ : E →ₗᵢ[𝕜] F₂`, have linearly isometric codomains: there is a linear isometric equivalence
`f : F₁ ≃ₗᵢ[𝕜] F₂` compatible with the embeddings, i.e. `f.comp ι₁ = ι₂`. The embedding `ι₂` is an
immediate extension (`embedding_isImmediate`), so `exists_linearIsometryEquiv_of_isImmediate`
applied to `ι₁` yields an equivalence `T : F₂ ≃ₗᵢ[𝕜] F₁` with `T.comp ι₂ = ι₁`; its inverse `T.symm`
is the required intertwining equivalence.
-/
theorem unique {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [IsUltrametricDist F₂]
    {ι₁ : E →ₗᵢ[𝕜] F₁} {ι₂ : E →ₗᵢ[𝕜] F₂} :
    IsSphericalCompletion ι₁ → IsSphericalCompletion ι₂ →
    ∃ f : F₁ ≃ₗᵢ[𝕜] F₂, f.toLinearIsometry.comp ι₁ = ι₂ :=
  unique_of_injective ι₁.injective ι₂.injective

section
variable {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {ι : E →ₗᵢ[𝕜] F}

/-- Weak universal property for an injective completion of a seminormed space. -/
theorem weak_universal_property_of_injective {H : Type*} [SeminormedAddCommGroup H]
    [NormedSpace 𝕜 H] [IsUltrametricDist H] [SphericallyCompleteSpace H]
    (f : E →ₗᵢ[𝕜] H) (hinj : Function.Injective ι) (hF : IsSphericalCompletion ι) :
    ∃ T : F →ₗᵢ[𝕜] H, T.comp ι = f :=
  IsImmediate.exists_linearIsometry_comp_eq_of_nnMetric ι hinj
    (((isLinearSphericalCompletion_iff ι).mpr ⟨hinj, hF⟩).immediate) f

end

section
variable {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {ι : E →ₗᵢ[𝕜] F}

/--
**Weak universal property of the spherical completion.**

Every linear isometry `f : E →ₗᵢ[𝕜] F'` into a spherically complete ultrametric space `F'` factors
through any spherical-completion embedding `ι : E →ₗᵢ[𝕜] F` of `E`: there is a linear isometry
`T : F →ₗᵢ[𝕜] F'` with `T.comp ι = f`. This is the extension property of the immediate embedding
`ι` (`embedding_isImmediate`) into the spherically complete target `F'`.
-/
theorem weak_universal_property
    {F' : Type*} [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F'] [IsUltrametricDist F']
    [SphericallyCompleteSpace F']
    (f : E →ₗᵢ[𝕜] F') (hF : IsSphericalCompletion ι) :
    ∃ T : F →ₗᵢ[𝕜] F', T.comp ι = f :=
  weak_universal_property_of_injective f ι.injective hF

end

section
variable {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {ι : E →ₗᵢ[𝕜] F}

/--
`E` is spherically complete if and only if a spherical-completion embedding `ι : E →ₗᵢ[𝕜] F` of `E`
is surjective.

If `E` is spherically complete then the range of `ι` is a spherically complete submodule
containing itself, so minimality forces it to be everything, i.e. `ι` is surjective. Conversely, a
surjective linear isometry makes `F` (which is spherically complete) linearly isometric to `E`,
transporting spherical completeness back to `E`.
-/
theorem iff_embedding_to_sphericalCompletion_surjective
    (hF : IsSphericalCompletion ι) :
    SphericallyCompleteSpace E ↔ Function.Surjective ι := by
  rw [sphericallyCompleteSpace_iff]
  constructor
  · intro h
    have hR := ((nnMetric E).isSphericallyComplete_iff_of_surjective (nnMetric ι.range)
      ι.toLinearMap.surjective_rangeRestrict ι.isometry.nndist_eq).mp h
    exact LinearMap.range_eq_top.mp (hF.minimal_of_sphericallyComplete ι.range
      ((sphericallyCompleteSpace_iff _).mpr hR) le_rfl)
  · exact fun h ↦ ((nnMetric E).isSphericallyComplete_iff_of_surjective (nnMetric F) h
      ι.isometry.nndist_eq).mpr inferInstance

end

end IsSphericalCompletion

/--
An ultrametric normed `𝕜`-vector space `E` is spherically complete if and only if it is *maximally
complete* (`MaximallyComplete 𝕜 E`), i.e. it admits no proper immediate extension.

For the forward direction, every point has a best approximation in a spherically complete image,
whereas immediacy would strictly improve that approximation at any point outside the image.
Conversely, if `E` is maximally complete, the canonical embedding
of `E` into its spherical completion is immediate (`IsSphericalCompletion.embedding_isImmediate`),
hence surjective by maximal completeness; so `E` is linearly isometric to the spherically complete
completion and is therefore itself spherically complete.
-/
theorem iff_maximallyComplete (𝕜 : Type*) [NormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    SphericallyCompleteSpace E ↔ MaximallyComplete 𝕜 E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro F _ _ _ f hf
    exact ((isImmediate_iff_nnMetric f).mp hf).surjective (Metric.nnMetric E) (Metric.nnMetric F)
      f.isometry.nndist_eq
  · obtain ⟨F, _, _, _, i, hsc, hi⟩ := Metric.exists_normed_linearSphericalCompletion 𝕜 E
    have hs := h i ((isImmediate_iff_nnMetric i).mpr hi)
    exact of_isometryEquiv (LinearIsometryEquiv.ofSurjective i hs).symm.toIsometryEquiv


end SphericallyCompleteSpace
