/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Defs

/-!
# Spherical completion: basic results

This file records the fundamental properties of the *spherical completion* of an ultrametric
normed `𝕜`-vector space `E`, organised around the class
`SphericallyCompleteSpace.IsSphericalCompletion 𝕜 E F`, which asserts that the spherically complete
space `F` is a *minimal* spherically complete extension of `E` (no proper spherically complete
submodule of `F` contains the image of `E`).

Building on the Zorn construction of a maximal immediate extension
(`exists_maximal_immediateExtensionSubmodule`) inside the canonical spherically complete extension,
we show:

* every `E` admits a spherical completion;
* the canonical embedding into any spherical completion is an *immediate* extension;
* the spherical completion is unique up to linear isometry and satisfies a universal property;
* `E` is spherically complete if and only if it is *maximally complete* — equivalently, iff the
  embedding of `E` into its spherical completion is surjective.

The key geometric input is the orthogonal-complement decomposition of a spherically complete
subspace (`isCompl_orthComp`): a proper spherically complete subspace has a nonzero orthogonal
complement, which supplies a vector metrically orthogonal to the range of the embedding and hence
contradicts immediacy.

## Main statements

* `SphericallyCompleteSpace.IsSphericalCompletion.exists_isSphericalCompletion`: every ultrametric
  normed `𝕜`-vector space admits a spherical completion.
* `SphericallyCompleteSpace.IsSphericalCompletion.embedding_isImmediate`: the canonical embedding
  of `E` into a spherical completion is an immediate extension.
* `SphericallyCompleteSpace.IsSphericalCompletion.unique`: any two spherical completions of `E`
  are linearly isometric.
* `SphericallyCompleteSpace.IsSphericalCompletion.universal_property`: linear isometries out of `E`
  into a spherically complete space factor through any spherical completion of `E`.
* `SphericallyCompleteSpace.iff_maximallyComplete`: `E` is spherically complete if and only if it
  is maximally complete.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

open IsImmediate

namespace IsSphericalCompletion

/--
The maximal immediate-extension submodule of `E` chosen inside a spherically complete ambient
space `E₀` (via `exists_maximal_immediateExtensionSubmodule`) is a spherical completion of `E`,
with canonical embedding `maximalImmediateExtensionEmbedding f`.

Minimality is forced by maximality of the submodule. Suppose some spherically complete intermediate
submodule `M`, containing the range of the embedding, were proper. Since `M` is spherically
complete it is complemented by its orthogonal complement (`isCompl_orthComp`), which is therefore
nonzero; a nonzero vector `b` of `orthComp 𝕜 M` is metrically orthogonal to `M`, hence to the range
of the embedding. But immediacy of the maximal extension forbids a nonzero vector orthogonal to
that range — a contradiction. Therefore every such `M` equals `⊤`.
-/
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    IsSphericalCompletion 𝕜 E (↥(exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose) where
  is_sph_comp := by
    use maximalImmediateExtensionEmbedding f
    intro M hsc hM
    by_contra hc
    have hMo : orthComp 𝕜 M ≠ ⊥ := by
      by_contra hc'
      have := (isCompl_orthComp 𝕜 M).sup_eq_top
      simp only [hc', bot_le, sup_of_le_left] at this
      exact hc this
    rcases (Submodule.ne_bot_iff _).1 hMo with ⟨b, hb1, hb2⟩
    apply IsMOrtho.of_mem_orthComp at hb1
    contrapose hb2
    apply (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f
      ).choose_spec.1.out.choose_spec
    rw [IsMOrtho.iff_forall_isVOrtho] at *
    intro y hy
    suffices hy' : y ∈ (maximalImmediateExtensionEmbedding f).range by
      exact hb1 _ <| hM hy'
    convert hy
    apply Submodule.ext_iff.mpr
    intro z
    rw [Submodule.range_inclusion, Submodule.mem_comap, Submodule.coe_subtype]
    simp only [LinearMap.mem_range, maximalImmediateExtensionEmbedding, LinearMap.coe_mk,
      AddHom.coe_mk]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e, rfl⟩
    · rintro ⟨e, he⟩
      exact ⟨e, Subtype.ext he⟩

/--
Every ultrametric normed `𝕜`-vector space `E` admits a spherical completion: there is a type `E₀`
carrying an ultrametric normed `𝕜`-vector-space structure for which `IsSphericalCompletion 𝕜 E E₀`
holds. Since that class `extends SphericallyCompleteSpace`, `E₀` is in particular spherically
complete.

The witness is the maximal immediate extension carved out of the canonical spherically complete
extension `canonicalSphericallyCompleteExtension 𝕜 E` (a quotient of an `ℓ∞`-type space): the
maximal immediate submodule selected by `exists_maximal_immediateExtensionSubmodule` is itself
spherically complete and, by maximality, a minimal spherically complete extension of `E`. All of
the required structure and the completion property are supplied by the surrounding instances.
-/
theorem exists_isSphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    ∃ E₀ : Type u,
      ∃ _ : NormedAddCommGroup E₀,
      ∃ _ : NormedSpace 𝕜 E₀,
      ∃ _ : IsUltrametricDist E₀,
        IsSphericalCompletion 𝕜 E E₀ := by
  let E₀ := ↥(exists_maximal_immediateExtensionSubmodule 𝕜 E _
    (canonicalSphericallyCompleteExtension 𝕜 E)).choose
  exact ⟨E₀, inferInstance, inferInstance, inferInstance, inferInstance⟩

/--
The canonical embedding of `E` into any spherical completion `F` (i.e. any `F` carrying an
`IsSphericalCompletion 𝕜 E F` instance) is an *immediate* extension.

Apply the Zorn construction `exists_maximal_immediateExtensionSubmodule` inside the spherically
complete ambient space `F` to the embedding `ι := hF.is_sph_comp.choose`: it selects a maximal
submodule `S ⊇ range ι` for which the inclusion `range ι →ₗᵢ S` is immediate. This `S` is itself
spherically complete, so minimality of the spherical completion forces `S = ⊤`. Immediacy of that
inclusion, read off in the ambient space via `mem_immediateExtensionSubmodules_iff`, is exactly
immediacy of `ι`.
-/
theorem embedding_isImmediate {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (hF : IsSphericalCompletion 𝕜 E F) :
    IsImmediate hF.is_sph_comp.choose := by
  obtain ⟨hSle, hSimm⟩ := mem_immediateExtensionSubmodules_iff.1
    (exists_maximal_immediateExtensionSubmodule 𝕜 E F hF.is_sph_comp.choose).choose_spec.1
  have hStop : (exists_maximal_immediateExtensionSubmodule 𝕜 E F
      hF.is_sph_comp.choose).choose = ⊤ :=
    hF.is_sph_comp.choose_spec _ inferInstance hSle
  intro v hv
  have hvS : v ∈ (exists_maximal_immediateExtensionSubmodule 𝕜 E F
      hF.is_sph_comp.choose).choose := by rw [hStop]; exact Submodule.mem_top
  simpa using congrArg Subtype.val (hSimm ⟨v, hvS⟩ hv)

/--
Uniqueness of the spherical completion (immediate-extension form).

If `F₁` is a spherical completion of `E` and `f : E →ₗᵢ[𝕜] F₂` is an immediate extension into a
spherically complete space `F₂`, then `F₁` and `F₂` are linearly isometric.

Extend `f` along its own immediacy to a linear isometry `T : F₂ →ₗᵢ[𝕜] F₁` with
`T.comp f = hF₁.is_sph_comp.choose`. The range of `T` is spherically complete and contains the
range of the embedding, so minimality of the spherical completion `F₁` forces `T` to be surjective,
hence a linear isometric equivalence.
-/
theorem nonempty_linearIsometryEquiv_of_isImmediate
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    (hF₁ : IsSphericalCompletion 𝕜 E F₁)
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [IsUltrametricDist F₂]
    [SphericallyCompleteSpace F₂]
    {f : E →ₗᵢ[𝕜] F₂} (hf : IsImmediate f) : Nonempty (F₁ ≃ₗᵢ[𝕜] F₂) := by
  rcases IsImmediate.exists_linearIsometry_comp_eq f hf hF₁.is_sph_comp.choose with ⟨T, hT⟩
  have hmin := hF₁.is_sph_comp.choose_spec (LinearMap.range T.toLinearMap)
    (of_isometryEquiv (Isometry.isometryEquivOnRange T.isometry))
  rw [← hT] at hmin
  exact ⟨(LinearIsometryEquiv.ofSurjective T (LinearMap.range_eq_top.mp
    (hmin (by apply LinearMap.range_comp_le_range)))).symm⟩

/--
Uniqueness of the spherical completion.

Any two spherical completions `F₁` and `F₂` of the same space `E` are linearly isometric. The
embedding of `F₂` is an immediate extension (`embedding_isImmediate`), so
`nonempty_linearIsometryEquiv_of_isImmediate` applied to `F₁` yields the
equivalence.
-/
theorem unique (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [IsUltrametricDist F₂] :
    IsSphericalCompletion 𝕜 E F₁ → IsSphericalCompletion 𝕜 E F₂ →
    Nonempty (F₁ ≃ₗᵢ[𝕜] F₂) := by
  intro hF₁ hF₂
  haveI := hF₂.toSphericallyCompleteSpace
  exact nonempty_linearIsometryEquiv_of_isImmediate F₁ hF₁
    (embedding_isImmediate hF₂)

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (hF : IsSphericalCompletion 𝕜 E F)

/--
**Universal property of the spherical completion.**

Every linear isometry `f : E →ₗᵢ[𝕜] F'` into a spherically complete ultrametric space `F'` factors
through the canonical embedding of any spherical completion `F` of `E`: there is a linear isometry
`T : F →ₗᵢ[𝕜] F'` with `T.comp (hF.is_sph_comp.choose) = f`. This is the extension property of the
immediate embedding (`embedding_isImmediate`) into the spherically complete target `F'`.
-/
theorem universal_property
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [IsUltrametricDist F']
    [SphericallyCompleteSpace F'] (f : E →ₗᵢ[𝕜] F') :
    ∃ T : F →ₗᵢ[𝕜] F', T.comp (hF.is_sph_comp.choose) = f :=
  IsImmediate.exists_linearIsometry_comp_eq hF.is_sph_comp.choose (embedding_isImmediate hF) f

/--
`E` is spherically complete if and only if the canonical embedding into a spherical completion `F`
of `E` is surjective.

If `E` is spherically complete then the range of the embedding is a spherically complete submodule
containing itself, so minimality forces it to be everything, i.e. the embedding is surjective.
Conversely, a surjective linear isometry makes `F` (which is spherically complete) linearly
isometric to `E`, transporting spherical completeness back to `E`.
-/
theorem sphericallyCompleteSpace_iff_embedding_to_sphericalCompletion_surjective :
    SphericallyCompleteSpace E ↔ Function.Surjective (hF.is_sph_comp.choose) := by
  haveI := hF.toSphericallyCompleteSpace
  constructor
  · intro h
    exact LinearMap.range_eq_top.mp (hF.is_sph_comp.choose_spec
      (LinearMap.range hF.is_sph_comp.choose.toLinearMap)
      (of_isometryEquiv (Isometry.isometryEquivOnRange hF.is_sph_comp.choose.isometry)) le_rfl)
  · exact fun h ↦ of_isometryEquiv
      (LinearIsometryEquiv.ofSurjective _ h).symm.toIsometryEquiv

end

end IsSphericalCompletion

/--
An ultrametric normed `𝕜`-vector space `E` is spherically complete if and only if it is *maximally
complete* (`MaximallyComplete 𝕜 E`), i.e. it admits no proper immediate extension.

For the forward direction, if `E` were spherically complete yet had a non-surjective immediate
extension `f : E →ₗᵢ[𝕜] F`, then `range f` would be a proper spherically complete subspace of `F`,
whose orthogonal complement `orthComp 𝕜 (range f)` is nonzero (the two are complementary,
`isCompl_orthComp`); a nonzero vector of that complement is metrically orthogonal to `range f`,
contradicting immediacy of `f`. Conversely, if `E` is maximally complete, the canonical embedding
of `E` into its spherical completion is immediate (`IsSphericalCompletion.embedding_isImmediate`),
hence surjective by maximal completeness; so `E` is linearly isometric to the spherically complete
completion and is therefore itself spherically complete.
-/
theorem iff_maximallyComplete (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    SphericallyCompleteSpace E ↔ MaximallyComplete 𝕜 E := by
  constructor
  · intro h
    unfold MaximallyComplete
    by_contra hc
    push Not at hc
    rcases hc with ⟨F, _, _, _, f, hf1, hf2⟩
    replace hf2 : LinearMap.range f.toLinearMap < ⊤ := by
      by_contra hc
      simp only [not_lt_top_iff] at hc
      exact hf2 <| LinearMap.range_eq_top.mp hc
    haveI : SphericallyCompleteSpace (LinearMap.range f.toLinearMap) :=
      of_isometryEquiv <|
        Isometry.isometryEquivOnRange f.isometry
    have : orthComp 𝕜 (LinearMap.range f.toLinearMap) ≠ ⊥ := by
      by_contra hc'
      have := (isCompl_orthComp 𝕜 (LinearMap.range f.toLinearMap)).sup_eq_top
      simp only [hc', bot_le, sup_of_le_left] at this
      simp only [this, lt_self_iff_false] at hf2
    rcases (Submodule.ne_bot_iff _).1 this with ⟨v, hv⟩
    exact hv.2 <| hf1 v (IsMOrtho.of_mem_orthComp _ _ hv.1)
  · intro h
    have hE₀ : IsSphericalCompletion 𝕜 E
        (↥(exists_maximal_immediateExtensionSubmodule 𝕜 E _
          (canonicalSphericallyCompleteExtension 𝕜 E)).choose) := inferInstance
    exact of_isometryEquiv (LinearIsometryEquiv.ofSurjective _
      (h hE₀.is_sph_comp.choose
        (IsSphericalCompletion.embedding_isImmediate hE₀))).symm.toIsometryEquiv

end SphericallyCompleteSpace
