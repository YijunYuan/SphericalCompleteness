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
`SphericallyCompleteSpace.IsSphericalCompletion ι`, indexed by a linear isometry
`ι : E →ₗᵢ[𝕜] F`, which asserts that `ι` realises the spherically complete space `F` as a *minimal*
spherically complete extension of `E` (no proper spherically complete submodule of `F` contains the
image of `E`).

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
instance instIsSphericalCompletionOfMaximalImmediateExtensionSubmodule
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    IsSphericalCompletion (maximalImmediateExtensionEmbedding f) where
  minimal_of_sphericallyComplete := by
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
carrying an ultrametric normed `𝕜`-vector-space structure together with a linear isometry
`ι : E →ₗᵢ[𝕜] E₀` for which `IsSphericalCompletion ι` holds. Since that class `extends
SphericallyCompleteSpace`, `E₀` is in particular spherically complete.

The witness is the maximal immediate extension carved out of the canonical spherically complete
extension `canonicalSphericallyCompleteExtension 𝕜 E` (a quotient of an `ℓ∞`-type space): the
maximal immediate submodule selected by `exists_maximal_immediateExtensionSubmodule` is itself
spherically complete and, by maximality, a minimal spherically complete extension of `E`, embedded
via `maximalImmediateExtensionEmbedding`. All of the required structure and the completion property
are supplied by the surrounding instances.
-/
theorem exists_isSphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    ∃ E₀ : Type u,
      ∃ _ : NormedAddCommGroup E₀,
      ∃ _ : NormedSpace 𝕜 E₀,
      ∃ _ : IsUltrametricDist E₀,
      ∃ ι : E →ₗᵢ[𝕜] E₀,
        IsSphericalCompletion ι := by
  let E₀ := ↥(exists_maximal_immediateExtensionSubmodule 𝕜 E _
    (canonicalSphericallyCompleteExtension 𝕜 E)).choose
  exact ⟨E₀, inferInstance, inferInstance, inferInstance,
    maximalImmediateExtensionEmbedding (canonicalSphericallyCompleteExtension 𝕜 E), inferInstance⟩

/--
Any embedding `ι : E →ₗᵢ[𝕜] F` realising `F` as a spherical completion of `E` (i.e. carrying an
`IsSphericalCompletion ι` instance) is an *immediate* extension.

Apply the Zorn construction `exists_maximal_immediateExtensionSubmodule` inside the spherically
complete ambient space `F` to the embedding `ι`: it selects a maximal submodule `S ⊇ range ι` for
which the inclusion `range ι →ₗᵢ S` is immediate. This `S` is itself spherically complete, so
minimality of the spherical completion forces `S = ⊤`. Immediacy of that inclusion, read off in the
ambient space via `mem_immediateExtensionSubmodules_iff`, is exactly immediacy of `ι`.
-/
theorem embedding_isImmediate {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {ι : E →ₗᵢ[𝕜] F} (hF : IsSphericalCompletion ι) :
    IsImmediate ι := by
  obtain ⟨hSle, hSimm⟩ := mem_immediateExtensionSubmodules_iff.1
    (exists_maximal_immediateExtensionSubmodule 𝕜 E F ι).choose_spec.1
  have hStop : (exists_maximal_immediateExtensionSubmodule 𝕜 E F ι).choose = ⊤ :=
    hF.minimal_of_sphericallyComplete _ inferInstance hSle
  intro v hv
  have hvS : v ∈ (exists_maximal_immediateExtensionSubmodule 𝕜 E F ι).choose := by
    rw [hStop]; exact Submodule.mem_top
  simpa using congrArg Subtype.val (hSimm ⟨v, hvS⟩ hv)

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
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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

/--
Uniqueness of the spherical completion.

Any two spherical completions of the same space `E`, given by embeddings `ι₁ : E →ₗᵢ[𝕜] F₁` and
`ι₂ : E →ₗᵢ[𝕜] F₂`, have linearly isometric codomains: there is a linear isometric equivalence
`f : F₁ ≃ₗᵢ[𝕜] F₂` compatible with the embeddings, i.e. `f.comp ι₁ = ι₂`. The embedding `ι₂` is an
immediate extension (`embedding_isImmediate`), so `exists_linearIsometryEquiv_of_isImmediate`
applied to `ι₁` yields an equivalence `T : F₂ ≃ₗᵢ[𝕜] F₁` with `T.comp ι₂ = ι₁`; its inverse `T.symm`
is the required intertwining equivalence.
-/
theorem unique {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [IsUltrametricDist F₂]
    {ι₁ : E →ₗᵢ[𝕜] F₁} {ι₂ : E →ₗᵢ[𝕜] F₂} :
    IsSphericalCompletion ι₁ → IsSphericalCompletion ι₂ →
    ∃ f : F₁ ≃ₗᵢ[𝕜] F₂, f.toLinearIsometry.comp ι₁ = ι₂ := by
  intro hF₁ hF₂
  rcases exists_linearIsometryEquiv_of_isImmediate hF₁ (embedding_isImmediate hF₂) with ⟨T, hT⟩
  refine ⟨T.symm, ?_⟩
  ext x
  exact T.injective <| by simpa using (congrArg (fun g => g x) hT).symm

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [IsUltrametricDist F']
    [SphericallyCompleteSpace F']
    (f : E →ₗᵢ[𝕜] F') (hF : IsSphericalCompletion ι) :
    ∃ T : F →ₗᵢ[𝕜] F', T.comp ι = f :=
  IsImmediate.exists_linearIsometry_comp_eq ι (embedding_isImmediate hF) f

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
  constructor
  · intro h
    exact LinearMap.range_eq_top.mp (hF.minimal_of_sphericallyComplete
      (LinearMap.range ι.toLinearMap)
      (of_isometryEquiv (Isometry.isometryEquivOnRange ι.isometry)) le_rfl)
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
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · unfold MaximallyComplete
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
  · exact of_isometryEquiv (LinearIsometryEquiv.ofSurjective _
      (h (maximalImmediateExtensionEmbedding (canonicalSphericallyCompleteExtension 𝕜 E))
        (IsSphericalCompletion.embedding_isImmediate inferInstance))).symm.toIsometryEquiv

end SphericallyCompleteSpace
