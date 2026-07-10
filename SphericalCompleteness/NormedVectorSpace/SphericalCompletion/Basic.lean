/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Defs

/-!
# Spherical completion: basic results

-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

open IsImmediate

namespace IsSphericalCompletion

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [iud : IsUltrametricDist E₀]
    [hsc : SphericallyCompleteSpace E₀]
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

theorem exist (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    ∃ E₀ : Type u,
      ∃ _ : NormedAddCommGroup E₀,
      ∃ _ : NormedSpace 𝕜 E₀,
      ∃ _ : IsUltrametricDist E₀,
      ∃ _ : SphericallyCompleteSpace E₀,
        IsSphericalCompletion 𝕜 E E₀ := by
  let E₀ := ↥(exists_maximal_immediateExtensionSubmodule 𝕜 E _
    (canonicalSphericallyCompleteExtension 𝕜 E)).choose
  exact ⟨E₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

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
    [SphericallyCompleteSpace F] (hF : IsSphericalCompletion 𝕜 E F) :
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
theorem linearIsometry_of_immediateExtension_in_sphericallyCompleteSpace
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    [SphericallyCompleteSpace F₁] (hF₁ : IsSphericalCompletion 𝕜 E F₁)
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
`linearIsometry_of_immediateExtension_in_sphericallyCompleteSpace` applied to `F₁` yields the
equivalence.
-/
theorem unique (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [IsUltrametricDist F₁]
    [SphericallyCompleteSpace F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [IsUltrametricDist F₂]
    [SphericallyCompleteSpace F₂] :
    IsSphericalCompletion 𝕜 E F₁ → IsSphericalCompletion 𝕜 E F₂ →
    Nonempty (F₁ ≃ₗᵢ[𝕜] F₂) := by
  intro hF₁ hF₂
  exact linearIsometry_of_immediateExtension_in_sphericallyCompleteSpace F₁ hF₁
    (embedding_isImmediate hF₂)

/--
**Universal property of the spherical completion.**

Every linear isometry `f : E →ₗᵢ[𝕜] F'` into a spherically complete ultrametric space `F'` factors
through the canonical embedding of any spherical completion `F` of `E`: there is a linear isometry
`T : F →ₗᵢ[𝕜] F'` with `T.comp (hF.is_sph_comp.choose) = f`. This is the extension property of the
immediate embedding (`embedding_isImmediate`) into the spherically complete target `F'`.
-/
theorem universal_property {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    [SphericallyCompleteSpace F] (hF : IsSphericalCompletion 𝕜 E F)
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
theorem sphericalCompleteSpacee_iff_embeding_to_sphericalCompletion_surjective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    [SphericallyCompleteSpace F] (hF : IsSphericalCompletion 𝕜 E F) :
    SphericallyCompleteSpace E ↔ Function.Surjective (hF.is_sph_comp.choose) := by
  constructor
  · intro h
    exact LinearMap.range_eq_top.mp (hF.is_sph_comp.choose_spec
      (LinearMap.range hF.is_sph_comp.choose.toLinearMap)
      (of_isometryEquiv (Isometry.isometryEquivOnRange hF.is_sph_comp.choose.isometry)) le_rfl)
  · exact fun h ↦ of_isometryEquiv
      (LinearIsometryEquiv.ofSurjective _ h).symm.toIsometryEquiv

end IsSphericalCompletion

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
