/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Defs

/-!
# Spherical completion: basic results

Basic results on the spherical completion of a normed vector space.
-/

open Metric

namespace SphericallyCompleteSpace

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [iud : IsUltrametricDist E₀]
[hsc : SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
SphericallyCompleteSpace (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := by
  rw [sphericallyCompleteSpace_iff_strictAnti_radius]
  set K := (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose with hK
  by_contra hc
  push Not at hc
  rcases hc with ⟨c, r, hsr, hanti, hemp⟩
  have := @hsc.isSphericallyComplete (fun n => (c n).1) r (by
    intro m n hmn z hz
    simp only [mem_closedBall] at *
    refine le_trans (iud.dist_triangle_max z (c n).val (c m).val) ?_
    refine max_le (le_trans hz <| hsr.antitone hmn) ?_
    have h_in : c n ∈ closedBall (c m) ↑(r m) :=
      hanti hmn <| mem_closedBall_self NNReal.zero_le_coe
    rw [mem_closedBall] at h_in
    rw [show dist ((c n).val) ((c m).val) = dist (c n) (c m) from rfl]
    exact h_in)
  simp only [Set.nonempty_iInter, mem_closedBall] at this
  rcases this with ⟨a, ha⟩
  if haa : a ∈ K then
    contrapose hemp
    refine Set.nonempty_iff_ne_empty.mp ⟨⟨a, haa⟩, ?_⟩
    simp only [Set.mem_iInter, mem_closedBall]
    intro i
    have := ha i
    change dist (⟨a, haa⟩ : _) (c i) ≤ ↑(r i)
    rw [show dist (⟨a, haa⟩ : _) (c i) = dist a (c i).val from rfl]
    exact this
  else
  have : (K + Submodule.span 𝕜 {a}) ∉ imm_ext_in_sph_comp E E₀ f := by
    by_contra hc
    have : K < K + Submodule.span 𝕜 {a} := by
      simpa only [Submodule.add_eq_sup, left_lt_sup, Submodule.span_singleton_le_iff_mem]
    exact (not_le_of_gt this) <|
      (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.2 hc (le_of_lt this)
  rw [mem_imm_ext_iff, not_exists] at this
  specialize this <| le_sup_of_le_left
    (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.choose
  simp only [not_forall] at this
  rcases this with ⟨b', hb'1, hb'2⟩
  rcases Submodule.mem_sup.1 b'.prop with ⟨x', hx', v', hv', hx'v'⟩
  rcases Submodule.mem_span_singleton.1 hv' with ⟨s, hs⟩
  rw [← hs] at hx'v'
  have hhs : s ≠ 0 := by
    by_contra hc
    simp only [hc, zero_smul, add_zero] at hx'v'
    subst hx'v'
    obtain ⟨_, himmK⟩ := mem_imm_ext_iff.1 (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1
    exact hb'2 (ZeroMemClass.coe_eq_zero.mp (congrArg Subtype.val (himmK ⟨b', hx'⟩ hb'1)))
  let b := s⁻¹ • b'
  let x := - s⁻¹ • x'
  have : b = a - x := by
    simp only [SetLike.val_smul, ← hx'v', smul_add, neg_smul, sub_neg_eq_add, b, x]
    rw [add_comm]
    simpa only [add_left_inj] using inv_smul_smul₀ hhs a
  have hb'1' : MOrth 𝕜 b' (LinearMap.range (inclusionᵢ (le_sup_of_le_left
      (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.choose)).toLinearMap) :=
    (morth_range_inclusionᵢ_iff _ b').2 hb'1
  have hb1 := @smul_morth_of_morth 𝕜 _ _ _ _ inferInstance b' _ s⁻¹ hb'1'
  replace hb1 : MOrth 𝕜 b.val K := by
    by_contra hc
    rcases not_morth_iff_exists_dist_lt_norm.1 hc with ⟨g, hg1, hg2⟩
    rw [dist_eq_norm] at hg2
    have hg2' := norm_eq_of_norm_sub_lt_left hg2
    have hgg : g ≠ 0 := by
      by_contra hc
      simp only [hc, norm_zero, norm_eq_zero, ZeroMemClass.coe_eq_zero] at hg2'
      simp only [dist_le_coe, MOrth, ne_eq,
        hg2', ZeroMemClass.coe_zero, norm_zero] at *
      contrapose hc
      exact infDist_zero_of_mem <| by simp only [SetLike.mem_coe, zero_mem]
    have hChooseSpec := (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.choose_spec
    have hNMorth := mt (hChooseSpec ⟨g, hg1⟩)
        (fun h => hgg (congrArg Subtype.val h))
    rcases @not_morth_iff_exists_dist_lt_norm 𝕜 _ (↥K)
        _ _ inferInstance (⟨g, hg1⟩) _ |>.1 hNMorth with ⟨e, he1, he2⟩
    simp only [Submodule.coe_norm, ← hg2', dist_eq_norm, AddSubgroupClass.coe_sub] at he2
    suffices hh : ‖b.val - e.val‖ < ‖b.val‖ by
      contrapose hb1
      apply @not_morth_iff_exists_dist_lt_norm 𝕜 _ _ _ _ inferInstance |>.2
      use ⟨e.val, Submodule.mem_sup_left e.prop⟩
      simp only [LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk,
        inclusionᵢ, Subtype.exists] at he1
      rcases he1 with ⟨q1, q2, q3⟩
      replace q3 : q1 = e.val := by simp [← q3]
      constructor
      · exact ⟨⟨q1, q2⟩, by subst q3; rfl⟩
      · rw [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_norm]
        exact hh
    rw [(by abel : b.val - e.val = (b.val - g) + (g - e.val))]
    exact lt_of_le_of_lt (iud.norm_add_le_max _ _) <| max_lt hg2 he2
  have hx : x ∈ K := Submodule.smul_mem K (-s⁻¹) hx'
  suffices h : ∀ i : ℕ, ⟨x,hx⟩ ∈ closedBall (c i) ↑(r i) by
    contrapose hemp
    exact Set.nonempty_iff_ne_empty.mp ⟨⟨x, hx⟩, by simpa only [Set.mem_iInter]⟩
  intro i
  simp only [mem_closedBall]
  have hbval : b.val = a - x := this
  have hb1' : infDist b.val ↑K = ‖b.val‖ := hb1
  have hcix : (↑(c i) - x : E₀) ∈ K := Submodule.sub_mem _ (c i).prop hx
  have hdist : dist ⟨x, hx⟩ (c i) = ‖x - ↑(c i)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  have hda : dist a ↑(c i) = ‖b.val - (↑(c i) - x)‖ := by
    rw [dist_eq_norm, hbval]; congr 1; abel
  rw [hdist]
  calc ‖x - ↑(c i)‖
      ≤ max ‖x - ↑(c i)‖ ‖b.val‖ := le_max_left _ _
    _ ≤ ‖b.val - (↑(c i) - x)‖ := by
        if hf : ‖x - ↑(c i)‖ = ‖b.val‖ then
          rw [hf, max_self, ← hb1', ← dist_eq_norm]
          exact infDist_le_dist_of_mem (SetLike.mem_coe.mpr hcix)
        else
          have hnorm_ne : ‖b.val‖ ≠ ‖x - ↑(c i)‖ := Ne.symm hf
          rw [show b.val - (↑(c i) - x) = b.val + (x - ↑(c i)) by abel,
            max_comm, iud.norm_add_eq_max_of_norm_ne_norm hnorm_ne]
    _ = dist a ↑(c i) := hda.symm
    _ ≤ ↑(r i) := ha i

/-- The spherical completion of an ultrametric normed space is spherically complete. -/
instance instSphericallyCompleteSpaceSphericalCompletion
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
  SphericallyCompleteSpace (SphericalCompletion 𝕜 E) :=
  show SphericallyCompleteSpace ↥(exists_max_imm_ext_in_sph_comp 𝕜 E
    _ (sphericallyCompleteExtension 𝕜 E)).choose from inferInstance

/-- The canonical embedding into the spherical completion is an immediate extension. -/
theorem SphericalCompletionEmbedding_isImmediate (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    IsImmediate (SphericalCompletionEmbedding 𝕜 E) := by
  have himm := (exists_max_imm_ext_in_sph_comp 𝕜 E
      (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)
      ).choose_spec.1.choose_spec
  unfold IsImmediate at himm ⊢
  intro v hv
  apply himm v
  -- Convert hv : MOrth 𝕜 v (range SphericalCompletionEmbedding) to
  -- MOrth 𝕜 v (range gChoose) by showing the ranges are equal
  convert hv using 2 <;> try rfl
  apply Submodule.ext_iff.mpr
  intro z
  simp only [LinearMap.mem_range, SphericalCompletionEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    inclusionᵢ]
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨e', he'⟩ := LinearMap.mem_range.mp e.prop
    exact ⟨e', by simp [← he']⟩
  · rintro ⟨e, rfl⟩
    exact ⟨⟨(sphericallyCompleteExtension 𝕜 E) e, LinearMap.mem_range_self _ _⟩, rfl⟩

/--
Minimality of the spherical completion.

If `M` is a `𝕜`-submodule of `SphericalCompletion 𝕜 E` that contains the range of the canonical
embedding `SphericalCompletionEmbedding 𝕜 E` and is itself spherically complete, then `M` must be
the whole space.

In other words, there is no proper spherically complete intermediate submodule between `E` (via its
embedding) and its spherical completion.
-/
theorem sphericalCompletion_minimal (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
∀ M : Submodule 𝕜 (SphericalCompletion 𝕜 E),
LinearMap.range (SphericalCompletionEmbedding 𝕜 E).toLinearMap ≤ M →
SphericallyCompleteSpace M → M = ⊤ := by
  intro M hM hsc
  by_contra hc
  have hMo : OrthComp 𝕜 M ≠ ⊥ := by
    by_contra hc'
    have := (isCompl_orthcomp 𝕜 M).sup_eq_top
    simp only [hc', bot_le, sup_of_le_left] at this
    exact hc this
  replace hMo := (Submodule.eq_bot_iff (OrthComp 𝕜 M)).not.1 hMo
  push Not at hMo
  rcases hMo with ⟨b, hb1, hb2⟩
  apply morth_of_mem_orthComp at hb1
  refine hb2 (SphericalCompletionEmbedding_isImmediate 𝕜 E b ?_)
  rw [morth_iff_forall_orth] at *
  exact fun y hy => hb1 y <| hM hy

/--
Uniqueness of the spherical completion.

If `F` is spherically complete and `f : E →ₗᵢ[𝕜] F` is such that every spherically complete
`𝕜`-submodule of `F` containing `range f` is the whole space, then `F` is (linearly) isometric to
`SphericalCompletion 𝕜 E`.
-/
theorem sphericalCompletion_unique (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
{F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
[SphericallyCompleteSpace F]
{f : E →ₗᵢ[𝕜] F}
(hf : ∀ M : Submodule 𝕜 F, LinearMap.range f.toLinearMap ≤ M → SphericallyCompleteSpace M → M = ⊤) :
Nonempty (SphericalCompletion 𝕜 E ≃ₗᵢ[𝕜] F) := by
  rcases exists_linearIsometry_comp_eq_of_isImmediate (SphericalCompletionEmbedding 𝕜 E)
    (SphericalCompletionEmbedding_isImmediate 𝕜 E) f with ⟨T, hT⟩
  specialize hf (LinearMap.range T) (by
    rw [← hT]
    apply LinearMap.range_comp_le_range
    ) <| sphericallyCompleteSpace_of_isometryEquiv <| Isometry.isometryEquivOnRange T.isometry
  exact Nonempty.intro <| LinearIsometryEquiv.ofSurjective T <| LinearMap.range_eq_top.mp hf

/--
Uniqueness of the spherical completion (immediate-extension form).

If `F` is spherically complete and `f : E →ₗᵢ[𝕜] F` is an immediate extension, then `F` is
linearly isometric to `SphericalCompletion 𝕜 E`.

This is a streamlined version of `sphericalCompletion_unique` where the minimality hypothesis is
replaced by the assumption `IsImmediate f`.
-/
theorem sphericalCompletion_unique' (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
{F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
[SphericallyCompleteSpace F]
{f : E →ₗᵢ[𝕜] F} (hf : IsImmediate f) :
Nonempty (SphericalCompletion 𝕜 E ≃ₗᵢ[𝕜] F) := by
  rcases exists_linearIsometry_comp_eq_of_isImmediate f hf
    (SphericalCompletionEmbedding 𝕜 E) with ⟨T, hT⟩
  have := sphericalCompletion_minimal 𝕜 E (LinearMap.range T.toLinearMap)
  rw [← hT] at this
  specialize this (by apply LinearMap.range_comp_le_range) <|
    sphericallyCompleteSpace_of_isometryEquiv <| Isometry.isometryEquivOnRange T.isometry
  exact Nonempty.intro <| (LinearIsometryEquiv.ofSurjective T <|
    LinearMap.range_eq_top.mp this).symm

/-!
## Universal property

Any linear isometry `f : E →ₗᵢ[𝕜] F` into a spherically complete ultrametric space `F` uniquely
extends along the canonical embedding `SphericalCompletionEmbedding 𝕜 E` to a linear isometry
`T : SphericalCompletion 𝕜 E →ₗᵢ[𝕜] F`.
-/
theorem sphericalCompletion_universal_property (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
{F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
[SphericallyCompleteSpace F]
(f : E →ₗᵢ[𝕜] F) :
∃ (T : SphericalCompletion 𝕜 E →ₗᵢ[𝕜] F), T.comp (SphericalCompletionEmbedding 𝕜 E) = f :=
  exists_linearIsometry_comp_eq_of_isImmediate (SphericalCompletionEmbedding 𝕜 E)
    (SphericalCompletionEmbedding_isImmediate 𝕜 E) f

/--
`E` is spherically complete if and only if it is maximally complete.

Here `MaximallyComplete 𝕜 E` means that `E` admits no proper immediate extension (as a `𝕜`-normed
space with ultrametric distance).
-/
theorem sphericallyComplete_iff_maximallyComplete (𝕜 : Type*) [NontriviallyNormedField 𝕜]
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
      sphericallyCompleteSpace_of_isometryEquiv <|
        Isometry.isometryEquivOnRange f.isometry
    have : OrthComp 𝕜 (LinearMap.range f.toLinearMap) ≠ ⊥ := by
      by_contra hc'
      have := (isCompl_orthcomp 𝕜 (LinearMap.range f.toLinearMap)).sup_eq_top
      simp only [hc', bot_le, sup_of_le_left] at this
      simp only [this, lt_self_iff_false] at hf2
    rcases (Submodule.ne_bot_iff _).1 this with ⟨v, hv⟩
    exact hv.2 <| hf1 v (morth_of_mem_orthComp _ _ hv.1)
  · intro h
    specialize h (SphericalCompletionEmbedding 𝕜 E) (SphericalCompletionEmbedding_isImmediate 𝕜 E)
    exact sphericallyCompleteSpace_of_isometryEquiv
      (LinearIsometryEquiv.ofSurjective _ h).symm.toIsometryEquiv

/--
`E` is spherically complete if and only if the canonical embedding
`SphericalCompletionEmbedding 𝕜 E : E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E` is surjective.

Equivalently, `E` is spherically complete iff it already coincides (up to linear isometry) with
its spherical completion.
-/
theorem sphericallyComplete_iff_eq_sphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
SphericallyCompleteSpace E ↔ Function.Surjective
  (SphericalCompletionEmbedding 𝕜 E) := by
  constructor
  · intro h
    have := sphericalCompletion_minimal 𝕜 _
      (LinearMap.range (SphericalCompletionEmbedding 𝕜 E).toLinearMap) (le_refl _) ?_
    · exact LinearMap.range_eq_top.mp this
    · exact sphericallyCompleteSpace_of_isometryEquiv <|
        Isometry.isometryEquivOnRange (SphericalCompletionEmbedding 𝕜 E).isometry
  · exact fun h => sphericallyCompleteSpace_of_isometryEquiv
      (LinearIsometryEquiv.ofSurjective _ h).symm.toIsometryEquiv

end SphericallyCompleteSpace
