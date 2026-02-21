import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Defs

open Metric

namespace SphericallyCompleteSpace

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [iud : IsUltrametricDist E₀]
[hsc : SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
SphericallyCompleteSpace (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := by
  rw [sphericallyCompleteSpace_iff_strictAnti_radius]
  by_contra hc
  push_neg at hc
  rcases hc with ⟨c, r, hsr, hanti, hemp⟩
  have := @hsc.isSphericallyComplete (fun n => (c n).1) r (by
    intro m n hmn z hz
    simp only [mem_closedBall] at *
    refine le_trans (iud.dist_triangle_max z (c n).val (c m).val) ?_
    refine max_le (le_trans hz <| hsr.antitone hmn) ?_
    simpa only [← mem_closedBall] using hanti hmn <| mem_closedBall_self NNReal.zero_le_coe )
  simp only [Set.nonempty_iInter, mem_closedBall] at this
  rcases this with ⟨a, ha⟩
  if haa : a ∈ (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose then
    contrapose hemp
    refine Set.nonempty_iff_ne_empty.mp ⟨⟨a, haa⟩, ?_⟩
    simp only [Set.mem_iInter, mem_closedBall]
    intro i
    simpa only [dist_le_coe] using ha i
  else
  have : ((exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose +
    Submodule.span 𝕜 {a}) ∉ imm_ext_in_sph_comp E E₀ f := by
    by_contra hc
    have : (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose <
      (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose + Submodule.span 𝕜 {a} := by
      simpa only [Submodule.add_eq_sup, left_lt_sup, Submodule.span_singleton_le_iff_mem]
    exact (not_le_of_gt this) <|
      (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.2 hc (le_of_lt this)
  simp only [imm_ext_in_sph_comp, Set.mem_setOf_eq, Submodule.add_eq_sup, not_exists] at this
  specialize this <| le_sup_of_le_left
    (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.out.choose
  unfold IsImmediate at this
  push_neg at this
  rcases this with ⟨b', hb'1, hb'2⟩
  rcases Submodule.mem_sup.1 b'.prop with ⟨x', hx', v', hv', hx'v'⟩
  rcases Submodule.mem_span_singleton.1 hv' with ⟨s, hs⟩
  rw [← hs] at hx'v'
  have hhs : s ≠ 0 := by
    by_contra hc
    simp only [hc, zero_smul, add_zero] at hx'v'
    subst hx'v'
    have := (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.out.choose_spec
    specialize this ⟨b', hx'⟩ ?_
    · unfold MOrth at *
      simp only [AddSubgroupClass.coe_norm] at *
      rw [← hb'1]
      refine eq_of_le_of_ge ?_ ?_
      · apply (le_infDist (by use 0; simp)).2
        intro y hy
        simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] at hy
        rcases hy with ⟨z, hm, hz⟩
        refine le_trans (infDist_le_dist_of_mem (?_ : ⟨y,?_⟩ ∈ _)) (le_of_eq rfl)
        · simpa only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] using ⟨z, hm, by simp only [← hz]⟩
        · refine (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.out.choose ?_
          simp only [← hz, LinearMap.mem_range, hm]
      · apply (le_infDist (by use 0; simp)).2
        intro y hy
        simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] at hy
        rcases hy with ⟨z, hm, hz⟩
        refine le_trans (infDist_le_dist_of_mem (?_ : ⟨y, ?_⟩ ∈ _)) (le_of_eq rfl)
        · simpa only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] using ⟨z, hm, by simp only [← hz]⟩
        · refine Submodule.mem_sup_left <|
            (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.out.choose ?_
          simp only [← hz, LinearMap.mem_range, hm]
    simp only [Submodule.mk_eq_zero, ZeroMemClass.coe_eq_zero] at this
    exact hb'2 this
  let b := s⁻¹ • b'
  let x := - s⁻¹ • x'
  have : b = a - x := by
    simp only [SetLike.val_smul, ← hx'v', smul_add, neg_smul, sub_neg_eq_add, b, x]
    rw [add_comm]
    simpa only [add_left_inj] using inv_smul_smul₀ hhs a
  have hb1 := smul_morth_of_morth (s⁻¹) hb'1
  replace hb1 : MOrth 𝕜 b.val (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose := by
    by_contra hc
    rcases not_morth_iff_exists_dist_lt_norm.1 hc with ⟨g, hg1, hg2⟩
    rw [dist_eq_norm] at hg2
    have hg2' := norm_eq_of_norm_sub_lt_left hg2
    have hgg : g ≠ 0 := by
      by_contra hc
      simp only [hc, norm_zero, norm_eq_zero, ZeroMemClass.coe_eq_zero] at hg2'
      simp only [dist_le_coe, MOrth, AddSubgroupClass.coe_norm, ne_eq, Subtype.forall,
        Submodule.mk_eq_zero, hg2', ZeroMemClass.coe_zero, SetLike.val_smul, norm_zero] at *
      contrapose hc
      exact infDist_zero_of_mem <| by simp only [SetLike.mem_coe, zero_mem]
    have := (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose_spec.1.out.choose_spec
    rcases not_morth_iff_exists_dist_lt_norm.1
      ((fun x => mt (this x)) ⟨g,hg1⟩ (by simp [hgg])) with ⟨e, he1, he2⟩
    simp only [AddSubgroupClass.coe_norm, ← hg2'] at he2
    rw [(by rfl : dist ⟨g, hg1⟩ e = dist g e.val), dist_eq_norm] at he2
    suffices hh : ‖b.val - e.val‖ < ‖b.val‖ by
      contrapose hb1
      apply not_morth_iff_exists_dist_lt_norm.2
      use ⟨e.val, Submodule.mem_sup_left e.prop⟩
      simp only [LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk,
        Subtype.exists] at he1
      rcases he1 with ⟨q1,q2,q3⟩
      replace q3 : q1 = e.val := by simp [← q3]
      simp only [← q3, LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk,
        Subtype.mk.injEq, Subtype.exists, exists_prop, exists_eq_right, q2,
        AddSubgroupClass.coe_norm, SetLike.val_smul, true_and, gt_iff_lt]
      simpa only [q3, dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub,
        SetLike.val_smul]
    rw [(by abel : b.val - e.val = (b.val - g) + (g - e.val))]
    exact lt_of_le_of_lt (iud.norm_add_le_max _ _) <| max_lt hg2 he2
  have hx : x ∈ (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose :=
    Submodule.smul_mem (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose (-s⁻¹) hx'
  suffices h : ∀ i : ℕ, ⟨x,hx⟩ ∈ closedBall (c i) ↑(r i) by
    contrapose hemp
    exact Set.nonempty_iff_ne_empty.mp ⟨⟨x, hx⟩, by simpa only [Set.mem_iInter]⟩
  intro i
  simp only [mem_closedBall, dist_eq_norm]
  refine le_trans (by simp : ‖⟨x, hx⟩ - c i‖ ≤ max ‖⟨x, hx⟩ - c i‖ ‖b‖) <| le_trans ?_ (ha i)
  have : a - (c i).val = b - ((c i).val - x) := by
    simp only [this, sub_sub_sub_cancel_right]
  rw [dist_eq_norm, this]
  conv => arg 1; simp only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
  refine le_of_eq <| Eq.symm <| eq_of_le_of_ge ?_ ?_
  · rw [sub_sub_eq_add_sub, ← add_sub, max_comm]
    exact iud.norm_add_le_max _ _
  · if hf : ‖x - ↑(c i)‖ = ‖↑b‖ then
      simp only [hf, AddSubgroupClass.coe_norm, max_self, ← dist_eq_norm, b, SetLike.val_smul]
      simp only [MOrth, AddSubgroupClass.coe_norm, SetLike.val_smul, b] at hb1
      rw [← hb1]
      apply infDist_le_dist_of_mem
      refine SetLike.mem_coe.mpr <|
        Submodule.sub_mem (exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose ?_ hx
      simp only [SetLike.coe_mem]
    else
    have := iud.norm_add_eq_max_of_norm_ne_norm hf
    simp only [LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply] at this
    rw [← this]
    apply le_of_eq
    congr
    abel

/-- The spherical completion of an ultrametric normed space is spherically complete. -/
instance instSphericallyCompleteSpaceSphericalCompletion
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
  SphericallyCompleteSpace (SphericalCompletion 𝕜 E) := inferInstance

/-- The canonical embedding into the spherical completion is an immediate extension. -/
theorem SphericalCompletionEmbedding_isImmediate (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    IsImmediate (SphericalCompletionEmbedding 𝕜 E) := by
  have := (exists_max_imm_ext_in_sph_comp 𝕜 E
      (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)
      ).choose_spec.1.out.choose_spec
  refine fun v hv => this v ?_
  convert hv
  ext z
  simp only [sphericallyCompleteExtension, QuotientAddGroup.mk'_apply,
    LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Subtype.exists]
  constructor
  · rintro ⟨_, _, ha2⟩
    simpa only [← ha2, Subtype.mk.injEq, Subtype.forall, Submodule.mk_eq_zero]
  · rintro ⟨_, ha⟩
    simp only [← ha, Subtype.mk.injEq, exists_prop, exists_eq_right, exists_apply_eq_apply]

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
  push_neg at hMo
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
    push_neg at hc
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
