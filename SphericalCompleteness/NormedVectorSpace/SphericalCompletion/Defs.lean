import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension
import SphericalCompleteness.NormedVectorSpace.Immediate
import SphericalCompleteness.NormedVectorSpace.Existance
import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

open Metric

namespace SphericallyCompleteSpace

def IsSphericalComletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
(F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] : Prop :=
SphericallyCompleteSpace F ∧
∃ (f : E →ₗᵢ[𝕜] F), ∀ M : Submodule 𝕜 F, LinearMap.range f ≤ M → SphericallyCompleteSpace M → M = ⊤

def ayaka {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀)
: Set (Submodule 𝕜 E₀) := {M : Submodule 𝕜 E₀ |
    ∃ hc : LinearMap.range f ≤ M,
    IsImmediate ({toFun x := ⟨x.1, hc x.2⟩
                  map_add' _ _ := rfl
                  map_smul' _ _ := rfl
                  norm_map' _ := rfl} : LinearMap.range f →ₗᵢ[𝕜] M)
  }

lemma ayaka_nonempty {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀)
: (ayaka E E₀ f).Nonempty := by
  use LinearMap.range f
  simp [ayaka, IsImmediate, MOrth]
  intro a x hc hh
  suffices hh : ‖a‖ = 0 by
    exact norm_eq_zero.mp hh
  rw [← hh]
  refine Metric.infDist_zero_of_mem ?_
  simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, exists_eq]

theorem zorn_ayaka (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) : ∃ m, Maximal (fun x ↦ x ∈ ayaka E E₀ f) m := by
  apply zorn_le₀
  intro C hC1 hC2
  if hC : ¬ C.Nonempty then
    refine ⟨(ayaka_nonempty E E₀ f).some, Set.Nonempty.some_mem (ayaka_nonempty E E₀ f), ?_⟩
    intro c hc
    contrapose hC
    use c
  else
  use ⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i
  constructor
  · simp [ayaka]
    use (by
      intro z hz
      rw [Submodule.mem_iSup]
      intro N hN
      simp only [not_not] at hC
      exact (hN ⟨hC.some, hC.some_mem⟩)  <| (hC1 hC.some_mem).1 hz
      )
    simp only [IsImmediate, MOrth, AddSubgroupClass.coe_norm, Subtype.forall, Submodule.mk_eq_zero]
    intro x hx hh
    haveI : Nonempty ↑C := by
      refine Set.Nonempty.coe_sort ?_
      simpa using hC
    have t : x ∈ (↑(@iSup (Submodule 𝕜 E₀) (↑C)
      CompleteLattice.toConditionallyCompleteLattice.toSupSet fun i ↦ ↑i : Set E₀)) := hx
    rw [Submodule.coe_iSup_of_directed (fun x => x.val : C → Submodule 𝕜 E₀) hC2.directed] at t
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at t
    rcases t with ⟨N, hN, hx⟩
    rcases (hC1 hN).out with ⟨hc, himm⟩
    simp only [IsImmediate, MOrth, AddSubgroupClass.coe_norm, Subtype.forall,
      Submodule.mk_eq_zero] at himm
    apply himm x hx
    rw [← hh]
    repeat rw [infDist_eq_iInf]
    refine eq_of_le_of_ge ?_ ?_
    · apply le_ciInf
      intro w
      apply csInf_le
      · use 0
        simp only [lowerBounds, SetLike.coe_sort_coe, Set.mem_range, Subtype.exists,
          LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, exists_prop,
          Subtype.mk.injEq, exists_eq_right, exists_and_left, exists_exists_eq_and,
          forall_exists_index, Set.mem_setOf_eq]
        intro _ _ _ h
        simp only [← h, dist_nonneg]
      · rcases Set.mem_range.1 w.prop with ⟨v,hv⟩
        simp only [LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at hv
        simp [← hv]
        rcases LinearMap.mem_range.1 v.prop with ⟨u,hu⟩
        use u
        rw [hu]
        exact ⟨hc v.prop, rfl⟩
    · apply le_ciInf
      intro w
      apply csInf_le
      · use 0
        simp only [lowerBounds, SetLike.coe_sort_coe, Set.mem_range, Subtype.exists,
          LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, exists_prop,
          Subtype.mk.injEq, exists_eq_right, exists_and_left, exists_exists_eq_and,
          forall_exists_index, Set.mem_setOf_eq]
        intro _ _ _ h
        simp only [← h, dist_nonneg]
      · rcases Set.mem_range.1 w.prop with ⟨v,hv⟩
        simp only [LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at hv
        simp [← hv]
        rcases LinearMap.mem_range.1 v.prop with ⟨u,hu⟩
        use u
        rw [hu]
        refine ⟨(?_ : N ≤ _) <| hc v.prop ,rfl⟩
        exact le_csSup ⟨⊤, by simp [upperBounds]⟩ (by use ⟨N, hN⟩)
  · intro M hM z hz
    rw [Submodule.mem_iSup]
    intro N hN
    exact (hN ⟨M, hM⟩) hz

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
NormedAddCommGroup (↥(zorn_ayaka 𝕜 E E₀ f).choose) := inferInstance

noncomputable instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
NormedSpace 𝕜 (↥(zorn_ayaka 𝕜 E E₀ f).choose) := inferInstance

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
IsUltrametricDist (↥(zorn_ayaka 𝕜 E E₀ f).choose) := inferInstance

noncomputable instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [iud : IsUltrametricDist E₀]
[hsc : SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
SphericallyCompleteSpace (↥(zorn_ayaka 𝕜 E E₀ f).choose) := by
  rw [sphericallyComplete_iff']
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
  if haa : a ∈ (zorn_ayaka 𝕜 E E₀ f).choose then
    contrapose hemp
    refine Set.nonempty_iff_ne_empty.mp ⟨⟨a, haa⟩, ?_⟩
    simp only [Set.mem_iInter, mem_closedBall]
    intro i
    simpa only [dist_le_coe] using ha i
  else
  have : ((zorn_ayaka 𝕜 E E₀ f).choose + Submodule.span 𝕜 {a}) ∉ ayaka E E₀ f := by
    by_contra hc
    have : (zorn_ayaka 𝕜 E E₀ f).choose < (zorn_ayaka 𝕜 E E₀ f).choose + Submodule.span 𝕜 {a} := by
      simpa only [Submodule.add_eq_sup, left_lt_sup, Submodule.span_singleton_le_iff_mem]
    exact (not_le_of_gt this) <| (zorn_ayaka 𝕜 E E₀ f).choose_spec.2 hc (le_of_lt this)
  simp only [ayaka, Set.mem_setOf_eq, Submodule.add_eq_sup, not_exists] at this
  specialize this <| le_sup_of_le_left (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose
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
    have := (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose_spec
    specialize this ⟨b', hx'⟩ ?_
    · unfold MOrth at *
      simp only [AddSubgroupClass.coe_norm] at *
      rw [← hb'1]
      refine eq_of_le_of_ge ?_ ?_
      · apply (le_infDist (by use 0; simp)).2
        intro y hy
        simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] at hy
        rcases hy with ⟨z, hm, hz⟩
        refine le_trans (infDist_le_dist_of_mem (?_ : ⟨y,?_⟩ ∈ _)) (le_of_eq rfl)
        · simpa only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] using ⟨z, hm, by simp only [← hz]⟩
        · refine (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose ?_
          simp only [← hz, LinearMap.mem_range, hm]
      · apply (le_infDist (by use 0; simp)).2
        intro y hy
        simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] at hy
        rcases hy with ⟨z, hm, hz⟩
        refine le_trans (infDist_le_dist_of_mem (?_ : ⟨y, ?_⟩ ∈ _)) (le_of_eq rfl)
        · simpa only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] using ⟨z, hm, by simp only [← hz]⟩
        · refine Submodule.mem_sup_left <| (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose ?_
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
  replace hb1 : MOrth 𝕜 b.val (zorn_ayaka 𝕜 E E₀ f).choose := by
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
    have := (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose_spec
    rcases not_morth_iff_exists_dist_lt_norm.1
      ((fun x => mt (this x)) ⟨g,hg1⟩ (by simp [hgg])) with ⟨e, he1, he2⟩
    simp only [AddSubgroupClass.coe_norm, ← hg2'] at he2
    rw [(by rfl : dist ⟨g, hg1⟩ e = dist g e.val), dist_eq_norm] at he2
    suffices hh : ‖b.val - e.val‖ < ‖b.val‖ by
      contrapose hb1
      apply not_morth_iff_exists_dist_lt_norm.2
      use ⟨e.val, Submodule.mem_sup_left e.prop⟩
      simp only [LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
        Subtype.exists] at he1
      rcases he1 with ⟨q1,q2,q3⟩
      replace q3 : q1 = e.val := by simp [← q3]
      simp only [← q3, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
        Subtype.mk.injEq, Subtype.exists, exists_prop, exists_eq_right, q2,
        AddSubgroupClass.coe_norm, SetLike.val_smul, true_and, gt_iff_lt]
      simpa only [q3, dist_eq_norm, AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub,
        SetLike.val_smul]
    rw [(by abel : b.val - e.val = (b.val - g) + (g - e.val))]
    exact lt_of_le_of_lt (iud.norm_add_le_max _ _) <| max_lt hg2 he2
  have hx : x ∈ (zorn_ayaka 𝕜 E E₀ f).choose :=
    Submodule.smul_mem (zorn_ayaka 𝕜 E E₀ f).choose (-s⁻¹) hx'
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
      refine SetLike.mem_coe.mpr <| Submodule.sub_mem (zorn_ayaka 𝕜 E E₀ f).choose ?_ hx
      simp only [SetLike.coe_mem]
    else
    have := iud.norm_add_eq_max_of_norm_ne_norm hf
    simp only [LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply] at this
    rw [← this]
    apply le_of_eq
    congr
    abel

abbrev SphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: Type u :=
  ↥(zorn_ayaka 𝕜 E (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)).choose

abbrev SphericalCompletionInclusion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E := {
    toFun x := ⟨(sphericallyCompleteExtension 𝕜 E) x, (zorn_ayaka 𝕜 E
      (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)
      ).choose_spec.1.out.choose <| LinearMap.mem_range_self _ _⟩
    map_add' _ _:= rfl
    map_smul' _ _:= rfl
    norm_map' x := by simp
  }

theorem ssss (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
IsImmediate (SphericalCompletionInclusion 𝕜 E) := by
  have := (zorn_ayaka 𝕜 E
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

theorem spherical_completion_minimal (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
∀ M : Submodule 𝕜 (SphericalCompletion 𝕜 E),
LinearMap.range (SphericalCompletionInclusion 𝕜 E) ≤ M →
SphericallyCompleteSpace M → M = ⊤ := by
  intro M hM hsc
  by_contra hc
  --simp [← lt_top_iff_ne_top] at hc
  let Mo := OrthComp 𝕜 M
  have hMo : OrthComp 𝕜 M ≠ ⊥ := by
    by_contra hc'
    have := (isCompl_orthcomp 𝕜 M).sup_eq_top
    simp only [hc', bot_le, sup_of_le_left] at this
    exact hc this
  replace hMo := (Submodule.eq_bot_iff (OrthComp 𝕜 M)).not.1 hMo
  push_neg at hMo
  rcases hMo with ⟨b, hb1, hb2⟩

  sorry

end SphericallyCompleteSpace
