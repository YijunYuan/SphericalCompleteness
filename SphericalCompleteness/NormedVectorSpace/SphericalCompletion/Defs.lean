import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension
import SphericalCompleteness.NormedVectorSpace.Immediate
import SphericalCompleteness.NormedVectorSpace.Existance

open Metric

namespace SphericallyCompleteSpace

def IsSphericalComletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
(F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] : Prop :=
SphericallyCompleteSpace F ∧
∃ (f : E →ₗᵢ[𝕜] F), ∀ M : Submodule 𝕜 F, LinearMap.range f ≤ M → SphericallyCompleteSpace M → M = ⊤

abbrev LinearIsometry.submodule_subset_submodule (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{F₁ F₂ : Submodule 𝕜 E} (h : F₁ ≤ F₂) :
↥F₁ →ₗᵢ[𝕜] ↥F₂ where
  toFun x := ⟨x.1, h x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

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
    intro m n hmn
    simp
    specialize hanti hmn
    simp at hanti
    intro z hz
    simp only [mem_closedBall] at *
    refine le_trans (iud.dist_triangle_max z (c n).val (c m).val) ?_
    apply max_le
    · exact le_trans hz <| hsr.antitone hmn
    · rw [← mem_closedBall]
      exact hanti <| mem_closedBall_self NNReal.zero_le_coe
      )
  simp only [Set.nonempty_iInter, mem_closedBall] at this
  rcases this with ⟨a, ha⟩
  if haa : a ∈ (zorn_ayaka 𝕜 E E₀ f).choose then
    contrapose hemp
    refine Set.nonempty_iff_ne_empty.mp ?_
    use ⟨a, haa⟩
    simp only [Set.mem_iInter, mem_closedBall]
    intro i
    specialize ha i
    simpa only [dist_le_coe]
  else
  have : ((zorn_ayaka 𝕜 E E₀ f).choose + Submodule.span 𝕜 {a}) ∉ ayaka E E₀ f := by
    by_contra hc
    have : (zorn_ayaka 𝕜 E E₀ f).choose < (zorn_ayaka 𝕜 E E₀ f).choose + Submodule.span 𝕜 {a} := by
      simpa only [Submodule.add_eq_sup, left_lt_sup, Submodule.span_singleton_le_iff_mem]
    exact (not_le_of_gt this) <| (zorn_ayaka 𝕜 E E₀ f).choose_spec.2 hc (le_of_lt this)
  simp [ayaka] at this
  specialize this <| le_sup_of_le_left (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose
  unfold IsImmediate at this
  push_neg at this
  rcases this with ⟨b', hb'1, hb'2⟩
  rcases Submodule.mem_sup.1 b'.prop with ⟨x', hx', v', hv', hx'v'⟩
  rcases Submodule.mem_span_singleton.1 hv' with ⟨s, hs⟩
  rw [← hs] at hx'v'
  have hhs : s ≠ 0 := by
    by_contra hc
    simp [hc] at hx'v'
    subst hx'v'
    have := (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose_spec
    unfold IsImmediate at this
    specialize this ⟨b', hx'⟩ ?_
    · unfold MOrth at *
      simp
      simp at hb'1
      rw [← hb'1]
      refine eq_of_le_of_ge ?_ ?_
      · apply (le_infDist (by use 0; simp)).2
        intro y hy
        simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] at hy
        rcases hy with ⟨z, hm, hz⟩
        refine le_trans (infDist_le_dist_of_mem (?_ : ⟨y,?_⟩ ∈ _)) (le_of_eq rfl)
        · simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists]
          use z, hm
          simp only [← hz]
        · refine (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose ?_
          simp only [← hz, LinearMap.mem_range, hm]
      · apply (le_infDist (by use 0; simp)).2
        intro y hy
        simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists] at hy
        rcases hy with ⟨z, hm, hz⟩
        refine le_trans (infDist_le_dist_of_mem (?_ : ⟨y,?_⟩ ∈ _)) (le_of_eq rfl)
        · simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
          AddHom.coe_mk, Subtype.exists]
          use z, hm
          simp only [← hz]
        · apply Submodule.mem_sup_left
          refine (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose ?_
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
    unfold MOrth
    by_contra hc
    simp at hc
    replace hc := lt_of_le_of_ne ?_ hc
    · rcases (infDist_lt_iff (by use 0; simp)).1 hc with ⟨g, hg1, hg2⟩
      rw [dist_eq_norm] at hg2
      replace hg2 := norm_eq_of_norm_sub_lt_left hg2
      have hgg : g ≠ 0 := by
        by_contra hc
        simp [hc] at hg2
        simp [hg2] at *
        contrapose hc
        simpa using infDist_nonneg
      -- need not_morth_iff_exists_dist_lt
      have := (zorn_ayaka 𝕜 E E₀ f).choose_spec.1.out.choose_spec
      unfold IsImmediate at this
      replace this := fun x => mt (this x)
      specialize this ⟨g,hg1⟩ (by simp [hgg])

      sorry

    · nth_rw 2 [← sub_zero b.val]
      rw [← dist_eq_norm]
      apply infDist_le_dist_of_mem
      simp only [SetLike.mem_coe, zero_mem]
  have hx : x ∈ (zorn_ayaka 𝕜 E E₀ f).choose :=
    Submodule.smul_mem (zorn_ayaka 𝕜 E E₀ f).choose (-s⁻¹) hx'
  suffices h : ∀ i : ℕ, ⟨x,hx⟩ ∈ closedBall (c i) ↑(r i) by
    contrapose hemp
    refine Set.nonempty_iff_ne_empty.mp ?_
    use ⟨x, hx⟩
    simpa only [Set.mem_iInter]
  intro i
  simp only [mem_closedBall, dist_eq_norm]
  refine le_trans (by simp : ‖⟨x, hx⟩ - c i‖ ≤ max ‖⟨x, hx⟩ - c i‖ ‖b‖) ?_
  refine le_trans ?_ (ha i)
  have : a - (c i).val = b - ((c i).val - x) := by
    simp only [this, sub_sub_sub_cancel_right]
  rw [dist_eq_norm, this]
  conv => arg 1; simp only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub]
  refine le_of_eq <| Eq.symm ?_
  refine eq_of_le_of_ge ?_ ?_
  · rw [sub_sub_eq_add_sub, ← add_sub, max_comm]
    exact iud.norm_add_le_max _ _
  · if hf : ‖x - ↑(c i)‖ = ‖↑b‖ then
      simp only [hf, AddSubgroupClass.coe_norm, max_self]
      rw [← dist_eq_norm]
      unfold MOrth at hb1
      unfold b
      simp only [SetLike.val_smul]
      simp only [AddSubgroupClass.coe_norm, SetLike.val_smul, b] at hb1
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
: E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E := by
  have := (zorn_ayaka 𝕜 E (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)).choose_spec.1.out.choose


  sorry
end SphericallyCompleteSpace
