import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension
import SphericalCompleteness.NormedVectorSpace.Immediate
import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

open Metric

namespace SphericallyCompleteSpace

def imm_ext_in_sph_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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

lemma imm_ext_nonempty {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀)
: (imm_ext_in_sph_comp E E₀ f).Nonempty := by
  use LinearMap.range f
  simp [imm_ext_in_sph_comp, IsImmediate, MOrth]
  intro a x hc hh
  suffices hh : ‖a‖ = 0 by
    exact norm_eq_zero.mp hh
  rw [← hh]
  refine Metric.infDist_zero_of_mem ?_
  simp only [SetLike.mem_coe, LinearMap.mem_range, LinearIsometry.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, exists_eq]

theorem exists_max_imm_ext_in_sph_comp (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) : ∃ m, Maximal (fun x ↦ x ∈ imm_ext_in_sph_comp E E₀ f) m := by
  apply zorn_le₀
  intro C hC1 hC2
  if hC : ¬ C.Nonempty then
    refine ⟨(imm_ext_nonempty E E₀ f).some,
      Set.Nonempty.some_mem (imm_ext_nonempty E E₀ f), ?_⟩
    intro c hc
    contrapose hC
    use c
  else
  use ⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i
  constructor
  · simp [imm_ext_in_sph_comp]
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

abbrev SphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: Type u :=
  ↥(exists_max_imm_ext_in_sph_comp 𝕜 E
    (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)).choose

abbrev SphericalCompletionEmbedding (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E := {
    toFun x := ⟨(sphericallyCompleteExtension 𝕜 E) x, (exists_max_imm_ext_in_sph_comp 𝕜 E
      (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) (sphericallyCompleteExtension 𝕜 E)
      ).choose_spec.1.out.choose <| LinearMap.mem_range_self _ _⟩
    map_add' _ _:= rfl
    map_smul' _ _:= rfl
    norm_map' x := by simp
  }

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
NormedAddCommGroup (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := inferInstance

noncomputable instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
NormedSpace 𝕜 (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := inferInstance

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
IsUltrametricDist (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := inferInstance

end SphericallyCompleteSpace
