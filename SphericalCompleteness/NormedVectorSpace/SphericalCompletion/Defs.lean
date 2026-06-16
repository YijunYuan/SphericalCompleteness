/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension
import SphericalCompleteness.NormedVectorSpace.Immediate
import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

/-!
# Spherical completion: definitions

Definitions for the spherical completion of a normed vector space.
-/

open Metric

namespace SphericallyCompleteSpace

/--
`imm_ext_in_sph_comp E E₀ f` is the set of `𝕜`-submodules `M ≤ E₀` such that:

* the range of the linear isometry `f : E →ₗᵢ[𝕜] E₀` is contained in `M`, and
* the induced linear isometry `(LinearMap.range f) →ₗᵢ[𝕜] M` is an *immediate* extension
  (in the sense of `IsImmediate`).

This is the collection of candidate intermediate spaces used to build a maximal immediate
extension inside a fixed spherically complete ambient space.
-/
def imm_ext_in_sph_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀)
: Set (Submodule 𝕜 E₀) := {M : Submodule 𝕜 E₀ |
    ∃ hc : f.range ≤ M,
    by
      letI : IsUltrametricDist ↥f.range := instIsUltrametricDistSubmodule (F := f.range)
      letI : IsUltrametricDist ↥M := instIsUltrametricDistSubmodule (F := M)
      let g : f.range →ₗᵢ[𝕜] M := {
        toFun := fun x => ⟨x.1, hc x.2⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro c x; rfl
        norm_map' := by intro x; rfl
      }
      exact @IsImmediate 𝕜 _ f.range _ _ (instIsUltrametricDistSubmodule (F := f.range))
        M _ _ (instIsUltrametricDistSubmodule (F := M)) g
  }

/--
The set of candidate intermediate spaces for immediate extensions is nonempty.
Specifically, the range of `f` itself is always a candidate, with the identity map
serving as an immediate extension.
-/
lemma imm_ext_nonempty {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀)
: (imm_ext_in_sph_comp E E₀ f).Nonempty := by
  use f.range
  refine ⟨le_rfl, ?_⟩
  letI : IsUltrametricDist ↥f.range := instIsUltrametricDistSubmodule (F := f.range)
  let g : f.range →ₗᵢ[𝕜] f.range := {
    toFun := fun x => x
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl
    norm_map' := by intro x; rfl
  }
  change @IsImmediate 𝕜 _ f.range _ _ (instIsUltrametricDistSubmodule (F := f.range))
    f.range _ _ (instIsUltrametricDistSubmodule (F := f.range)) g
  intro a ha
  exact @eq_zero_of_morth_of_mem 𝕜 _ f.range _ _
    (instIsUltrametricDistSubmodule (F := f.range)) a (LinearMap.range g.toLinearMap)
    (LinearMap.mem_range.2 ⟨a, rfl⟩) ha

/-
 Existence of a maximal *immediate* intermediate space inside a fixed spherically complete ambient
 space.

 Concretely, for a linear isometry `f : E →ₗᵢ[𝕜] E₀` into a spherically complete space `E₀`, we
 consider the set `imm_ext_in_sph_comp E E₀ f` of submodules `M ≤ E₀` that contain the range of `f`
 and for which the induced inclusion `LinearMap.range f →ₗᵢ[𝕜] M` is an immediate extension.

 This theorem applies Zorn's lemma (on the poset of such submodules ordered by `≤`) to produce a
 maximal element, which is later used to define the `SphericalCompletion` of `E`.
 -/
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
  · simp only [imm_ext_in_sph_comp, Set.mem_setOf_eq]
    use (by
      intro z hz
      rw [Submodule.mem_iSup]
      intro N hN
      simp only [not_not] at hC
      exact (hN ⟨hC.some, hC.some_mem⟩)  <| (hC1 hC.some_mem).1 hz
      )
    intro x horth
    haveI : Nonempty ↑C := by
      refine Set.Nonempty.coe_sort ?_
      simpa using hC
    have t : (x : E₀) ∈ (↑(@iSup (Submodule 𝕜 E₀) (↑C)
      CompleteLattice.toConditionallyCompleteLattice.toSupSet fun i ↦ ↑i : Set E₀)) := x.prop
    rw [Submodule.coe_iSup_of_directed (fun x => x.val : C → Submodule 𝕜 E₀) hC2.directed] at t
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at t
    rcases t with ⟨N, hN, hxN⟩
    rcases (hC1 hN).out with ⟨hc, himm⟩
    let gSup : f.range →ₗᵢ[𝕜] ↥(⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i) := {
      toFun := fun y => ⟨y.1, (show y.1 ∈ ⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i from by
        rw [Submodule.mem_iSup]
        intro P hP
        simp only [not_not] at hC
        exact (hP ⟨hC.some, hC.some_mem⟩) ((hC1 hC.some_mem).1 y.2))⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c y; rfl
      norm_map' := by intro y; rfl
    }
    let gN : f.range →ₗᵢ[𝕜] N := {
      toFun := fun y => ⟨y.1, hc y.2⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c y; rfl
      norm_map' := by intro y; rfl
    }
    have hrangeSup : ((↑) : ↥(⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i) → E₀) ''
        (LinearMap.range gSup.toLinearMap : Set ↥(⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i)) =
        f.range := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases LinearMap.mem_range.1 hw with ⟨u, rfl⟩
        exact u.2
      · intro hz
        refine ⟨⟨z, ?_⟩, ?_, rfl⟩
        · exact (show z ∈ ⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i from by
          rw [Submodule.mem_iSup]
          intro P hP
          simp only [not_not] at hC
          exact (hP ⟨hC.some, hC.some_mem⟩) ((hC1 hC.some_mem).1 hz))
        · exact LinearMap.mem_range.2 ⟨⟨z, hz⟩, rfl⟩
    have hrangeN : ((↑) : N → E₀) '' (LinearMap.range gN.toLinearMap : Set N) = f.range := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases LinearMap.mem_range.1 hw with ⟨u, rfl⟩
        exact u.2
      · intro hz
        refine ⟨⟨z, hc hz⟩, LinearMap.mem_range.2 ⟨⟨z, hz⟩, rfl⟩, rfl⟩
    have horthE0 : Metric.infDist (x : E₀) f.range = ‖(x : E₀)‖ := by
      unfold MOrth at horth
      change
        Metric.infDist x
            (LinearMap.range gSup.toLinearMap :
              Set ↥(⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i)) =
          ‖x‖ at horth
      rw [(Metric.infDist_image isometry_subtype_coe
          (x := x)
          (t :=
            (LinearMap.range gSup.toLinearMap :
              Set ↥(⨆ i, (fun x => x.val : C → Submodule 𝕜 E₀) i)))).symm]
        at horth
      simpa [hrangeSup] using horth
    apply Subtype.ext
    letI : IsUltrametricDist ↥N := instIsUltrametricDistSubmodule (F := N)
    have horthN : @MOrth 𝕜 _ N _ _ (instIsUltrametricDistSubmodule (F := N))
      (⟨(x : E₀), hxN⟩ : N) (LinearMap.range gN.toLinearMap) := by
      unfold MOrth
      change Metric.infDist (⟨(x : E₀), hxN⟩ : N) (LinearMap.range gN.toLinearMap : Set N) =
        ‖(⟨(x : E₀), hxN⟩ : N)‖
      rw [(Metric.infDist_image isometry_subtype_coe
          (x := (⟨(x : E₀), hxN⟩ : N)) (t := (LinearMap.range gN.toLinearMap : Set N))).symm]
      change Metric.infDist ((⟨(x : E₀), hxN⟩ : N) : E₀)
          (((↑) : N → E₀) '' (LinearMap.range gN.toLinearMap : Set N)) = ‖(⟨(x : E₀), hxN⟩ : N)‖
      rw [hrangeN]
      simpa using horthE0
    simpa using congrArg Subtype.val (himm ⟨x, hxN⟩ horthN)
  · intro M hM z hz
    rw [Submodule.mem_iSup]
    intro N hN
    exact (hN ⟨M, hM⟩) hz

/--
`SphericalCompletion 𝕜 E` is a (non-canonical) choice of a maximal *immediate* extension of `E`
inside a fixed spherically complete ambient space.

More precisely, we first embed `E` by a linear isometry
`sphericallyCompleteExtension 𝕜 E : E →ₗᵢ[𝕜] (lp (fun _ ↦ E) ⊤ ⧸ c₀ 𝕜 (fun _ ↦ E))` into a
spherically complete space. We then apply `exists_max_imm_ext_in_sph_comp` to obtain a submodule
of the ambient space that contains the range of this embedding and is maximal among those for
which the induced inclusion is an immediate extension.

The underlying type of this chosen maximal submodule is defined to be `SphericalCompletion 𝕜 E`.
-/
noncomputable abbrev SphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] : Type u :=
  ↥(exists_max_imm_ext_in_sph_comp 𝕜 E
      _ (sphericallyCompleteExtension 𝕜 E)).choose

noncomputable instance instNormedAddCommGroupSphericalCompletionAbbrev
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
NormedAddCommGroup (SphericalCompletion 𝕜 E) :=
  show NormedAddCommGroup
      ↥(exists_max_imm_ext_in_sph_comp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose
    from inferInstance

noncomputable instance instNormedSpaceSphericalCompletionAbbrev
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
NormedSpace 𝕜 (SphericalCompletion 𝕜 E) :=
  show NormedSpace 𝕜
      ↥(exists_max_imm_ext_in_sph_comp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose
    from inferInstance

noncomputable instance instIsUltrametricDistSphericalCompletionAbbrev
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
IsUltrametricDist (SphericalCompletion 𝕜 E) :=
  show IsUltrametricDist
      ↥(exists_max_imm_ext_in_sph_comp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose
    from inferInstance

noncomputable instance instNormedAddCommGroupSphericalCompletion
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
NormedAddCommGroup (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := inferInstance

noncomputable instance instNormedSpaceSphericalCompletion
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
NormedSpace 𝕜 (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := inferInstance

instance instIsUltrametricDistSphericalCompletion
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
[SphericallyCompleteSpace E₀]
(f : E →ₗᵢ[𝕜] E₀) :
IsUltrametricDist (↥(exists_max_imm_ext_in_sph_comp 𝕜 E E₀ f).choose) := inferInstance

/--
`SphericalCompletionEmbedding 𝕜 E` is the canonical linear isometric embedding of `E` into the
chosen spherical completion `SphericalCompletion 𝕜 E`.

It is obtained by composing the fixed linear isometry
`sphericallyCompleteExtension 𝕜 E : E →ₗᵢ[𝕜] E₀` into a spherically complete ambient space `E₀` with
the inclusion of `LinearMap.range` into the maximal immediate intermediate submodule selected in the
definition of `SphericalCompletion`.
-/
noncomputable def SphericalCompletionEmbedding (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
: E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E := {
    toFun x := ⟨(sphericallyCompleteExtension 𝕜 E) x, (exists_max_imm_ext_in_sph_comp 𝕜 E _
    (sphericallyCompleteExtension 𝕜 E)
      ).choose_spec.1.out.choose <| LinearMap.mem_range_self _ _⟩
    map_add' _ _:= rfl
    map_smul' _ _:= rfl
    norm_map' x := by
      change ‖(⟨(sphericallyCompleteExtension 𝕜 E) x, _⟩ :
        ↥(exists_max_imm_ext_in_sph_comp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose)‖ = ‖x‖
      simp
  }

end SphericallyCompleteSpace
