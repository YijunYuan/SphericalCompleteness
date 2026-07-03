/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.Immediate
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.SphericallyCompleteExtension

/-!
# Spherical completion: definitions

Definitions for the spherical completion of a normed vector space.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/-- The isometric inclusion of one submodule into a larger one (identity on underlying vectors). -/
def inclusionᵢ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₀ : Type*}
    [SeminormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] {p q : Submodule 𝕜 E₀} (h : p ≤ q) :
    p →ₗᵢ[𝕜] q where
  toFun x := ⟨x.1, h x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The image in the ambient space of the range of `inclusionᵢ h` is `p`. -/
private lemma range_inclusionᵢ_image {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₀ : Type*}
    [SeminormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] {p q : Submodule 𝕜 E₀} (h : p ≤ q) :
    ((↑) : q → E₀) '' (LinearMap.range (inclusionᵢ h).toLinearMap : Set q) = (p : Set E₀) := by
  ext z
  simp only [Set.mem_image, SetLike.mem_coe, LinearMap.mem_range]
  refine ⟨?_, fun hz ↦ ⟨⟨z, h hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩⟩
  rintro ⟨w, ⟨u, rfl⟩, rfl⟩
  exact u.2

/-- Metric orthogonality of `x : q` to the range of the inclusion `p ≤ q`, computed inside `q`,
is the same as metric orthogonality of `(x : E₀)` to `p` in the ambient space. This is the key
transport principle for immediate extensions built from submodule inclusions. -/
lemma morth_range_inclusionᵢ_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₀ : Type*}
    [SeminormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    {p q : Submodule 𝕜 E₀} (h : p ≤ q) (x : q) :
    (MOrth 𝕜 x (LinearMap.range (inclusionᵢ h).toLinearMap)) ↔
      Metric.infDist (x : E₀) p = ‖(x : E₀)‖ := by
  rw [MOrth, ← range_inclusionᵢ_image h,
    Metric.infDist_image (Φ := ((↑) : q → E₀)) isometry_subtype_coe (x := x)]
  exact Iff.rfl

/--
`immExtInSphComp E E₀ f` is the set of `𝕜`-submodules `M ≤ E₀` such that:

* the range of the linear isometry `f : E →ₗᵢ[𝕜] E₀` is contained in `M`, and
* the induced linear isometry `(LinearMap.range f) →ₗᵢ[𝕜] M` is an *immediate* extension
  (in the sense of `IsImmediate`).

This is the collection of candidate intermediate spaces used to build a maximal immediate
extension inside a fixed spherically complete ambient space.
-/
def immExtInSphComp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀)
    : Set (Submodule 𝕜 E₀) := {M : Submodule 𝕜 E₀ |
    ∃ hc : f.range ≤ M, IsImmediate (inclusionᵢ hc) }

/-- Clean membership criterion for `immExtInSphComp`, expressed entirely in the ambient
space `E₀`: `M` contains `f.range`, and any `v ∈ M` metrically orthogonal to `f.range`
(in `E₀`) is `0`. -/
lemma mem_immExtInSphComp_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀] {f : E →ₗᵢ[𝕜] E₀} {M : Submodule 𝕜 E₀} :
    M ∈ immExtInSphComp E E₀ f ↔
      ∃ _ : f.range ≤ M,
        ∀ v : M, Metric.infDist (v : E₀) f.range = ‖(v : E₀)‖ → v = 0 := by
  simp only [immExtInSphComp, Set.mem_setOf_eq, IsImmediate]
  refine exists_congr fun hc ↦ forall_congr' fun v ↦ ?_
  rw [morth_range_inclusionᵢ_iff]


/--
The set of candidate intermediate spaces for immediate extensions is nonempty.
Specifically, the range of `f` itself is always a candidate, with the identity map
serving as an immediate extension.
-/
lemma immExtInSphComp_nonempty {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀)
    : (immExtInSphComp E E₀ f).Nonempty := by
  refine ⟨f.range, mem_immExtInSphComp_iff.2 ⟨le_rfl, fun v hv ↦ ?_⟩⟩
  rw [Metric.infDist_zero_of_mem v.2] at hv
  exact Submodule.coe_eq_zero.mp (norm_eq_zero.mp hv.symm)

/-
 Existence of a maximal *immediate* intermediate space inside a fixed spherically complete ambient
 space.

 Concretely, for a linear isometry `f : E →ₗᵢ[𝕜] E₀` into a spherically complete space `E₀`, we
 consider the set `immExtInSphComp E E₀ f` of submodules `M ≤ E₀` that contain the range of `f`
 and for which the induced inclusion `LinearMap.range f →ₗᵢ[𝕜] M` is an immediate extension.

 This theorem applies Zorn's lemma (on the poset of such submodules ordered by `≤`) to produce a
 maximal element, which is later used to define the `SphericalCompletion` of `E`.
 -/
theorem exists_max_immExtInSphComp (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) : ∃ m, Maximal (fun x ↦ x ∈ immExtInSphComp E E₀ f) m := by
  apply zorn_le₀
  intro C hC1 hC2
  if hC : ¬ C.Nonempty then
    refine ⟨(immExtInSphComp_nonempty E E₀ f).some,
      Set.Nonempty.some_mem (immExtInSphComp_nonempty E E₀ f), ?_⟩
    intro c hc
    contrapose hC
    use c
  else
  use ⨆ i, (fun x ↦ x.val : C → Submodule 𝕜 E₀) i
  simp only [not_not] at hC
  have hf_le : f.range ≤ ⨆ i, (fun x ↦ x.val : C → Submodule 𝕜 E₀) i := fun z hz ↦
    Submodule.mem_iSup _ |>.2 fun N hN ↦ (hN ⟨hC.some, hC.some_mem⟩) ((hC1 hC.some_mem).1 hz)
  refine ⟨mem_immExtInSphComp_iff.2 ⟨hf_le, fun x horth ↦ ?_⟩, fun M hM z hz ↦
    Submodule.mem_iSup _ |>.2 fun N hN ↦ (hN ⟨M, hM⟩) hz⟩
  haveI : Nonempty ↑C := hC.to_subtype
  have hxmem : (x : E₀) ∈ ⨆ i, (fun x ↦ x.val : C → Submodule 𝕜 E₀) i := x.2
  rw [Submodule.mem_iSup_of_directed _ hC2.directed] at hxmem
  rcases hxmem with ⟨N, hxN⟩
  obtain ⟨hc, himm⟩ := mem_immExtInSphComp_iff.1 (hC1 N.2)
  apply Subtype.ext
  have := himm ⟨(x : E₀), hxN⟩ (by simpa using horth)
  simpa using congrArg Subtype.val this

/--
`SphericalCompletion 𝕜 E` is a (non-canonical) choice of a maximal *immediate* extension of `E`
inside a fixed spherically complete ambient space.

More precisely, we first embed `E` by a linear isometry
`sphericallyCompleteExtension 𝕜 E : E →ₗᵢ[𝕜] (lp (fun _ ↦ E) ⊤ ⧸ c₀ 𝕜 (fun _ ↦ E))` into a
spherically complete space. We then apply `exists_max_immExtInSphComp` to obtain a submodule
of the ambient space that contains the range of this embedding and is maximal among those for
which the induced inclusion is an immediate extension.

The underlying type of this chosen maximal submodule is defined to be `SphericalCompletion 𝕜 E`.
-/
noncomputable abbrev SphericalCompletion (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] : Type u :=
  ↥(exists_max_immExtInSphComp 𝕜 E
      _ (sphericallyCompleteExtension 𝕜 E)).choose

noncomputable instance instNormedAddCommGroupSphericalCompletionAbbrev
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    NormedAddCommGroup (SphericalCompletion 𝕜 E) :=
  show NormedAddCommGroup
      ↥(exists_max_immExtInSphComp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose
    from inferInstance

noncomputable instance instNormedSpaceSphericalCompletionAbbrev
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    NormedSpace 𝕜 (SphericalCompletion 𝕜 E) :=
  show NormedSpace 𝕜
      ↥(exists_max_immExtInSphComp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose
    from inferInstance

noncomputable instance instIsUltrametricDistSphericalCompletionAbbrev
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] :
    IsUltrametricDist (SphericalCompletion 𝕜 E) :=
  show IsUltrametricDist
      ↥(exists_max_immExtInSphComp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose
    from inferInstance

noncomputable instance instNormedAddCommGroupSphericalCompletion
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    NormedAddCommGroup (↥(exists_max_immExtInSphComp 𝕜 E E₀ f).choose) := inferInstance

noncomputable instance instNormedSpaceSphericalCompletion
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    NormedSpace 𝕜 (↥(exists_max_immExtInSphComp 𝕜 E E₀ f).choose) := inferInstance

instance instIsUltrametricDistSphericalCompletion
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    IsUltrametricDist (↥(exists_max_immExtInSphComp 𝕜 E E₀ f).choose) := inferInstance

/--
`sphericalCompletionEmbedding 𝕜 E` is the canonical linear isometric embedding of `E` into the
chosen spherical completion `SphericalCompletion 𝕜 E`.

It is obtained by composing the fixed linear isometry
`sphericallyCompleteExtension 𝕜 E : E →ₗᵢ[𝕜] E₀` into a spherically complete ambient space `E₀` with
the inclusion of `LinearMap.range` into the maximal immediate intermediate submodule selected in the
definition of `SphericalCompletion`.
-/
noncomputable def sphericalCompletionEmbedding (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    : E →ₗᵢ[𝕜] SphericalCompletion 𝕜 E := {
    toFun x := ⟨(sphericallyCompleteExtension 𝕜 E) x, (exists_max_immExtInSphComp 𝕜 E _
    (sphericallyCompleteExtension 𝕜 E)
      ).choose_spec.1.out.choose <| LinearMap.mem_range_self _ _⟩
    map_add' _ _:= rfl
    map_smul' _ _:= rfl
    norm_map' x := by
      change ‖(⟨(sphericallyCompleteExtension 𝕜 E) x, _⟩ :
        ↥(exists_max_immExtInSphComp 𝕜 E _ (sphericallyCompleteExtension 𝕜 E)).choose)‖ = ‖x‖
      simp
  }

end SphericallyCompleteSpace
