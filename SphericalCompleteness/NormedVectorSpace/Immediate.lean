/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.HahnBanach

/-!
# Immediate extensions

This file develops the theory of *immediate extensions* of ultrametric normed vector spaces.

A linear isometry `f : E →ₗᵢ[𝕜] F` is *immediate* (`IsImmediate f`) when no nonzero vector of `F`
is metrically orthogonal to the range of `f`; equivalently, every `v : F` can be approximated by
vectors of `range f` strictly better than by `0`. Intuitively, `F` adds no genuinely new
"directions" beyond those already present in `E`. A space is *maximally complete*
(`MaximallyComplete 𝕜 E`) when it admits no proper immediate extension.

The central results are an *extension property* — an isometry out of `E` into a spherically
complete space extends along any immediate embedding of `E` — and a **Zorn's lemma** construction:
inside a fixed ambient space `E₀`, we collect the intermediate subspaces through which `f` factors
as an immediate extension into the set `immediateExtensionSubmodules` and extract a maximal such
subspace. When the ambient space `E₀` is *spherically complete*, this maximal subspace is again
spherically complete, and the induced embedding of `E` into it
(`maximalImmediateExtensionEmbedding`) is the space underlying the spherical completion of `E`.

## Main definitions

* `SphericallyCompleteSpace.IsImmediate`: the predicate that a linear isometry is an immediate
  embedding.
* `SphericallyCompleteSpace.MaximallyComplete`: the predicate that a space admits no proper
  immediate extension.
* `SphericallyCompleteSpace.IsImmediate.immediateExtensionSubmodules`: the set of intermediate
  subspaces of a fixed ambient space through which a linear isometry factors as an immediate
  extension.
* `SphericallyCompleteSpace.IsImmediate.maximalImmediateExtensionEmbedding`: the embedding of `E`
  into a maximal immediate-extension subspace of a spherically complete ambient space.

## Main statements

* `SphericallyCompleteSpace.IsImmediate.exists_linearIsometry_comp_eq`: any linear isometry from
  `E` into a spherically complete space extends along an immediate embedding of `E`.
* `SphericallyCompleteSpace.IsImmediate.exists_maximal_immediateExtensionSubmodule`: inside a
  fixed ambient space, **Zorn's lemma** produces a maximal immediate-extension subspace containing
  the range of `f`.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/--
`IsImmediate f` means that the linear isometry `f : E →ₗᵢ[𝕜] F` has *immediate* image in `F`
(in the ultrametric sense): the only vector in `F` that is metrically orthogonal to the range
of `f` is `0`.

More precisely, it asserts:
`∀ v : F, (v ⟂ₘ LinearMap.range f) → v = 0`,
where `v ⟂ₘ S` is the predicate expressing metric orthogonality of `v` to the subspace `S`.
This rules out nontrivial orthogonal complements to `LinearMap.range f`.
-/
def IsImmediate {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type v} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    (f : E →ₗᵢ[𝕜] F) : Prop :=
∀ v : F, (v ⟂ₘ LinearMap.range f.toLinearMap) → v = 0

def IsImmediateExtension {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (D : Submodule 𝕜 E) : Prop :=
    ∀ v : E, (v ⟂ₘ D) → v = 0

/--
`MaximallyComplete 𝕜 E` expresses a maximal completeness (a spherical-completeness–style)
property of the ultrametric normed `𝕜`-vector space `E`.

It requires that for every ultrametric normed `𝕜`-vector space `F` and every linear isometry
`f : E →ₗᵢ[𝕜] F`, if `f` is *immediate* (in the sense of `IsImmediate f`),
then `f` is surjective.

In other words, `E` admits no proper immediate extensions: any immediate
linear isometry out of `E` must hit all of its codomain.
-/
def MaximallyComplete (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E] : Prop :=
∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
(f : E →ₗᵢ[𝕜] F), IsImmediate f → Function.Surjective f

namespace IsImmediate

/--
`weakInv f` is the (weak, partial) inverse of a linear isometry
`f : E →ₗᵢ[𝕜] F`.

Since `f` is an isometry it is injective, hence a linear isometric isomorphism onto its range
`↥f.range` (given by `f.equivRange`). Its inverse is the linear isometry
`weakInv f : ↥f.range →ₗᵢ[𝕜] E`, defined on the range of `f` rather than on all of `F` — whence
"weak". It satisfies `weakInv f ⟨f x, _⟩ = x` for every `x : E`, i.e. it undoes `f` on its image.
-/
private noncomputable def weakInv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) : ↥f.range →ₗᵢ[𝕜] E := f.equivRange.symm.toLinearIsometry

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [IsUltrametricDist H]
    [SphericallyCompleteSpace H]

omit [SphericallyCompleteSpace H] in
/--
Key norm-preservation step behind `IsImmediate.exists_linearIsometry_comp_eq`.

Suppose `f : E →ₗᵢ[𝕜] F` is immediate (`IsImmediate f`), `g : E →ₗᵢ[𝕜] H` is a linear isometry into
a spherically complete ultrametric normed space `H`, and `h : F →L[𝕜] H` is a continuous linear map
that agrees with `g ∘ weakInv f` on the range of `f` (hypothesis `hf1`) and whose operator norm
matches that composite (hypothesis `hf2`). Then `h` is norm-preserving: `‖h v‖ = ‖v‖` for every
`v : F`.

The upper bound `‖h v‖ ≤ ‖v‖` follows from `‖h‖ ≤ 1`, while the lower bound uses immediacy of `f`:
any `v` can be approximated within distance `< ‖v‖` by a vector in the range of `f`, on which `h`
already preserves norms. This is what promotes the continuous linear map `h` to a linear isometry.
-/
private lemma norm_map (f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f)
    (g : E →ₗᵢ[𝕜] H) (h : F →L[𝕜] H)
    (hf2 : ‖h‖ = ‖g.toContinuousLinearMap.comp (weakInv f).toContinuousLinearMap‖)
    (hf1 : ∀ (v : F) (x : E) (h_1 : f x = v), h v = g ((weakInv f) ⟨v, Exists.intro
    x h_1⟩))
    (v : F) : ‖(↑h : F →ₗ[𝕜] H) v‖ = ‖v‖ := by
  have hh : ‖h‖ ≤ 1 := by
    rw [hf2]; exact (g.comp (weakInv f)).norm_toContinuousLinearMap_le
  refine eq_of_le_of_ge ?_ ?_
  · simpa only [one_mul, ContinuousLinearMap.coe_coe] using h.le_of_opNorm_le hh v
  · if hv : v = 0 then
      simp [hv]
    else
    replace hf := hf v
    simp only [IsMOrtho, hv, imp_false] at hf
    replace hf : infDist v ↑(LinearMap.range f.toLinearMap) < ‖v‖ := by
      refine lt_of_le_of_ne ?_ hf
      rw [← dist_zero_right v]
      exact infDist_le_dist_of_mem <| zero_mem (LinearMap.range f.toLinearMap)
    rcases (infDist_lt_iff <| Submodule.nonempty (LinearMap.range f.toLinearMap)).1 hf with ⟨x, hx⟩
    rw [dist_eq_norm] at hx
    have : ‖h x - h v‖ < ‖v‖ := by
      rw [← map_sub]
      refine (ContinuousLinearMap.le_opNorm h (x - v)).trans_lt ?_
      refine (mul_le_of_le_one_left (norm_nonneg _) hh).trans_lt ?_
      rw [norm_sub_rev]; exact hx.2
    have hx' := IsUltrametricDist.norm_eq_of_norm_sub_lt_left hx.2
    have t : ‖h x‖ = ‖x‖ := by
      obtain ⟨z, hz⟩ := hx.1; rw [hf1 x z hz]; simp
    rw [hx', ← t] at this
    apply IsUltrametricDist.norm_eq_of_norm_sub_lt_left at this
    simp only [hx', ContinuousLinearMap.coe_coe, ← this, t, le_refl]

/--
Given an immediate linear isometry `f : E →ₗᵢ[𝕜] F` and a linear isometry `g : E →ₗᵢ[𝕜] H` into a
spherically complete ultrametric normed space `H`, there exists a linear isometry
`h : F →ₗᵢ[𝕜] H` such that `h.comp f = g`.

This is an extension property: along an immediate embedding `f`, any isometric map out of `E`
into a spherically complete target extends to an isometric map out of `F`. The proof extends the
composite `g ∘ weakInv f` (defined on the range of `f`) to all of `F` by the non-Archimedean
**Hahn-Banach** theorem, then uses immediacy of `f` to promote the resulting continuous linear map
to a norm-preserving one (`IsImmediate.norm_map`): every `v : F` is approximated arbitrarily well
by vectors of `range f`, on which the extension already preserves norms.

The conclusion is stated using `LinearIsometry.comp` with explicit type ascriptions on its
arguments to avoid elaboration issues.
-/
theorem exists_linearIsometry_comp_eq
    (f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f)
    (g : E →ₗᵢ[𝕜] H) :
    ∃ (h : F →ₗᵢ[𝕜] H), LinearIsometry.comp (h : F →ₗᵢ[𝕜] H) (f : E →ₗᵢ[𝕜] F) = g := by
  rcases hahn_banach (D := LinearMap.range f.toLinearMap) (F := H)
    (LinearIsometry.comp g (weakInv f)).toContinuousLinearMap with ⟨h, hf1, hf2⟩
  simp only [LinearMap.mem_range, forall_exists_index] at hf1
  let h : F →ₗᵢ[𝕜] H := {
    toFun := h.toFun,
    map_add' := h.map_add',
    map_smul' := h.map_smul',
    norm_map' := fun v ↦ IsImmediate.norm_map f hf g h hf2 hf1 v
  }
  use h
  ext z
  simp only [LinearIsometry.coe_comp, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    Function.comp_apply, h]
  rw [hf1 (f z) z rfl]
  exact congrArg g (f.equivRange.symm_apply_apply z)

end

/-- Metric orthogonality of `x : q` to the range of the inclusion `p ≤ q`, computed inside `q`,
is the same as metric orthogonality of `(x : E₀)` to `p` in the ambient space. This is the key
transport principle for immediate extensions built from submodule inclusions. -/
lemma isMOrtho_range_inclusion_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₀ : Type*}
    [SeminormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    {p q : Submodule 𝕜 E₀} (h : p ≤ q) (x : q) :
    (IsMOrtho x (LinearMap.range (Submodule.inclusion h))) ↔
      Metric.infDist (x : E₀) p = ‖(x : E₀)‖ := by
  rw [IsMOrtho, show (p : Set E₀) =
      ((↑) : q → E₀) '' (LinearMap.range (Submodule.inclusion h)) from by
    rw [← Submodule.coe_subtype, ← Submodule.map_coe, Submodule.range_inclusion,
      Submodule.map_comap_subtype, inf_of_le_right h],
    Metric.infDist_image (Φ := ((↑) : q → E₀)) isometry_subtype_coe (x := x)]
  exact Iff.rfl

/--
`immediateExtensionSubmodules E E₀ f` is the set of `𝕜`-submodules `M ≤ E₀`
such that:

* the range of the linear isometry `f : E →ₗᵢ[𝕜] E₀` is contained in `M`, and
* the inclusion `Submodule.inclusion : (LinearMap.range f) →ₗ[𝕜] M` is an *immediate* extension,
  i.e. every `v : M` metrically orthogonal to its range is `0` (as in `IsImmediate`).

This is the collection of candidate intermediate spaces used to build a maximal immediate
extension inside a fixed ambient space `E₀`; taking `E₀` spherically complete yields the spherical
completion of `E`.
-/
def immediateExtensionSubmodules {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    Set (Submodule 𝕜 E₀) := {M : Submodule 𝕜 E₀ | ∃ hc : f.range ≤ M,
      ∀ v : M, (v ⟂ₘ LinearMap.range (Submodule.inclusion hc)) → v = 0 }

/-- Membership criterion for `immediateExtensionSubmodules`, expressed entirely in the ambient
space `E₀`: `M` belongs to the set iff it contains `f.range` and every `v ∈ M` that is metrically
orthogonal to `f.range` (measured in `E₀`) is `0`. This transports the immediacy condition — stated
inside `M` via `Submodule.inclusion` — down to the ambient norm, which is what makes the Zorn
argument in `exists_maximal_immediateExtensionSubmodule` manageable. -/
lemma mem_immediateExtensionSubmodules_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    {f : E →ₗᵢ[𝕜] E₀} {M : Submodule 𝕜 E₀} :
    M ∈ immediateExtensionSubmodules E E₀ f ↔
      ∃ _ : f.range ≤ M,
        ∀ v : M, Metric.infDist (v : E₀) f.range = ‖(v : E₀)‖ → v = 0 := by
  simp only [immediateExtensionSubmodules, Set.mem_setOf_eq]
  refine exists_congr fun hc ↦ forall_congr' fun v ↦ ?_
  rw [isMOrtho_range_inclusion_iff]

/--
The set of candidate intermediate spaces for immediate extensions is nonempty.
Specifically, the range of `f` itself is always a candidate, with the identity map
serving as an immediate extension.
-/
lemma immediateExtensionSubmodules_nonempty
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    (f : E →ₗᵢ[𝕜] E₀)
    : (immediateExtensionSubmodules E E₀ f).Nonempty := by
  refine ⟨f.range, mem_immediateExtensionSubmodules_iff.2
    ⟨le_rfl, fun v hv ↦ ?_⟩⟩
  rw [Metric.infDist_zero_of_mem v.2] at hv
  exact Submodule.coe_eq_zero.mp (norm_eq_zero.mp hv.symm)

/--
Existence of a maximal *immediate* intermediate space inside a fixed ambient space.

Concretely, for a linear isometry `f : E →ₗᵢ[𝕜] E₀`, we consider the set
`immediateExtensionSubmodules E E₀ f` of submodules `M ≤ E₀` that contain the range of `f` and for
which the induced inclusion `LinearMap.range f →ₗᵢ[𝕜] M` is an immediate extension.

Ordered by inclusion, this set is closed under unions of chains — the union of a chain of immediate
extensions is again immediate, since any vector orthogonal to the union is orthogonal to some member
of the chain. **Zorn's lemma** then produces a maximal element. No hypothesis on `E₀` beyond the
ultrametric structure is needed here; when `E₀` is additionally spherically complete, the maximal
submodule is itself spherically complete
(`instSphericallyCompleteSpaceOfMaximalImmediateExtensionSubmodule`) and underlies the spherical
completion of `E`.
-/
theorem exists_maximal_immediateExtensionSubmodule
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    ∃ m, Maximal (fun x ↦ x ∈ immediateExtensionSubmodules E E₀ f) m := by
  apply zorn_le₀
  intro C hC1 hC2
  if hC : ¬ C.Nonempty then
    refine ⟨(immediateExtensionSubmodules_nonempty E E₀ f).some,
      Set.Nonempty.some_mem (immediateExtensionSubmodules_nonempty E E₀ f), ?_⟩
    intro c hc
    contrapose hC
    use c
  else
  use ⨆ i, (fun x ↦ x.val : C → Submodule 𝕜 E₀) i
  simp only [not_not] at hC
  have hf_le : f.range ≤ ⨆ i, (fun x ↦ x.val : C → Submodule 𝕜 E₀) i := fun z hz ↦
    Submodule.mem_iSup _ |>.2 fun N hN ↦ (hN ⟨hC.some, hC.some_mem⟩) ((hC1 hC.some_mem).1 hz)
  refine ⟨mem_immediateExtensionSubmodules_iff.2
    ⟨hf_le, fun x hIsMOrtho ↦ ?_⟩, fun M hM z hz ↦
    Submodule.mem_iSup _ |>.2 fun N hN ↦ (hN ⟨M, hM⟩) hz⟩
  haveI : Nonempty ↑C := hC.to_subtype
  have hxmem : (x : E₀) ∈ ⨆ i, (fun x ↦ x.val : C → Submodule 𝕜 E₀) i := x.2
  rw [Submodule.mem_iSup_of_directed _ hC2.directed] at hxmem
  rcases hxmem with ⟨N, hxN⟩
  obtain ⟨hc, himm⟩ := mem_immediateExtensionSubmodules_iff.1 (hC1 N.2)
  apply Subtype.ext
  have := himm ⟨(x : E₀), hxN⟩ (by simpa using hIsMOrtho)
  simpa using congrArg Subtype.val this

/--
The maximal immediate-extension subspace of a spherically complete ambient space is itself
spherically complete.

For `f : E →ₗᵢ[𝕜] E₀` with `E₀` spherically complete, let `K` be the maximal element
`(exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose` of
`immediateExtensionSubmodules E E₀ f`. Then `K` inherits spherical completeness from `E₀`: a nested
family of closed balls in `K`, pushed forward along the isometric inclusion `K ↪ E₀`, is again a
nested family of closed balls in `E₀` (same radii), which meets in a point `a : E₀` by spherical
completeness of `E₀`. If `a ∈ K` we are done. Otherwise `K + 𝕜 ∙ a` would be a strictly larger
immediate extension of `E` — one checks, using immediacy of `K` and the strong triangle inequality,
that no nonzero vector of `K + 𝕜 ∙ a` is metrically orthogonal to `range f` — contradicting
maximality of `K`. Hence the intersection point lies in `K` and every
nested family of balls in `K` has a common point.
-/
instance instSphericallyCompleteSpaceOfMaximalImmediateExtensionSubmodule
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    (E₀ : Type*) [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [iud : IsUltrametricDist E₀]
    [hsc : SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    SphericallyCompleteSpace
      (↥(exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose) := by
  rw [iff_strictAnti_radius]
  set K := (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose with hK
  by_contra hc
  push Not at hc
  rcases hc with ⟨c, r, hsr, hanti, hemp⟩
  have := @hsc.isSphericallyComplete (fun n ↦ (c n).1) r (by
    intro m n hmn z hz
    simp only [mem_closedBall] at *
    refine le_trans (iud.dist_triangle_max z (c n).val (c m).val) ?_
    refine max_le (le_trans hz <| hsr.antitone hmn) ?_
    have h_in : c n ∈ closedBall (c m) ↑(r m) :=
      hanti hmn <| mem_closedBall_self NNReal.zero_le_coe
    rw [mem_closedBall] at h_in
    exact h_in)
  simp only [Set.nonempty_iInter, mem_closedBall] at this
  rcases this with ⟨a, ha⟩
  if haa : a ∈ K then
    contrapose hemp
    refine Set.nonempty_iff_ne_empty.mp ⟨⟨a, haa⟩, ?_⟩
    simp only [Set.mem_iInter, mem_closedBall]
    intro i
    exact ha i
  else
  have : (K + Submodule.span 𝕜 {a}) ∉ immediateExtensionSubmodules E E₀ f := by
    by_contra hc
    have : K < K + Submodule.span 𝕜 {a} := by
      simpa only [Submodule.add_eq_sup, left_lt_sup, Submodule.span_singleton_le_iff_mem]
    exact (not_le_of_gt this) <|
      (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose_spec.2 hc
        (le_of_lt this)
  rw [mem_immediateExtensionSubmodules_iff, not_exists] at this
  specialize this <| le_sup_of_le_left
    (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose_spec.1.choose
  simp only [not_forall] at this
  rcases this with ⟨b', hb'1, hb'2⟩
  rcases Submodule.mem_sup.1 b'.prop with ⟨x', hx', v', hv', hx'v'⟩
  rcases Submodule.mem_span_singleton.1 hv' with ⟨s, hs⟩
  rw [← hs] at hx'v'
  have hhs : s ≠ 0 := by
    by_contra hc
    simp only [hc, zero_smul, add_zero] at hx'v'
    subst hx'v'
    obtain ⟨_, himmK⟩ :=
      mem_immediateExtensionSubmodules_iff.1
        (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose_spec.1
    exact hb'2 (ZeroMemClass.coe_eq_zero.mp (congrArg Subtype.val (himmK ⟨b', hx'⟩ hb'1)))
  let b := s⁻¹ • b'
  let x := - s⁻¹ • x'
  have : b = a - x := by
    simp only [SetLike.val_smul, ← hx'v', smul_add, neg_smul, sub_neg_eq_add, b, x]
    rw [add_comm]
    simpa only [add_left_inj] using inv_smul_smul₀ hhs a
  have hb'1' : IsMOrtho b' (LinearMap.range (Submodule.inclusion (le_sup_of_le_left
      (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀
        f).choose_spec.1.choose))) :=
    (isMOrtho_range_inclusion_iff _ b').2 hb'1
  have hb1 := @IsMOrtho.smul 𝕜 _ _ _ _ inferInstance b' _ s⁻¹ hb'1'
  replace hb1 : IsMOrtho b.val K := by
    by_contra hc
    rcases IsMOrtho.not_iff_exists_dist_lt_norm.1 hc with ⟨g, hg1, hg2⟩
    rw [dist_eq_norm] at hg2
    have hg2' := IsUltrametricDist.norm_eq_of_norm_sub_lt_left hg2
    have hgg : g ≠ 0 := by
      by_contra hc
      simp only [hc, norm_zero, norm_eq_zero, ZeroMemClass.coe_eq_zero] at hg2'
      simp only [dist_le_coe, IsMOrtho, ne_eq,
        hg2', ZeroMemClass.coe_zero, norm_zero] at *
      contrapose hc
      exact infDist_zero_of_mem <| by simp only [SetLike.mem_coe, zero_mem]
    have hChooseSpec :=
      (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀
        f).choose_spec.1.choose_spec
    have hNIsMOrtho := mt (hChooseSpec ⟨g, hg1⟩)
        (fun h ↦ hgg (congrArg Subtype.val h))
    rcases @IsMOrtho.not_iff_exists_dist_lt_norm 𝕜 _ (↥K)
        _ _ inferInstance (⟨g, hg1⟩) _ |>.1 hNIsMOrtho with ⟨e, he1, he2⟩
    simp only [Submodule.coe_norm, ← hg2', dist_eq_norm, AddSubgroupClass.coe_sub] at he2
    suffices hh : ‖b.val - e.val‖ < ‖b.val‖ by
      contrapose hb1
      apply @IsMOrtho.not_iff_exists_dist_lt_norm 𝕜 _ _ _ _ inferInstance |>.2
      use ⟨e.val, Submodule.mem_sup_left e.prop⟩
      simp only [LinearMap.mem_range, Submodule.inclusion_apply, Subtype.exists] at he1
      rcases he1 with ⟨q1, q2, q3⟩
      replace q3 : q1 = e.val := by simp [← q3]
      constructor
      · exact ⟨⟨q1, q2⟩, by subst q3; rfl⟩
      · rw [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub, Submodule.coe_norm]
        exact hh
    rw [← sub_add_sub_cancel b.val g e.val]
    exact lt_of_le_of_lt (iud.norm_add_le_max _ _) <| max_lt hg2 he2
  have hx : x ∈ K := Submodule.smul_mem K (-s⁻¹) hx'
  suffices h : ∀ i : ℕ, ⟨x, hx⟩ ∈ closedBall (c i) ↑(r i) by
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

/--
`maximalImmediateExtensionEmbedding f` is the canonical linear isometry embedding `E` into a
maximal immediate-extension subspace of the spherically complete ambient space `E₀`.

Given `f : E →ₗᵢ[𝕜] E₀` with `E₀` spherically complete,
`exists_maximal_immediateExtensionSubmodule` provides a maximal element `M` of
`immediateExtensionSubmodules E E₀ f`; in particular `M` contains `range f`. This definition sends
`x : E` to `f x`, viewed as an element of `M`. Since `f` is an isometry and the inclusion
`M ↪ E₀` preserves norms, the result is again an isometric embedding. Together with the spherical
completeness of `M` (`instSphericallyCompleteSpaceOfMaximalImmediateExtensionSubmodule`), this is
the isometry realising `M` as a spherical completion of `E`.
-/
noncomputable def maximalImmediateExtensionEmbedding {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀] [IsUltrametricDist E₀]
    [SphericallyCompleteSpace E₀]
    (f : E →ₗᵢ[𝕜] E₀) :
    E →ₗᵢ[𝕜] ↥(exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f).choose := {
    toFun x := ⟨f x, (exists_maximal_immediateExtensionSubmodule 𝕜 E E₀ f
      ).choose_spec.1.out.choose <| LinearMap.mem_range_self _ _⟩
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    norm_map' := f.norm_map
  }

end IsImmediate
end SphericallyCompleteSpace
