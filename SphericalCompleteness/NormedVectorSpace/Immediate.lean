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
is metrically orthogonal to the range of `f`; intuitively, `F` adds no genuinely new "directions"
beyond those already present in `E`. A space is *maximally complete* (`MaximallyComplete 𝕜 E`) when
it admits no proper immediate extension.

## Main definitions

* `SphericallyCompleteSpace.IsImmediate`: the predicate that a linear isometry is an immediate
  embedding.
* `SphericallyCompleteSpace.MaximallyComplete`: the predicate that a space admits no proper
  immediate extension.

## Main statements

* `SphericallyCompleteSpace.exists_linearIsometry_comp_eq_of_isImmediate`: any linear isometry from
  `E` into a spherically complete space extends along an immediate embedding of `E`.
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

/--
`LinearIsometry.weakInv f` is the (weak, partial) inverse of a linear isometry
`f : E →ₗᵢ[𝕜] F`.

Since `f` is an isometry it is injective, hence a linear isometric isomorphism onto its range
`↥f.range` (given by `f.equivRange`). Its inverse is the linear isometry
`weakInv f : ↥f.range →ₗᵢ[𝕜] E`, defined on the range of `f` rather than on all of `F` — whence
"weak". It satisfies `weakInv f ⟨f x, _⟩ = x` for every `x : E`, i.e. it undoes `f` on its image.
-/
private noncomputable def LinearIsometry.weakInv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) := f.equivRange.symm.toLinearIsometry

/--
Key norm-preservation step behind `exists_linearIsometry_comp_eq_of_isImmediate`.

Suppose `f : E →ₗᵢ[𝕜] F` is immediate (`IsImmediate f`), `g : E →ₗᵢ[𝕜] H` is a linear isometry into
a spherically complete ultrametric normed space `H`, and `h : F →L[𝕜] H` is a continuous linear map
that agrees with `g ∘ weakInv f` on the range of `f` (hypothesis `hf1`) and whose operator norm
matches that composite (hypothesis `hf2`). Then `h` is norm-preserving: `‖h v‖ = ‖v‖` for every
`v : F`.

The upper bound `‖h v‖ ≤ ‖v‖` follows from `‖h‖ ≤ 1`, while the lower bound uses immediacy of `f`:
any `v` can be approximated within distance `< ‖v‖` by a vector in the range of `f`, on which `h`
already preserves norms. This is what promotes the continuous linear map `h` to a linear isometry.
-/
private lemma norm_map_of_isImmediate {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [IsUltrametricDist E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [IsUltrametricDist F] {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    [IsUltrametricDist H] [SphericallyCompleteSpace H] (f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f)
    (g : E →ₗᵢ[𝕜] H) (h : F →L[𝕜] H)
    (hf2 : ‖h‖ = ‖g.toContinuousLinearMap.comp (LinearIsometry.weakInv f).toContinuousLinearMap‖)
    (hf1 : ∀ (v : F) (x : E) (h_1 : f x = v), h v = g ((LinearIsometry.weakInv f) ⟨v, Exists.intro
    x h_1⟩))
    (v : F) : ‖(↑h : F →ₗ[𝕜] H) v‖ = ‖v‖ := by
  refine eq_of_le_of_ge ?_ ?_
  · suffices hh : ‖h‖ ≤ 1 by
      have := (ContinuousLinearMap.opNorm_le_iff zero_le_one).1 hh v
      simpa only [one_mul]
    rw [hf2]
    apply (ContinuousLinearMap.opNorm_le_iff zero_le_one).2
    intro x
    have : ‖(LinearIsometry.weakInv f).toContinuousLinearMap x‖ = ‖x‖ := by
      simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
    rw [← this]
    simp only [ContinuousLinearMap.coe_comp, LinearIsometry.coe_toContinuousLinearMap,
      Function.comp_apply, LinearIsometry.norm_map, one_mul, le_refl]
  · if hv : v = 0 then
      simp [hv]
    else
    simp only [IsImmediate] at hf
    specialize hf v
    simp only [MOrth, hv, imp_false] at hf
    replace hf : infDist v ↑(LinearMap.range f.toLinearMap) < ‖v‖ := by
      refine lt_of_le_of_ne ?_ hf
      rw [← dist_zero_right v]
      exact infDist_le_dist_of_mem <| zero_mem (LinearMap.range f.toLinearMap)
    rcases(infDist_lt_iff <| Submodule.nonempty (LinearMap.range f.toLinearMap)).1 hf with ⟨x, hx⟩
    rw [dist_eq_norm] at hx
    have : ‖h x - h v‖ < ‖v‖ := by
      rw [(by simp : h x - h v = h (x - v))]
      refine lt_of_le_of_lt (ContinuousLinearMap.le_opNorm h (x - v)) ?_
      if hrf : ¬ Nontrivial (LinearMap.range f.toLinearMap) then
        rw [Submodule.nontrivial_iff_ne_bot] at hrf
        push Not at hrf
        simp only [hrf, Submodule.bot_coe, Set.mem_singleton_iff] at hx
        simp only [hx.1, sub_zero, lt_self_iff_false, and_false] at hx
      else
      have : ‖h‖ = 1 := by
        have : ‖(g.comp (LinearIsometry.weakInv f)).toContinuousLinearMap‖ =
          ‖ (g.toContinuousLinearMap).comp (LinearIsometry.weakInv f).toContinuousLinearMap‖ := rfl
        rw [← this] at hf2
        rw [hf2]
        haveI := not_not.1 hrf
        exact LinearIsometry.norm_toContinuousLinearMap _
      rw [this, one_mul, norm_sub_rev]
      exact hx.2
    have hx' := norm_eq_of_norm_sub_lt_left hx.2
    have t : ‖h x‖ = ‖x‖ := by
      obtain ⟨z, hz⟩ := hx.1; rw [hf1 x z hz]; simp
    rw [hx', ← t] at this
    apply norm_eq_of_norm_sub_lt_left at this
    simp only [hx', ContinuousLinearMap.coe_coe, ← this, t, le_refl]

/--
Given an immediate linear isometry `f : E →ₗᵢ[𝕜] F` and a linear isometry `g : E →ₗᵢ[𝕜] H` into a
spherically complete ultrametric normed space `H`, there exists a linear isometry
`h : F →ₗᵢ[𝕜] H` such that `h.comp f = g`.

This is an extension property: along an immediate embedding `f`, any isometric map out of `E`
into a spherically complete target extends to an isometric map out of `F`.

The conclusion is stated using an explicit `@LinearIsometry.comp` to avoid elaboration issues.
-/
theorem exists_linearIsometry_comp_eq_of_isImmediate {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [IsUltrametricDist H]
    [SphericallyCompleteSpace H]
    (f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f)
    (g : E →ₗᵢ[𝕜] H) :
    ∃ (h : F →ₗᵢ[𝕜] H), LinearIsometry.comp (h : F →ₗᵢ[𝕜] H) (f : E →ₗᵢ[𝕜] F) = g := by
  rcases hahn_banach' _
    (LinearIsometry.comp g (LinearIsometry.weakInv f)).toContinuousLinearMap with ⟨h, hf1, hf2⟩
  simp only [LinearMap.mem_range, forall_exists_index] at hf1
  have hf2' : ‖h‖ =
      ‖g.toContinuousLinearMap.comp (LinearIsometry.weakInv f).toContinuousLinearMap‖ := by
    rw [hf2]; rfl
  let h : F →ₗᵢ[𝕜] H := {
    toFun := h.toFun,
    map_add' := h.map_add',
    map_smul' := h.map_smul',
    norm_map' := fun v ↦ norm_map_of_isImmediate f hf g h hf2' hf1 v
  }
  use h
  ext z
  simp only [LinearIsometry.coe_comp, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    Function.comp_apply, h]
  have : (LinearIsometry.weakInv f) ⟨f z, LinearMap.mem_range_self f.toLinearMap z⟩ = z :=
    f.equivRange.symm_apply_apply z
  rw [hf1 (f z) z rfl]
  change g ((LinearIsometry.weakInv f) ⟨f z, LinearMap.mem_range_self f.toLinearMap z⟩) = g z
  rw [this]

end SphericallyCompleteSpace
