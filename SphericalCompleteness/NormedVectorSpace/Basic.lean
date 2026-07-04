/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.IsMOrtho

/-!
# Spherical completeness of normed vector spaces

This file establishes that finite-dimensional ultrametric normed spaces over a spherically
complete base field are spherically complete.

The proof proceeds by induction on the dimension: starting from the trivial subspace, one
repeatedly adjoins a vector metrically orthogonal to the current subspace, identifying the
enlarged subspace with a product of spherically complete spaces.

## Main statements

* `SphericallyCompleteSpace.of_locallyCompactSpace`: a locally compact normed vector space over a
  nontrivially normed field is spherically complete.
* `SphericallyCompleteSpace.of_finiteDimensional`: a finite-dimensional
  ultrametric normed `𝕜`-vector space over a spherically complete, nontrivially normed field is
  spherically complete.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/--
A locally compact normed vector space over a nontrivially normed field is spherically complete.

Local compactness upgrades to `ProperSpace` over a nontrivially normed field (so every closed ball
is compact), and properness already gives spherical completeness via Cantor's intersection
theorem. -/
theorem of_locallyCompactSpace
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] :
    SphericallyCompleteSpace E := by
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace 𝕜
  infer_instance

/--
Constructs a `SphericallyCompleteSpace` instance on the one-dimensional subspace
`Submodule.span 𝕜 {z}` (viewed as a subtype of `E`), assuming the scalar field `𝕜`
is nontrivially normed and spherically complete.

This is a convenience instance allowing downstream results to use spherical
completeness on the span of a single vector without explicitly transporting the
structure from `𝕜`.
-/
instance instSphericallyCompleteSpaceSpanSingleton (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [scsk : SphericallyCompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (z : E) : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) where
  isSphericallyComplete := by
    if h: z = 0 then
      rw [h, Submodule.span_zero_singleton]
      intro ci ri hanti
      use 0
      simp only [Set.mem_iInter, mem_closedBall]
      intro i
      simp [(Submodule.eq_zero_of_bot_submodule (ci i) : ci i = 0)]
    else
    intro ci ri hanti
    have := @scsk.isSphericallyComplete
      (fun n ↦ (Submodule.mem_span_singleton.1 (ci n).prop).choose)
      (fun n ↦ ⟨ri n / ‖z‖, div_nonneg NNReal.zero_le_coe <| norm_nonneg z⟩) (by
      refine antitone_nat_of_succ_le ?_
      intro n x hx
      simp only [mem_closedBall] at *
      have := hanti (by linarith : n ≤ n + 1)
      simp only [Set.le_eq_subset] at this
      have this' : x • ⟨z, Submodule.mem_span_singleton_self z⟩
        ∈ closedBall (ci (n + 1)) ↑(ri (n + 1)) := by
        simp only [SetLike.mk_smul_mk, mem_closedBall, Subtype.dist_eq]
        rw [← (Submodule.mem_span_singleton.1 (ci (n+1)).prop).choose_spec,
          dist_eq_norm, ← sub_smul, norm_smul]
        rw [dist_eq_norm] at hx
        exact mul_le_of_le_div₀ NNReal.zero_le_coe (norm_nonneg z) hx
      replace this' := Set.mem_of_mem_of_subset this' this
      simp only [SetLike.mk_smul_mk, mem_closedBall, Subtype.dist_eq] at this'
      simp only [ge_iff_le]
      rw [← (Submodule.mem_span_singleton.1 (ci n).prop).choose_spec,
        dist_eq_norm, ← sub_smul, norm_smul, ← dist_eq_norm] at this'
      exact (le_div_iff₀ (norm_pos_iff.mpr h)).mpr this'
      )
    simp only [Set.nonempty_iInter, mem_closedBall] at this
    rcases this with ⟨x, hx⟩
    use x • ⟨z, Submodule.mem_span_singleton_self z⟩
    simp only [SetLike.mk_smul_mk, Set.mem_iInter, mem_closedBall]
    intro i
    specialize hx i
    rwa [Subtype.dist_eq, dist_eq_norm, ← (Submodule.mem_span_singleton.1 (ci i).prop).choose_spec,
      ← sub_smul, norm_smul, ← dist_eq_norm, ← le_div_iff₀ (norm_pos_iff.mpr h)]

/--
The inductive step for `of_finiteDimensional`.

If `E` is a finite-dimensional ultrametric normed space over a spherically complete, nontrivially
normed field `𝕜`, then for every `n < Module.finrank 𝕜 E`, the existence of an
`n`-dimensional spherically complete subspace `M` of `E` yields an `(n + 1)`-dimensional
spherically complete subspace `M'`.

The larger subspace is obtained as `Submodule.span 𝕜 {z} + M`, where `z` is a nonzero vector
metrically orthogonal to `M` (which exists since `M` is not the whole space). This sum is
isometrically isomorphic to the product `Submodule.span 𝕜 {z} × M` of two spherically complete
spaces, and spherical completeness transfers along the isometry.
-/
private lemma induction_sphericallyCompleteSpace_of_finiteDimensional
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [SphericallyCompleteSpace 𝕜]
    (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [IsUltrametricDist E] [FiniteDimensional 𝕜 E] :
    ∀ n < Module.finrank 𝕜 E,
    (∃ M : Subspace 𝕜 E, Module.finrank 𝕜 M = n ∧ SphericallyCompleteSpace M)
    → (∃ M' : Subspace 𝕜 E, Module.finrank 𝕜 M' = (n + 1) ∧ SphericallyCompleteSpace M')
    := by
  rintro n hn ⟨M, hM1, _⟩
  rcases exists_morth_vec_of_finrank_lt 𝕜 M (by linarith) with ⟨z, hz', hz⟩
  use ((Submodule.span 𝕜 {z}) + M)
  let φ := IsMOrtho.directProdIsoSum 𝕜 z M hz
  constructor
  · rw [← FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.1
      (Nonempty.intro φ.toLinearEquiv)]
    simp only [Module.finrank_prod, hM1, add_comm, Nat.add_left_cancel_iff]
    exact finrank_span_singleton hz'
  · letI : SphericallyCompleteSpace M := ‹SphericallyCompleteSpace M›
    let hsSpan : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) :=
      instSphericallyCompleteSpaceSpanSingleton 𝕜 z
    let hsProd : SphericallyCompleteSpace ((Submodule.span 𝕜 {z}) × M) := by
      letI : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) := hsSpan
      infer_instance
    exact of_isometryEquiv
      (E := (Submodule.span 𝕜 {z}) × M) (he := hsProd) φ.toIsometryEquiv

/--
If `E` is a finite-dimensional normed vector space over a spherically complete, nontrivially normed
field `𝕜`, and the metric on `E` is ultrametric, then `E` is spherically complete.

This is the standard permanence result: spherical completeness descends from the base field to any
finite-dimensional ultrametric normed `𝕜`-vector space.
-/
theorem of_finiteDimensional
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [SphericallyCompleteSpace 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [IsUltrametricDist E] [FiniteDimensional 𝕜 E] :
    SphericallyCompleteSpace E := by
  suffices h : ∀ n ≤ Module.finrank 𝕜 E,
    (∃ M : Subspace 𝕜 E, Module.finrank 𝕜 M = n ∧ SphericallyCompleteSpace M) by
    rcases h (Module.finrank 𝕜 E) le_rfl with ⟨M, hM1, hM2⟩
    rw [Submodule.eq_top_of_finrank_eq hM1] at hM2
    refine { isSphericallyComplete := fun ci ri h ↦ ?_ }
    rcases @hM2.isSphericallyComplete (fun i ↦ ⟨ci i,trivial⟩) ri (
      fun _ _ hab _ hz ↦ (h hab) hz
    ) with ⟨x, hx⟩
    use x.val
    simp only [Set.mem_iInter, mem_closedBall, dist_le_coe] at hx ⊢
    intro i
    exact hx i
  intro n hn
  induction n
  · case zero => exact ⟨⊥, ⟨finrank_bot 𝕜 E, inferInstance⟩⟩
  · case succ n hn' => exact
    induction_sphericallyCompleteSpace_of_finiteDimensional 𝕜 E n hn <| hn' <| Nat.le_of_succ_le hn

end SphericallyCompleteSpace
