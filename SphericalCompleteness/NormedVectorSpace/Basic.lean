/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.MOrth

/-!
# Spherical completeness of normed vector spaces

Finite-dimensional ultrametric normed spaces over a spherically complete base are
spherically complete.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/--
Constructs a `SphericallyCompleteSpace` instance for a normed vector space `E` over a
nontrivially normed field `𝕜`, assuming `E` is locally compact as a topological space.

In this setting, local compactness (together with the nontriviality of the norm on `𝕜`)
is used to deduce spherical completeness of `E`.
-/
theorem SphericallyComplete.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
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
instance instSubtypeMemSubmoduleSpanSingletonSet (𝕜 : Type*) [NontriviallyNormedField 𝕜]
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

private lemma induction_sphericallyCompleteSpace_of_finiteDimensional
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [SphericallyCompleteSpace 𝕜]
    (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [IsUltrametricDist E] [FiniteDimensional 𝕜 E] :
    ∀ n < Module.finrank 𝕜 E,
    (∃ M : Subspace 𝕜 E, Module.finrank 𝕜 M = n ∧ SphericallyCompleteSpace M)
    → (∃ M' : Subspace 𝕜 E, Module.finrank 𝕜 M' = (n + 1) ∧ SphericallyCompleteSpace M')
    := by
  rintro n hn ⟨M, hM1, _⟩
  rcases exists_morth_vec_of_not_full_finrank 𝕜 M (by linarith) with ⟨z, hz', hz⟩
  use ((Submodule.span 𝕜 {z}) + M)
  let φ := directProdIsoSumOfOrth 𝕜 z M hz
  constructor
  · rw [← FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.1
      (Nonempty.intro φ.toLinearEquiv)]
    simp only [Module.finrank_prod, hM1, add_comm, Nat.add_left_cancel_iff]
    exact finrank_span_singleton hz'
  · letI : SphericallyCompleteSpace M := ‹SphericallyCompleteSpace M›
    let hsSpan : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) :=
      instSubtypeMemSubmoduleSpanSingletonSet 𝕜 z
    let hsProd : SphericallyCompleteSpace ((Submodule.span 𝕜 {z}) × M) := by
      letI : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) := hsSpan
      infer_instance
    exact sphericallyCompleteSpace_of_isometryEquiv
      (E := (Submodule.span 𝕜 {z}) × M) (he := hsProd) φ.toIsometryEquiv

/--
If `E` is a finite-dimensional normed vector space over a spherically complete, nontrivially normed
field `𝕜`, and the metric on `E` is ultrametric, then `E` is spherically complete.

This is the standard permanence result: spherical completeness descends from the base field to any
finite-dimensional ultrametric normed `𝕜`-vector space.
-/
theorem sphericallyCompleteSpace_of_finiteDimensional
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
