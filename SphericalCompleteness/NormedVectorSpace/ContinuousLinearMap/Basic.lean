/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.External.Sequence
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Extension

/-!
# Spherical completeness of operator spaces

Spherical completeness for spaces of continuous linear maps.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/--
`SphericallyCompleteSpace` instance for the space of continuous linear maps `E →L[𝕜] F`
over a nontrivially normed field `𝕜`.

Assumptions:
* `E` and `F` are seminormed additive commutative groups equipped with an ultrametric distance
  (`[IsUltrametricDist E]`, `[IsUltrametricDist F]`) and are normed spaces over `𝕜`.
* The codomain `F` is spherically complete.

Conclusion:
* The space of continuous linear maps `E →L[𝕜] F` is spherically complete.

This is useful for transferring spherical completeness to function-like spaces of operators,
enabling fixed point / completeness arguments in non-Archimedean functional analysis.
-/
instance instSphericallyCompleteSpaceContinuousLinearMap {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
    {F : Type*} [SeminormedAddCommGroup F] [IsUltrametricDist F]
    [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] :
    SphericallyCompleteSpace (E →L[𝕜] F) := by
  rw [iff_strictAnti_radius]
  intro c' r' hsar' hanti'
  if hseq : ∀ n : ℕ, ∃ N, ∀ i > N, c' n ≠ c' i then
  rcases exists_injective_subseq_of_finite_duplication c' hseq with ⟨φ, hφ⟩
  let c := c' ∘ φ
  let r := r' ∘ φ
  have hsar : StrictAnti r := StrictAnti.comp_strictMono hsar' hφ.1
  have hanti : Antitone fun i ↦ closedBall (c i) ↑(r i) :=
    fun m n hmn ↦ hanti' <| hφ.1.monotone hmn
  have hrnneg : ∀ i, 0 < r i := fun i ↦
    lt_of_le_of_lt zero_le <| hsar' (Nat.lt_succ_self (φ i))
  let 𝒰 := c '' Set.univ
  have := @exists_extension_opNorm_le 𝕜 _ E _ _ _ ⊥ F _ _ _ _
    0 𝒰 ⟨c 0, 0, Set.mem_univ 0, rfl⟩ (fun U ↦ r U.prop.out.choose) (fun _ ↦ hrnneg _) (by
    intro U V
    set nu := U.prop.out.choose with hnu
    set nv := V.prop.out.choose with hnv
    have hU : U.val = c nu := by simpa [hnu] using U.prop.out.choose_spec.2.symm
    have hV : V.val = c nv := by simpa [hnv] using V.prop.out.choose_spec.2.symm
    rw [hU, hV]
    rcases @trichotomous ℕ (fun a b ↦ a < b) inferInstance nu nv with hlt | heq | hgt
    · rw [show max (↑(r nu) : ℝ) ↑(r nv) = ↑(max (r nu) (r nv)) from rfl,
        max_eq_left <| le_of_lt (hsar hlt), ← dist_eq_norm, dist_comm, ← mem_closedBall]
      exact (hanti <| le_of_lt hlt) (by simp [mem_closedBall])
    · rw [heq]; simp
    · rw [show max (↑(r nu) : ℝ) ↑(r nv) = ↑(max (r nu) (r nv)) from rfl,
        max_eq_right <| le_of_lt (hsar hgt), ← dist_eq_norm, ← mem_closedBall]
      exact (hanti <| le_of_lt hgt) (by simp [mem_closedBall])) (by
    intro U x
    rw [Subsingleton.elim x 0]; simp)
  rcases this with ⟨T, _, hT2⟩
  use T
  simp only [Set.mem_iInter]
  suffices hh : ∀ (i : ℕ), T ∈ closedBall (c i) ↑(r i) by
    intro i
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop_iff_of_monotone hφ.1.monotone).1
      (StrictMono.tendsto_atTop hφ.1) i
    simpa [c, r, Function.comp_apply] using (hanti' hN) <| hh N
  simp only [mem_closedBall]
  intro i
  have : c i ∈ 𝒰 := ⟨i, Set.mem_univ i, rfl⟩
  specialize hT2 ⟨c i, this⟩
  simp only [← dist_eq_norm, Set.mem_univ, true_and] at hT2
  convert hT2
  conv_lhs => rw [← hφ.2 <| this.out.choose_spec.2]
  simp only [Set.mem_univ, true_and]
  else
  push Not at hseq
  rcases hseq with ⟨N, hN⟩
  use c' N
  simp only [Set.mem_iInter]
  intro i
  rcases hN i with ⟨t, ht⟩
  rw [ht.2]
  refine (hanti' <| le_of_lt ht.1) ?_
  simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]

end SphericallyCompleteSpace
