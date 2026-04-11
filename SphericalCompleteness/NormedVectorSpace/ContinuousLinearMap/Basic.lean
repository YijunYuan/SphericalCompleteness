import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.SupportingResults
import SphericalCompleteness.External.Sequence

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
instance instSphericallyCompleteSpaceContinuousLinearMap
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
[NormedSpace 𝕜 E]
{F : Type*} [SeminormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F] :
SphericallyCompleteSpace (E →L[𝕜] F) := by
  rw [sphericallyCompleteSpace_iff_strictAnti_radius]
  intro c' r' hsar' hanti'
  if hseq : ∀ n : ℕ, ∃ N, ∀ i > N, c' n ≠ c' i then
  rcases exists_bijective_subseq_of_finite_duplication c' hseq with ⟨φ, hφ⟩
  let c := c' ∘ φ
  let r := r' ∘ φ
  have hsar : StrictAnti r := StrictAnti.comp_strictMono hsar' hφ.1
  have hanti : Antitone fun i ↦ closedBall (c i) ↑(r i) := by
    intro m n hmn
    exact hanti' <| hφ.1.monotone hmn
  have hrnneg : ∀ i, 0 < r i := by
    intro i
    unfold r
    simp only [Function.comp_apply]
    exact lt_of_le_of_lt (zero_le _) <| hsar' (Nat.lt_succ_self (φ i))
  let 𝒰 := c '' Set.univ
  have h𝒰 : 𝒰.Nonempty := by
    use c 0, 0
    simp only [Set.mem_univ, and_self]
  let htriv : ↥(⊥ : Submodule 𝕜 E) →L[𝕜] F := 0
  have := @exists_extension_opNorm_le 𝕜 _ E _ _ _ ⊥ F _ _ _ _
    htriv 𝒰 h𝒰 (fun U => r U.prop.out.choose) (fun _ => hrnneg _) (by
    intro U V
    set nu := U.prop.out.choose with hnu
    set nv := V.prop.out.choose with hnv
    have hU : U.val = c nu := by
      simpa [hnu] using U.prop.out.choose_spec.2.symm
    have hV : V.val = c nv := by
      simpa [hnv] using V.prop.out.choose_spec.2.symm
    rw [hU, hV]
    rcases @trichotomous ℕ (fun a b => a < b) inferInstance nu nv with hlt | heq | hgt
    · rw [show max (↑(r nu) : ℝ) ↑(r nv) = ↑(max (r nu) (r nv)) from rfl,
        max_eq_left <| le_of_lt (hsar hlt), ← dist_eq_norm, dist_comm, ← mem_closedBall]
      exact (hanti <| le_of_lt hlt) (by simp [mem_closedBall])
    · rw [heq]; simp
    · rw [show max (↑(r nu) : ℝ) ↑(r nv) = ↑(max (r nu) (r nv)) from rfl,
        max_eq_right <| le_of_lt (hsar hgt), ← dist_eq_norm, ← mem_closedBall]
      exact (hanti <| le_of_lt hgt) (by simp [mem_closedBall])) (by
    intro U x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp [htriv])
  rcases this with ⟨T, _, hT2⟩
  use T
  simp only [Set.mem_iInter]
  suffices hh : ∀ (i : ℕ), T ∈ closedBall (c i) ↑(r i) by
    intro i
    have := (Filter.tendsto_atTop_atTop_iff_of_monotone hφ.1.monotone).1
    rcases this (StrictMono.tendsto_atTop hφ.1) i with ⟨N, hN⟩
    specialize hh N
    simp only [c, r, Function.comp_apply] at hh
    exact (hanti' hN) hh
  simp only [mem_closedBall]
  intro i
  have : c i ∈ 𝒰 := by
    use i
    simp only [Set.mem_univ, and_self]
  specialize hT2 ⟨c i, this⟩
  simp only [← dist_eq_norm, Set.mem_univ, true_and] at hT2
  convert hT2
  conv_lhs => rw [← hφ.2 <| this.out.choose_spec.2]
  simp only [Set.mem_univ, true_and]
  else
  push_neg at hseq
  rcases hseq with ⟨N, hN⟩
  use c' N
  simp only [Set.mem_iInter]
  intro i
  rcases hN i with ⟨t, ht⟩
  rw [ht.2]
  refine (hanti' <| le_of_lt ht.1) ?_
  simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]

end SphericallyCompleteSpace
