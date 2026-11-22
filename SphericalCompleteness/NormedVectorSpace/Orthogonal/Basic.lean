/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SphericalCompleteness.Metric.Seminormed.Basic
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.Defs

/-!
# Orthogonality: basic results

Basic results on (norm) orthogonality in ultrametric normed spaces, building on the definitions
`IsVOrtho` (`x ⟂[𝕜] y`), `IsMOrtho` (`x ⟂ₘ F`) and `IsOrtho` (`F ⟂ₛ G`) from
`SphericalCompleteness.NormedVectorSpace.Orthogonal.Defs`.

## Main statements

* Orthogonality of vectors is symmetric (`IsVOrtho.symm`) and admits two reformulations: it
  coincides with **Birkhoff–James orthogonality** (`IsVOrtho.iff_birkhoffJames`) and with the
  ultrametric identity "the norm of a linear combination is the maximum of the norms of its terms"
  (`IsVOrtho.iff_norm_add_eq_max`).
* All three relations are invariant under nonzero scalar multiplication
  (`IsVOrtho.smul_left_iff`, `IsVOrtho.smul_right_iff`,
  `IsMOrtho.smul_iff`).
* Metric orthogonality to a subspace is orthogonality to each of its vectors
  (`IsMOrtho.iff_forall_isVOrtho`); subspace orthogonality unfolds to orthogonality of all pairs of
  vectors (`IsOrtho.iff_forall_isVOrtho`) and is symmetric (`IsOrtho.symm`).
* A vector that both lies in `F` and is orthogonal to `F` is zero (`IsMOrtho.eq_zero_of_mem`).
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

section
variable {𝕜 : Type*} [NormedField 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E]

/-- The distance-comparison formulation of orthogonality agrees with the normed-space API. -/
theorem isMOrtho_iff_nnMetric {x : E} {F : Submodule 𝕜 E} :
    (x ⟂ₘ F) ↔ (nnMetric E).IsOrthogonalTo x F := by
  have hzero : infDist x (F : Set E) ≤ ‖x‖ := by
    simpa only [dist_zero_right] using infDist_le_dist_of_mem F.zero_mem
  change infDist x (F : Set E) = ‖x‖ ↔ _
  rw [le_antisymm_iff, and_iff_right hzero, le_infDist F.nonempty]
  simp only [PseudoMetric.IsOrthogonalTo, nnMetric_apply, ← NNReal.coe_le_coe, coe_nndist,
    dist_zero_right]

private theorem isVOrtho_iff_nnMetric {x y : E} :
    (x ⟂[𝕜] y) ↔ (nnMetric E).IsOrthogonalTo x (𝕜 ∙ y) := isMOrtho_iff_nnMetric

/-! ### Orthogonality of vectors -/

namespace IsVOrtho

/-- Orthogonality of vectors is symmetric: `x ⟂[𝕜] y` if and only if `y ⟂[𝕜] x`. Although `IsVOrtho`
is defined asymmetrically (as a distance to the line spanned by the second vector), the relation
does not depend on the order of its arguments. -/
lemma symm {x y : E} :
    (x ⟂[𝕜] y) ↔ (y ⟂[𝕜] x) :=
  isVOrtho_iff_nnMetric.trans <| PseudoMetric.isOrthogonalTo_span_singleton_comm.trans
    isVOrtho_iff_nnMetric.symm

/-- **Birkhoff–James characterization of orthogonality**: `x ⟂[𝕜] y` if and only if `x` is a
best approximation of itself along the line `𝕜 ∙ y`, i.e. `‖x‖ ≤ ‖x + c • y‖` for every scalar
`c`. This rephrases the `infDist`-based definition of `IsVOrtho` as a norm-minimality condition. -/
lemma iff_birkhoffJames
    (x y : E) : (x ⟂[𝕜] y) ↔ ∀ c : 𝕜, ‖x‖ ≤ ‖x + c • y‖ := by
  refine ⟨fun h c ↦ ?_, fun h ↦ ?_⟩
  · rw [← sub_neg_eq_add, ← neg_smul, ← h, ← dist_eq_norm]
    exact infDist_le_dist_of_mem (Submodule.mem_span_singleton.mpr ⟨-c, by simp⟩)
  · by_contra hc
    have hd : infDist x ↑(𝕜 ∙ y) ≤ ‖x‖ := by
      rw [← dist_zero, dist_comm]
      exact infDist_le_dist_of_mem (by simp)
    obtain ⟨y', hy', hy''⟩ := (infDist_lt_iff ⟨0, by simp⟩).1 (lt_of_le_of_ne hd hc)
    rcases Submodule.mem_span_singleton.1 hy' with ⟨c, hc⟩
    rw [← hc, dist_eq_norm, sub_eq_add_neg, ← neg_smul] at hy''
    specialize h (-c); linarith

/-- Orthogonality of vectors is equivalent to the ultrametric "norm of a sum equals the maximum
of the norms" identity on the spanned plane: `x ⟂[𝕜] y` if and only if
`‖α • x + β • y‖ = max ‖α • x‖ ‖β • y‖` for all scalars `α` and `β`. In particular `x` and `y`
then span a plane on which the norm is completely determined by the norms of the two axes. -/
lemma iff_norm_add_eq_max {x y : E} :
    (x ⟂[𝕜] y) ↔ (∀ α β : 𝕜, ‖α • x + β • y‖ = max ‖α • x‖ ‖β • y‖) := by
  rw [isVOrtho_iff_nnMetric, PseudoMetric.isOrthogonalTo_span_singleton_iff_max]
  simp only [nnMetric_apply, nndist_zero_right, ← NNReal.coe_inj, NNReal.coe_max, coe_nnNorm]

/-- Orthogonality is preserved by scaling the first vector: if `x ⟂[𝕜] y` then `(a • x) ⟂[𝕜] y`
for every scalar `a` (including `a = 0`, since `0` is orthogonal to everything). -/
theorem smul_left {x y : E}
    (a : 𝕜) : (x ⟂[𝕜] y) → ((a • x) ⟂[𝕜] y) := by
  intro h
  rw [iff_norm_add_eq_max] at h ⊢
  intro b c
  simpa only [smul_smul] using h (b * a) c

/-- For a nonzero scalar `a`, scaling the first vector preserves and reflects orthogonality:
`x ⟂[𝕜] y` if and only if `(a • x) ⟂[𝕜] y`. -/
theorem smul_left_iff {x y : E}
    {a : 𝕜} (ha : a ≠ 0) : (x ⟂[𝕜] y) ↔ ((a • x) ⟂[𝕜] y) := by
  refine ⟨smul_left a, fun h ↦ ?_⟩
  apply smul_left a⁻¹ at h
  rwa [inv_smul_smul₀ ha x] at h

/-- Orthogonality is preserved by scaling the second vector: if `x ⟂[𝕜] y` then `x ⟂[𝕜] (a • y)`
for every scalar `a`. This is the counterpart of `IsVOrtho.smul_left` obtained through symmetry. -/
theorem smul_right {x y : E}
    (a : 𝕜) : (x ⟂[𝕜] y) → (x ⟂[𝕜] (a • y)) := by
  intro h
  rw [symm] at *
  exact smul_left a h

/-- For a nonzero scalar `a`, scaling the second vector preserves and reflects orthogonality:
`x ⟂[𝕜] y` if and only if `x ⟂[𝕜] (a • y)`. -/
theorem smul_right_iff {x y : E}
    {a : 𝕜} (ha : a ≠ 0) : (x ⟂[𝕜] y) ↔ (x ⟂[𝕜] (a • y)) := by
  nth_rw 1 [symm]
  nth_rw 2 [symm]
  exact smul_left_iff ha

end IsVOrtho

/-! ### Metric orthogonality to a subspace -/

namespace IsMOrtho

/-- Metric orthogonality to a subspace reduces to orthogonality to each of its vectors: `x ⟂ₘ F`
if and only if `x ⟂[𝕜] y` for every `y ∈ F`. This links the subspace notion `IsMOrtho` to the
vector notion `IsVOrtho`. -/
lemma iff_forall_isVOrtho
    (x : E) (F : Subspace 𝕜 E) :
    (x ⟂ₘ F) ↔ ∀ y ∈ F, (x ⟂[𝕜] y) := by
  simp_rw [isMOrtho_iff_nnMetric, isVOrtho_iff_nnMetric]
  exact PseudoMetric.isOrthogonalTo_iff_forall_span_singleton

end IsMOrtho

end

namespace IsMOrtho

/-- A vector that both lies in a subspace `F` and is metrically orthogonal to `F` must be zero:
`x ∈ F` and `x ⟂ₘ F` force `x = 0`. Membership makes the distance from `x` to `F` vanish, so
`‖x‖ = 0`.

Unlike the surrounding results this requires the genuine `NormedAddCommGroup E` (rather than only
`SeminormedAddCommGroup E`), since it is where `‖x‖ = 0` is upgraded to `x = 0`. -/
theorem eq_zero_of_mem {𝕜 : Type*} [NormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {x : E} {F : Subspace 𝕜 E} : x ∈ F → (x ⟂ₘ F) → x = 0 :=
  fun h1 h2 ↦ norm_eq_zero.mp (infDist_zero_of_mem h1 ▸ h2 : (0 : ℝ) = ‖x‖).symm

end IsMOrtho

section
variable {𝕜 : Type*} [NormedField 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E]

namespace IsMOrtho

/-- Metric orthogonality to a subspace is preserved by scaling: if `x ⟂ₘ F` then `(a • x) ⟂ₘ F`
for every scalar `a`. -/
theorem smul
    {x : E} {F : Subspace 𝕜 E} (a : 𝕜) :
    (x ⟂ₘ F) → ((a • x) ⟂ₘ F) := by
  intro h
  rw [iff_forall_isVOrtho] at *
  exact fun y hy ↦ IsVOrtho.smul_left a (h y hy)

/-- For a nonzero scalar `a`, scaling preserves and reflects metric orthogonality to a subspace:
`x ⟂ₘ F` if and only if `(a • x) ⟂ₘ F`. -/
theorem smul_iff
    {x : E} {F : Subspace 𝕜 E} {a : 𝕜} (ha : a ≠ 0) :
    (x ⟂ₘ F) ↔ ((a • x) ⟂ₘ F) := by
  refine ⟨smul a, fun h ↦ ?_⟩
  apply smul a⁻¹ at h
  rwa [inv_smul_smul₀ ha x] at h

/-- Failure of metric orthogonality is witnessed by a strictly better approximation: `x` is *not*
metrically orthogonal to `F` if and only if some `y ∈ F` satisfies `dist x y < ‖x‖`. This is the
negation of `IsMOrtho` phrased as the existence of a point of `F` closer to `x` than `0` is. -/
theorem not_iff_exists_dist_lt_norm
    {x : E} {F : Subspace 𝕜 E} :
    ¬ (x ⟂ₘ F) ↔ ∃ y ∈ F, dist x y < ‖x‖ := by
  have hle : infDist x (F : Set E) ≤ ‖x‖ := by
    simpa only [dist_zero_right] using infDist_le_dist_of_mem F.zero_mem
  change infDist x (F : Set E) ≠ ‖x‖ ↔ _
  simpa only [lt_iff_le_and_ne, hle, true_and, SetLike.mem_coe] using
    (infDist_lt_iff (x := x) (r := ‖x‖) F.nonempty)

end IsMOrtho

/-! ### Orthogonality of subspaces -/

namespace IsOrtho

/-- Subspace orthogonality unfolds to orthogonality of all pairs of vectors: `F₁ ⟂ₛ F₂` if and
only if `x ⟂[𝕜] y` for every `x ∈ F₁` and every `y ∈ F₂`. -/
theorem iff_forall_isVOrtho
    (F1 F2 : Subspace 𝕜 E) : (F1 ⟂ₛ F2) ↔ ∀ x ∈ F1, ∀ y ∈ F2, (x ⟂[𝕜] y) := by
  simp only [SphericallyCompleteSpace.IsOrtho, IsMOrtho.iff_forall_isVOrtho]

/-- Subspace orthogonality is symmetric: `F₁ ⟂ₛ F₂` if and only if `F₂ ⟂ₛ F₁`. Despite the
asymmetric definition of `IsOrtho` (quantifying over vectors of the first subspace only), the
relation is independent of the order of its arguments. -/
theorem symm
    {F1 F2 : Subspace 𝕜 E} : (F1 ⟂ₛ F2) ↔ (F2 ⟂ₛ F1) := by
  simp_rw [SphericallyCompleteSpace.IsOrtho, isMOrtho_iff_nnMetric]
  exact PseudoMetric.forall_isOrthogonalTo_comm

end IsOrtho

end

end SphericallyCompleteSpace
