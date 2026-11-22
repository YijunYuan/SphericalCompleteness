/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.External.Sequence
public import SphericalCompleteness.External.Ultrametric.NormedSpace
public import SphericalCompleteness.Metric.Seminormed.Basic
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Extension
public import SphericalCompleteness.PseudoMetric.Module.Operator

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
  apply (Metric.sphericallyCompleteSpace_iff _).mpr
  apply PseudoMetric.IsSphericallyComplete.of_linearMap_bounds
    (nnMetric E) (nnMetric F) (nnMetric (E →L[𝕜] F))
    (fun A ↦ A.toLinearMap) (fun r t ↦ r * t)
    (fun r _ ↦ fun _ _ h ↦ mul_le_mul_of_nonneg_left h zero_le)
    (fun _ _ _ hrs t ↦ mul_le_mul_of_nonneg_right hrs zero_le)
  · intro r _ c u x h
    simp only [nnMetric_apply, nndist_zero_right] at h ⊢
    rw [nnNorm_smul, nnNorm_smul, mul_left_comm r]
    apply mul_le_mul_of_nonneg_left _ zero_le
    exact h
  · intro A B r _
    change nndist A B ≤ r ↔ ∀ x, nndist (A x) (B x) ≤ r * nndist x 0
    simp only [← NNReal.coe_le_coe, coe_nndist, NNReal.coe_mul, dist_eq_norm, sub_zero]
    exact ContinuousLinearMap.opNorm_le_iff (f := A - B) r.coe_nonneg
  · intro g B r _ h
    let A := (g - B.toLinearMap).mkContinuous r (fun x ↦ by
      have hx := NNReal.coe_le_coe.mpr (h x)
      simpa only [nnMetric_apply, coe_nndist, NNReal.coe_mul, dist_eq_norm, sub_zero,
        LinearMap.sub_apply] using hx)
    exact ⟨A + B, sub_add_cancel g B.toLinearMap⟩

end SphericallyCompleteSpace
