/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import SphericalCompleteness.Metric.Defs
public import SphericalCompleteness.Valuation.Basic

/-!
# Norms and valuations

An ultrametric norm and its associated valuation have equivalent spherical completeness
predicates. The same holds for a rank-one valuation and its induced norm.
-/

@[expose] public section

open scoped NNReal

/-- The valuation supplied by an ultrametric norm has the same closed balls. -/
theorem NormedField.valuation_isSphericallyComplete_iff (K : Type*) [NormedField K]
    [IsUltrametricDist K] :
    (NormedField.valuation (K := K)).IsSphericallyComplete ↔ SphericallyCompleteSpace K := by
  rw [Metric.sphericallyCompleteSpace_iff]
  apply PseudoMetric.isSphericallyComplete_iff_of_le_iff
  intro x c y
  change ‖x - c‖₊ ≤ ‖y - c‖₊ ↔ nndist x c ≤ nndist y c
  rw [nnDist_eq_nnNorm, nnDist_eq_nnNorm]

open scoped Valued in
/-- The norm induced by a rank-one valuation preserves spherical completeness. -/
theorem Valued.isSphericallyComplete_iff_toNormedField
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀] [v : Valued K Γ₀]
    [Valuation.RankOne v.v] :
    v.v.IsSphericallyComplete ↔ SphericallyCompleteSpace K := by
  have h : (NormedField.valuation (K := K)).IsEquiv v.v := by
    intro x y
    exact Valued.toNormedField.norm_le_iff
  exact h.isSphericallyComplete_iff.symm.trans (NormedField.valuation_isSphericallyComplete_iff K)
