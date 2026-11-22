/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import SphericalCompleteness.Metric.Seminormed.Basic
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.IsMOrtho
public import SphericalCompleteness.PseudoMetric.Compare
public import SphericalCompleteness.PseudoMetric.Module.FiniteDimensional

/-!
# Spherical completeness of normed vector spaces

This file establishes that finite-dimensional ultrametric normed spaces over a spherically
complete base field are spherically complete.

Each scalar line carries a rescaling of the scalar distance. The finite-dimensional theorem
then follows from the arbitrary-valued result for finitely generated subspaces.

## Main statements

* `SphericallyCompleteSpace.of_locallyCompactSpace`: a locally compact normed vector space over a
  nontrivially normed field is spherically complete.
* `SphericallyCompleteSpace.of_finiteDimensional`: a finite-dimensional
  ultrametric normed `𝕜`-vector space over a spherically complete normed field is
  spherically complete.
-/

@[expose] public section

open Metric

namespace Metric

variable {K E : Type*} [NormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]

/-- The parametrization of a scalar line preserves spherical completeness from the field,
also when its generator has seminorm zero. -/
theorem isSphericallyComplete_span_singleton [SphericallyCompleteSpace K] (x : E) :
    ((nnMetric E).comap ((↑) : (K ∙ x) → E)).IsSphericallyComplete := by
  rw [PseudoMetric.isSphericallyComplete_span_singleton_iff]
  have hdist (a b : K) : nndist (a • x) (b • x) = nndist a b * ‖x‖₊ := by
    rw [nnDist_eq_nnNorm, ← sub_smul, nnNorm_smul, ← nnDist_eq_nnNorm]
  by_cases hx : ‖x‖₊ = 0
  · apply PseudoMetric.isSphericallyComplete_of_forall_eq_zero
    intro a b
    exact (hdist a b).trans (by rw [hx, mul_zero])
  · apply PseudoMetric.IsSphericallyComplete.of_closedBalls_subset
      (d := nnMetric K) inferInstance
    rintro _ ⟨c, r, rfl⟩
    refine ⟨c, r / ‖x‖₊, Set.ext fun a ↦ ?_⟩
    change nndist (a • x) (c • x) ≤ r ↔ nndist a c ≤ r / ‖x‖₊
    rw [hdist, le_div_iff₀ (zero_lt_iff.mpr hx)]

end Metric

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
  have : ProperSpace E := ProperSpace.of_locallyCompactSpace 𝕜
  infer_instance

/--
Constructs a `SphericallyCompleteSpace` instance on the one-dimensional subspace
`Submodule.span 𝕜 {z}` (viewed as a subtype of `E`), assuming the scalar field `𝕜`
is spherically complete.

This is a convenience instance allowing downstream results to use spherical
completeness on the span of a single vector without explicitly transporting the
structure from `𝕜`.
-/
instance instSphericallyCompleteSpaceSpanSingleton (𝕜 : Type*) [NormedField 𝕜]
    [scsk : SphericallyCompleteSpace 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (z : E) : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) :=
  (sphericallyCompleteSpace_iff _).mpr (Metric.isSphericallyComplete_span_singleton (K := 𝕜) z)

/-- Every finite-dimensional ultrametric seminormed space over a spherically complete normed
field is spherically complete. This also applies to trivially normed fields. -/
theorem of_finiteDimensional (𝕜 : Type*) [NormedField 𝕜] [SphericallyCompleteSpace 𝕜]
    (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [IsUltrametricDist E] [FiniteDimensional 𝕜 E] : SphericallyCompleteSpace E :=
  (sphericallyCompleteSpace_iff E).mpr <|
    (nnMetric E).isSphericallyComplete_of_finiteDimensional
      (Metric.isSphericallyComplete_span_singleton (K := 𝕜))

end SphericallyCompleteSpace
