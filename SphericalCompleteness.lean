/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Examples.Padic
public import SphericalCompleteness.Metric.Basic
public import SphericalCompleteness.Metric.Dense
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Basic
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.HahnBanach
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Basic
public import SphericalCompleteness.Valuation.Complete
public import SphericalCompleteness.Valuation.Normed

/-!
# Spherical completeness

This is the root file of the `SphericalCompleteness` library, importing the whole development.

Spherical completeness is a strengthening of metric completeness adapted to the ultrametric
(non-Archimedean) setting: a space is spherically complete when every nested (antitone) family of
closed balls has nonempty intersection, regardless of whether the radii tend to zero. The library
develops the theory over nontrivially normed fields and normed vector spaces, culminating in the
construction and universal property of the spherical completion.

## Main results

- `PseudoMetric.IsSphericallyComplete`: intersection of arbitrary nests for a bundled distance.
- `Metric.sphericallyCompleteSpace_iff`: the bridge to the real-valued sequence class
  `SphericallyCompleteSpace` used in the normed vector space files.
- `Valuation.IsSphericallyComplete`: spherical completeness of a valuation of arbitrary rank.
- `Valuation.IsEquiv.isSphericallyComplete_iff`: invariance under equivalent valuations.
- `SphericallyCompleteSpace.of_finiteDimensional`: a finite-dimensional
  ultrametric normed space over a spherically complete field is spherically complete.
- `SphericallyCompleteSpace.hahn_banach`: the non-Archimedean Hahn-Banach extension theorem.
- `SphericallyCompleteSpace.IsSphericalCompletion`: the class characterising a *spherical
  completion* of an ultrametric normed space `E` as a minimal spherically complete extension of `E`,
  shown to exist (`IsSphericalCompletion.exists_isSphericalCompletion`), to be unique up to linear
  isometry (`IsSphericalCompletion.unique`), and to satisfy a universal property
  (`IsSphericalCompletion.universal_property`).
- `SphericallyCompleteSpace.iff_maximallyComplete`: spherical completeness is
  equivalent to admitting no proper immediate extension.
-/
