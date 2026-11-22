/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Examples.Padic
public import SphericalCompleteness.Metric.Basic
public import SphericalCompleteness.Metric.Dense
public import SphericalCompleteness.Metric.Extension
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Basic
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.HahnBanach
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Basic
public import SphericalCompleteness.PseudoMetric.SphericalCompletion
public import SphericalCompleteness.Valuation.Complete
public import SphericalCompleteness.Valuation.Module.FiniteDimensional
public import SphericalCompleteness.Valuation.Immediate
public import SphericalCompleteness.Valuation.Module.Extension
public import SphericalCompleteness.Valuation.Module.Quotient
public import SphericalCompleteness.Valuation.Normed
public import SphericalCompleteness.Valuation.Module.Operator
public import SphericalCompleteness.Valuation.Module.SphericalCompletion

/-!
# Spherical completeness

This is the root file of the `SphericalCompleteness` library, importing the whole development.

Spherical completeness is a strengthening of metric completeness adapted to the ultrametric
(non-Archimedean) setting: a space is spherically complete when every nested (antitone) family of
closed balls has nonempty intersection, regardless of whether the radii tend to zero. The library
develops this property for bundled pseudometrics, valued vector spaces and normed spaces.

## Main results

- `PseudoMetric.IsSphericallyComplete`: intersection of arbitrary nests for a bundled distance.
- `Metric.sphericallyCompleteSpace_iff`: the bridge to the real-valued sequence class
  `SphericallyCompleteSpace` used in the normed vector space files.
- `Valuation.IsSphericallyComplete`: spherical completeness of a valuation of arbitrary rank.
- `Valuation.IsEquiv.isSphericallyComplete_iff`: invariance under equivalent valuations.
- `PseudoMetric.exists_sphericallyComplete_immediate_extension` embeds a pseudoultrametric space
  in a spherically complete immediate extension, including when distinct points have distance zero.
- `PseudoMetric.exists_linearExtension_of_le_modulus` extends linear maps into a spherically
  complete target under a bound compatible with scalar multiplication.
- `Valuation.HasExtension.isSphericallyComplete` transports spherical completeness to a valuation
  on a finite-dimensional algebra over the base field.
- `PseudoMetric.exists_linearSphericalCompletion` gives an immediate linear spherical completion
  with the same distance values. `PseudoMetric.IsLinearSphericalCompletion.unique` identifies two
  such completions by a linear isometry over their common base.
- `Valuation.IsHomogeneous.exists_linearSphericalCompletion` preserves the scalar valuation.
- `SphericallyCompleteSpace.of_finiteDimensional`: a finite-dimensional
  ultrametric normed space over a spherically complete field is spherically complete.
- `SphericallyCompleteSpace.hahn_banach`: the non-Archimedean Hahn-Banach extension theorem.
- `SphericallyCompleteSpace.IsSphericalCompletion`: the class characterising a *spherical
  completion* of an ultrametric normed space `E` as a minimal spherically complete extension of `E`,
  shown to exist (`IsSphericalCompletion.exists_isSphericalCompletion`), to be unique up to linear
  isometry (`IsSphericalCompletion.unique`), and to satisfy a universal property
  (`IsSphericalCompletion.weak_universal_property`).
- `SphericallyCompleteSpace.iff_maximallyComplete`: spherical completeness is
  equivalent to admitting no proper immediate extension.
-/
