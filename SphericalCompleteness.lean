/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Basic
public import SphericalCompleteness.Defs
public import SphericalCompleteness.Dense
public import SphericalCompleteness.External.Complete
public import SphericalCompleteness.External.DenselyNormedField
public import SphericalCompleteness.External.PadicAlgCl
public import SphericalCompleteness.External.PadicComplex
public import SphericalCompleteness.External.Sequence
public import SphericalCompleteness.External.Submodule
public import SphericalCompleteness.External.Ultrametric
public import SphericalCompleteness.NormedVectorSpace.Basic
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Basic
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.HahnBanach
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Extension
public import SphericalCompleteness.NormedVectorSpace.Immediate
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.Basic
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.Defs
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.IsMOrtho
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp
public import SphericalCompleteness.NormedVectorSpace.Quotient
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Basic
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.Defs
public import SphericalCompleteness.NormedVectorSpace.SphericalCompletion.LpQuotient

/-!
# Spherical completeness

This is the root file of the `SphericalCompleteness` library, importing the whole development.

Spherical completeness is a strengthening of metric completeness adapted to the ultrametric
(non-Archimedean) setting: a space is spherically complete when every nested (antitone) family of
closed balls has nonempty intersection, regardless of whether the radii tend to zero. The library
develops the theory over nontrivially normed fields and normed vector spaces, culminating in the
construction and universal property of the spherical completion.

## Main results

- `SphericallyCompleteSpace`: the class of spherically complete pseudometric spaces.
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
