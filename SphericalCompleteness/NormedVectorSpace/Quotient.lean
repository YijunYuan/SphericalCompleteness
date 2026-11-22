/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.External.Ultrametric.NormedSpace
public import SphericalCompleteness.Metric.Basic
public import SphericalCompleteness.Metric.Seminormed.Quotient

/-!
# Spherical completeness of quotients of normed spaces

The quotient seminorm is the one on the additive quotient by the underlying subgroup.
-/

@[expose] public section

/-- The quotient of a spherically complete ultrametric seminormed space by any submodule
is spherically complete. -/
theorem Quotient.sphericallyCompleteSpace (𝕜 : Type*) [NormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [iud : IsUltrametricDist E] [scsk : SphericallyCompleteSpace E] {F : Submodule 𝕜 E} :
    SphericallyCompleteSpace (E ⧸ F) :=
  QuotientAddGroup.sphericallyCompleteSpace F.toAddSubgroup
