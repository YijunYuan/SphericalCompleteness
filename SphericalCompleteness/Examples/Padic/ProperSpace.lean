/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import SphericalCompleteness.Metric.Basic

/-!
# Spherical completeness of the p-adic metric
-/

@[expose] public section

namespace SphericallyCompleteSpace

/-- For a prime `p`, the field of `p`-adic numbers `ℚ_[p]` is spherically complete. `ℚ_[p]` is
locally compact, hence proper, so its closed balls are compact and spherical completeness follows
from `instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpacePadic {p : ℕ} [Fact (Nat.Prime p)] :
    SphericallyCompleteSpace (ℚ_[p]) := inferInstance

end SphericallyCompleteSpace
