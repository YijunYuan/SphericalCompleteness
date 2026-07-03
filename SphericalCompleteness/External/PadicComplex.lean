/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.External.DenselyNormedField
public import SphericalCompleteness.External.PadicAlgCl
public import SphericalCompleteness.External.Ultrametric

/-!
# The field `ℂ_[p]`

Auxiliary results on the completed algebraic closure of the `p`-adic numbers.
-/

@[expose] public section

open PadicComplex
open TopologicalSpace

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The `p`-adic complex numbers `ℂ_[p]` form a densely normed field: their norm takes a dense set
of values, inherited from the completed algebraic closure of `ℚ_[p]`. -/
noncomputable instance instDenselyNormedFieldPadicComplex : DenselyNormedField ℂ_[p] :=
  inferInstance

/-- The `p`-adic complex numbers `ℂ_[p]` form a separable topological space. -/
instance instSeparableSpacePadicComplex : SeparableSpace ℂ_[p] := inferInstance

