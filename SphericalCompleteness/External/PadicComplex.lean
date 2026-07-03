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

noncomputable instance instDenselyNormedFieldPadicComplex : DenselyNormedField ℂ_[p] :=
  inferInstance

instance instSeparableSpacePadicComplex : SeparableSpace ℂ_[p] := inferInstance

