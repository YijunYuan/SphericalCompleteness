/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import SphericalCompleteness.External.PadicAlgCl
import SphericalCompleteness.External.DenselyNormedField
import SphericalCompleteness.External.Ultrametric

/-!
# The field `ℂ_[p]`

Auxiliary results on the completed algebraic closure of the `p`-adic numbers.
-/

open PadicComplex
open TopologicalSpace

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable instance instDenselyNormedFieldPadicComplex : DenselyNormedField ℂ_[p] :=
  inferInstance

instance instSeparableSpacePadicComplex : SeparableSpace ℂ_[p] := inferInstance

instance : @IsUltrametricDist ℂ_[p] UniformSpace.Completion.instMetricSpace.toDist := inferInstance
