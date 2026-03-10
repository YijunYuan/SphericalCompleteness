import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.Normed.Group.Ultra
import SphericalCompleteness.Dense

/-
# Miscellaneous code snippets (Not a part of the main library)
This file contains some code snippets that appear in the paper. It is not intended to be a part of
the main library, and it `includes an error intendedly` to illustrate the inconsistency of the
norms on `ℂ_[p]`.
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

-- Embedding the algebraic closure of `ℚ` into the algebraic closure of `ℚ_[p]` by the universal
-- property of algebraic closures.
#check (Set.range <| @IsAlgClosed.lift (PadicAlgCl p) _ _ ℚ _ _ (AlgebraicClosure ℚ) _ _ _ _ _ _ _)

open SphericallyCompleteSpace
open IsUltrametricDist
-- This will cause an error due to the inconsistency of the norms on `ℂ_[p]`, which should be
-- coincide.
#check @not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric (ℂ_[p]) inferInstance (isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p))
