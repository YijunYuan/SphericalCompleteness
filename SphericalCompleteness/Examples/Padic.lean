/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.Padics.ValuativeRel
public import SphericalCompleteness.Examples.Padic.ProperSpace
public import SphericalCompleteness.External.PadicComplex
public import SphericalCompleteness.Metric.Dense
public import SphericalCompleteness.Valuation.Normed

/-!
# Spherical completeness of the p-adic numbers and their completed algebraic closure

The norm, the multiplicative valuation, the additive valuation and the canonical valuative
relation on the p-adic numbers are spherically complete. The norm valuation on their completed
algebraic closure admits a nest with empty intersection.
-/

@[expose] public section

namespace SphericallyCompleteSpace

/--
For any prime `p`, the `p`-adic complex field `ℂ_[p]` is not spherically complete.

This is a direct specialization of
`not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric` to `ℂ_[p]`,
using the previously established instances showing that `ℂ_[p]` is ultrametric,
separable, and spherically dense in the required sense.
-/
theorem not_sphericallyCompleteSpace_padicComplex (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ¬ SphericallyCompleteSpace ℂ_[p] :=
  not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric ℂ_[p]

end SphericallyCompleteSpace

namespace Padic

variable {p : ℕ} [Fact p.Prime]

/-- The norm and the integer-valued multiplicative valuation give the same comparisons on ℚₚ. -/
theorem normedField_valuation_isEquiv_mulValuation :
    (NormedField.valuation (K := ℚ_[p])).IsEquiv mulValuation := by
  intro x y
  change ‖x‖ ≤ ‖y‖ ↔ _
  rw [← not_lt, ← not_lt (a := mulValuation y) (b := mulValuation x),
    norm_lt_norm_iff_mulValuation_lt]

/-- The multiplicative p-adic valuation is spherically complete. -/
instance isSphericallyComplete_mulValuation : (mulValuation (p := p)).IsSphericallyComplete :=
  normedField_valuation_isEquiv_mulValuation.isSphericallyComplete_iff.mp
    ((NormedField.valuation_isSphericallyComplete_iff _).mpr inferInstance)

/-- The canonical p-adic valuative relation is spherically complete. -/
instance isSphericallyComplete_valuativeRel : ValuativeRel.IsSphericallyComplete ℚ_[p] :=
  (Valuation.isSphericallyComplete_iff_valuativeRel mulValuation).mp inferInstance

/-- The additive p-adic valuation is spherically complete. -/
instance isSphericallyComplete_addValuation : (addValuation (p := p)).IsSphericallyComplete := by
  rw [AddValuation.isSphericallyComplete_iff_toValuation]
  have h : (mulValuation (p := p)).IsEquiv (AddValuation.toValuation addValuation) := by
    intro x y
    change mulValuation x ≤ mulValuation y ↔ addValuation y ≤ addValuation x
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy, hx, Padic.addValuation.apply hx]
    simp [Padic.mulValuation_toFun, hx, hy, Padic.addValuation.apply]
  exact h.isSphericallyComplete_iff.mp inferInstance

end Padic

/-- The valuation induced by the norm on ℂₚ admits a nest with empty intersection. -/
theorem PadicComplex.not_isSphericallyComplete_normedField_valuation
    (p : ℕ) [Fact p.Prime] :
    ¬ (NormedField.valuation (K := ℂ_[p])).IsSphericallyComplete :=
  fun h ↦ SphericallyCompleteSpace.not_sphericallyCompleteSpace_padicComplex p
    ((NormedField.valuation_isSphericallyComplete_iff _).mp h)

/-- The extended valuation on the completed algebraic closure of ℚₚ is not spherically complete. -/
theorem PadicComplex.not_isSphericallyComplete_valuation (p : ℕ) [Fact p.Prime] :
    ¬ (PadicComplex.valued p).v.IsSphericallyComplete := by
  have he : (NormedField.valuation (K := ℂ_[p])).IsEquiv (PadicComplex.valued p).v := by
    intro x y
    change ‖x‖ ≤ ‖y‖ ↔ _
    rw [PadicComplex.norm_eq_norm p x, PadicComplex.norm_eq_norm p y]
    simp only [Valuation.norm_def, NNReal.coe_le_coe,
      (Valuation.RankLeOne.strictMono' (v := (PadicComplex.valued p).v)).le_iff_le,
      Valuation.restrict_le_iff]
  exact fun h ↦ PadicComplex.not_isSphericallyComplete_normedField_valuation p
    (he.isSphericallyComplete_iff.mpr h)
