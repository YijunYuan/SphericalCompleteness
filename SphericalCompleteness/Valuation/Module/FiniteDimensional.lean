/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import SphericalCompleteness.PseudoMetric.Module.FiniteDimensional
public import SphericalCompleteness.Valuation.Module.Basic

/-!
# Spherical completeness in finite-dimensional valued algebras

A valuation on a finite-dimensional algebra over a field is spherically complete whenever
its restriction to the field is. The valuation may have arbitrary rank and nonzero support.
-/

@[expose] public section

namespace Valuation

variable {K E Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [LinearOrderedCommMonoidWithZero Γ] {v : Valuation K Γ} {d : PseudoMetric E (MaxTropical Γ)}
    [d.IsAddInvariant]

/-- Each scalar line of a homogeneous pseudometric over a spherically complete valued field
is spherically complete, including lines of zero pseudodiameter. -/
theorem IsHomogeneous.isSphericallyComplete_span_singleton
    (hd : v.IsHomogeneous d) (hv : v.IsSphericallyComplete) (x : E) :
    (d.comap ((↑) : (K ∙ x) → E)).IsSphericallyComplete := by
  rw [PseudoMetric.isSphericallyComplete_span_singleton_iff]
  by_cases hx : MaxTropical.untrop (d x 0) = 0
  · apply PseudoMetric.isSphericallyComplete_of_forall_eq_zero
    intro a b
    apply MaxTropical.untrop_injective
    change MaxTropical.untrop (d (a • x) (b • x)) = ⊥
    rw [hd.dist_smul, hx, mul_zero, bot_eq_zero]
  · apply (PseudoMetric.isSphericallyComplete_iff_of_le_iff v.toPseudoMetric _ ?_).mp hv
    intro a b c
    change v (a - b) ≤ v (c - b) ↔
      MaxTropical.untrop (d (a • x) (b • x)) ≤ MaxTropical.untrop (d (c • x) (b • x))
    rw [hd.dist_smul, hd.dist_smul, mul_le_mul_iff_left₀ (zero_lt_iff.mpr hx)]

/-- Finite-dimensional valued vector spaces over a spherically complete valued division ring
are spherically complete. Distinct vectors may have distance zero. -/
theorem IsHomogeneous.isSphericallyComplete_of_finiteDimensional [Module.Finite K E]
    (hd : v.IsHomogeneous d) (hv : v.IsSphericallyComplete) : d.IsSphericallyComplete := by
  let := hd.isSMulMono
  exact d.isSphericallyComplete_of_finiteDimensional (hd.isSphericallyComplete_span_singleton hv)

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] (w : Valuation A Γ)

/-- A valuation on a finite-dimensional algebra over a spherically complete valued field
is spherically complete, for any linearly ordered value group with zero. -/
theorem isSphericallyComplete_of_finiteDimensional [Module.Finite k A]
    (h : (w.comap (algebraMap k A)).IsSphericallyComplete) : w.IsSphericallyComplete :=
  w.isHomogeneous_comap.isSphericallyComplete_of_finiteDimensional h

/-- A finite-dimensional extension stays spherically complete even when the two valuations
are presented in different value monoids. -/
theorem HasExtension.isSphericallyComplete [Module.Finite k A]
    {Δ : Type*} [LinearOrderedCommMonoidWithZero Δ] (v : Valuation k Δ) [v.HasExtension w]
    (h : v.IsSphericallyComplete) : w.IsSphericallyComplete :=
  w.isSphericallyComplete_of_finiteDimensional <|
    (val_isEquiv_comap (vR := v) (vA := w)).isSphericallyComplete_iff.mp h

end Valuation
