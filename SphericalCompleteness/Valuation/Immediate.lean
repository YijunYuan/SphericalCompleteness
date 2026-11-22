/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import SphericalCompleteness.PseudoMetric.Immediate
public import SphericalCompleteness.Valuation.Basic

/-! # The strict approximation criterion for immediate valued extensions -/

@[expose] public section

namespace Valuation

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A] [LinearOrderedCommMonoidWithZero Γ]
    (w : Valuation A Γ)

/-- An algebra extension is immediate for its valuative distance exactly when every element
outside the scalar image can be approximated strictly better than by zero. -/
theorem isImmediate_algebraMap_iff :
    w.toPseudoMetric.IsImmediate (algebraMap K A) ↔
      ∀ x ∉ Set.range (algebraMap K A), ∃ a : K, w (x - algebraMap K A a) < w x := by
  constructor
  · intro h x hx
    obtain ⟨a, ha⟩ := (h x hx).2 0
    change w (x - algebraMap K A a) < w (x - algebraMap K A 0) at ha
    exact ⟨a, by simpa only [_root_.map_zero, sub_zero] using ha⟩
  · intro h x hx
    refine ⟨inferInstance, fun b ↦ ?_⟩
    have hn : x - algebraMap K A b ∉ Set.range (algebraMap K A) := by
      rintro ⟨c, hc⟩
      exact hx ⟨c + b, by rw [_root_.map_add, hc, sub_add_cancel]⟩
    obtain ⟨a, ha⟩ := h _ hn
    refine ⟨b + a, ?_⟩
    change w (x - algebraMap K A (b + a)) < w (x - algebraMap K A b)
    rwa [_root_.map_add (algebraMap K A), ← sub_sub]

/-- A spherically complete valued field has no proper immediate valued algebra extension.
Equivalent presentations of the scalar valuation may use different value monoids. -/
theorem HasExtension.surjective_algebraMap_of_isImmediate
    {Δ : Type*} [LinearOrderedCommMonoidWithZero Δ] (v : Valuation K Δ) [v.HasExtension w]
    (hv : v.IsSphericallyComplete) (hi : w.toPseudoMetric.IsImmediate (algebraMap K A)) :
    Function.Surjective (algebraMap K A) := by
  have : (w.comap (algebraMap K A)).IsSphericallyComplete :=
    (val_isEquiv_comap (vR := v) (vA := w)).isSphericallyComplete_iff.mp hv
  apply hi.surjective (w.comap (algebraMap K A)).toPseudoMetric w.toPseudoMetric
  intro a b
  change MaxTropical.trop (w (algebraMap K A a - algebraMap K A b)) =
    MaxTropical.trop (w (algebraMap K A (a - b)))
  rw [_root_.map_sub (algebraMap K A)]

end Valuation
