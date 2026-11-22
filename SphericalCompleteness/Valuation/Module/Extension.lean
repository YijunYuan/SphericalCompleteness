/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.Extension
public import SphericalCompleteness.Valuation.Module.Basic

/-!
# Hahn–Banach over a valued division ring

A bound by a constant in the value monoid is preserved under linear extension to the
whole space when the target is spherically complete. The seminorms may have kernels.
-/

@[expose] public section

namespace Valuation

variable {K E F Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [LinearOrderedCommMonoidWithZero Γ] {v : Valuation K Γ}
    {d : PseudoMetric E (MaxTropical Γ)} {e : PseudoMetric F (MaxTropical Γ)}
    [d.IsAddInvariant] [e.IsAddInvariant]

/-- Extend a linear map with its prescribed valuative bound, including bound zero. -/
theorem IsHomogeneous.exists_linearExtension (hd : v.IsHomogeneous d) (he : v.IsHomogeneous e)
    [e.IsSphericallyComplete] (C : Γ) (D : Submodule K E) (f : D →ₗ[K] F)
    (hf : ∀ x : D, MaxTropical.untrop (e (f x) 0) ≤ C * MaxTropical.untrop (d x 0)) :
    ∃ g : E →ₗ[K] F, (∀ x : D, g x = f x) ∧
      ∀ x, MaxTropical.untrop (e (g x) 0) ≤ C * MaxTropical.untrop (d x 0) := by
  let φ (r : MaxTropical Γ) := MaxTropical.trop (C * MaxTropical.untrop r)
  apply d.exists_linearExtension_of_le_modulus e φ _ _ D f hf
  · exact fun a b h ↦ mul_le_mul_right (show MaxTropical.untrop a ≤ MaxTropical.untrop b from h) C
  · intro a y x h
    change MaxTropical.untrop (e (a • y) 0) ≤ C * MaxTropical.untrop (d (a • x) 0)
    change MaxTropical.untrop (e y 0) ≤ C * MaxTropical.untrop (d x 0) at h
    rw [hd, he, mul_left_comm C]
    exact mul_le_mul_right h _

/-- A linear form dominated by a valuative seminorm extends over a spherically complete
valued division ring with the same bound. -/
theorem IsHomogeneous.exists_linearForm_extension (hd : v.IsHomogeneous d)
    [v.IsSphericallyComplete] (C : Γ) (D : Submodule K E) (f : D →ₗ[K] K)
    (hf : ∀ x : D, v (f x) ≤ C * MaxTropical.untrop (d x 0)) :
    ∃ g : E →ₗ[K] K, (∀ x : D, g x = f x) ∧ ∀ x, v (g x) ≤ C * MaxTropical.untrop (d x 0) := by
  simpa only [toPseudoMetric_apply, sub_zero, MaxTropical.untrop_trop] using
    hd.exists_linearExtension v.isHomogeneous_self C D f (by
      simpa only [toPseudoMetric_apply, sub_zero, MaxTropical.untrop_trop] using hf)

end Valuation
