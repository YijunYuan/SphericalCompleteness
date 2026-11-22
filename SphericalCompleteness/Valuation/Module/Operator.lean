/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Module.Operator
public import SphericalCompleteness.Valuation.Module.Basic

/-!
# Operator balls over a valued division ring

The bound for an operator is a value-group element. Its closed balls have the nested
intersection property even when an individual operator has no least bound in that group.
-/

@[expose] public section

open Set

namespace Valuation

variable {K E F Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [LinearOrderedCommMonoidWithZero Γ] {v : Valuation K Γ}
    (d : PseudoMetric E (MaxTropical Γ)) (e : PseudoMetric F (MaxTropical Γ))

/-- The pointwise ball of valuative radius `C` about a linear operator. -/
def linearMapBall (C : Γ) (T : E →ₗ[K] F) : Set (E →ₗ[K] F) :=
  {g | ∀ x, MaxTropical.untrop (e (g x) (T x)) ≤ C * MaxTropical.untrop (d x 0)}

variable {d e} [d.IsAddInvariant] [e.IsAddInvariant] [e.IsSphericallyComplete]

/-- A nest of operator balls over a valued division ring has a common point if the codomain
is spherically complete. This holds for valuations of arbitrary rank. -/
theorem IsHomogeneous.isDescendingCompleteFamily_linearMapBalls
    (hd : v.IsHomogeneous d) (he : v.IsHomogeneous e) :
    {B | ∃ (C : Γ) (T : E →ₗ[K] F), B = linearMapBall d e C T}.IsDescendingCompleteFamily := by
  let φ (C : Γ) (r : MaxTropical Γ) := MaxTropical.trop (C * MaxTropical.untrop r)
  apply (d.isDescendingCompleteFamily_linearMapBalls (K := K) e (range φ) ?_ ?_ ?_).mono
  · rintro B ⟨C, T, rfl⟩
    exact ⟨φ C, mem_range_self C, T, rfl⟩
  · rintro _ ⟨C, rfl⟩ r s hrs
    exact mul_le_mul_right (show MaxTropical.untrop r ≤ MaxTropical.untrop s from hrs) C
  · rintro _ ⟨C, rfl⟩ _ ⟨D, rfl⟩ _
    exact (le_total C D).imp (fun h r ↦ mul_le_mul_left h (MaxTropical.untrop r))
      (fun h r ↦ mul_le_mul_left h (MaxTropical.untrop r))
  · rintro _ ⟨C, rfl⟩ a y x h
    change MaxTropical.untrop (e (a • y) 0) ≤ C * MaxTropical.untrop (d (a • x) 0)
    change MaxTropical.untrop (e y 0) ≤ C * MaxTropical.untrop (d x 0) at h
    rw [hd, he, mul_left_comm C]
    exact mul_le_mul_right h _

end Valuation
