/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Group.Basic
public import SphericalCompleteness.PseudoMetric

/-! # Translation-invariant bundled pseudometrics on additive groups -/

@[expose] public section

namespace PseudoMetric

variable {E Γ : Type*} [Zero Γ] [Add Γ] [LE Γ] (d : PseudoMetric E Γ)

/-- Translating both arguments by the same vector preserves distance. -/
class IsAddInvariant [Add E] : Prop where
  add_right : ∀ x y a : E, d (x + a) (y + a) = d x y

variable [AddGroup E]

theorem sub_zero_eq [d.IsAddInvariant] (x y : E) : d (x - y) 0 = d x y := by
  simpa only [sub_add_cancel, zero_add] using
    (IsAddInvariant.add_right (d := d) (x - y) 0 y).symm

theorem sub_right_eq [d.IsAddInvariant] (x y a : E) : d (x - a) (y - a) = d x y := by
  simpa only [sub_eq_add_neg] using IsAddInvariant.add_right (d := d) x y (-a)

end PseudoMetric
