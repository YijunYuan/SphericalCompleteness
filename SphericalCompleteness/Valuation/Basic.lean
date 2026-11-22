/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.RingTheory.Valuation.Quotient
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import SphericalCompleteness.PseudoMetric.Compare
public import SphericalCompleteness.PseudoMetric.Constructions

/-!
# Spherical completeness of valuations

A multiplicative valuation gives an ultrapseudometric with values in its max-tropical codomain.
The intersection property for its balls depends only on the equivalence class of the valuation.
-/

@[expose] public section

open Set

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- The ultrapseudometric whose distances are the valuations of differences. -/
def toPseudoMetric (v : Valuation R Γ₀) : PseudoMetric R (MaxTropical Γ₀) where
  toFun x y := MaxTropical.trop (v (x - y))
  refl' x := by
    change MaxTropical.trop _ = MaxTropical.trop (⊥ : Γ₀)
    rw [sub_self, map_zero, bot_eq_zero]
  symm' x y := congrArg _ (v.map_sub_swap x y)
  triangle' x y z := by
    change v (x - z) ≤ max (v (x - y)) (v (y - z))
    simpa only [sub_add_sub_cancel] using v.map_add (x - y) (y - z)

@[simp] theorem toPseudoMetric_apply (v : Valuation R Γ₀) (x y : R) :
    v.toPseudoMetric x y = MaxTropical.trop (v (x - y)) := rfl

/-- A closed valuation ball consists of the points at valuation at most its radius. -/
@[simp] theorem toPseudoMetric_closedBall (v : Valuation R Γ₀) (c : R) (r : Γ₀) :
    v.toPseudoMetric.closedBall c (MaxTropical.trop r) = {x | v (x - c) ≤ r} := rfl

/-- Every nonempty nest of valuation balls has a common point. -/
abbrev IsSphericallyComplete (v : Valuation R Γ₀) := v.toPseudoMetric.IsSphericallyComplete

end Valuation

/-- Tropical addition gives the strong triangle inequality for every such pseudometric. -/
instance PseudoMetric.isUltra_maxTropical {X Γ : Type*} [LinearOrder Γ] [OrderBot Γ]
    (d : PseudoMetric X (MaxTropical Γ)) : d.IsUltra := ⟨d.triangle⟩

/-- Spherical completeness for the canonical valuation of a valuative relation. -/
abbrev ValuativeRel.IsSphericallyComplete (R : Type*) [Ring R] [ValuativeRel R] :=
  (ValuativeRel.valuation R).IsSphericallyComplete

/-- The radius-zero ball is the translate of the valuation's support. -/
theorem Valuation.mem_closedBall_zero_iff_sub_mem_supp
    {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) (c x : R) :
    x ∈ v.toPseudoMetric.closedBall c (MaxTropical.trop 0) ↔ x - c ∈ v.supp := by
  change v (x - c) ≤ 0 ↔ _
  simp [Valuation.mem_supp_iff]

/-- Equivalent valuations have the same balls of realized radius. -/
theorem Valuation.IsEquiv.isSphericallyComplete_iff
    {R Γ₀ Γ₁ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
    [LinearOrderedCommMonoidWithZero Γ₁] {v : Valuation R Γ₀} {w : Valuation R Γ₁}
    (h : v.IsEquiv w) : v.IsSphericallyComplete ↔ w.IsSphericallyComplete := by
  apply PseudoMetric.isSphericallyComplete_iff_of_le_iff
  exact fun x c y ↦ h (x - c) (y - c)

/-- A compatible representative computes spherical completeness of the valuative relation. -/
theorem Valuation.isSphericallyComplete_iff_valuativeRel
    {R Γ₀ : Type*} [Ring R] [ValuativeRel R] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] :
    v.IsSphericallyComplete ↔ ValuativeRel.IsSphericallyComplete R :=
  ((Valuation.compatible_iff_isEquiv v).mp inferInstance).isSphericallyComplete_iff

/-- A surjective ring map preserves and reflects spherical completeness of the pulled-back
valuation. -/
theorem Valuation.isSphericallyComplete_comap_iff {R S Γ₀ : Type*} [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation S Γ₀) (f : R →+* S)
    (hf : Function.Surjective f) : (v.comap f).IsSphericallyComplete ↔ v.IsSphericallyComplete := by
  apply PseudoMetric.isSphericallyComplete_iff_of_surjective _ _ hf
  intro x y
  change MaxTropical.trop (v (f x - f y)) = MaxTropical.trop (v (f (x - y)))
  rw [_root_.map_sub f]

/-- Quotienting by an ideal contained in the support preserves spherical completeness.
In particular this applies to the quotient by the entire support. -/
theorem Valuation.isSphericallyComplete_onQuot_iff {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) {I : Ideal R} (hI : I ≤ v.supp) :
    (v.onQuot hI).IsSphericallyComplete ↔ v.IsSphericallyComplete := by
  simpa using ((v.onQuot hI).isSphericallyComplete_comap_iff (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective).symm

namespace AddValuation

variable {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]

/-- The pseudometric of an additive valuation, with reversed order on its radii. -/
def toPseudoMetric (v : AddValuation R Γ) : PseudoMetric R (MaxTropical Γᵒᵈ) :=
  (toValuation v).toPseudoMetric

@[simp] theorem toPseudoMetric_apply (v : AddValuation R Γ) (x y : R) :
    v.toPseudoMetric x y = MaxTropical.trop (OrderDual.toDual (v (x - y))) := rfl

@[simp] theorem toPseudoMetric_closedBall (v : AddValuation R Γ) (c : R) (r : Γ) :
    v.toPseudoMetric.closedBall c (MaxTropical.trop (OrderDual.toDual r)) =
      {x | r ≤ v (x - c)} := rfl

/-- Every nonempty nest of additive valuation balls has a common point. -/
abbrev IsSphericallyComplete (v : AddValuation R Γ) := v.toPseudoMetric.IsSphericallyComplete

/-- Changing an additive valuation to multiplicative notation preserves spherical completeness. -/
theorem isSphericallyComplete_iff_toValuation (v : AddValuation R Γ) :
    v.IsSphericallyComplete ↔ (toValuation v).IsSphericallyComplete := Iff.rfl

end AddValuation
