/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.AddGroup.Basic
public import SphericalCompleteness.PseudoMetric.Immediate

/-!
# A cardinal bound for immediate additive extensions

In a fixed closed ball of positive radius, its open subballs can be distinguished by points
of the immediate source after translation by a common center. Recording one such label at
every radius distinguishes points at positive distance. An extra source coordinate distinguishes
points at distance zero, so the bound also holds without a separation axiom.
-/

@[expose] public section

open Set Function

namespace PseudoMetric

/-- An immediate extension in a translation-invariant pseudoultrametric group has cardinal at
most that of `E × (Γ → E)` when the source image contains zero. -/
theorem IsImmediate.exists_injective_prod_fun {E F Γ : Type*} [AddCommGroup F]
    [Zero Γ] [Add Γ] [LinearOrder Γ] (d : PseudoMetric F Γ) [d.IsUltra] [d.IsAddInvariant]
    {i : E → F} (hi : d.IsImmediate i) (h0 : (0 : F) ∈ range i) :
    ∃ f : F → E × (Γ → E), Injective f := by
  classical
  obtain ⟨o, ho⟩ := h0
  let center (B : Set F) := if h : B.Nonempty then h.some else 0
  have center_mem (x : F) {r : Γ} (hr : 0 ≤ r) : center (d.closedBall x r) ∈ d.closedBall x r := by
    have h : (d.closedBall x r).Nonempty := d.nonempty_closedBall.mpr hr
    simpa only [center, dite_eq_left h] using h.some_mem
  have residual_le (x : F) {r : Γ} (hr : 0 ≤ r) :
      d (x - center (d.closedBall x r)) 0 ≤ r := by
    rw [d.sub_zero_eq, d.symm]
    exact center_mem x hr
  -- The radius-zero coordinate must recover the residual exactly.
  have recover (x : F) : ∃ u, i u = x - center (d.closedBall x 0) := by
    by_contra h
    obtain ⟨u, hu⟩ := (hi _ h).2 o
    rw [ho] at hu
    exact (hu.trans_le (residual_le x le_rfl)).not_ge (d.nonneg_of_ultra _ _)
  choose zeroLabel hzero using recover
  have approximate (x : F) (r : Γ) : ∃ u, 0 < r → d (x - center (d.closedBall x r)) (i u) < r := by
    let z := x - center (d.closedBall x r)
    by_cases hr : 0 < r
    · by_cases h : z ∈ range i
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ ↦ by change d z (i u) < r; rwa [hu, d.refl]⟩
      · obtain ⟨u, hu⟩ := (hi z h).2 o
        rw [ho] at hu
        exact ⟨u, fun _ ↦ hu.trans_le (residual_le x hr.le)⟩
    · exact ⟨o, fun h ↦ (hr h).elim⟩
  choose label hlabel using approximate
  refine ⟨fun x ↦ (zeroLabel x, label x), fun x y heq ↦ ?_⟩
  rcases (d.nonneg_of_ultra x y).lt_or_eq with hpos | hzeroDist
  · let r := d x y
    have hball : d.closedBall x r = d.closedBall y r := d.closedBall_eq_of_mem le_rfl
    have hlabels : label x r = label y r := congrFun (congrArg Prod.snd heq) r
    have hx := hlabel x r hpos
    rw [hball, hlabels] at hx
    have hy := hlabel y r hpos
    have hlt := (IsUltra.le_sup' (d := d) (x - center (d.closedBall y r)) (i (label y r))
      (y - center (d.closedBall y r))).trans_lt (max_lt hx ((d.symm _ _).trans_lt hy))
    rw [d.sub_right_eq] at hlt
    exact (lt_irrefl r hlt).elim
  · have hball : d.closedBall x 0 = d.closedBall y 0 := d.closedBall_eq_of_mem hzeroDist.ge
    have h := congrArg i (congrArg Prod.fst heq)
    rw [hzero, hzero, hball] at h
    exact sub_left_inj.mp h

end PseudoMetric
