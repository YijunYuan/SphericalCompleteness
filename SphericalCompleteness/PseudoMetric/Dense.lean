/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric
public import Mathlib.Order.Monotone.Basic

/-!
# An obstruction to spherical completeness

A countable cover by balls of radii `r (n + 1)` can be avoided one ball at a time if
every ball at level `r n` contains two points farther apart than `r (n + 1)`.
The resulting nest has empty intersection. The argument uses only comparisons of distances.
-/

@[expose] public section

namespace PseudoMetric

open Set

variable {X R : Type*} [Zero R] [Add R] [LinearOrder R] (d : PseudoMetric X R)

/-- A bundled pseudometric is spherically dense if, inside each ball of radius `r`,
distances exceed every nonnegative `s < r` while remaining at most `r`. -/
class IsSphericallyDense : Prop where
  /-- Every nonnegative lower bound below the radius can be exceeded inside the ball. -/
  exists_dist_mem_Ioc : ∀ (c : X) ⦃s r : R⦄, 0 ≤ s → s < r →
    ∃ x y, x ∈ d.closedBall c r ∧ y ∈ d.closedBall c r ∧ d x y ∈ Ioc s r

variable [d.IsUltra]

/-- A countable cover and splitting at successive radii obstruct spherical completeness.

At step `n`, the two separated points provide disjoint subballs of radius `r (n + 1)`.
At least one avoids the ball about `u n`. A point in every selected subball would
therefore lie outside the cover. -/
theorem not_isSphericallyComplete_of_splitting (u : ℕ → X) (r : ℕ → R)
    (hcover : ∀ x, ∃ n, x ∈ d.closedBall (u n) (r (n + 1)))
    (hsplit : ∀ n c, ∃ a ∈ d.closedBall c (r n), ∃ b ∈ d.closedBall c (r n),
      r (n + 1) < d a b) :
    ¬ d.IsSphericallyComplete := by
  classical
  have step (n : ℕ) (c : X) : ∃ c', d.closedBall c' (r (n + 1)) ⊆ d.closedBall c (r n) ∧
      u n ∉ d.closedBall c' (r (n + 1)) := by
    obtain ⟨a, ha, b, hb, hab⟩ := hsplit n c
    have hr : r (n + 1) ≤ r n := hab.le.trans <|
      (IsUltra.le_sup' (d := d) a c b).trans (max_le ha ((d.symm c b).trans_le hb))
    by_cases hua : u n ∈ d.closedBall a (r (n + 1))
    · refine ⟨b, d.closedBall_subset_of_mem hb hr, fun hub ↦ hab.not_ge ?_⟩
      exact (IsUltra.le_sup' (d := d) a (u n) b).trans (max_le ((d.symm a _).trans_le hua) hub)
    · exact ⟨a, d.closedBall_subset_of_mem ha hr, hua⟩
  let c : ℕ → X := Nat.rec (u 0) (fun n z ↦ (step n z).choose)
  let B (n : ℕ) := d.closedBall (c n) (r n)
  have anti : Antitone B :=
    antitone_nat_of_succ_le fun n ↦ (step n (c n)).choose_spec.1
  have hr (n : ℕ) : 0 ≤ r n := by
    obtain ⟨a, ha, _⟩ := hsplit n (c n)
    exact (d.nonneg_of_ultra a (c n)).trans ha
  intro h
  obtain ⟨x, hx⟩ := h.nonempty_iInter_of_antitone d c r hr anti
  obtain ⟨n, hn⟩ := hcover x
  have hxB := mem_iInter.mp hx (n + 1)
  apply (step n (c n)).choose_spec.2
  exact (IsUltra.le_sup' (d := d) (u n) x (c (n + 1))).trans <|
    max_le ((d.symm _ x).trans_le hn) hxB

/-- In a spherically dense ultrametric, a cover by balls from a strictly decreasing
sequence of nonnegative radii obstructs spherical completeness. -/
theorem not_isSphericallyComplete_of_isSphericallyDense [h : d.IsSphericallyDense]
    (u : ℕ → X) (r : ℕ → R) (hr : StrictAnti r) (hr₀ : ∀ n, 0 ≤ r n)
    (hcover : ∀ x, ∃ n, x ∈ d.closedBall (u n) (r (n + 1))) :
    ¬ d.IsSphericallyComplete := by
  apply d.not_isSphericallyComplete_of_splitting u r hcover
  intro n c
  obtain ⟨a, b, ha, hb, hab⟩ := h.exists_dist_mem_Ioc c (hr₀ (n + 1)) (hr (Nat.lt_succ_self n))
  exact ⟨a, ha, b, hb, hab.1⟩

end PseudoMetric
