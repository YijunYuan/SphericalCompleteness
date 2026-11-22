/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric

/-!
# Changing the value type of an ultrametric

The relative order of distances from each center determines its realized balls, and hence
its spherical completeness. The two value types can have different unrealized radii.
-/

@[expose] public section

namespace PseudoMetric

variable {X Γ Δ : Type*} [Zero Γ] [Add Γ] [Zero Δ] [Add Δ]

/-- If each ball of the second distance is a ball of the first, spherical completeness transfers.
This also applies to distances with different value types. -/
theorem IsSphericallyComplete.of_closedBalls_subset [LE Γ] [LE Δ] {d : PseudoMetric X Γ}
    (hd : d.IsSphericallyComplete) (e : PseudoMetric X Δ) (h : e.closedBalls ⊆ d.closedBalls) :
    e.IsSphericallyComplete := ⟨hd.nonempty_sInter.mono h⟩

/-- A pseudometric identically equal to zero is spherically complete. -/
theorem isSphericallyComplete_of_forall_eq_zero [LE Γ] (d : PseudoMetric X Γ)
    (hd : ∀ x y, d x y = 0) : d.IsSphericallyComplete where
  nonempty_sInter S hS hne hn _ := by
    obtain ⟨B, hB⟩ := hne
    obtain ⟨x, _⟩ := hn B hB
    refine ⟨x, Set.mem_sInter.mpr fun C hC ↦ ?_⟩
    obtain ⟨y, hy⟩ := hn C hC
    obtain ⟨c, r, rfl⟩ := hS hC
    simpa only [mem_closedBall, hd] using hy

/-- Distances that give the same comparisons at each center have identical realized balls. -/
theorem realizedBalls_eq_of_le_iff [LE Γ] [LE Δ] (d : PseudoMetric X Γ) (e : PseudoMetric X Δ)
    (h : ∀ x c y, d x c ≤ d y c ↔ e x c ≤ e y c) :
    d.realizedBalls = e.realizedBalls := by
  have hb (c y : X) : d.closedBall c (d y c) = e.closedBall c (e y c) :=
    Set.ext fun x ↦ h x c y
  ext B
  exact ⟨fun ⟨c, y, eq⟩ ↦ ⟨c, y, eq.trans (hb c y)⟩,
    fun ⟨c, y, eq⟩ ↦ ⟨c, y, eq.trans (hb c y).symm⟩⟩

/-- Spherical completeness is invariant under replacing ultrametric distances by ones
with the same ordering of distances to each center. -/
theorem isSphericallyComplete_iff_of_le_iff [LinearOrder Γ] [LinearOrder Δ]
    (d : PseudoMetric X Γ) (e : PseudoMetric X Δ) [d.IsUltra] [e.IsUltra]
    (h : ∀ x c y, d x c ≤ d y c ↔ e x c ≤ e y c) :
    d.IsSphericallyComplete ↔ e.IsSphericallyComplete := by
  rw [d.isSphericallyComplete_iff_realized, e.isSphericallyComplete_iff_realized,
    d.realizedBalls_eq_of_le_iff e h]

end PseudoMetric
