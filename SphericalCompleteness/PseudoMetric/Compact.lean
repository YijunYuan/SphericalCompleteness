/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.Compactness.Compact
public import SphericalCompleteness.PseudoMetric

/-!
# Spherical completeness from compact closed balls

The topology witnessing compactness and closedness can be chosen independently
of the value type of the pseudometric.
-/

@[expose] public section

open Set

/-- A nest of nonempty compact closed sets in a topological space has a common point. -/
theorem Set.IsDescendingCompleteFamily.of_isCompact_isClosed {X : Type*} [TopologicalSpace X]
    {balls : Set (Set X)} (hcompact : ∀ B ∈ balls, IsCompact B)
    (hclosed : ∀ B ∈ balls, IsClosed B) : balls.IsDescendingCompleteFamily := by
  intro S hS hne hn hc
  have : Nonempty S := hne.to_subtype
  have hdesc : IsChain (· ⊇ ·) S := hc.symm
  exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdesc.directedOn hn
    (fun B hB ↦ hcompact B (hS hB)) (fun B hB ↦ hclosed B (hS hB))

/-- If every closed ball of a bundled pseudometric is compact and closed in the given
topology, the pseudometric is spherically complete. -/
theorem PseudoMetric.IsSphericallyComplete.of_isCompact_closedBall {X R : Type*}
    [TopologicalSpace X] [Zero R] [Add R] [LE R] (d : PseudoMetric X R)
    (hcompact : ∀ c r, IsCompact (d.closedBall c r))
    (hclosed : ∀ c r, IsClosed (d.closedBall c r)) : d.IsSphericallyComplete where
  nonempty_sInter := .of_isCompact_isClosed
    (by rintro _ ⟨c, r, rfl⟩; exact hcompact c r)
    (by rintro _ ⟨c, r, rfl⟩; exact hclosed c r)
