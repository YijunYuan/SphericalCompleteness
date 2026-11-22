/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.IsLUB
public import SphericalCompleteness.PseudoMetric.Sequence

/-!
# Spherical completeness of ordinary pseudometric spaces

`Metric.nnMetric X` bundles the usual nonnegative distance. Every set of nonnegative
real radii has a countable coinitial subset, so spherical completeness for this distance
is equivalent to the usual nested-sequence criterion.
-/

@[expose] public section

open Set Metric Filter
open scoped NNReal Topology

/--
A `PseudoMetricSpace` is *spherically complete* if every nested (antitone) sequence
of closed balls has nonempty intersection.

More precisely, given centers `ci : ℕ → α` and radii `ri : ℕ → NNReal`, if the family
of closed balls `i ↦ closedBall (ci i) (ri i)` is antitone with respect to inclusion
(i.e. the balls are decreasing as `i` increases), then the intersection
`⋂ i, closedBall (ci i) (ri i)` is nonempty.

This is a standard completeness-type axiom used in non-Archimedean/ultrametric settings,
but it is stated here for general pseudo-metric spaces.
-/
class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  nonempty_iInter_of_antitone : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty

namespace Metric

/-- The nonnegative distance of a pseudometric space as a bundled pseudometric. -/
def nnMetric (X : Type*) [PseudoMetricSpace X] : PseudoMetric X ℝ≥0 where
  toFun := nndist
  refl' := nndist_self
  symm' := nndist_comm
  triangle' := nndist_triangle

@[simp] theorem nnMetric_apply {X : Type*} [PseudoMetricSpace X] (x y : X) :
    nnMetric X x y = nndist x y := rfl

@[simp] theorem ball_nnMetric {X : Type*} [PseudoMetricSpace X] (c : X) (r : ℝ≥0) :
    (nnMetric X).closedBall c r = closedBall c r := by
  ext y
  exact dist_le_coe.symm

instance (X : Type*) [PseudoMetricSpace X] [IsUltrametricDist X] : (nnMetric X).IsUltra where
  le_sup' x y z := by exact_mod_cast IsUltrametricDist.dist_triangle_max x y z

/-- Choose radii coinitial in a nonempty set by approaching its infimum. -/
theorem exists_seq_le_of_nonempty_radii (s : Set ℝ≥0) (hs : s.Nonempty) :
    ∃ u : ℕ → s, ∀ r ∈ s, ∃ n, (u n).val ≤ r := by
  by_cases hm : sInf s ∈ s
  · exact ⟨fun _ ↦ ⟨_, hm⟩, fun r hr ↦ ⟨0, csInf_le' hr⟩⟩
  obtain ⟨f, _, ht, hf⟩ := exists_seq_tendsto_sInf hs (OrderBot.bddBelow _)
  refine ⟨fun n ↦ ⟨f n, hf n⟩, fun r hr ↦ ?_⟩
  have hlt : sInf s < r := lt_of_le_of_ne (csInf_le' hr) (fun h ↦ hm (h ▸ hr))
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hlt)).exists
  exact ⟨n, hn.le⟩

/-- The sequence criterion on a real-valued pseudometric space is equivalent to the
arbitrary-nest criterion for its bundled distance. -/
theorem sphericallyCompleteSpace_iff (X : Type*) [PseudoMetricSpace X] :
    SphericallyCompleteSpace X ↔ (nnMetric X).IsSphericallyComplete := by
  rw [(nnMetric X).isSphericallyComplete_iff_antitone_sequence
    (fun _ _ ↦ zero_le) exists_seq_le_of_nonempty_radii]
  simp only [ball_nnMetric]
  exact ⟨fun h _ _ _ ha ↦ h.nonempty_iInter_of_antitone ha,
    fun h ↦ ⟨fun {c r} ↦ h c r (fun _ ↦ zero_le)⟩⟩

instance (X : Type*) [PseudoMetricSpace X] [h : SphericallyCompleteSpace X] :
    (nnMetric X).IsSphericallyComplete := (sphericallyCompleteSpace_iff X).mp h

/-- A nonempty spherically complete subset of an ultrametric pseudometric space
contains a point nearest to any prescribed ambient point. -/
theorem exists_dist_le_of_sphericallyComplete {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X]
    (s : Set X) (hs : s.Nonempty) [SphericallyCompleteSpace s] (x : X) :
    ∃ y : s, ∀ z : s, dist x y ≤ dist x z := by
  have : ((nnMetric X).comap (Subtype.val : s → X)).IsSphericallyComplete :=
    (sphericallyCompleteSpace_iff s).mp inferInstance
  obtain ⟨y, hy⟩ := (nnMetric X).exists_bestApprox s hs x
  exact ⟨y, fun z ↦ NNReal.coe_le_coe.mpr (hy z)⟩

end Metric
