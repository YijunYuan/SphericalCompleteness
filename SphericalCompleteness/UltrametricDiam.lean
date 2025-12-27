import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Metric
open NNReal

theorem diam_le_radius_of_ultrametric {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α]
(z : α) (r : ℝ≥0) :
diam (closedBall z r) ≤ r := by
  apply diam_le_of_forall_dist_le
  · exact r.prop
  · intro x hx y hy
    simp only [closedBall, Set.mem_setOf_eq] at hx hy
    rw [dist_comm] at hy
    have := hiud.dist_triangle_max x z y
    grind only [= max_def]
