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

theorem closedBall_subset_closedBall_of_le_radius_of_nonempty_intersection_of_ultrametric
{α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α]
{z1 z2 : α} {r1 r2 : ℝ≥0}
(hle : r1 ≤ r2)
(hne : (closedBall z1 r1 ∩ closedBall z2 r2).Nonempty) :
closedBall z1 r1 ⊆ closedBall z2 r2 := by
  intro x hx
  simp only [closedBall, Set.mem_setOf_eq] at hx
  rcases hne with ⟨y, hy1, hy2⟩
  simp only [mem_closedBall] at *
  refine le_trans (hiud.dist_triangle_max x y z2) <| sup_le_iff.2 ⟨?_, hy2⟩
  refine le_trans (hiud.dist_triangle_max x z1 y) <| sup_le_iff.2 ⟨le_trans hx hle, ?_⟩
  simpa only [dist_comm] using le_trans hy1 hle
