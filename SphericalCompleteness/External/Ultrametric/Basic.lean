/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Ultrametric balls, norms, and completions

Bounds and inclusions for closed balls, norm comparisons in ultrametric groups,
and ultrametric instances for the completion and the one-point space.
-/

@[expose] public section

open Metric
open NNReal

namespace IsUltrametricDist

section
variable {α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α]

/--
In an ultrametric (pseudo)metric space, the diameter of a closed ball is bounded by its radius.

More precisely, assuming `IsUltrametricDist α`, for any center `z : α` and radius `r : ℝ≥0`,
the set `closedBall z r` has `diam (closedBall z r) ≤ r`. This is a characteristic feature of
ultrametrics: any two points in the same ball are at distance at most the ball's radius.
-/
theorem diam_le_radius
    (z : α) (r : ℝ≥0) :
    diam (closedBall z r) ≤ r :=
  diam_le_of_forall_dist_le r.prop fun _ hx _ hy ↦
    (hiud.dist_triangle_max _ z _).trans <|
      max_le hx <| (dist_comm _ _).trans_le hy

/--
In an ultrametric space, if two closed balls `closedBall z1 r1` and `closedBall z2 r2` intersect
nontrivially and `r1 ≤ r2`, then the smaller-radius ball is contained in the larger-radius one.

More precisely, assuming `IsUltrametricDist α`, `r1 ≤ r2`, and
`(closedBall z1 r1 ∩ closedBall z2 r2).Nonempty`, this theorem proves
`closedBall z1 r1 ⊆ closedBall z2 r2`.

This is a standard “nesting of intersecting balls” property characteristic of ultrametric spaces.
-/
theorem closedBall_subset_closedBall_of_le_radius_of_nonempty_inter
    {z1 z2 : α} {r1 r2 : ℝ≥0}
    (hle : r1 ≤ r2)
    (hne : (closedBall z1 r1 ∩ closedBall z2 r2).Nonempty) :
    closedBall z1 r1 ⊆ closedBall z2 r2 := by
  obtain ⟨y, hy1, hy2⟩ := hne
  rw [closedBall_eq_of_mem hy1, closedBall_eq_of_mem hy2]
  exact closedBall_subset_closedBall (NNReal.coe_le_coe.mpr hle)

end

section
variable {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S] {x y : S}

/-!
### Norm equality from a strictly smaller sum or difference

In an ultrametric seminormed additive group the strong triangle inequality forces a *dominance*
principle: if `‖x ± y‖` is strictly smaller than one of `‖x‖`, `‖y‖`, then that inequality cannot
have been strict on both sides, so `‖x‖ = ‖y‖`. The four lemmas below package this in the
`add`/`sub` and `left`/`right` forms needed downstream; each is a thin wrapper around
`IsUltrametricDist.norm_eq_of_add_norm_lt_max`.
-/

/-- If `‖x + y‖ < ‖x‖` then `‖x‖ = ‖y‖`: the sum cannot drop below the larger summand's norm
unless the two norms coincide. -/
theorem norm_eq_of_norm_add_lt_left (h : ‖x + y‖ < ‖x‖) : ‖x‖ = ‖y‖ :=
  IsUltrametricDist.norm_eq_of_add_norm_lt_max <| by simp_all [true_or]

/-- If `‖x + y‖ < ‖y‖` then `‖x‖ = ‖y‖`, the right-hand companion of
`norm_eq_of_norm_add_lt_left`. -/
theorem norm_eq_of_norm_add_lt_right (h : ‖x + y‖ < ‖y‖) : ‖x‖ = ‖y‖ :=
  IsUltrametricDist.norm_eq_of_add_norm_lt_max <| by simp_all [or_true]

/-- If `‖x - y‖ < ‖x‖` then `‖x‖ = ‖y‖`: the difference form of `norm_eq_of_norm_add_lt_left`. -/
theorem norm_eq_of_norm_sub_lt_left (h : ‖x - y‖ < ‖x‖) : ‖x‖ = ‖y‖ :=
  norm_neg y ▸ norm_eq_of_norm_add_lt_left (sub_eq_add_neg x y ▸ h)

/-- If `‖x - y‖ < ‖y‖` then `‖x‖ = ‖y‖`, the right-hand companion of
`norm_eq_of_norm_sub_lt_left`. -/
theorem norm_eq_of_norm_sub_lt_right (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ :=
  (norm_eq_of_norm_sub_lt_left (by rwa [← norm_neg, neg_sub])).symm

end

/--
Lifts the ultrametric inequality on distances from `𝕜` to its uniform completion.

If `𝕜` is a `PseudoMetricSpace` whose distance is ultrametric (`IsUltrametricDist 𝕜`),
then `UniformSpace.Completion 𝕜` inherits an ultrametric distance with respect to the
canonical `dist` coming from `UniformSpace.Completion.instMetricSpace.toPseudoMetricSpace.toDist`.

This instance is useful for transferring non-Archimedean/ultrametric arguments to the
completion, allowing one to work in a complete ultrametric space without changing the
underlying distance structure.
-/
instance instIsUltrametricDistCompletion {𝕜 : Type*} [PseudoMetricSpace 𝕜]
    [IsUltrametricDist 𝕜] :
    IsUltrametricDist (UniformSpace.Completion 𝕜) where
  dist_triangle_max x y z := by
    refine UniformSpace.Completion.induction_on₃ x y z (isClosed_le ?_ ?_) fun a b c ↦ ?_
    · fun_prop
    · fun_prop
    · simp_rw [UniformSpace.Completion.dist_eq]
      exact IsUltrametricDist.dist_triangle_max a b c

/--
`PUnit` carries an ultrametric distance.

This is immediate because all points in `PUnit` are equal, hence all distances are `0`, and
the strong triangle inequality is trivial. It lets the one-point space serve as a base case and
as a witness that the hypotheses of the ultrametric development are satisfiable. -/
instance instIsUltrametricDistPUnit : IsUltrametricDist PUnit where
  dist_triangle_max x y z := by simp

end IsUltrametricDist
