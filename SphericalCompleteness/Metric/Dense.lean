/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.External.Ultrametric.Basic
public import SphericalCompleteness.Metric.Basic
public import SphericalCompleteness.PseudoMetric.Dense

/-!
# A non-spherical-completeness mechanism

A mechanism for exhibiting ultrametric spaces that fail to be spherically complete, driven by
*spherical density*.

A space is *spherically dense* (`IsSphericallyDense`) when every closed ball realizes its radius as
its diameter; equivalently one can always find points inside a ball separated by almost the full
radius. This supplies the splitting hypothesis of
`PseudoMetric.not_isSphericallyComplete_of_isSphericallyDense`. In a nonempty separable space, a
dense sequence supplies a countable cover by balls of radius `1`. Splitting at
radii `1 + 1 / (n + 1)` shows that the space cannot be spherically complete. The p-adic application
is in `SphericalCompleteness.Examples.Padic`.

The final `SchikhofCounterexample` namespace records a related density condition
(`IsDenseMetric`) and shows, via `PUnit`, that separability and the ultrametric hypothesis cannot
simply be dropped.

## Main definitions

* `IsSphericallyDense`: closed balls realize their radius as their diameter.
* `SchikhofCounterexample.IsDenseMetric`: inside every ball, the realized distances are dense in
  `[0, diam]`.

## Main statements

* `exists_dist_lt_diam_iff_isSphericallyDense`: characterization of spherical density via
  almost-diameter-realizing pairs.
* `not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric`: a separable,
  spherically dense ultrametric space is not spherically complete.
-/

@[expose] public section

open Metric
open Filter
open TopologicalSpace
open NNReal

namespace SphericallyCompleteSpace

/--
`IsSphericallyDense α` is a predicate on a pseudo-metric space asserting that closed balls
realize their radius as their diameter.

More precisely, for every center `c : α` and radius `r : ℝ≥0`, the diameter of the closed ball
`closedBall c r` is exactly `r`:
`diam (closedBall c r) = r`.

This expresses a form of “spherical density”: points occur in the closed ball at (up to) the
maximal possible distance allowed by the radius, so the ball is not “degenerate” in diameter.
-/
class IsSphericallyDense (α : Type*) [PseudoMetricSpace α] : Prop where
  /-- Every closed ball realizes its radius as its diameter. -/
  spherically_dense : ∀ (c : α) (r : ℝ≥0), diam (closedBall c r) = r

namespace IsSphericallyDense

/--
Builds an `IsSphericallyDense` instance on `α` from the assumptions that `α` is a
`DenselyNormedField` and that its distance is ultrametric (`IsUltrametricDist α`).

Intuitively: in an ultrametric normed field where values (norms) are dense in the
relevant sense, every (nonempty) nested family of closed balls has a point that is
arbitrarily close to being in all of them, i.e. `α` is *spherically dense*.
-/
instance instIsSphericallyDenseOfDenselyNormedField (α : Type*)
    [dnf : DenselyNormedField α] [hiud : IsUltrametricDist α] :
    IsSphericallyDense α where
  spherically_dense := by
    refine fun z r ↦ eq_of_le_of_ge (IsUltrametricDist.diam_le_radius _ _) ?_
    by_contra hc
    simp only [not_le] at hc
    rcases dnf.lt_norm_lt (diam (closedBall z ↑r)) ↑r diam_nonneg hc with ⟨δ, _, hδ2⟩
    have hmem : z + δ ∈ closedBall z r := by
      simp only [mem_closedBall, dist_self_add_left, le_of_lt hδ2]
    have := dist_le_diam_of_mem isBounded_closedBall hmem (mem_closedBall_self zero_le_coe)
    simp only [dist_self_add_left] at this
    linarith

/--
Converse to `instIsSphericallyDenseOfDenselyNormedField`: an ultrametric normed field that is
*spherically dense* is in fact a `DenselyNormedField`.

Spherical density gives `diam (closedBall 0 r) = r` for every `r`, so for any target window
`x < ‖·‖ < y` we may pick an intermediate radius `m ∈ (x, y)` and apply
`IsSphericallyDense.exists_dist_lt_diam` inside `closedBall 0 m`: it yields points `u, v` with
`x < nndist u v ≤ m`. In a normed field `nndist u v = ‖u - v‖`, so `a := u - v` witnesses
`x < ‖a‖ < y`, which is exactly the density condition `lt_norm_lt`. -/
instance instDenselyNormedFieldOfIsSphericallyDenseOfUltrametricNormedField (α : Type*)
    [NormedField α] [IsUltrametricDist α] [IsSphericallyDense α] :
    DenselyNormedField α where
  lt_norm_lt := by
    intro x y hx hxy
    obtain ⟨m, hxm, hmy⟩ := exists_between hxy
    set xN : ℝ≥0 := ⟨x, hx⟩ with hxNdef
    set mN : ℝ≥0 := ⟨m, le_trans hx hxm.le⟩ with hmNdef
    have hlt : xN < mN := by rw [← NNReal.coe_lt_coe]; exact hxm
    have hdist :
        ∃ u v : α,
          u ∈ closedBall (0 : α) mN ∧ v ∈ closedBall (0 : α) mN ∧
            nndist u v ∈ Set.Ioc xN mN := by
      have hsd : diam (closedBall (0 : α) mN) = mN :=
        IsSphericallyDense.spherically_dense (α := α) (0 : α) mN
      have hlt' : (xN : ℝ) < mN := hlt
      rw [← hsd] at hlt'
      by_contra hc
      push Not at hc
      refine LT.lt.not_ge hlt' <| Metric.diam_le_of_forall_dist_le xN.prop ?_
      intro u hu v hv
      specialize hc u v hu hv
      simp only [Set.mem_Ioc, not_and_or] at hc
      simpa only [dist_le_coe, not_lt] using
        hc.resolve_right
          (by
            simp only [not_le, not_lt]
            rw [← dist_le_coe, ← hsd]
            exact dist_le_diam_of_mem isBounded_closedBall hu hv)
    obtain ⟨u, v, _, _, huv⟩ := hdist
    refine ⟨u - v, ?_, ?_⟩
    · have h1 : (xN : ℝ) < nndist u v := huv.1
      rwa [coe_nndist, dist_eq_norm] at h1
    · have h2 : (nndist u v : ℝ) ≤ mN := huv.2
      rw [coe_nndist, dist_eq_norm] at h2
      exact lt_of_le_of_lt h2 hmy

/--
From spherical density, any closed ball of positive radius has (at least) two points whose
distance is strictly larger than any prescribed `r' < r` while still remaining `≤ r`.

More precisely, assuming `IsSphericallyDense α`, for any center `z : α` and radii
`r' r : ℝ≥0` with `r' < r`, there exist `x y : α` such that `x, y ∈ closedBall z r` and
`nndist x y ∈ Set.Ioc r' r` (i.e. `r' < nndist x y ≤ r`).

This provides a convenient way to extract "almost diameter-realizing" pairs inside a ball,
with a quantitative lower bound on their separation.
-/
lemma exists_dist_lt_diam {α : Type*} [PseudoMetricSpace α]
    : IsSphericallyDense α →
    ∀ (z : α), ∀ ⦃r r' : ℝ≥0⦄, r' < r →
    ∃ x y : α, x ∈ closedBall z r ∧ y ∈ closedBall z r ∧ nndist x y ∈ Set.Ioc r' r := by
  intro isd z r r' hr
  replace isd := isd.spherically_dense z r
  replace hr : (↑r' : ℝ) < ↑r := hr
  rw [← isd] at hr
  by_contra hc
  push Not at hc
  refine LT.lt.not_ge hr <| Metric.diam_le_of_forall_dist_le r'.prop ?_
  intro x hx y hy
  specialize hc x y hx hy
  simp only [Set.mem_Ioc, not_and_or] at hc
  simpa only [dist_le_coe, not_lt] using
    hc.resolve_right
      (by
        simp only [not_le, not_lt]
        rw [← dist_le_coe, ← isd]
        exact dist_le_diam_of_mem isBounded_closedBall hx hy)

end IsSphericallyDense

/--
Characterization of spherical density via existence of pairs of points with controlled distance.

In a pseudo-metric space `α` equipped with an ultrametric distance (`[IsUltrametricDist α]`),
the typeclass predicate `IsSphericallyDense α` is equivalent to the following concrete
“radius-witness” property:

For every center `z : α` and radii `r' < r` in `ℝ≥0`, there exist two points `x y : α`
both lying in the closed ball `closedBall z r` such that their (nonnegative) distance
`nndist x y` lies in the half-open interval `Set.Ioc r' r` (i.e. `r' < nndist x y ≤ r`).

This expresses that within any closed ball of radius `r` one can find points separated by
a distance arbitrarily close to `r` from below (but still bounded by `r`), matching the
intuition that balls contain “enough” points at all intermediate distance scales.
-/
theorem exists_dist_lt_diam_iff_isSphericallyDense
    {α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α]
    : IsSphericallyDense α ↔
    ∀ (z : α), ∀ ⦃r r' : ℝ≥0⦄, r' < r →
    ∃ x y : α, x ∈ closedBall z r ∧ y ∈ closedBall z r ∧ nndist x y ∈ Set.Ioc r' r := by
  refine ⟨IsSphericallyDense.exists_dist_lt_diam, ?_⟩
  intro h
  refine {spherically_dense := fun z r ↦ eq_of_le_of_ge (IsUltrametricDist.diam_le_radius _ _) ?_}
  by_contra hc
  simp only [not_le] at hc
  rcases h z hc with ⟨x, y, hx, hy, hxy⟩
  have : diam (closedBall z ↑r) < dist x y := hxy.out.1
  have := dist_le_diam_of_mem isBounded_closedBall hx hy
  linarith

/-- Spherical density supplies the bundled distance witnesses without a separation assumption. -/
instance IsSphericallyDense.nnMetric {α : Type*} [PseudoMetricSpace α] [h : IsSphericallyDense α] :
    (Metric.nnMetric α).IsSphericallyDense where
  exists_dist_mem_Ioc c _ _ _ hr := by
    simpa only [ball_nnMetric, nnMetric_apply] using IsSphericallyDense.exists_dist_lt_diam h c hr

/-- In real-valued pseudo-ultrametrics, the diameter and bundled distance formulations
of spherical density are equivalent. -/
theorem isSphericallyDense_iff_nnMetric (α : Type*) [PseudoMetricSpace α] [IsUltrametricDist α] :
    IsSphericallyDense α ↔ (Metric.nnMetric α).IsSphericallyDense := by
  constructor
  · intro h
    infer_instance
  · intro h
    apply exists_dist_lt_diam_iff_isSphericallyDense.mpr
    intro c r s hsr
    simpa only [ball_nnMetric, nnMetric_apply] using h.exists_dist_mem_Ioc c (zero_le : 0 ≤ s) hsr

/-- A nonempty separable, spherically dense pseudo-ultrametric space contains a nest
of closed balls with empty intersection. -/
theorem not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric
    (α : Type*) [PseudoMetricSpace α] [IsUltrametricDist α] [hα : IsSphericallyDense α]
    [Nonempty α] [SeparableSpace α] : ¬ SphericallyCompleteSpace α := by
  obtain ⟨u, hu⟩ := exists_dense_seq α
  let r (n : ℕ) : ℝ≥0 := 1 + 1 / (n + 1)
  have hr (n : ℕ) : r (n + 1) < r n := by
    dsimp [r]
    apply add_lt_add_right
    apply one_div_lt_one_div_of_lt (by positivity)
    norm_num
  rw [Metric.sphericallyCompleteSpace_iff]
  apply (Metric.nnMetric α).not_isSphericallyComplete_of_isSphericallyDense u r
    (strictAnti_nat_of_succ_lt hr) (fun _ ↦ zero_le)
  intro x
  obtain ⟨n, hn⟩ := hu.exists_mem_open isOpen_ball
    (nonempty_ball.2 zero_lt_one : (ball x 1).Nonempty)
  refine ⟨n, ?_⟩
  rw [ball_nnMetric, mem_closedBall, dist_comm]
  apply (Metric.mem_ball.mp hn).le.trans
  rw [one_le_coe]
  exact le_add_of_nonneg_right (zero_le : 0 ≤ (1 : ℝ≥0) / _)

namespace SchikhofCounterexample

/--
`IsDenseMetric α` formalizes the metric-density condition used in Schikhof's discussion.

For every center `z : α` and radius `r : ℝ≥0`, consider the set of pairwise distances
between points in the closed ball `closedBall z r`:
`Set.image2 dist (closedBall z r) (closedBall z r)`.

The class asserts that the closure of this distance set is exactly the full interval
`Set.Icc 0 (diam (closedBall z r))`.

Intuitively, this says that distances occurring inside each closed ball are topologically
dense in all admissible values between `0` and the ball diameter.
-/
class IsDenseMetric (α : Type*) [PseudoMetricSpace α] : Prop where
  /-- Inside every closed ball, the pairwise distances are topologically dense in the whole
  interval from `0` to the ball's diameter. -/
  dense_metric : ∀ z : α, ∀ r : ℝ≥0,
    closure (Set.image2 dist (closedBall z r) (closedBall z r)) = Set.Icc 0 (diam (closedBall z r))

namespace IsDenseMetric
/--
Constructs `IsDenseMetric α` from spherical density in an ultrametric space.

Assuming:
* `PseudoMetricSpace α`,
* `IsUltrametricDist α`,
* `IsSphericallyDense α`,

the theorem proves that in every closed ball, realized distances are dense in the full
interval from `0` to the ball diameter.

The proof combines:
* an upper bound (`dist x y ≤ diam (closedBall z r)`), and
* approximation from below using `IsSphericallyDense.exists_dist_lt_diam`.
-/
theorem of_isSphericallyDense (α : Type*)
    [PseudoMetricSpace α] [IsUltrametricDist α] [IsSphericallyDense α] :
    IsDenseMetric α where
  dense_metric := by
    intro z r
    have hdiam : diam (closedBall z r) = (r : ℝ) := IsSphericallyDense.spherically_dense z r
    rw [hdiam]
    refine le_antisymm ?_ ?_
    · refine closure_minimal (fun t ht ↦ ?_) isClosed_Icc
      rcases Set.mem_image2.mp ht with ⟨x, hx, y, hy, rfl⟩
      exact ⟨dist_nonneg, (dist_le_diam_of_mem isBounded_closedBall hx hy).trans_eq hdiam⟩
    · rintro t ⟨ht0, htr⟩
      rcases eq_or_lt_of_le ht0 with rfl | ht0'
      · exact subset_closure <| Set.mem_image2.mpr ⟨z, by simp, z, by simp, by simp⟩
      · refine Metric.mem_closure_iff.mpr <| fun ε hε ↦ ?_
        let e : ℝ≥0 := ⟨ε / 2, by positivity⟩
        by_cases he : t ≤ (e : ℝ)
        · refine ⟨0, Set.mem_image2.mpr ⟨z, by simp, z, by simp, by simp⟩, ?_⟩
          have heps : (e : ℝ) < ε := by change ε / 2 < ε; nlinarith [hε]
          exact lt_of_le_of_lt (by simpa [Real.dist_eq, abs_of_nonneg ht0] using he) heps
        · let tNN : ℝ≥0 := ⟨t, le_of_lt ht0'⟩
          let r' : ℝ≥0 := ⟨t - e, by linarith [lt_of_not_ge he]⟩
          have hr'lt : r' < tNN := sub_lt_self _ (by change 0 < ε / 2; nlinarith [hε])
          rcases IsSphericallyDense.exists_dist_lt_diam (α := α) inferInstance z hr'lt with
            ⟨x, y, hx, hy, hxy⟩
          have hx' : x ∈ closedBall z r := by
            simpa [mem_closedBall] using le_trans hx htr
          have hy' : y ∈ closedBall z r := by
            simpa [mem_closedBall] using le_trans hy htr
          refine ⟨dist x y, Set.mem_image2.mpr ⟨x, hx', y, hy', rfl⟩, ?_⟩
          have hlow : (r' : ℝ) < dist x y := hxy.1
          have hupp : dist x y ≤ t := by exact_mod_cast hxy.2
          have hsub : t - dist x y < ε := by
            refine lt_trans ?_ (by change ε / 2 < ε; nlinarith)
            exact sub_lt_comm.mp <| RCLike.ofReal_lt_ofReal.mp hlow
          simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hupp)] using hsub

/--
For an ultrametric normed field, Schikhof's metric-density condition is equivalent to
spherical density.

Assuming:
* `NormedField α`,
* `IsUltrametricDist α`,

the theorem identifies the condition that, in every closed ball, the realized distances are dense
in the whole interval `[0, diam]` with the condition that every closed ball realizes its radius as
its diameter.

The reverse implication is `of_isSphericallyDense`. For the forward implication, the
density of realized distances first yields density of norm values in every interval `(x, y)`, which
upgrades `α` to a `DenselyNormedField`; the ultrametric argument then forces each closed ball to
have diameter exactly equal to its radius. -/
theorem iff_isSphericallyDense_of_normedField (α : Type*)
    [dnf : NormedField α] [hiud : IsUltrametricDist α] :
    IsDenseMetric α ↔ IsSphericallyDense α := by
  constructor
  · intro h
    have hlt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y := by
      intro x y hx hxy
      have hw : ∃ w : α, 1 < ‖w‖ := by
        have hdiam1 : diam (closedBall (0 : α) (1 : ℝ≥0)) = (1 : ℝ≥0) := by
          have hmem1 : (1 : ℝ) ∈ closure (Set.image2 dist (closedBall (0 : α) (1 : ℝ≥0))
              (closedBall (0 : α) (1 : ℝ≥0))) := by
            apply subset_closure
            refine Set.mem_image2.mpr ⟨(1 : α), ?_, (0 : α), by simp, by simp [dist_eq_norm]⟩
            simp [mem_closedBall, dist_eq_norm]
          rw [h.dense_metric (0 : α) (1 : ℝ≥0)] at hmem1
          exact le_antisymm (IsUltrametricDist.diam_le_radius _ _) hmem1.2
        have hhalf : (1 / 2 : ℝ) ∈ closure
          (Set.image2 dist (closedBall (0 : α) (1 : ℝ≥0)) (closedBall (0 : α) (1 : ℝ≥0))) := by
          rw [h.dense_metric (0 : α) (1 : ℝ≥0), hdiam1]
          norm_num
        rcases Metric.mem_closure_iff.mp hhalf (1 / 4) (by norm_num) with ⟨t, ht, htt⟩
        rcases Set.mem_image2.mp ht with ⟨u, hu, v, hv, rfl⟩
        have habs : |dist u v - 1 / 2| < 1 / 4 := by
          simpa [Real.dist_eq, abs_sub_comm] using htt
        have hdist0 : 0 < dist u v := by
          have hsplit := abs_lt.mp habs; nlinarith
        have hdist1 : dist u v < 1 := by
          have hsplit := abs_lt.mp habs; nlinarith
        refine ⟨(u - v)⁻¹, ?_⟩
        rw [norm_inv]
        have hnorm_pos : 0 < ‖u - v‖ := by simpa [dist_eq_norm] using hdist0
        have hnorm_lt : ‖u - v‖ < 1 := by simpa [dist_eq_norm] using hdist1
        exact (one_lt_inv₀ hnorm_pos).2 hnorm_lt
      obtain ⟨w, hw⟩ := hw
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt y hw
      let c : α := w ^ n
      have hyc : y < ‖c‖ := by
        simpa [c, norm_pow] using hn
      let r : ℝ≥0 := ‖c‖₊
      have hdiamr : diam (closedBall (0 : α) r) = r := by
        have hmemr : (r : ℝ) ∈ closure
          (Set.image2 dist (closedBall (0 : α) r) (closedBall (0 : α) r)) := by
          apply subset_closure
          refine Set.mem_image2.mpr ⟨c, ?_, (0 : α), by simp, by simp [r, dist_eq_norm]⟩
          simp [r, mem_closedBall, dist_eq_norm]
        rw [h.dense_metric (0 : α) r] at hmemr
        exact le_antisymm (IsUltrametricDist.diam_le_radius _ _) hmemr.2
      have hmid : (x + y) / 2 ∈ closure
          (Set.image2 dist (closedBall (0 : α) r) (closedBall (0 : α) r)) := by
        rw [h.dense_metric (0 : α) r, hdiamr]
        refine ⟨by nlinarith, ?_⟩
        have hyc' : y < (r : ℝ) := by simpa [r] using hyc
        nlinarith
      rcases Metric.mem_closure_iff.mp hmid ((y - x) / 4) (by nlinarith [hxy]) with ⟨t, ht, htt⟩
      rcases Set.mem_image2.mp ht with ⟨u, hu, v, hv, rfl⟩
      have habs : |dist u v - (x + y) / 2| < (y - x) / 4 := by
        simpa [Real.dist_eq, abs_sub_comm] using htt
      have hlow : x < dist u v := by
        have hsplit := abs_lt.mp habs; nlinarith
      have hupp : dist u v < y := by
        have hsplit := abs_lt.mp habs; nlinarith
      exact ⟨u - v, by simpa [dist_eq_norm] using hlow, by simpa [dist_eq_norm] using hupp⟩
    let hdnf' : DenselyNormedField α := { dnf with lt_norm_lt := hlt_norm_lt }
    have hsd : IsSphericallyDense α :=
      @IsSphericallyDense.instIsSphericallyDenseOfDenselyNormedField α hdnf' hiud
    exact hsd
  · intro h; exact of_isSphericallyDense α

end IsDenseMetric

/--
`PUnit` satisfies `IsDenseMetric`.

Since `PUnit` is a subsingleton, each closed ball is a singleton and every pairwise distance
is `0`, so both sides of `dense_metric` reduce to `{0}`.
-/
instance instIsDenseMetricPUnit : IsDenseMetric PUnit where
  dense_metric := by
    intros
    simp [dist_self, closedBall_eq_singleton_of_subsingleton zero_le_coe]

-- The one-point space is ultrametric, separable and has dense metric, yet is also spherically
-- complete; this shows Schikhof's implication (dense metric ⇒ not spherically complete) fails in
-- general, so the separability/ultrametric hypotheses in
-- `not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric` cannot simply be
-- dropped in favour of `IsDenseMetric`.
example : SeparableSpace PUnit := inferInstance
example : IsDenseMetric PUnit := inferInstance
example : IsUltrametricDist PUnit := inferInstance
example : SphericallyCompleteSpace PUnit := inferInstance

end SchikhofCounterexample


end SphericallyCompleteSpace
