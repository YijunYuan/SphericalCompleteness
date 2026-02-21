import SphericalCompleteness.Basic
import SphericalCompleteness.External.PadicComplex

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
  spherically_dense :
  ∀ (c : α) (r : ℝ≥0) , diam (closedBall c r) = r

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
  refine fun z r ↦ eq_of_le_of_ge (diam_le_radius_of_ultrametric _ _) ?_
  by_contra hc
  simp only [not_le] at hc
  rcases dnf.lt_norm_lt (diam (closedBall z ↑r)) ↑r diam_nonneg hc with ⟨δ, _, hδ2⟩
  have : z + δ ∈ closedBall z r := by
    simp only [mem_closedBall, dist_self_add_left, le_of_lt hδ2]
  have this' : z ∈ closedBall z r := by
    simp only [mem_closedBall, dist_self, zero_le_coe]
  have := dist_le_diam_of_mem isBounded_closedBall this this'
  simp only [dist_self_add_left] at this
  linarith

/--
From spherical density, any closed ball of positive radius has (at least) two points whose
distance is strictly larger than any prescribed `r' < r` while still remaining `≤ r`.

More precisely, assuming `IsSphericallyDense α`, for any center `z : α` and radii
`r' r : ℝ≥0` with `r' < r`, there exist `x y : α` such that `x, y ∈ closedBall z r` and
`nndist x y ∈ Set.Ioc r' r` (i.e. `r' < nndist x y ≤ r`).

This provides a convenient way to extract "almost diameter-realizing" pairs inside a ball,
with a quantitative lower bound on their separation.
-/
lemma exists_dist_lt_diam_of_isSphericallyDense {α : Type*} [PseudoMetricSpace α]
: IsSphericallyDense α →
∀ (z : α), ∀ ⦃r r' : ℝ≥0⦄, r' < r →
∃ x y : α, x ∈ closedBall z r ∧ y ∈ closedBall z r ∧  nndist x y ∈ Set.Ioc r' r := by
  intro isd z r r' hr
  replace isd := isd.spherically_dense z r
  replace hr : (↑r' : ℝ) < ↑r := hr
  rw [← isd] at hr
  by_contra hc
  push_neg at hc
  refine LT.lt.not_ge hr <| Metric.diam_le_of_forall_dist_le r'.prop ?_
  intro x hx y hy
  specialize hc x y hx hy
  simp only [Set.mem_Ioc, not_and_or] at hc
  simpa only [dist_le_coe, not_lt] using
    hc.resolve_right
      (by
        simp only [not_le, not_lt]
        suffices h : dist x y ≤ ↑r by exact h
        rw [← isd]
        exact dist_le_diam_of_mem isBounded_closedBall hx hy)

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
∃ x y : α, x ∈ closedBall z r ∧ y ∈ closedBall z r ∧  nndist x y ∈ Set.Ioc r' r := by
  refine ⟨exists_dist_lt_diam_of_isSphericallyDense, ?_⟩
  intro h
  refine {spherically_dense := fun z r ↦ eq_of_le_of_ge (diam_le_radius_of_ultrametric _ _) ?_}
  by_contra hc
  simp only [not_le] at hc
  rcases h z hc with ⟨x, y, hx, hy, hxy⟩
  have : diam (closedBall z ↑r) < dist x y := hxy.out.1
  have := dist_le_diam_of_mem isBounded_closedBall hx hy
  linarith

private lemma exists_sub_closedball_not_belong {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
(c₀ : α) (r₀ : ℝ≥0) (r₁ : ℝ≥0) (hr : r₁ < r₀) (z : α) :
∃ c₁ : α,
  closedBall c₁ r₁ ⊆ closedBall c₀ r₀ ∧
  z ∉ closedBall c₁ r₁
  := by
  apply exists_dist_lt_diam_of_isSphericallyDense at hα
  rcases hα c₀ hr with ⟨x, y, hx, hy, hxy⟩
  have : Disjoint (closedBall x r₁) (closedBall y r₁) := by
    refine (IsUltrametricDist.closedBall_eq_or_disjoint x y ↑r₁).resolve_left ?_
    by_contra hc
    have : x ∈ closedBall x ↑r₁ := by simp only [mem_closedBall, dist_self, zero_le_coe]
    simp only [hc, mem_closedBall, dist_le_coe] at this
    exact (lt_self_iff_false (nndist x y)).mp <| lt_of_le_of_lt this hxy.out.1
  if hzx : z ∈ closedBall x r₁ then
    refine ⟨y, ⟨?_, Disjoint.notMem_of_mem_left this hzx⟩⟩
    simp only [closedBall,  Set.setOf_subset_setOf]
    refine fun a ha ↦ le_trans (hiud.dist_triangle_max a y c₀) ?_
    simp only [sup_le_iff]
    exact ⟨le_of_lt <| lt_of_le_of_lt ha hr, hy⟩
  else
    refine ⟨x, ⟨fun a ha ↦ ?_, hzx⟩⟩
    simp only [mem_closedBall, not_le] at *
    refine le_trans (hiud.dist_triangle_max a x c₀) ?_
    simp only [sup_le_iff]
    exact ⟨le_of_lt <| lt_of_le_of_lt ha hr, hx⟩

private lemma exists_pos_dist (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] :
∃ z : α × α, nndist z.1 z.2 > 0 := by
  use ((exists_dist_lt_diam_of_isSphericallyDense hα nemp.some one_lt_two).choose,
  (exists_dist_lt_diam_of_isSphericallyDense hα nemp.some one_lt_two).choose_spec.choose)
  exact lt_trans zero_lt_one (exists_dist_lt_diam_of_isSphericallyDense
    hα nemp.some one_lt_two).choose_spec.choose_spec.2.2.out.1

private noncomputable def funk_radius (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] (n : ℕ) : ℝ≥0 :=
(nndist (exists_pos_dist α).choose.1 (exists_pos_dist α).choose.2)
  * (1 + 1 / (n + 1))

private lemma funk_radius_strictanti (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] :
StrictAnti (fun n => funk_radius α n) := by
  refine strictAnti_nat_of_succ_lt fun n↦ ?_
  unfold funk_radius
  refine (mul_lt_mul_iff_right₀ (exists_pos_dist α).choose_spec).mpr ?_
  simp only [Nat.cast_add, Nat.cast_one, one_div, add_lt_add_iff_left, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    lt_inv_iff_mul_lt]
  field_simp
  norm_num

private lemma funk_radius_range (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] (n : ℕ) :
(funk_radius α n) > (funk_radius α 0) / 2 := by
  unfold funk_radius
  rw [mul_div_assoc]
  refine (mul_lt_mul_iff_right₀ (exists_pos_dist α).choose_spec).mpr ?_
  simp only [CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true, div_self,
    add_self_div_two, one_div, lt_add_iff_pos_right, inv_pos, add_pos_iff, Nat.cast_pos,
    zero_lt_one, or_true]

private noncomputable def funk_chain_of_ball {α : Type*} [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) (n : ℕ) : α × ℝ≥0 :=
  match n with
  | 0 => ((exists_pos_dist α).choose.1, funk_radius α 0)
  | n + 1 => ⟨((exists_sub_closedball_not_belong (funk_chain_of_ball hα' n).1 (funk_radius α n)
      (funk_radius α (n + 1)) <| funk_radius_strictanti α (lt_add_one n))
        (hα'.ofNat hsep.exists_countable_dense.choose n)).choose, funk_radius α (n+1)⟩

private lemma funk_chain_of_ball_decreasing (α : Type*) [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) :
Antitone (fun n => closedBall (funk_chain_of_ball hα' n).1 (funk_chain_of_ball hα' n).2) := by
  refine antitone_nat_of_succ_le <| fun n ↦ ?_
  simp only [funk_chain_of_ball, mem_closedBall, dist_le_coe, not_le, Set.le_eq_subset]
  have := ((exists_sub_closedball_not_belong (funk_chain_of_ball hα' n).1 (funk_radius α n)
      (funk_radius α (n + 1)) <| funk_radius_strictanti α (lt_add_one n))
        (hα'.ofNat hsep.exists_countable_dense.choose n)).choose_spec.1
  conv => arg 2; arg 2; unfold funk_chain_of_ball
  cases n
  · simp only [zero_add, mem_closedBall, dist_le_coe, not_le] at *
    exact this
  · simp only [mem_closedBall, dist_le_coe, not_le] at *
    exact this

private lemma not_in_funk_chain_of_ball (α : Type*) [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) (n : ℕ) :
(hα'.ofNat hsep.exists_countable_dense.choose n).val ∉
closedBall (funk_chain_of_ball hα' (n + 1)).1 (funk_chain_of_ball hα' (n + 1)).2 :=
  ((exists_sub_closedball_not_belong (funk_chain_of_ball hα' n).1 (funk_radius α n)
      (funk_radius α (n + 1)) <| funk_radius_strictanti α (lt_add_one n))
        (hα'.ofNat hsep.exists_countable_dense.choose n)).choose_spec.2

private lemma funk_chain_radius_eq (α : Type*) [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) (n : ℕ) :
(funk_chain_of_ball hα' n).2 = (funk_radius α n):= by
  unfold funk_chain_of_ball
  cases n
  · simp only
  · simp only

/--
Shows that a separable ultrametric space which is *spherically dense* cannot be spherically
complete.

More precisely, assuming:
* `MetricSpace α`,
* `IsUltrametricDist α` (the metric satisfies the strong triangle inequality),
* `IsSphericallyDense α` (every closed ball properly contains a strictly smaller nonempty closed
  ball),
* `Nonempty α`,
* `SeparableSpace α`,

the space fails to be `SphericallyCompleteSpace α`, i.e. there exists a decreasing chain of closed
balls
with empty intersection.
-/
theorem not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric
(α : Type*) [MetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α] :
¬ SphericallyCompleteSpace α := by
  by_contra hc
  replace hc := hc.isSphericallyComplete
  if hinf : Nonempty (Denumerable hsep.exists_countable_dense.choose) then
    specialize hc <| funk_chain_of_ball_decreasing α hinf.some
    simp only [Set.nonempty_iInter] at hc
    rcases hc with ⟨z,hz⟩
    have : ∀ i : ℕ, ball z ((funk_radius α 0) / 2) ⊆
      closedBall (funk_chain_of_ball hinf.some i).1 ↑(funk_chain_of_ball hinf.some i).2 := by
      intro i t ht
      simp only [mem_closedBall, mem_ball] at *
      refine le_trans (hiud.dist_triangle_max _ z _) ?_
      replace ht := lt_trans ht ((funk_chain_radius_eq α hinf.some i) ▸ funk_radius_range α i)
      simpa only [sup_le_iff] using ⟨le_of_lt ht, hz i⟩
    have : ∀ i : ℕ, ((hinf.some.ofNat hsep.exists_countable_dense.choose i)).val ∉
      ball z ((funk_radius α 0) / 2) := by
      intro i
      by_contra hc
      exact (not_in_funk_chain_of_ball α hinf.some i) <| (this (i + 1) hc)
    have : Disjoint hsep.exists_countable_dense.choose (ball z ((funk_radius α 0) / 2)) := by
      refine Set.disjoint_iff_forall_ne.mpr ?_
      intro a ha b hb
      by_contra hc
      rw [← hc] at hb
      specialize this (hinf.some.encode (⟨a, ha⟩ : hsep.exists_countable_dense.choose))
      simp only [Denumerable.ofNat_encode] at this
      exact this hb
    have := hsep.exists_countable_dense.choose_spec.2.closure_eq ▸
      Disjoint.closure_left this isOpen_ball
    simp only [funk_radius, gt_iff_lt, CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero,
      not_false_eq_true, div_self, one_add_one_eq_two, NNReal.coe_mul, NNReal.coe_ofNat,
      OfNat.ofNat_ne_zero, mul_div_cancel_right₀, Set.univ_disjoint, ball_eq_empty] at this
    exact (not_lt.2 this) (exists_pos_dist α).choose_spec
  else
    have : ¬ Infinite hsep.exists_countable_dense.choose := by
      by_contra hc
      exact hinf <| nonempty_denumerable_iff.2 ⟨hsep.exists_countable_dense.choose_spec.1,hc⟩
    simp only [not_infinite_iff_finite, Set.finite_coe_iff] at this
    have hcl := Set.Finite.isClosed this
    rw [← closure_eq_iff_isClosed, hsep.exists_countable_dense.choose_spec.2.closure_eq] at hcl
    rw [← hcl, Set.finite_univ_iff] at this
    let S := Set.image (fun (x : α × α) => (nndist x.1 x.2)) {x : α × α | x.1 ≠ x.2}
    have hfin := Set.toFinite ((fun (x : α × α) ↦ nndist x.1 x.2) '' {x | x.1 ≠ x.2})
    have hnemp : S.Nonempty := by
      use nndist (exists_pos_dist α).choose.1 (exists_pos_dist α).choose.2
      simp only [ne_eq, gt_iff_lt, Set.mem_image, Set.mem_setOf_eq, Prod.exists, S]
      use (exists_pos_dist α).choose.1, (exists_pos_dist α).choose.2
      simp only [gt_iff_lt, and_true]
      by_contra hc
      have := hc ▸ (exists_pos_dist α).choose_spec
      simp only [gt_iff_lt, nndist_self, lt_self_iff_false] at this
    let r₀ := sInf S / 2
    have r₀pos : r₀ > 0 := by
      simp only [gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_right, r₀]
      have := (Set.Nonempty.csInf_mem hnemp hfin).out
      simp only [ne_eq, Set.mem_setOf_eq, Prod.exists] at this
      rcases this with ⟨a,b,hneq,dis⟩
      rw [← dis]
      contrapose hneq
      simpa only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, nndist_eq_zero] using hneq
    have : diam (closedBall nemp.some r₀) = 0 :=by
      refine diam_subsingleton ?_
      rw [Set.subsingleton_iff_singleton (by
      refine mem_closedBall.mpr ?_
      simp only [dist_self, zero_le_coe]
      : nemp.some ∈ closedBall nemp.some r₀)]
      ext x
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · simp only [mem_closedBall, dist_le_coe] at h
        simp only [Set.mem_singleton_iff]
        by_contra hc
        have : (nndist x nemp.some) ∈ S := by
          unfold S
          simp only [ne_eq, Set.mem_image, Set.mem_setOf_eq, Prod.exists]
          use x, nemp.some
        unfold r₀ at *
        field_simp at *
        replace h := le_trans h <| csInf_le' this
        simp only [mul_zero] at r₀pos
        rw [mul_le_iff_le_one_right <| Std.lt_of_lt_of_le r₀pos <| csInf_le' this] at h
        simp only [Nat.not_ofNat_le_one] at h
      · simp only [Set.mem_singleton_iff] at h
        simp only [h, mem_closedBall, dist_self, zero_le_coe]
    simp only [hα.spherically_dense, coe_eq_zero] at this
    simp only [this, gt_iff_lt, lt_self_iff_false] at r₀pos

instance instPadicComplex_not_sphercallyCompleteSpace (p : ℕ) [hp : Fact (Nat.Prime p)] :
¬ SphericallyCompleteSpace ℂ_[p] :=
  not_sphericallyCompleteSpace_of_isSphericallyDense_separable_ultrametric ℂ_[p]

end SphericallyCompleteSpace
