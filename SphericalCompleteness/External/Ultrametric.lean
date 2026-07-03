/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.Common

/-!
# Ultrametric auxiliary results

Supporting results on ultrametric distances, including transfer to completions,
quotients, submodules, operator spaces and `lp` spaces.
-/

open Metric
open NNReal

/--
In an ultrametric (pseudo)metric space, the diameter of a closed ball is bounded by its radius.

More precisely, assuming `IsUltrametricDist α`, for any center `z : α` and radius `r : ℝ≥0`,
the set `closedBall z r` has `diam (closedBall z r) ≤ r`. This is a characteristic feature of
ultrametrics: any two points in the same ball are at distance at most the ball's radius.
-/
theorem diam_le_radius_of_ultrametric {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α]
(z : α) (r : ℝ≥0) :
diam (closedBall z r) ≤ r :=
  diam_le_of_forall_dist_le r.prop fun _ hx _ hy =>
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
theorem closedBall_subset_closedBall_of_le_radius_of_nonempty_intersection_of_ultrametric
{α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α]
{z1 z2 : α} {r1 r2 : ℝ≥0}
(hle : r1 ≤ r2)
(hne : (closedBall z1 r1 ∩ closedBall z2 r2).Nonempty) :
closedBall z1 r1 ⊆ closedBall z2 r2 := by
  intro x hx
  rcases hne with ⟨y, hy1, hy2⟩
  simp only [mem_closedBall] at *
  refine le_trans (hiud.dist_triangle_max x y z2) <| sup_le_iff.2 ⟨?_, hy2⟩
  refine le_trans (hiud.dist_triangle_max x z1 y) <| sup_le_iff.2 ⟨le_trans hx hle, ?_⟩
  rw [dist_comm]
  exact le_trans hy1 hle

/--
Transfers an ultrametric distance from a seminormed `𝕜`-normed space `E` to the quotient `E ⧸ F`.

Assuming `[IsUltrametricDist E]`, this instance equips the quotient by a submodule
`F : Submodule 𝕜 E` with an `IsUltrametricDist` structure (for the quotient distance coming from the
seminormed additive group structure on `E ⧸ F`), i.e. the distance on `E ⧸ F` satisfies the strong
triangle inequality.

This is useful for working with non-Archimedean/ultrametric geometry in quotients while retaining
the ultrametric property needed for many standard arguments.
-/
instance instIsUltrametricDistQuotient
(𝕜 : Type u_1) [NormedField 𝕜]
{E : Type u_2} [inst_1 : SeminormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E]
{F : Submodule 𝕜 E} : IsUltrametricDist (E ⧸ F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm <| by
    intro x y
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨x', hx', hx'_norm⟩ := Submodule.Quotient.norm_mk_lt (S := F) x hε
    obtain ⟨y', hy', hy'_norm⟩ := Submodule.Quotient.norm_mk_lt (S := F) y hε
    rw [← hx', ← hy']
    refine le_of_lt <| calc
      ‖(Submodule.Quotient.mk x' : E ⧸ F) + Submodule.Quotient.mk y'‖
          = ‖(Submodule.Quotient.mk (x' + y') : E ⧸ F)‖ := by simp
      _ ≤ max ‖x'‖ ‖y'‖ :=
        (Submodule.Quotient.norm_mk_le (S := F) (x' + y')).trans <| iud.norm_add_le_max _ _
      _ < max (‖x‖ + ε) (‖y‖ + ε) := by
        simpa [hx', hy'] using max_lt_max hx'_norm hy'_norm
      _ = max ‖(Submodule.Quotient.mk x' : E ⧸ F)‖ ‖(Submodule.Quotient.mk y' : E ⧸ F)‖ + ε := by
        simpa [hx', hy'] using
          (max_add_add_right ‖(Submodule.Quotient.mk x' : E ⧸ F)‖
            ‖(Submodule.Quotient.mk y' : E ⧸ F)‖ ε)

/--
Provides an `IsUltrametricDist` instance on the space of continuous linear maps `E →L[𝕜] F`
whenever the codomain `F` has an ultrametric distance.

Intuitively, this lifts the ultrametric inequality from `F` to the operator norm distance on
`E →L[𝕜] F`, so that for `f g h : E →L[𝕜] F` one has an inequality of the form
`dist f h ≤ max (dist f g) (dist g h)`.

**Typeclass assumptions:**
- `𝕜` is a nontrivially normed field,
- `E` and `F` are seminormed additive commutative groups and normed spaces over `𝕜`,
- `F` carries an ultrametric distance via `[IsUltrametricDist F]`.

This instance is intended for use in developments involving non-Archimedean / ultrametric
normed spaces, where spaces of bounded linear operators inherit ultrametric behavior from
their codomain.
-/
instance instIsUltrametricDistContinuousLinearMap
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
{F : Type*} [SeminormedAddCommGroup F] [iud : IsUltrametricDist F]
[NormedSpace 𝕜 F] :
IsUltrametricDist (E →L[𝕜] F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g => by
    rw [ContinuousLinearMap.opNorm_le_iff (le_max_of_le_left (norm_nonneg _))]
    intro x
    rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
    exact (iud.norm_add_le_max _ _).trans (max_le_max (f.le_opNorm x) (g.le_opNorm x))

/--
`lp E ⊤` (the `ℓ∞`-product) inherits an ultrametric distance from its coordinate spaces.

Assuming each component `E i` is an ultrametric space (via `IsUltrametricDist (E i)`), and that
the index type `ι` is nonempty, the induced distance on `lp E ⊤` is also ultrametric, i.e.
for all `x y z : lp E ⊤` we have
`dist x z ≤ max (dist x y) (dist y z)`.

This instance is the standard fact that the supremum metric on a product of ultrametric spaces
remains ultrametric.
-/
instance instIsUltrametricDistLp
{ι : Type*} {E : ι → Type*} [Nonempty ι] [∀ i, NormedAddCommGroup (E i)]
[iiud : ∀ i, IsUltrametricDist (E i)] :
IsUltrametricDist (lp E ⊤) where
dist_triangle_max a b c := by
  simp only [dist_eq_norm, lp.norm_eq_ciSup]
  refine ciSup_le fun j => ?_
  rw [show ‖(↑(a - c) : (i : ι) → E i) j‖ = ‖a j - c j‖ from rfl, ← dist_eq_norm]
  refine ((iiud j).dist_triangle_max (a j) (b j) (c j)).trans (max_le_max ?_ ?_)
  · rw [dist_eq_norm, show ‖a j - b j‖ = ‖(↑(a - b) : (i : ι) → E i) j‖ from rfl]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ j
  · rw [dist_eq_norm, show ‖b j - c j‖ = ‖(↑(b - c) : (i : ι) → E i) j‖ from rfl]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero _ j

/--
Lemmas about equality of norms in an ultrametric seminormed additive group.

In a type `S` with `[SeminormedAddGroup S]` and `[IsUltrametricDist S]`, the ultrametric
(non-Archimedean) triangle inequality implies a strong “dominance” principle: if the norm of a
difference (or sum) is strictly smaller than one of the two norms, then the two norms must be equal.

This file provides four convenient variants:

* `norm_eq_of_norm_sub_lt_left`: if `‖x - y‖ < ‖x‖` then `‖x‖ = ‖y‖`.
* `norm_eq_of_norm_sub_lt_right`: if `‖x - y‖ < ‖y‖` then `‖x‖ = ‖y‖`.
* `norm_eq_of_norm_add_lt_left`: if `‖x + y‖ < ‖x‖` then `‖x‖ = ‖y‖`.
* `norm_eq_of_norm_add_lt_right`: if `‖x + y‖ < ‖y‖` then `‖x‖ = ‖y‖`.

The proofs are straightforward wrappers around
`IsUltrametricDist.norm_eq_of_add_norm_lt_max`, using simple rewriting
to convert between subtraction and addition and to manage negations.
-/
theorem norm_eq_of_norm_add_lt_left {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x + y‖ < ‖x‖) : ‖x‖ = ‖y‖ :=
  IsUltrametricDist.norm_eq_of_add_norm_lt_max <| by simp_all [lt_sup_iff, true_or]

theorem norm_eq_of_norm_add_lt_right {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x + y‖ < ‖y‖) : ‖x‖ = ‖y‖ :=
  IsUltrametricDist.norm_eq_of_add_norm_lt_max <| by simp_all [lt_sup_iff, or_true]

theorem norm_eq_of_norm_sub_lt_left {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x - y‖ < ‖x‖) : ‖x‖ = ‖y‖ := by
  rw [← norm_neg y]
  exact norm_eq_of_norm_add_lt_left (by rwa [sub_eq_add_neg] at h)

theorem norm_eq_of_norm_sub_lt_right {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ :=
  (norm_eq_of_norm_sub_lt_left (by rwa [← norm_neg, neg_sub])).symm

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
    refine UniformSpace.Completion.induction_on₃ x y z (isClosed_le ?_ ?_) fun a b c => ?_
    · exact UniformSpace.Completion.continuous_dist (by fun_prop) (by fun_prop)
    · exact Continuous.max
        (UniformSpace.Completion.continuous_dist (by fun_prop) (by fun_prop))
        (UniformSpace.Completion.continuous_dist (by fun_prop) (by fun_prop))
    · simp_rw [UniformSpace.Completion.dist_eq]
      exact IsUltrametricDist.dist_triangle_max a b c

/-
`PUnit` has an ultrametric distance.

This is immediate because all points in `PUnit` are equal, hence all distances are `0`, and
the strong triangle inequality is trivial.
-/
instance instIsUltrametricDistPUnit : IsUltrametricDist PUnit where
  dist_triangle_max x y z := by simp
