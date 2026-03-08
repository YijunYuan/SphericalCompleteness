import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace

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
diam (closedBall z r) ≤ r := by
  apply diam_le_of_forall_dist_le
  · exact r.prop
  · intro x hx y hy
    simp only [closedBall, Set.mem_setOf_eq] at hx hy
    rw [dist_comm] at hy
    have := hiud.dist_triangle_max x z y
    grind only [= max_def]

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
  simp only [closedBall, Set.mem_setOf_eq] at hx
  rcases hne with ⟨y, hy1, hy2⟩
  simp only [mem_closedBall] at *
  refine le_trans (hiud.dist_triangle_max x y z2) <| sup_le_iff.2 ⟨?_, hy2⟩
  refine le_trans (hiud.dist_triangle_max x z1 y) <| sup_le_iff.2 ⟨le_trans hx hle, ?_⟩
  simpa only [dist_comm] using le_trans hy1 hle

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
IsUltrametricDist (E →L[𝕜] F) where
  dist_triangle_max := by
    intro f g h
    repeat rw [dist_eq_norm]
    rw [ContinuousLinearMap.opNorm_le_iff]
    · intro x
      have : ‖(f - h) x‖ = ‖(f - g) x + (g - h) x‖ := by
        simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, sub_add_sub_cancel]
      rw [this, max_mul_of_nonneg _ _ (norm_nonneg _)]
      refine le_trans (iud.norm_add_le_max _ _) <| max_le_max ?_ ?_
      · exact ContinuousLinearMap.le_opNorm (f - g) x
      · exact ContinuousLinearMap.le_opNorm (g - h) x
    · simp only [le_sup_iff, norm_nonneg, or_self]

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
  repeat rw [dist_eq_norm, lp.norm_eq_ciSup]
  apply ciSup_le
  intro j
  have : ‖(↑(a - c): (i : ι) → E i) j‖ = ‖a j - c j‖ := rfl
  rw [this, ← dist_eq_norm]
  refine le_trans ((iiud j).dist_triangle_max (a j) (b j) (c j)) ?_
  repeat rw [dist_eq_norm]
  apply max_le_max
  · have : ‖(↑a: (i : ι) → E i) j - (↑b: (i : ι) → E i) j‖ = ‖(↑(a - b) : (i : ι) → E i) j‖ := rfl
    rw [this]
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero
  · have : ‖(↑b: (i : ι) → E i) j - (↑c: (i : ι) → E i) j‖ = ‖(↑(b - c) : (i : ι) → E i) j‖ := rfl
    rw [this]
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero

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
theorem norm_eq_of_norm_sub_lt_left {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x - y‖ < ‖x‖) : ‖x‖ = ‖y‖ := by
  rw [sub_eq_add_neg] at h
  nth_rw 2 [← norm_neg]
  apply IsUltrametricDist.norm_eq_of_add_norm_lt_max
  simp_all only [norm_neg, lt_sup_iff, true_or]

theorem norm_eq_of_norm_sub_lt_right {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  rw [← norm_neg] at h
  simp only [neg_sub] at h
  exact Eq.symm (norm_eq_of_norm_sub_lt_left h)

theorem norm_eq_of_norm_add_lt_left {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x + y‖ < ‖x‖) : ‖x‖ = ‖y‖ := by
  apply IsUltrametricDist.norm_eq_of_add_norm_lt_max
  simp_all only [lt_sup_iff, true_or]

theorem norm_eq_of_norm_add_lt_right {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
{x y : S} (h : ‖x + y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  apply IsUltrametricDist.norm_eq_of_add_norm_lt_max
  simp_all only [lt_sup_iff, or_true]

/--
Lifts the ultrametric inequality on distances from `𝕜` to its uniform completion.

If `𝕜` is a `PseudoMetricSpace` whose distance is ultrametric (`IsUltrametricDist 𝕜`),
then `UniformSpace.Completion 𝕜` inherits an ultrametric distance with respect to the
canonical `dist` coming from `UniformSpace.Completion.instMetricSpace.toDist`.

This instance is useful for transferring non-Archimedean/ultrametric arguments to the
completion, allowing one to work in a complete ultrametric space without changing the
underlying distance structure.
-/
instance instIsUltrametricDistCompletion {𝕜 : Type*} [PseudoMetricSpace 𝕜]
[IsUltrametricDist 𝕜] :
  @IsUltrametricDist (UniformSpace.Completion 𝕜)
  UniformSpace.Completion.instMetricSpace.toDist where
  dist_triangle_max x y z := by
    have := @UniformSpace.Completion.denseRange_coe 𝕜 _
    refine le_of_forall_pos_lt_add <| fun ε hε => ?_
    rcases Metric.mem_closure_iff.1 (this x) (ε / 4) (by linarith) with ⟨x'', hx'1, hx'2⟩
    rcases hx'1 with ⟨x', hx'⟩; rw [← hx'] at hx'2
    rcases Metric.mem_closure_iff.1 (this y) (ε / 4) (by linarith) with ⟨y'', hy'1, hy'2⟩
    rcases hy'1 with ⟨y', hy'⟩; rw [← hy'] at hy'2
    rcases Metric.mem_closure_iff.1 (this z) (ε / 4) (by linarith) with ⟨z'', hz'1, hz'2⟩
    rcases hz'1 with ⟨z', hz'⟩; rw [← hz'] at hz'2
    have : dist x z < dist (↑x' : UniformSpace.Completion 𝕜) ↑z' + ε / 4 + ε / 4 := by
      have t1 := dist_triangle x ↑x' z
      have t2 := dist_triangle ↑x' ↑z' z
      rw [dist_comm] at hz'2
      linarith
    refine lt_trans this ?_
    have t3 := dist_triangle_max x' y' z'
    have t4 := dist_triangle ↑x' x ↑y'
    have t5 := dist_triangle x y ↑y'
    have t6 := dist_triangle ↑y' y ↑z'
    have t7 := dist_triangle y z ↑z'
    have t8 : max (dist x y) (dist y z) + (ε / 4 + ε / 4 + ε / 4 + ε / 4) =
      max (dist x y) (dist y z) + (ε / 4 + ε / 4) + ε / 4 + ε / 4 := by abel
    nth_rw 1 [← UniformSpace.Completion.dist_eq] at t3
    nth_rw 2 [← UniformSpace.Completion.dist_eq] at t3
    nth_rw 3 [← UniformSpace.Completion.dist_eq] at t3
    nth_rw 2 [dist_comm] at t4
    nth_rw 2 [dist_comm] at t6
    nth_rw 3 [(by linarith : ε = ε / 4 + ε / 4 + ε / 4 + ε / 4)]
    rw [t8, max_add]
    nth_rw 1 [add_assoc]; nth_rw 1 [add_assoc]
    simp only [add_lt_add_iff_right]
    exact lt_of_le_of_lt t3 <| max_lt_max (by linarith) (by linarith)

/-
`PUnit` has an ultrametric distance.

This is immediate because all points in `PUnit` are equal, hence all distances are `0`, and
the strong triangle inequality is trivial.
-/
instance instIsUltrametricDistPUnit : IsUltrametricDist PUnit where
  dist_triangle_max x y z := by simp
