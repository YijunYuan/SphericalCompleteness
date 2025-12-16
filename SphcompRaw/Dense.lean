import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.Complex
import SphcompRaw.Basic
open Metric
open Filter
open TopologicalSpace
open NNReal

lemma icc_subset_closure_iff {a b : ℝ} (hab : a < b) (S : Set ℝ) :
  Set.Icc a b ⊆ closure S  ↔
    ∀ a' b' : ℝ, a' < b' → Set.Icc a' b' ⊆ Set.Icc a b → ∃ s ∈ S, s ∈ Set.Ioo a' b' := by
  constructor
  · intro h a' b' ha'b' hi
    by_contra hc
    push_neg at hc
    let c := (a' + b') / 2
    have hc' : c ∈ Set.Icc a' b' := by
      simp only [c, Set.mem_Icc]
      exact ⟨by linarith, by linarith⟩
    have hi' := Real.mem_closure_iff.1 <| h <| hi hc'
    rcases (hi' ((b' - c) / 2) (by unfold c; linarith)) with ⟨s, hs, hs'⟩
    rw [← abs_neg,neg_sub] at hs'
    have : Set.Icc (c - (b' - c) / 2) (c + (b' - c) / 2) ⊆ Set.Icc a' b' := by
      simp only [c]
      rw [Set.Icc_subset_Icc_iff]
      · exact ⟨by linarith, by linarith⟩
      · linarith
    simp only [abs_lt, neg_lt_sub_iff_lt_add, c] at hs'
    obtain ⟨hs'1, hs'2⟩ := hs'
    exact False.elim <| hc s hs <| Set.mem_Ioo.1 ⟨by linarith, by linarith⟩
  · intro h z hz
    rw [Real.mem_closure_iff]
    intro ε hε
    if hh : z = a then
      specialize h a (a + min (ε / 2) (b - a)) (by
        simp only [lt_add_iff_pos_right, lt_inf_iff, sub_pos]
        exact ⟨by linarith,hab⟩
      ) (by
        refine Set.Icc_subset_Icc_right ?_
        rw [add_comm, ← le_sub_iff_add_le]
        exact min_le_right (ε / 2) (b - a)
      )
      rcases h with ⟨w, hw1, hw2⟩
      use w
      rw [Set.mem_Ioo, ←hh] at hw2
      refine ⟨hw1, abs_sub_lt_iff.mpr ⟨?_, by linarith⟩⟩
      replace hw2 := hw2.2
      rw [add_comm, ← sub_lt_iff_lt_add] at hw2
      exact lt_trans hw2 <|
        lt_of_le_of_lt (min_le_left (ε / 2) (b - z)) (div_two_lt_of_pos hε)
    else
    specialize h (z - min (ε / 2) ((z - a) / 2)) z (by
      simp only [sub_lt_self_iff, lt_inf_iff, hε, div_pos_iff_of_pos_left, Nat.ofNat_pos, sub_pos,
        lt_of_le_of_ne hz.out.1 (Ne.symm hh), and_self]
      ) (by
      refine Set.Icc_subset_Icc ?_ hz.out.2
      rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
      refine le_of_lt <| lt_of_le_of_lt (min_le_right (ε / 2) ((z - a) / 2)) ?_
      simp only [half_lt_self_iff, sub_pos, lt_of_le_of_ne hz.out.1 (Ne.symm hh)]
      )
    rcases h with ⟨w, hw1, hw2⟩
    use w
    refine ⟨hw1, ?_⟩
    rw [abs_sub_comm]
    refine abs_sub_lt_iff.mpr ?_
    simp only [Set.mem_Ioo] at hw2
    rw [sub_lt_iff_lt_add',← sub_lt_iff_lt_add] at hw2
    exact ⟨lt_trans hw2.1 <| lt_of_le_of_lt (min_le_left _ _) <| div_two_lt_of_pos hε, by linarith⟩

theorem diam_le_radius_of_ultrametric {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α]
{z : α} {r : ℝ≥0} :
diam (closedBall z r) ≤ r := by
  apply diam_le_of_forall_dist_le
  · exact r.prop
  · intro x hx y hy
    simp only [closedBall, Set.mem_setOf_eq] at hx hy
    rw [dist_comm] at hy
    have := hiud.dist_triangle_max x z y
    grind only [= max_def]

class IsSphericallyDense (α : Type*) [PseudoMetricSpace α] : Prop where
  spherically_dense :
  ∀ (c : α) (r : ℝ≥0) , diam (closedBall c r) = r

instance diam_eq_radius_of_dense_ultrametric (α : Type*)
[dnf : DenselyNormedField α] [hiud : IsUltrametricDist α] :
IsSphericallyDense α where
spherically_dense := by
  refine fun z r ↦ eq_of_le_of_ge diam_le_radius_of_ultrametric ?_
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

lemma exists_dist_lt_diam_of_spherically_dense {α : Type*} [PseudoMetricSpace α]
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

lemma exists_dist_lt_diam_iff_spherically_dense {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α]
: IsSphericallyDense α ↔
∀ (z : α), ∀ ⦃r r' : ℝ≥0⦄, r' < r →
∃ x y : α, x ∈ closedBall z r ∧ y ∈ closedBall z r ∧  nndist x y ∈ Set.Ioc r' r := by
  refine ⟨exists_dist_lt_diam_of_spherically_dense, ?_⟩
  intro h
  refine {spherically_dense := fun z r ↦ eq_of_le_of_ge diam_le_radius_of_ultrametric ?_}
  by_contra hc
  simp only [not_le] at hc
  rcases h z hc with ⟨x, y, hx, hy, hxy⟩
  have : diam (closedBall z ↑r) < dist x y := hxy.out.1
  have := dist_le_diam_of_mem isBounded_closedBall hx hy
  linarith

lemma exists_sub_closedball_not_belong {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
-- Ball B(c,r) with positive diameter d
(c₀ : α) (r₀ : ℝ≥0)
--
(r₁ : ℝ≥0) (hr : r₁ < r₀)
--
(z : α) :
∃ c₁ : α,
  closedBall c₁ r₁ ⊆ closedBall c₀ r₀ ∧
  z ∉ closedBall c₁ r₁
  := by
  apply exists_dist_lt_diam_of_spherically_dense at hα
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

lemma exists_pos_dist (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] :
∃ z : α × α, nndist z.1 z.2 > 0 := by
  use ((exists_dist_lt_diam_of_spherically_dense hα nemp.some one_lt_two).choose,
  (exists_dist_lt_diam_of_spherically_dense hα nemp.some one_lt_two).choose_spec.choose)
  exact lt_trans zero_lt_one (exists_dist_lt_diam_of_spherically_dense
    hα nemp.some one_lt_two).choose_spec.choose_spec.2.2.out.1

noncomputable def fuck_radius (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] (n : ℕ) : ℝ≥0 :=
(nndist (exists_pos_dist α).choose.1 (exists_pos_dist α).choose.2)
  * (1 + 1 / (n + 1))

lemma fuck_radius_strictanti (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] :
StrictAnti (fun n => fuck_radius α n) := by
  refine strictAnti_nat_of_succ_lt fun n↦ ?_
  unfold fuck_radius
  refine (mul_lt_mul_iff_right₀ (exists_pos_dist α).choose_spec).mpr ?_
  simp only [Nat.cast_add, Nat.cast_one, one_div, add_lt_add_iff_left, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, Nat.cast_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    lt_inv_iff_mul_lt]
  field_simp
  norm_num

lemma fuck_radius_range (α : Type*)
[PseudoMetricSpace α] [hα : IsSphericallyDense α] [nemp : Nonempty α] (n : ℕ) :
(fuck_radius α n) > (fuck_radius α 0) / 2 := by
  unfold fuck_radius
  rw [mul_div_assoc]
  refine (mul_lt_mul_iff_right₀ (exists_pos_dist α).choose_spec).mpr ?_
  simp only [CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true, div_self,
    add_self_div_two, one_div, lt_add_iff_pos_right, inv_pos, add_pos_iff, Nat.cast_pos,
    zero_lt_one, or_true]

noncomputable def fuck_chain_of_ball {α : Type*} [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) (n : ℕ) : α × ℝ≥0 :=
  match n with
  | 0 => ((exists_pos_dist α).choose.1, fuck_radius α 0)
  | n + 1 => ⟨((exists_sub_closedball_not_belong (fuck_chain_of_ball hα' n).1 (fuck_radius α n)
      (fuck_radius α (n + 1)) <| fuck_radius_strictanti α (lt_add_one n))
        (hα'.ofNat hsep.exists_countable_dense.choose n)).choose, fuck_radius α (n+1)⟩

lemma fuck_chain_of_ball_decreasing (α : Type*) [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) :
Antitone (fun n => closedBall (fuck_chain_of_ball hα' n).1 (fuck_chain_of_ball hα' n).2) := by
  refine antitone_nat_of_succ_le <| fun n ↦ ?_
  simp only [fuck_chain_of_ball, mem_closedBall, dist_le_coe, not_le, Set.le_eq_subset]
  have := ((exists_sub_closedball_not_belong (fuck_chain_of_ball hα' n).1 (fuck_radius α n)
      (fuck_radius α (n + 1)) <| fuck_radius_strictanti α (lt_add_one n))
        (hα'.ofNat hsep.exists_countable_dense.choose n)).choose_spec.1
  conv => arg 2; arg 2; unfold fuck_chain_of_ball
  cases n
  · simp only [zero_add, mem_closedBall, dist_le_coe, not_le] at *
    exact this
  · simp only [mem_closedBall, dist_le_coe, not_le] at *
    exact this

lemma not_in_fuck_chain_of_ball (α : Type*) [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) (n : ℕ) :
(hα'.ofNat hsep.exists_countable_dense.choose n).val ∉
closedBall (fuck_chain_of_ball hα' (n + 1)).1 (fuck_chain_of_ball hα' (n + 1)).2 :=
  ((exists_sub_closedball_not_belong (fuck_chain_of_ball hα' n).1 (fuck_radius α n)
      (fuck_radius α (n + 1)) <| fuck_radius_strictanti α (lt_add_one n))
        (hα'.ofNat hsep.exists_countable_dense.choose n)).choose_spec.2

lemma fuck_chain_radius_eq (α : Type*) [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α]
(hα' : Denumerable hsep.exists_countable_dense.choose) (n : ℕ) :
(fuck_chain_of_ball hα' n).2 = (fuck_radius α n):= by
  unfold fuck_chain_of_ball
  cases n
  · simp only
  · simp only

instance not_spherically_complete_of_dense_separable_ultrametric
{α : Type*} [PseudoMetricSpace α]
[hiud : IsUltrametricDist α] [hα : IsSphericallyDense α]
[nemp : Nonempty α] [hsep : SeparableSpace α] :
IsEmpty (SphericallyCompleteSpace α) := by
  by_contra hc
  simp only [isEmpty_Prop, not_not] at hc
  replace hc := hc.isSphericallyComplete
  if hinf : Nonempty (Denumerable hsep.exists_countable_dense.choose) then
    specialize hc <| fuck_chain_of_ball_decreasing α hinf.some
    simp only [Set.nonempty_iInter] at hc
    rcases hc with ⟨z,hz⟩
    have : ∀ i : ℕ, ball z ((fuck_radius α 0) / 2) ⊆
      closedBall (fuck_chain_of_ball hinf.some i).1 ↑(fuck_chain_of_ball hinf.some i).2 := by
      intro i t ht
      simp only [mem_closedBall, mem_ball] at *
      refine le_trans (hiud.dist_triangle_max _ z _) ?_
      replace ht := lt_trans ht ((fuck_chain_radius_eq α hinf.some i) ▸ fuck_radius_range α i)
      simpa only [sup_le_iff] using ⟨le_of_lt ht, hz i⟩
    have : ∀ i : ℕ, ((hinf.some.ofNat hsep.exists_countable_dense.choose i)).val ∉
      ball z ((fuck_radius α 0) / 2) := by
      intro i
      by_contra hc
      exact (not_in_fuck_chain_of_ball α hinf.some i) <| (this (i + 1) hc)
    sorry
  else
    sorry

#check PadicComplex
