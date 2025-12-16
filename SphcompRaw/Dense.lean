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

theorem diam_eq_radius_of_dense_ultrametric {α : Type*}
[dnf : DenselyNormedField α] [hiud : IsUltrametricDist α]
{z : α} {r : ℝ≥0} :
diam (closedBall z r) = r := by
  refine eq_of_le_of_ge diam_le_radius_of_ultrametric ?_
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

lemma test {α : Type*}
[dnf : DenselyNormedField α]
(z : α) {r : ℝ≥0} {r' : ℝ≥0} (hr : r' < r) :
∃ x y : α, x ∈ closedBall z r ∧ y ∈ closedBall z r ∧  nndist x y ∈ Set.Ioo r' r := by
  rcases dnf.lt_norm_lt r' r r'.prop hr with ⟨δ, hδ1, hδ2⟩
  use z + δ, z
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · simp only [mem_closedBall, dist_self_add_left, le_of_lt hδ2]
  · simp only [mem_closedBall, dist_self, zero_le_coe]
  · simp only [nndist, dist_self_add_left, Set.mem_Ioo]
    exact ⟨hδ1, hδ2⟩

lemma noname {α : Type*} [dnf : DenselyNormedField α] [hiud : IsUltrametricDist α]
-- Ball B(c,r) with positive diameter d
(c₀ : α) (r₀ : ℝ≥0)
--
(r₁ : ℝ≥0) (hr : r₁ ∈ Set.Ioo 0 r₀)
--
(z : α) :
∃ c₁ : α,
  closedBall c₁ r₁ ⊆ closedBall c₀ r₀ ∧
  z ∉ closedBall c₁ r₁
  := by
  rcases test c₀ hr.out.2 with ⟨x, y, hx, hy, hxy⟩
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
    exact ⟨le_of_lt <| lt_of_le_of_lt ha hr.out.2, hy⟩
  else
    refine ⟨x, ⟨fun a ha ↦ ?_, hzx⟩⟩
    simp only [Set.mem_Ioo, mem_closedBall, not_le] at *
    refine le_trans (hiud.dist_triangle_max a x c₀) ?_
    simp only [sup_le_iff]
    exact ⟨le_of_lt <| lt_of_le_of_lt ha hr.2, hx⟩

instance not_spherically_complete_of_dense_separable_ultrametric
{α : Type*} [dnf : DenselyNormedField α] [hiud : IsUltrametricDist α] [hs' : SeparableSpace α] :
IsEmpty (SphericallyCompleteSpace α) := by

  sorry

#check PadicComplex
