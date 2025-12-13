import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

open Metric
open Filter
open TopologicalSpace
open NNReal

lemma closure_eq_icc_iff {a b : ℝ} (hab : a < b) (S : Set ℝ) :
  Set.Icc a b ⊆ closure S  ↔
    ∀ a' b' : ℝ, a' < b' → Set.Icc a' b' ⊆ Set.Icc a b → ∃ s ∈ S, s ∈ Set.Icc a' b' := by
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
    exact False.elim <| hc s hs <| this <| Set.mem_Icc_iff_abs_le.1 <| le_of_lt hs'
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
      rw [Set.mem_Icc, ←hh] at hw2
      refine ⟨hw1, abs_sub_lt_iff.mpr ⟨?_, by linarith⟩⟩
      replace hw2 := hw2.2
      rw [add_comm, ← sub_le_iff_le_add] at hw2
      exact lt_of_le_of_lt hw2 <|
        lt_of_le_of_lt (min_le_left (ε / 2) (b - z)) (div_two_lt_of_pos hε)
    else
    specialize h (z - min (ε / 2) (z - a)) z (by
      simp only [sub_lt_self_iff, lt_inf_iff, hε, div_pos_iff_of_pos_left, Nat.ofNat_pos, sub_pos,
        lt_of_le_of_ne hz.out.1 (Ne.symm hh), and_self]
      ) (by
      refine Set.Icc_subset_Icc ?_ hz.out.2
      rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
      exact min_le_right (ε / 2) (z - a)
      )
    rcases h with ⟨w, hw1, hw2⟩
    use w
    refine ⟨hw1, ?_⟩
    rw [abs_sub_comm]
    refine abs_sub_lt_iff.mpr ?_
    simp only [Set.mem_Icc, tsub_le_iff_right] at hw2
    constructor
    · rw [sub_lt_iff_lt_add]
      refine lt_of_le_of_lt hw2.1 ?_
      nth_rw 1 [add_comm]
      simp only [add_lt_add_iff_right, inf_lt_iff, half_lt_self_iff, hε, true_or]
    · linarith

class DensePseudoMetricSpace (α : Type*) extends PseudoMetricSpace α where
  is_dense : ∀ z : α, ∀ ε : ℝ≥0,
  closure (Set.image2 dist (closedBall z ε) (closedBall z ε)) = Set.Icc 0 (diam (closedBall z ε))

theorem test {α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α] (z : α) (r : ℝ≥0) :
diam (closedBall z r) ≤ r := by
  apply diam_le_of_forall_dist_le
  · exact r.prop
  · intro x hx y hy
    simp only [closedBall, Set.mem_setOf_eq] at hx hy
    rw [dist_comm] at hy
    have := hiud.dist_triangle_max x z y
    grind only [= max_def]

theorem test' {α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α] (z : α) (r : ℝ≥0)
(h : ∃ z' : α, dist z z' = r) :
diam (closedBall z r) = r := by
  refine eq_of_le_of_ge (test _ _) ?_
  rw [← h.choose_spec]
  refine dist_le_diam_of_mem isBounded_closedBall ?_ ?_
  · simp only [mem_closedBall, dist_self, dist_nonneg]
  · simp only [mem_closedBall, dist_comm, le_refl]

lemma noname {α : Type*} [hdpm : DensePseudoMetricSpace α] [hiud : IsUltrametricDist α]
-- Ball B(c,r) with positive diameter d
(c : α) (r : ℝ) (hr : r > 0)
(d : ℝ) (hd : d > 0) (hdi : diam (closedBall c r) = d)
--
(d' : ℝ) (hd' : d' ∈ Set.Ioo 0 d) (z : α) :
∃ c' : α, ∃ r' : ℝ≥0, ∃ d'' : ℝ,
  closedBall c' r' ⊆ closedBall c r ∧
  z ∉ closedBall c' r' ∧
  diam (closedBall c' r') = d''
  := by
  replace hdpm := hdpm.is_dense c ⟨r, by linarith⟩

  sorry
