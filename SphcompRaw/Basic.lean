import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic

open Metric
class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → ℝ⦄,
    Antitone (fun i => closedBall (ci i) (ri i)) → Nonempty (⋂ i, ball (ci i) (ri i))

noncomputable def dcballs {α : Type*}
  [PseudoMetricSpace α] [SphericallyCompleteSpace α]
  {seq : ℕ → α} (hseq : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (seq m) (seq n) < ε)
  : ℕ → ℕ × ℝ := fun n =>
  match n with
  | 0 => (1, 1)
  | k + 1 => by
    have hseq' := hseq (1/ (k + 2)) (by
      simp only [one_div, gt_iff_lt, inv_pos]
      linarith
    )
    let c := max hseq'.choose (n + 1)
    let r := min (1/ (k + 2) : ℝ) ((dcballs hseq k).2 - (dist (seq c) (seq (dcballs hseq k).1)))
    exact (c, r)

lemma dcballs_n_lt_first {α : Type*}
  [PseudoMetricSpace α] [SphericallyCompleteSpace α]
  {seq : ℕ → α} (hseq : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (seq m) (seq n) < ε)
  (n : ℕ) : n < (dcballs hseq n).1 := by
  induction n
  · simp [dcballs]
  · simp [dcballs]

lemma dcballs_antitone {α : Type*}
  [PseudoMetricSpace α] [SphericallyCompleteSpace α]
  {seq : ℕ → α} (hseq : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (seq m) (seq n) < ε)
  : Antitone (fun i => closedBall (seq (dcballs hseq i).1) ((dcballs hseq i).2)) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [Set.le_eq_subset]
  intro z hz
  simp only [mem_closedBall] at *
  simp only [dcballs, ge_iff_le, one_div, le_inf_iff] at hz
  exact le_trans (dist_triangle _ _ _) <| add_le_of_le_sub_right hz.2

lemma dcballs_radius_inv_k_succ {α : Type*}
  [PseudoMetricSpace α] [SphericallyCompleteSpace α]
  {seq : ℕ → α} (hseq : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (seq m) (seq n) < ε)
  (i : ℕ) : (dcballs hseq i).2 ≤ 1 / (i + 1) := by
  induction i
  · unfold dcballs
    norm_num
  · simp only [dcballs, ge_iff_le, one_div, Nat.cast_add, Nat.cast_one, inf_le_iff,
    tsub_le_iff_right]
    exact Or.inl <| inv_anti₀ (by linarith) (by linarith)

open Classical in
instance instCompleteOfSphericallyComplete (α : Type*)
  [PseudoMetricSpace α] [sc : SphericallyCompleteSpace α] : CompleteSpace α := by
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro seq hseq
  simp only [Metric.tendsto_nhds, gt_iff_lt, Filter.eventually_atTop, ge_iff_le]
  rw [Metric.cauchySeq_iff] at hseq
  obtain ⟨z, hz⟩ := sc.isSphericallyComplete <| dcballs_antitone hseq
  use z
  intro ε hε
  simp only [Set.mem_iInter, mem_ball] at hz
  replace hz : ∀ (i : ℕ), dist z (seq (dcballs hseq i).1) < 1 / (i + 1) :=
    fun i ↦ lt_of_lt_of_le (hz i) (dcballs_radius_inv_k_succ hseq i)
  let N₀ := Nat.ceil (2 / ε) - 1
  let N := max N₀ (hseq (ε / 2) (by linarith)).choose
  use N
  intro n hn
  have c1 : dist z (seq (dcballs hseq N).1) ≤ ε / 2 := by
    specialize hz N
    refine le_of_lt <| lt_of_lt_of_le hz ?_
    suffices h : 1 / (↑N₀ + 1) ≤ ε / 2 by
      refine le_trans ?_ h
      field_simp; simp; omega
    unfold N₀
    field_simp
    rw [(by aesop : (↑(⌈2 / ε⌉₊ - 1) + 1 : ℝ) = ⌈2 / ε⌉₊)]
    exact (div_le_iff₀' hε).mp <| Nat.le_ceil _
  have c2 : dist (seq (dcballs hseq N).1) (seq n) < ε / 2 := by
    rw [dist_comm]
    apply (hseq (ε / 2) (by linarith)).choose_spec n (le_trans (by omega) hn)
    exact le_trans (by omega) (dcballs_n_lt_first hseq N)
  rw [dist_comm]
  refine lt_of_le_of_lt (dist_triangle _ (seq (dcballs hseq N).1) _) ?_
  linarith

#check NormedField.toValued

#check NormedSpace

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

theorem direct_sum_spherically_complete {E F : Type*}
[SeminormedAddCommGroup E] [NormedSpace K E]
[SeminormedAddCommGroup F] [NormedSpace K F]
[SphericallyCompleteSpace E] [SphericallyCompleteSpace F] :
    SphericallyCompleteSpace (E × F) where
  isSphericallyComplete := by
    intro ci ri hanti

    sorry
