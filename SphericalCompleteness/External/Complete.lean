/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Completeness via nested balls

Auxiliary results relating completeness to nested closed balls whose radii tend to zero.
-/

@[expose] public section

open Metric
open Filter

/--
Characterization of completeness in a (pseudo)metric space via nested closed balls
with radii tending to `0`.

This theorem states that a `PseudoMetricSpace α` is complete if and only if
every *nested* (antitone) sequence of closed balls `closedBall (ci i) (ri i)`
whose radii `ri i` converge to `0` (in the filter sense `Filter.Tendsto ri atTop (nhds 0)`)
has nonempty intersection.

More precisely:
* `Antitone (fun i ↦ closedBall (ci i) (ri i))` expresses that the balls are nested
  (`i ≤ j` implies `closedBall (ci j) (ri j) ⊆ closedBall (ci i) (ri i)`).
* `Filter.Tendsto ri atTop (nhds 0)` means the radii shrink to `0`.
* The conclusion `(⋂ i, closedBall (ci i) (ri i)).Nonempty` asserts there exists
  a point lying in every ball.

This is a standard “Cantor intersection / nested balls” criterion for completeness,
formulated for closed balls and radii in `NNReal`.
-/
theorem completeSpace_iff_nonempty_iInter_closedBall_of_tendsto_zero
    (α : Type*) [PseudoMetricSpace α] :
    CompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄ ⦃ri : ℕ → NNReal⦄,
      Antitone (fun i ↦ closedBall (ci i) (ri i)) →
      Filter.Tendsto ri atTop (nhds 0) →
      (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  constructor
  · intro hcomplete ci ri hanti hri
    apply Metric.nonempty_iInter_of_nonempty_biInter
      (fun n ↦ isClosed_closedBall) (fun n ↦ isBounded_closedBall)
    · refine fun N ↦ ⟨ci N, Set.mem_iInter.2 fun n ↦ Set.mem_iInter.2 fun hn ↦ ?_⟩
      exact hanti hn (mem_closedBall_self (by positivity))
    · have h2 : Tendsto (fun n ↦ 2 * (ri n : ℝ)) atTop (nhds 0) := by
        simpa using (NNReal.tendsto_coe.2 hri).const_mul 2
      exact squeeze_zero (fun n ↦ Metric.diam_nonneg) (fun n ↦ Metric.diam_closedBall
        (ri n).coe_nonneg) h2
  · refine fun hballs ↦ Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    choose N hN using fun n : ℕ ↦
      Metric.cauchySeq_iff.1 hu (((1 / 2 : NNReal) ^ n : NNReal) : ℝ) (by positivity)
    let φ : ℕ → ℕ := Nat.rec (N 0) fun n prev ↦ max (N (n + 1)) (prev + 1)
    have hN_le_φ : ∀ n, N n ≤ φ n := fun n ↦ by induction n <;> simp [φ]
    have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ fun n ↦ by simp [φ]
    let ri : ℕ → NNReal := fun n ↦ 2 * (1 / 2 : NNReal) ^ n
    have hanti : Antitone fun n ↦ closedBall (u (φ n)) (ri n) := by
      refine antitone_nat_of_succ_le fun n x hx ↦ ?_
      simp only [mem_closedBall] at hx ⊢
      have htail : dist (u (φ (n + 1))) (u (φ n)) < (((1 / 2 : NNReal) ^ n : NNReal) : ℝ) :=
        hN n (φ (n + 1)) (le_trans (hN_le_φ n) (le_of_lt (hφ_strict (Nat.lt_succ_self n))))
          (φ n) (hN_le_φ n)
      calc
        dist x (u (φ n)) ≤ dist x (u (φ (n + 1))) + dist (u (φ (n + 1))) (u (φ n)) :=
          dist_triangle _ _ _
        _ ≤ ((ri (n + 1) : NNReal) : ℝ) + (((1 / 2 : NNReal) ^ n : NNReal) : ℝ) :=
          add_le_add hx (le_of_lt htail)
        _ = (ri n : ℝ) := by simpa [ri, pow_succ] using by ring
    have hri : Tendsto ri atTop (nhds 0) := by
      simpa [ri] using ((NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (1 / 2 : NNReal) < 1)).const_mul (2 : NNReal))
    rcases hballs hanti hri with ⟨x, hx⟩
    refine ⟨x, tendsto_nhds_of_cauchySeq_of_subseq hu hφ_strict.tendsto_atTop ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) (NNReal.tendsto_coe.2 hri)
    simpa [Function.comp, mem_closedBall, dist_comm] using Set.mem_iInter.1 hx n
