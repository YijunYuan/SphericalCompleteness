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
  · refine fun hballs ↦ Metric.complete_of_convergent_controlled_sequences
      (fun n ↦ (1 / 2 : ℝ) ^ n) (fun n ↦ by positivity) fun u hu ↦ ?_
    let ri : ℕ → NNReal := fun n ↦ 2 * (1 / 2 : NNReal) ^ n
    have hanti : Antitone fun n ↦ closedBall (u n) (ri n) := by
      refine antitone_nat_of_succ_le fun n x hx ↦ ?_
      simp only [mem_closedBall] at hx ⊢
      calc
        dist x (u n) ≤ dist x (u (n + 1)) + dist (u (n + 1)) (u n) := dist_triangle _ _ _
        _ ≤ ((ri (n + 1) : NNReal) : ℝ) + (1 / 2 : ℝ) ^ n :=
          add_le_add hx (le_of_lt (hu n (n + 1) n (Nat.le_succ n) le_rfl))
        _ = (ri n : ℝ) := by push_cast [ri]; ring
    have hri : Tendsto ri atTop (nhds 0) := by
      simpa [ri] using ((NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (1 / 2 : NNReal) < 1)).const_mul (2 : NNReal))
    rcases hballs hanti hri with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) (NNReal.tendsto_coe.2 hri)
    simpa [mem_closedBall, dist_comm] using Set.mem_iInter.1 hx n
