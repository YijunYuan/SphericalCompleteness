import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

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
* `Antitone (fun i => closedBall (ci i) (ri i))` expresses that the balls are nested
  (`i ≤ j` implies `closedBall (ci j) (ri j) ⊆ closedBall (ci i) (ri i)`).
* `Filter.Tendsto ri atTop (nhds 0)` means the radii shrink to `0`.
* The conclusion `(⋂ i, closedBall (ci i) (ri i)).Nonempty` asserts there exists
  a point lying in every ball.

This is a standard “Cantor intersection / nested balls” criterion for completeness,
formulated for closed balls and radii in `NNReal`.
-/
theorem completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter
  (α : Type*) [PseudoMetricSpace α] :
    CompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄ ⦃ri : ℕ → NNReal⦄,
      Antitone (fun i => closedBall (ci i) (ri i)) →
      Filter.Tendsto ri atTop (nhds 0) →
      (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  constructor
  · intro hcomplete ci ri hanti hri
    have hci_cauchy : CauchySeq ci := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      have hsmall : ∀ᶠ n in atTop, ri n < ⟨ε / 2, le_of_lt (half_pos hε)⟩ := by
        simpa only [Filter.Eventually, Set.mem_setOf_eq, Set.preimage, Set.Iio]
          using hri (Iio_mem_nhds (show 0 < ε / 2 by positivity))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
      refine ⟨N, fun m hm n hn => ?_⟩
      have hm_ball : ci m ∈ closedBall (ci N) (ri N) := (hanti hm) (by simp [mem_closedBall])
      have hn_ball : ci n ∈ closedBall (ci N) (ri N) := (hanti hn) (by simp [mem_closedBall])
      have hm_dist : dist (ci m) (ci N) ≤ (ri N : ℝ) := by simpa [mem_closedBall] using hm_ball
      have hn_dist : dist (ci N) (ci n) ≤ (ri N : ℝ) := by
        simpa [mem_closedBall, dist_comm] using hn_ball
      have hN' : (ri N : ℝ) < ε / 2 := by exact_mod_cast hN N le_rfl
      calc
        dist (ci m) (ci n) ≤ dist (ci m) (ci N) + dist (ci N) (ci n) := dist_triangle _ _ _
        _ ≤ (ri N : ℝ) + (ri N : ℝ) := add_le_add hm_dist hn_dist
        _ < ε := by linarith
    obtain ⟨x, hxlim⟩ := cauchySeq_tendsto_of_complete hci_cauchy
    refine ⟨x, Set.mem_iInter.2 ?_⟩
    intro i
    have hmem : ∀ᶠ n in atTop, ci n ∈ closedBall (ci i) (ri i) :=
      Filter.eventually_atTop.2 ⟨i, fun n hn => (hanti hn) (by simp [mem_closedBall])⟩
    exact isClosed_closedBall.mem_of_tendsto hxlim hmem
  · refine fun hballs => Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    choose N hN using fun n : ℕ =>
      Metric.cauchySeq_iff.1 hu (((1 / 2 : NNReal) ^ n : NNReal) : ℝ) (by positivity)
    let φ : ℕ → ℕ := Nat.rec (N 0) fun n prev => max (N (n + 1)) (prev + 1)
    have hN_le_φ : ∀ n, N n ≤ φ n := by
      intro n
      induction n with
      | zero => simp [φ]
      | succ n ihn => simp [φ]
    have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ fun n => by simp [φ]
    let ri : ℕ → NNReal := fun n => 2 * (1 / 2 : NNReal) ^ n
    have hanti : Antitone fun n => closedBall (u (φ n)) (ri n) := by
      refine antitone_nat_of_succ_le fun n => fun x hx => ?_
      simp only [mem_closedBall] at hx ⊢
      have htail : dist (u (φ (n + 1))) (u (φ n)) < (((1 / 2 : NNReal) ^ n : NNReal) : ℝ) := by
        refine hN n (φ (n + 1)) (le_trans (hN_le_φ n) (le_of_lt (hφ_strict (Nat.lt_succ_self n))))
          (φ n) (hN_le_φ n)
      calc
        dist x (u (φ n)) ≤ dist x (u (φ (n + 1))) + dist (u (φ (n + 1))) (u (φ n)) :=
          dist_triangle _ _ _
        _ ≤ ((ri (n + 1) : NNReal) : ℝ) + (((1 / 2 : NNReal) ^ n : NNReal) : ℝ) := by
          exact add_le_add hx (le_of_lt htail)
        _ = (ri n : ℝ) := by
          simpa [ri, pow_succ] using by ring
    have hri : Tendsto ri atTop (nhds 0) := by
      simpa [ri] using ((NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (1 / 2 : NNReal) < 1)).const_mul (2 : NNReal))
    rcases hballs hanti hri with ⟨x, hx⟩
    refine ⟨x, Metric.tendsto_atTop.2 <| fun ε hε => ?_⟩
    have hbound : Tendsto (fun n : ℕ => (3 : ℝ) * (1 / 2 : ℝ) ^ n) atTop (nhds 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (3 : ℝ))
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 <| hbound (Iio_mem_nhds hε)
    refine ⟨φ n, fun m hm => ?_⟩
    have htail : dist (u m) (u (φ n)) < ((((1 / 2 : NNReal) ^ n : NNReal)) : ℝ) := by
      refine hN n m (le_trans (hN_le_φ n) hm) (φ n) (hN_le_φ n)
    have hx_ball : dist (u (φ n)) x ≤ (ri n : ℝ) := by
      have : x ∈ closedBall (u (φ n)) (ri n) := Set.mem_iInter.1 hx n
      simpa [mem_closedBall, dist_comm] using this
    calc
      dist (u m) x ≤ dist (u m) (u (φ n)) + dist (u (φ n)) x := dist_triangle _ _ _
      _ < ((((1 / 2 : NNReal) ^ n : NNReal)) : ℝ) + (ri n : ℝ) := by
        exact add_lt_add_of_lt_of_le htail hx_ball
      _ = (3 : ℝ) * (1 / 2 : ℝ) ^ n := by
        simpa [ri] using by ring
      _ < ε := hn n le_rfl
