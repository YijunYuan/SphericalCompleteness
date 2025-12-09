import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
open Metric
open Filter

-- Mathlib.Topology.UniformSpace.Cauchy, after CauchySeq.subseq_mem
theorem CauchySeq.subseq_mem' {α : Type u} [uniformSpace : UniformSpace α] {V : ℕ → SetRel α α}
    (hV : ∀ (n : ℕ), V n ∈ uniformity α) {u : ℕ → α} (hu : CauchySeq u) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ {n m: ℕ} (h : φ n ≤ m), (u (φ n), u m) ∈ V n := by
  sorry

theorem foo {α : Type*} [PseudoMetricSpace α] {u : ℕ → α}
    (hu : CauchySeq u) : ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∀ {n m: ℕ}
    (_h : φ n ≤ m),  dist (u (φ n)) (u m) < 1 / (2 : ℝ) ^ n :=
  CauchySeq.subseq_mem' (fun n ↦ Metric.dist_mem_uniformity (by positivity)) hu

noncomputable def dcidx {α : Type*} [PseudoMetricSpace α] {seq : ℕ → α}
  (hseq : CauchySeq seq) (n : ℕ) : ℕ :=
  match n with
  | 0 =>
      ((Metric.cauchySeq_iff.1 hseq) 1 zero_lt_one).choose
  | n + 1 => max (1 + dcidx hseq n) ((Metric.cauchySeq_iff.1 hseq)
      (1 / (2 : ℝ) ^ (n + 1)) (by positivity)).choose

lemma dcidx_prop {α : Type*} [PseudoMetricSpace α] {seq : ℕ → α}
  (hseq : CauchySeq seq) (k : ℕ) :
  ∀ n > (dcidx hseq k), dist (seq n) (seq (dcidx hseq k)) < 1 / (2 : ℝ) ^ k := by
  intro n hn
  if hk : k = 0 then
    simp [hk, dcidx]
    rw [Metric.cauchySeq_iff] at hseq
    have := (hseq 1 zero_lt_one).choose_spec
    apply this
    · rw [hk] at hn
      unfold dcidx at hn
      linarith
    · exact Nat.le_refl _
  else
    have : k = (k - 1) + 1 := by omega
    rw [this, dcidx]
    have this':= ((Metric.cauchySeq_iff.1 hseq) (1 / (2 : ℝ) ^ k) (by norm_num)).choose_spec
    simp only [Nat.sub_one_add_one hk]
    apply this'
    · rw [this] at hn
      unfold dcidx at hn
      simp at hn
      replace hn := hn.2
      apply le_of_lt
      convert hn
      unfold Inv.inv HDiv.hDiv Real.instDivInvMonoid instHDiv
      unfold DivInvMonoid.div' Real.instInv
      simp
    · exact
      Nat.le_max_right _ _

theorem completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter
  (α : Type*) [PseudoMetricSpace α] :
    CompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄ ⦃ri : ℕ → NNReal⦄,
      Antitone (fun i => closedBall (ci i) (ri i)) →
      Filter.Tendsto ri atTop (nhds 0) →
      (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  constructor
  · intro hc ci ri hanti htd
    apply Metric.nonempty_iInter_of_nonempty_biInter
    · exact fun _ ↦ isClosed_closedBall
    · exact fun _ ↦ isBounded_closedBall
    · intro n
      simp only [Set.nonempty_iInter, Set.mem_iInter, mem_closedBall, dist_le_coe]
      use ci n
      intro i hi
      specialize hanti hi
      simp at hanti
      refine mem_closedBall.mp <| hanti ?_
      simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
    · refine Metric.tendsto_atTop'.mpr ?_
      rw [Metric.tendsto_atTop'] at htd
      intro ε hε
      specialize htd (ε / 2) (by linarith)
      use htd.choose
      replace htd := htd.choose_spec
      intro n hn
      specialize htd n hn
      simp only [dist_zero_right, Real.norm_eq_abs]
      rw [abs_eq_self.2]
      · refine lt_of_le_of_lt (diam_closedBall (ri n).prop) ?_
        simp [NNReal.dist_eq] at htd
        linarith
      · exact diam_nonneg
  · intro h
    refine UniformSpace.complete_of_cauchySeq_tendsto ?_
    intro seq hseq


    sorry


class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty

open Classical in
instance instCompleteOfSphericallyComplete (α : Type*)
  [PseudoMetricSpace α] [sc : SphericallyCompleteSpace α] : CompleteSpace α := by
  rw [completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter]
  exact fun _ _ hanti _ ↦ sc.isSphericallyComplete hanti

#check NormedField.toValued

#check NormedSpace

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

lemma closedBall_prod_eq {E F : Type*}
[SeminormedAddCommGroup E] [NormedSpace K E]
[SeminormedAddCommGroup F] [NormedSpace K F]
(c : E × F) (r : ℝ) :
    closedBall c r = (closedBall c.1 r) ×ˢ (closedBall c.2 r) := by
  rw [closedBall_prod_same]


theorem direct_sum_spherically_complete {E F : Type*}
[SeminormedAddCommGroup E] [NormedSpace K E]
[SeminormedAddCommGroup F] [NormedSpace K F]
[SphericallyCompleteSpace E] [SphericallyCompleteSpace F] :
    SphericallyCompleteSpace (E × F) where
  isSphericallyComplete := by
    intro ci ri hanti
    have hE : Antitone (fun i => closedBall (ci i).1 (ri i)) := by
      intro m n hmn
      simp
      specialize hanti hmn
      simp at hanti
      have hprod:=
        closedBall_prod_eq (K := K) (E := E) (F := F) (c := ci n) (r := ri n)
      rw [hprod] at hanti
      replace hprod:=
        closedBall_prod_eq (K := K) (E := E) (F := F) (c := ci m) (r := ri m)
      rw [hprod] at hanti

      sorry
    sorry
