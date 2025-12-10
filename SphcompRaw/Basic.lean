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

lemma dcidx_controlled_converge {α : Type*} [PseudoMetricSpace α] {seq : ℕ → α}
  (hseq : CauchySeq seq) (k : ℕ) :
  ∀ n > (dcidx hseq k), dist (seq n) (seq (dcidx hseq k)) < 1 / (2 : ℝ) ^ k := by
  intro n hn
  if hk : k = 0 then
    simp only [hk, dcidx, ge_iff_le, pow_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    rw [Metric.cauchySeq_iff] at hseq
    apply (hseq 1 zero_lt_one).choose_spec
    · rw [hk, dcidx] at hn
      linarith
    · exact Nat.le_refl _
  else
    have : k = (k - 1) + 1 := by omega
    rw [this, dcidx]
    simp only [Nat.sub_one_add_one hk]
    apply ((Metric.cauchySeq_iff.1 hseq) (1 / (2 : ℝ) ^ k) (by positivity)).choose_spec
    · rw [this, dcidx] at hn
      simp only [ge_iff_le, one_div, gt_iff_lt, sup_lt_iff] at hn
      apply le_of_lt
      convert hn.2
      unfold Inv.inv HDiv.hDiv Real.instDivInvMonoid instHDiv DivInvMonoid.div' Real.instInv
      simp only [one_mul]
    · exact Nat.le_max_right _ _

lemma dcidx_strict_mono {α : Type*} [PseudoMetricSpace α] {seq : ℕ → α}
  (hseq : CauchySeq seq) : StrictMono (dcidx hseq) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  conv => arg 2; unfold dcidx
  simp only [ge_iff_le, one_div, lt_sup_iff, lt_add_iff_pos_left, zero_lt_one, true_or]

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
      refine ⟨ci n, fun i hi ↦ mem_closedBall.mp <| hanti hi ?_⟩
      simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
    · apply Metric.tendsto_atTop'.mpr
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
    refine UniformSpace.complete_of_cauchySeq_tendsto fun seq hseq ↦ ?_
    let ci := fun n => seq (dcidx hseq n)
    let ri : ℕ → NNReal := fun n => ⟨1 / (2 : ℝ) ^ (n - 1 : ℤ), by positivity⟩
    have hanti : Antitone (fun i => closedBall (ci i) (ri i)) := by
      refine antitone_nat_of_succ_le <| fun n z hz ↦ ?_
      simp only [mem_closedBall, ci, ri] at *
      simp only [NNReal.coe_mk] at hz
      refine le_trans (dist_triangle _ (seq (dcidx hseq (n + 1))) _) ?_
      have := dcidx_controlled_converge hseq n ((dcidx hseq (n+1))) (
        dcidx_strict_mono hseq (by norm_num))
      refine le_trans (add_le_add hz (le_of_lt this)) ?_
      field_simp
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, zpow_natCast, one_div,
        NNReal.coe_mk]
      refine (le_mul_inv_iff₀ (by positivity)).mpr ?_
      field_simp
      rw [(by norm_num : ((1 : ℝ) + 1 = 2))]
      apply le_of_eq
      rw [zpow_natCast_sub_one₀ <| Ne.symm (NeZero.ne' 2), mul_div,mul_comm]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_right₀]
    have : Tendsto ri atTop (nhds 0) := by
      simp only [Metric.tendsto_nhds, gt_iff_lt, Filter.eventually_atTop, ge_iff_le]
      intro ε hε
      simp only [one_div, NNReal.dist_eq, NNReal.coe_mk, NNReal.coe_zero, sub_zero, abs_inv, ri]
      obtain ⟨n, hn⟩ := @ENNReal.exists_inv_two_pow_lt ε.toNNReal (by simp [hε])
      refine ⟨n.succ, fun m hm ↦ ?_⟩
      have : (2 : ENNReal)⁻¹ ^ n = ENNReal.ofNNReal ⟨(2 : ℝ)⁻¹ ^ n, by positivity⟩ := by
        refine (ENNReal.toReal_eq_toReal_iff' (LT.lt.ne_top hn) ENNReal.coe_ne_top).mp ?_
        simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, inv_pow,
          ENNReal.coe_toReal, NNReal.coe_mk]
      simp only [this, inv_pow, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_mk,
        Real.coe_toNNReal', lt_sup_iff, inv_neg''] at hn
      replace hn := hn.resolve_right (by norm_num)
      field_simp at hn
      rw [abs_eq_self.2 <| by positivity]
      field_simp
      refine lt_of_lt_of_le hn <| mul_le_mul_of_nonneg_right ?_ <| le_of_lt hε
      rw [zpow_natCast_sub_one₀ (by linarith)]
      field_simp
      rw [← zpow_natCast, ← zpow_eq_pow, ← DivInvMonoid.zpow_succ']
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zpow_eq_pow, ← zpow_natCast]
      exact (zpow_le_zpow_iff_right₀ one_lt_two).mpr (by linarith)
    obtain ⟨x, hx⟩ := h hanti this
    simp only [Set.mem_iInter, mem_closedBall] at hx
    refine ⟨x, Metric.tendsto_atTop'.mpr <| fun ε hε ↦ ?_⟩
    simp only [dist_comm, ci, ri] at *
    obtain ⟨n₁, hn₁⟩ := @ENNReal.exists_inv_two_pow_lt (ε / 4).toNNReal (by simp [hε])
    refine ⟨max n₁ (dcidx hseq n₁), fun m hm ↦ ?_⟩
    have := dcidx_controlled_converge hseq n₁ m (by omega)
    rw [dist_comm] at this
    refine lt_of_le_of_lt (dist_triangle _ (seq (dcidx hseq n₁)) _) ?_
    refine lt_trans (add_lt_add_of_le_of_lt (hx n₁) this) ?_
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zpow_natCast_sub_one₀, one_div,
      inv_div, NNReal.coe_mk]
    rw [(by norm_num : (2 : ENNReal)⁻¹ ^ n₁ = 2⁻¹ ^ (n₁ : ℤ)),
        ENNReal.inv_zpow', ENNReal.zpow_neg] at hn₁
    simp only [zpow_natCast, Real.toNNReal, (by simp; linarith : max (ε / 4) 0 = ε / 4)] at hn₁
    rw [(by norm_num : (2 : ENNReal) ^ n₁ = ((2 : NNReal) ^ n₁ : NNReal)),
        ← ENNReal.coe_inv (by norm_num)] at hn₁
    unfold ENNReal.ofNNReal at hn₁
    rw [WithTop.coe_lt_coe] at hn₁
    field_simp at *
    simp only [← NNReal.coe_lt_coe, NNReal.coe_one, NNReal.coe_mul,
        NNReal.coe_pow, NNReal.coe_ofNat,
        NNReal.coe_mk] at hn₁
    rw [mul_div_assoc',lt_div_iff₀ four_pos] at hn₁
    linarith

class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty

instance instCompleteOfSphericallyComplete (α : Type*)
  [PseudoMetricSpace α] [sc : SphericallyCompleteSpace α] : CompleteSpace α := by
  rw [completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter]
  exact fun _ _ hanti _ ↦ sc.isSphericallyComplete hanti

#check NormedField.toValued

#check NormedSpace

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

theorem direct_sum_spherically_complete {E F : Type*}
[SeminormedAddCommGroup E] [NormedSpace K E]
[SeminormedAddCommGroup F] [NormedSpace K F]
[hse : SphericallyCompleteSpace E] [hsf : SphericallyCompleteSpace F] :
    SphericallyCompleteSpace (E × F) where
  isSphericallyComplete := by
    intro ci ri hanti
    have hE : Antitone (fun i => closedBall (ci i).1 (ri i)) := by
      intro m n hmn
      simp only [Set.le_eq_subset]
      specialize hanti hmn
      simp only [Set.le_eq_subset] at hanti
      rw [← closedBall_prod_same (ci n).1 (r := ri n),
          ← closedBall_prod_same (ci m).1 (r := ri m)] at hanti
      intro z hz
      have : (z , (ci n).2) ∈ closedBall (ci n).1 ↑(ri n) ×ˢ closedBall (ci n).2 ↑(ri n) := by
        simp only [Set.mem_prod, mem_closedBall, dist_self, NNReal.zero_le_coe,and_true]
        simpa only [mem_closedBall] using hz
      exact (Set.mem_prod.1 <| hanti this).1
    have hF : Antitone (fun i => closedBall (ci i).2 (ri i)) := by
      intro m n hmn
      simp only [Set.le_eq_subset]
      specialize hanti hmn
      simp only [Set.le_eq_subset] at hanti
      rw [← closedBall_prod_same (ci n).1 (r := ri n),
          ← closedBall_prod_same (ci m).1 (r := ri m)] at hanti
      intro z hz
      have : ((ci n).1 , z) ∈ closedBall (ci n).1 ↑(ri n) ×ˢ closedBall (ci n).2 ↑(ri n) := by
        simpa only [Set.mem_prod, mem_closedBall, dist_self, NNReal.zero_le_coe, dist_le_coe,
          true_and] using hz
      exact (Set.mem_prod.1 <| hanti this).2
    replace hE := hse.isSphericallyComplete hE
    replace hF := hsf.isSphericallyComplete hF
    simp only [Set.nonempty_iInter, mem_closedBall, Prod.exists] at *
    obtain ⟨xE, hxE⟩ := hE
    obtain ⟨xF, hxF⟩ := hF
    use xE, xF
    intro n
    simpa only [Prod.dist_eq, sup_le_iff] using ⟨hxE n, hxF n⟩
