import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

import SphericalCompleteness.External.Complete
import SphericalCompleteness.External.Ultrametric
import SphericalCompleteness.External.Sequence

open Metric
open Filter

class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty

namespace SphericallyCompleteSpace

theorem sphericallyComplete_iff (α : Type*) [PseudoMetricSpace α] [iud : IsUltrametricDist α] :
  SphericallyCompleteSpace α ↔
  ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone ri →
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  constructor
  · exact fun h ci ri hri hanti => h.isSphericallyComplete hanti
  · intro h
    refine { isSphericallyComplete := ?_ }
    intro c r hanti
    let r' : ℕ → NNReal := fun n => sInf {r k | k ≤ n}
    have hr'_Antitone : Antitone r' := by
      refine antitone_nat_of_succ_le fun n => ?_
      unfold r'
      refine csInf_le_csInf' ?_ ?_
      · use r n, n
      · simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        intro a ha
        use a
        simp only [and_true]
        linarith
    have : Antitone fun i ↦ closedBall (c i) ↑(r' i) := by
      refine antitone_nat_of_succ_le fun n => ?_
      intro x hx
      simp only [mem_closedBall, dist_le_coe, r']  at *
      rw [le_csInf_iff''] at *
      · intro b hb
        rcases hb with ⟨k, hk1, hk2⟩
        rw [← hk2]
        specialize hx (r k) ⟨k, ⟨by linarith, rfl⟩⟩
        rw [← dist_le_coe] at *
        refine le_trans (iud.dist_triangle_max x (c (n + 1)) (c n)) <| max_le_iff.2 ⟨hx, ?_⟩
        refine le_trans ?_ <| diam_le_radius_of_ultrametric (c k) (r k)
        apply dist_le_diam_of_mem isBounded_closedBall
        · refine (hanti (by linarith : k ≤ n + 1)) ?_
          simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
        · refine (hanti hk1) ?_
          simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
      · use r (n + 1), n + 1
      · use r n, n
    specialize h hr'_Antitone this
    simp only [Set.nonempty_iInter, mem_closedBall] at h
    rcases h with ⟨z, hz⟩
    use z
    simp only [Set.mem_iInter, mem_closedBall]
    refine fun i => le_trans (hz i) ?_
    simp only [NNReal.coe_le_coe, r']
    exact csInf_le (OrderBot.bddBelow _) (by use i)

theorem sphericallyComplete_iff' (α : Type*) [PseudoMetricSpace α] [iud : IsUltrametricDist α] :
  SphericallyCompleteSpace α ↔
  ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    StrictAnti ri →
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  constructor
  · exact fun h ci ri hri hanti => h.isSphericallyComplete hanti
  · rw [sphericallyComplete_iff α]
    intro h ci ri hri hanti
    rcases eventually_stable_or_exists_strictanti_of_antitone hri with hc | hc
    · rcases hc with ⟨N, hN⟩
      use (ci N)
      simp only [Set.mem_iInter]
      intro i
      if hiN : i ≤ N then
        refine (hanti hiN) ?_
        simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
      else
        simp only [not_le] at hiN
        rw [mem_closedBall, dist_comm,← mem_closedBall, hN i (by linarith)]
        refine (hanti (by linarith : N ≤ i)) ?_
        simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
    · rcases hc with ⟨φ, hφ1, hφ2⟩
      have := @h (ci ∘ φ) (ri ∘ φ) hφ2
        (antitone_nat_of_succ_le fun n => hanti <| le_of_lt <| hφ1 (by linarith : n < n + 1)
      )
      simp only [Function.comp_apply, Set.nonempty_iInter] at this
      rcases this with ⟨z, hz⟩
      use z
      simp only [Set.mem_iInter]
      intro i
      have := StrictMono.tendsto_atTop hφ1
      rw [Filter.tendsto_atTop_atTop_iff_of_monotone <| StrictMono.monotone hφ1] at this
      rcases this i with ⟨N, hN⟩
      exact (hanti hN) <| hz N

theorem smaller_radius {α : Type*}
  [PseudoMetricSpace α] [SphericallyCompleteSpace α]
  {S : Set (α × NNReal)} [hS : Nonempty ↑S]
  (hw : (∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2)) :
  ∀ (n : ℕ) (s : ↑S), ∃ b ∈ {x | ∃ w ∈ S, w.2 = x},
  b < min (sInf {x | ∃ w ∈ S, w.2 = x} + 1 / 2 ^ n) s.val.2 := by
  intro m s
  exact ((csInf_lt_iff (by simp) (by
      use hS.some.val.2
      simp only [Prod.exists, exists_eq_right, Set.mem_setOf_eq]
      use hS.some.1.1
      simp only [Prod.mk.eta, Subtype.coe_prop]
      : {x | ∃ w ∈ S, w.2 = x}.Nonempty)).1 (by
      simp only [Prod.exists, exists_eq_right, one_div, lt_inf_iff, lt_add_iff_pos_right, inv_pos,
        Nat.ofNat_pos, pow_pos, true_and]
      simpa only [Prod.exists, exists_eq_right] using hw
        s.val s.prop
      : sInf {x | ∃ w ∈ S, w.2 = x} <
      min (sInf {x | ∃ w ∈ S, w.2 = x} + 1 / 2 ^ m)
        s.val.2))

noncomputable def countable_chain_of_ball {α : Type*}
  [PseudoMetricSpace α] [iud : IsUltrametricDist α]
  [SphericallyCompleteSpace α]
  {S : Set (α × NNReal)} [hS : Nonempty S]
  (hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2) : ℕ → ↑S := fun n =>
  match n with
  | 0 => ⟨(smaller_radius hw 0 hS.some).choose_spec.1.out.choose,
     (smaller_radius hw 0 hS.some).choose_spec.1.out.choose_spec.1⟩
  | m + 1 =>
    ⟨(smaller_radius hw (m + 1) (countable_chain_of_ball hw m)).choose_spec.1.out.choose,
     (smaller_radius hw (m + 1) (countable_chain_of_ball hw m)).choose_spec.1.out.choose_spec.1⟩

lemma antitone_of_countable_chain_of_ball {α : Type*}
  [PseudoMetricSpace α] [iud : IsUltrametricDist α]
  [SphericallyCompleteSpace α]
  {S : Set (α × NNReal)} [hS : Nonempty S]
  (hS' : ∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty)
  (hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2) :
  Antitone (fun n => closedBall
    (countable_chain_of_ball hw n).val.1
    (countable_chain_of_ball hw n).val.2) := by
  refine antitone_nat_of_succ_le fun n => ?_
  apply closedBall_subset_closedBall_of_le_radius_of_nonempty_intersection_of_ultrametric
  · conv => arg 1; unfold countable_chain_of_ball
    rw [((smaller_radius hw (n + 1)
      (countable_chain_of_ball hw n))).choose_spec.1.out.choose_spec.2]
    refine le_trans (le_of_lt ((smaller_radius hw (n + 1)
      (countable_chain_of_ball hw n))).choose_spec.2) ?_
    simp only [inf_le_right]
  · apply hS'

lemma exists_add_one_div_pow_two_lt (a b : NNReal) (h : a < b) : ∃ n : ℕ, a + 1 / 2 ^ n < b := by
  let c : NNReal := ⟨b - a, by
    simpa only [sub_nonneg, NNReal.coe_le_coe] using le_of_lt h
    ⟩
  have hc : c > 0 := by
    unfold c
    refine NNReal.coe_pos.mp ?_
    simpa only [NNReal.coe_mk, sub_pos, NNReal.coe_lt_coe]
  rcases NNReal.exists_nat_pos_inv_lt hc with ⟨N, hN1, hN2⟩
  use N
  simp only [gt_iff_lt, one_div, c] at *
  field_simp at hN2
  replace hN2 : 1 < N * (b.val - a.val) := hN2
  field_simp
  suffices hh : 1 < 2 ^ N * (b.val - a.val) by
    nth_rw 1 [mul_sub, lt_sub_iff_add_lt, add_comm] at hh
    have : 2 ^ N * a.val + 1 = ↑(2 ^ N * a + 1) := rfl
    rw [this] at hh
    have : 2 ^ N * b.val = ↑(2 ^ N * b) := rfl
    nth_rw 1 [this, mul_comm] at hh
    exact NNReal.coe_lt_coe.mp hh
  refine lt_trans hN2 ?_
  refine mul_lt_mul_of_lt_of_le_of_pos_of_nonneg ?_ (le_refl _) hc <| pow_nonneg zero_le_two N
  suffices _ : N < 2 ^ N by norm_cast
  exact Nat.lt_two_pow_self

lemma cofinal_of_countable_chain_of_ball {α : Type*}
  [PseudoMetricSpace α] [IsUltrametricDist α]
  [SphericallyCompleteSpace α]
  {S : Set (α × NNReal)} [hS : Nonempty S]
  (hS' : ∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty)
  (hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2) : ∀ s ∈ S, ∃ n : ℕ, closedBall
    (countable_chain_of_ball hw n).val.1
    (countable_chain_of_ball hw n).val.2 ⊆ closedBall s.1 s.2 := by
  intro s hs
  rcases exists_add_one_div_pow_two_lt (sInf {x | ∃ w ∈ S, w.2 = x}) s.2 (hw s hs) with ⟨n, hn⟩
  use n
  apply closedBall_subset_closedBall_of_le_radius_of_nonempty_intersection_of_ultrametric
  · refine le_of_lt <| lt_of_le_of_lt ?_ hn
    conv => arg 1; unfold countable_chain_of_ball
    cases n
    · rw [(smaller_radius hw 0 hS.some).choose_spec.1.out.choose_spec.2]
      exact le_of_lt <| lt_of_lt_of_le (smaller_radius hw 0 hS.some).choose_spec.2 inf_le_left
    · expose_names
      rw [(smaller_radius hw (n + 1)
        (countable_chain_of_ball hw n)).choose_spec.1.out.choose_spec.2]
      exact le_of_lt <| lt_of_lt_of_le (smaller_radius hw (n + 1)
        (countable_chain_of_ball hw n)).choose_spec.2 inf_le_left
  · exact hS' (countable_chain_of_ball hw n) ⟨s, hs⟩

theorem sphericallyComplete_iff'' (α : Type*) [PseudoMetricSpace α] [iud : IsUltrametricDist α] :
  SphericallyCompleteSpace α ↔ (
  ∀ S : Set (α × NNReal), S.Nonempty →
  (∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty) →
  (⋂ w : ↑S, closedBall w.val.1 w.val.2).Nonempty) := by
  refine ⟨fun h S hSne h'=> ?_, fun h => { isSphericallyComplete := ?_ }⟩
  · if hw : ∃ w ∈ S, w.2 = sInf {w.2 | w ∈ S} then
      rcases hw with ⟨w, hwS, hwr⟩
      have : ∀ w' ∈ S, closedBall w.1 w.2 ⊆ closedBall w'.1 w'.2 := by
        intro w' hw'
        apply closedBall_subset_closedBall_of_le_radius_of_nonempty_intersection_of_ultrametric
        · rw [hwr]
          apply csInf_le
          · simp only [Prod.exists, exists_eq_right, OrderBot.bddBelow]
          · simp only [Prod.exists, exists_eq_right, Set.mem_setOf_eq]
            use w'.1
        · exact h' ⟨w,hwS⟩ ⟨w',hw'⟩
      use w.1
      simp only [Set.iInter_coe_set, Set.mem_iInter]
      refine fun v hv => this v hv ?_
      simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
    else
      push_neg at hw
      replace hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2 := by
        refine fun w hw' => lt_of_le_of_ne (csInf_le ?_ ?_) <| Ne.symm <| hw w hw'
        · simp only [Prod.exists, exists_eq_right, OrderBot.bddBelow]
        · simp only [Prod.exists, exists_eq_right, Set.mem_setOf_eq]
          use w.1
      haveI := Set.Nonempty.to_subtype hSne
      rcases h.isSphericallyComplete (antitone_of_countable_chain_of_ball h' hw) with ⟨u, hu⟩
      use u
      simp only [Set.mem_iInter] at *
      intro s
      rcases cofinal_of_countable_chain_of_ball h' hw s s.prop with ⟨n, hn⟩
      exact hn <| hu n
  · intro c r hanti
    specialize h {(c i, r i) | (i : ℕ)} (by
      use (c 0, r 0), 0
      ) (by
      intro w1 w2
      rcases w1.prop with ⟨i1, hi1⟩
      rcases w2.prop with ⟨i2, hi2⟩
      simp only [Set.mem_setOf_eq, ← hi1, ← hi2]
      if hi : i2 ≤ i1 then
        rw [Set.inter_eq_self_of_subset_left <| hanti hi]
        simp only [nonempty_closedBall, NNReal.zero_le_coe]
      else
        rw [Set.inter_eq_self_of_subset_right <| hanti (le_of_lt <| lt_of_not_ge hi)]
        simp only [nonempty_closedBall, NNReal.zero_le_coe]
        )
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.nonempty_iInter] at h
    rcases h with ⟨z, hz⟩
    exact ⟨z, Set.mem_iInter.2 <| fun i => hz ⟨(c i, r i), Exists.intro i (Eq.refl (c i, r i))⟩⟩

instance instCompleteOfSphericallyComplete (α : Type*)
  [PseudoMetricSpace α] [sc : SphericallyCompleteSpace α] : CompleteSpace α := by
  rw [completeSpace_iff_nested_ball_with_radius_tendsto_zero_has_nonempty_inter]
  exact fun _ _ hanti _ ↦ sc.isSphericallyComplete hanti

instance instSpericallyComplete_of_properSpace (α : Type*)
  [PseudoMetricSpace α] [ProperSpace α] : SphericallyCompleteSpace α where
  isSphericallyComplete := by
    intro ci ri hanti
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    <| fun i ↦ closedBall (ci i) ↑(ri i)
    · exact fun _ ↦  hanti (by linarith)
    · exact fun h ↦ nonempty_closedBall.mpr (ri h).prop
    · exact isCompact_closedBall (ci 0) ↑(ri 0)
    · exact fun i ↦ isClosed_closedBall

theorem sphericallyCompleteSpace_of_isometryEquiv {E F : Type*}
  [PseudoMetricSpace E] [PseudoMetricSpace F]
  [he : SphericallyCompleteSpace E]
  (f : E ≃ᵢ F) : SphericallyCompleteSpace F where
  isSphericallyComplete := by
    intro ci ri hanti
    let ci' := fun n => f.symm (ci n)
    have hanti' : Antitone (fun i => closedBall (ci' i) (ri i)) := by
      intro m n hmn
      simp only [Set.le_eq_subset]
      rw [← IsometryEquiv.preimage_closedBall f (ci m) ↑(ri m),
          ← IsometryEquiv.preimage_closedBall f (ci n) ↑(ri n)]
      specialize hanti hmn
      simp only [Set.le_eq_subset] at hanti
      grind only [= Set.subset_def, = Set.mem_preimage]
    rcases he.isSphericallyComplete hanti' with ⟨z',hz'⟩
    simp only [Set.mem_iInter, mem_closedBall, Set.nonempty_iInter] at *
    refine ⟨f z', fun i ↦ ?_⟩
    specialize hz' i
    unfold ci' at hz'
    rw [← IsometryEquiv.apply_symm_apply f (ci i), Isometry.dist_eq]
    · exact hz'
    · exact IsometryEquiv.isometry f

instance Prod.sphericallyCompleteSpace {E F : Type*}
[PseudoMetricSpace E] [PseudoMetricSpace F]
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

open Classical in
instance Pi.sphericallyCompleteSpace {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, PseudoMetricSpace (E i)]
  [hh : ∀ i, SphericallyCompleteSpace (E i)] :
    SphericallyCompleteSpace (∀ i, E i) where
  isSphericallyComplete := by
    intro ci ri hanti
    have hE : ∀ i, Antitone (fun n => closedBall (ci n i) (ri n)) := by
      intro i m n hmn
      simp only [Set.le_eq_subset]
      specialize hanti hmn
      simp only [Set.le_eq_subset] at hanti
      rw [closedBall_pi, closedBall_pi] at hanti
      · intro z hz
        let Z : ((i : ι) → E i) := fun (j : ι) => if hij : j = i then hij ▸ z else (ci n j)
        have : Z ∈ (Set.univ.pi fun b ↦ closedBall (ci n b) ↑(ri n)) := by
          simp only [Z, Set.mem_pi, Set.mem_univ]
          intro j _
          if hij : j = i then
            simp only [hij, ↓reduceDIte]
            cases hij
            simpa only [mem_closedBall, dist_le_coe] using hz
          else
            simp only [hij, ↓reduceDIte, mem_closedBall, dist_self, NNReal.zero_le_coe]
        specialize hanti this
        simp only [Set.mem_pi, Set.mem_univ, forall_const] at hanti
        specialize hanti i
        unfold Z at hanti
        simpa only [↓reduceDIte] using hanti
      · exact (ri m).prop
      · exact (ri n).prop
    use fun i ↦ ((hh i).isSphericallyComplete (hE i)).choose
    simp only [Set.mem_iInter]
    intro i
    rw [closedBall_pi]
    · simp only [Set.mem_pi, Set.mem_univ, forall_const]
      intro j
      exact Set.mem_iInter.1 ((hh j).isSphericallyComplete (hE j)).choose_spec i
    · exact (ri i).prop

instance instSphericallyCompleteSpaceComplex : SphericallyCompleteSpace ℂ  := inferInstance

instance instSphericallyCompleteSpaceReal : SphericallyCompleteSpace ℝ  := inferInstance

instance instSphericallyCompleteOfWeaklyLocallyCompactNormedField
{α : Type*} [NontriviallyNormedField α] [WeaklyLocallyCompactSpace α] :
SphericallyCompleteSpace α := by
  haveI := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace α
  infer_instance

instance instSphericallyCompletePadic {p : ℕ} [Fact (Nat.Prime p)] :
  SphericallyCompleteSpace (ℚ_[p]) := inferInstance

end SphericallyCompleteSpace
