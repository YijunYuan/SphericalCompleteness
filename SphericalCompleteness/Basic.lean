import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

import SphericalCompleteness.Complete
import SphericalCompleteness.UltrametricDiam

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

class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  isSphericallyComplete : ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone (fun i => closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty

noncomputable def esoesoa {α : Type u_1} [inst : PartialOrder α]
  {f : ℕ → α} (hanti : Antitone f) (h : ∀ (N : ℕ), ∃ n ≥ N, f n ≠ f N) : ℕ → ℕ := fun n =>
  match n with
  | 0 => 0
  | Nat.succ m => (h (esoesoa hanti h m)).choose

theorem eventually_stable_or_exists_strictanti_of_antitone {α : Type*} [PartialOrder α]
  {f : ℕ → α} (hanti : Antitone f) :
  (∃ N : ℕ, ∀ n ≥ N, f n = f N) ∨ (∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (f ∘ φ)) := by
  if h : ∃ N, ∀ n ≥ N, f n = f N then
    exact Or.inl h
  else
    right
    push_neg at h
    use esoesoa hanti h
    constructor
    · refine strictMono_nat_of_lt_succ <| fun n => ?_
      simp only [esoesoa]
      have := (esoesoa._proof_2 hanti h n).choose_spec
      refine lt_of_le_of_ne this.1 ?_
      by_contra hc
      rw [← hc] at this
      simp only [ge_iff_le, le_refl, ne_eq, not_true_eq_false, and_false] at this
    · refine strictAnti_nat_of_succ_lt <| fun n => lt_of_le_of_ne ?_ ?_
      · refine hanti ?_
        simp only [esoesoa]
        exact (esoesoa._proof_2 hanti h n).choose_spec.1
      · by_contra hc
        simp only [Function.comp_apply, esoesoa, ge_iff_le, ne_eq] at hc
        exact (esoesoa._proof_2 hanti h n).choose_spec.2 hc


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
        simp at hiN
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
