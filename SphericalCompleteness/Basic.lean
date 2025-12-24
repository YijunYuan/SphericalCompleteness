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

namespace SphericallyCompleteSpace

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
