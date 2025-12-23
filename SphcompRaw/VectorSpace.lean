import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

import SphcompRaw.Orthogonal

open Metric
open Filter


namespace SphericallyCompleteSpace

theorem SphericallyComplete.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] :
SphericallyCompleteSpace E := by
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace 𝕜
  infer_instance

instance instSubtypeMemSubmoduleSpanSingletonSet (𝕜 : Type*) [NontriviallyNormedField 𝕜]
[scsk : SphericallyCompleteSpace 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
 (z : E) : SphericallyCompleteSpace (Submodule.span 𝕜 {z}) where
  isSphericallyComplete := by
    if h: z = 0 then
      rw [h,Submodule.span_zero_singleton]
      intro ci ri hanti
      use 0
      simp only [Set.mem_iInter, mem_closedBall, dist_zero, AddSubgroupClass.coe_norm]
      intro i
      simp only [(Submodule.eq_zero_of_bot_submodule (ci i) : ci i = 0), ZeroMemClass.coe_zero,
        norm_zero, NNReal.zero_le_coe]
    else
    intro ci ri hanti
    have := @scsk.isSphericallyComplete (fun n => (Submodule.mem_span_singleton.1 (ci n).prop).choose) (fun n => ⟨ri n / ‖z‖, div_nonneg NNReal.zero_le_coe <| norm_nonneg z⟩) (by
      refine antitone_nat_of_succ_le ?_
      intro n x hx
      simp only [mem_closedBall] at *
      have := hanti (by linarith : n ≤ n + 1)
      simp at this
      have this' : x • ⟨z, Submodule.mem_span_singleton_self z⟩
        ∈ closedBall (ci (n + 1)) ↑(ri (n + 1)) := by
        simp only [SetLike.mk_smul_mk, mem_closedBall, Subtype.dist_eq]
        rw [← (Submodule.mem_span_singleton.1 (ci (n+1)).prop).choose_spec,
          dist_eq_norm, ← sub_smul, norm_smul]
        rw [dist_eq_norm, NNReal.coe_mk] at hx
        exact mul_le_of_le_div₀ NNReal.zero_le_coe (norm_nonneg z) hx
      replace this' := Set.mem_of_mem_of_subset this' this
      simp only [SetLike.mk_smul_mk, mem_closedBall, Subtype.dist_eq] at this'
      simp
      rw [← (Submodule.mem_span_singleton.1 (ci n).prop).choose_spec,
        dist_eq_norm, ← sub_smul, norm_smul, ← dist_eq_norm] at this'
      rw [le_div_iff₀]
      · exact this'
      ·
        sorry)
    sorry

lemma test_ind (𝕜 : Type u_1) [NontriviallyNormedField 𝕜] [SphericallyCompleteSpace 𝕜]
(E : Type u_2) [NormedAddCommGroup E]
[NormedSpace 𝕜 E] [IsUltrametricDist E] [FiniteDimensional 𝕜 E] :
∀ n < Module.finrank 𝕜 E,
  (∃ M : Subspace 𝕜 E, Module.finrank 𝕜 M = n ∧ SphericallyCompleteSpace M)
→ (∃ M' : Subspace 𝕜 E, Module.finrank 𝕜 M' = (n + 1) ∧ SphericallyCompleteSpace M')
:= by
  intro n hn h
  rcases h with ⟨M, hM1, hM2⟩
  haveI : NormedSpace 𝕜 M := Submodule.normedSpace M
  rcases exists_orth_vec 𝕜 M (by linarith) with ⟨z, hz', hz⟩
  use ((Submodule.span 𝕜 {z}) + M)
  let φ := direct_prod_iso_sum_of_orth 𝕜 z M hz
  constructor
  · rw [← FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq.1
    (Nonempty.intro φ.toContinuousLinearEquiv)]
    simp only [Module.finrank_prod, hM1, add_comm, Nat.add_left_cancel_iff]
    exact finrank_span_singleton hz'
  · exact sphericallyCompleteSpace_of_isometryEquiv φ.toIsometryEquiv

theorem sphericallyCompleteSpace_of_finiteDimensional
(𝕜 : Type*) [NontriviallyNormedField 𝕜] [SphericallyCompleteSpace 𝕜]
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[IsUltrametricDist E] [FiniteDimensional 𝕜 E] :
SphericallyCompleteSpace E := by
  suffices h : ∀ n ≤ Module.finrank 𝕜 E,
    (∃ M : Subspace 𝕜 E, Module.finrank 𝕜 M = n ∧ SphericallyCompleteSpace M) by
    rcases h (Module.finrank 𝕜 E) le_rfl with ⟨M, hM1, hM2⟩
    rw [Submodule.eq_top_of_finrank_eq hM1] at hM2
    refine { isSphericallyComplete := fun ci ri h => ?_ }
    rcases @hM2.isSphericallyComplete (fun i => ⟨ci i,trivial⟩) ri (
      fun _ _ hab _ hz => (h hab) hz
    ) with ⟨x, hx⟩
    use x.val
    simpa only [Set.mem_iInter, mem_closedBall, dist_le_coe] using hx
  intro n hn
  induction n
  · case zero => exact ⟨⊥, ⟨finrank_bot 𝕜 E, by infer_instance⟩⟩
  · case succ n hn' => exact test_ind 𝕜 E n hn <| hn' <| Nat.le_of_succ_le hn

--instance (α : Type*) [Field α] [ValuativeRel α] [TopologicalSpace α] [IsNonarchimedeanLocalField α] : MetricSpace α := inferInstance

end SphericallyCompleteSpace
