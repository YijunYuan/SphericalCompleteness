import SphericalCompleteness.NormedVectorSpace.Orthogonal.Basic
import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.SupportingResults
import Mathlib.Algebra.Module.Submodule.Ker

open Metric

namespace SphericallyCompleteSpace

theorem orth_of_orthcomp
  (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E]
  [IsUltrametricDist E] [NormedSpace 𝕜 E] (F : Submodule 𝕜 E) [SphericallyCompleteSpace ↥F]
  (T : E →L[𝕜] ↥F) (hT1 : ∀ (a : E) (b : a ∈ F), T a = ⟨a, b⟩)
  : IsCompl F (LinearMap.ker T) := by
  refine IsCompl.of_eq ?_ ?_
  · ext x
    simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro h
      specialize hT1 x h.1
      simp only [h.2] at hT1
      exact (AddSubmonoid.mk_eq_zero F.toAddSubmonoid).mp (id (Eq.symm hT1))
    · intro h
      rw [h]
      simp only [zero_mem, map_zero, and_self]
  · ext x
    simp only [Submodule.mem_top, iff_true]
    rw [(by abel : x = (T x) + (x - T x))]
    refine Submodule.add_mem_sup (T x).prop <| LinearMap.sub_mem_ker_iff.mpr ?_
    simp only [SetLike.coe_mem, hT1, Subtype.coe_eta]

theorem exists_orthproj_of_spherically_complete_space
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
∃ T : E →L[𝕜] ↥F, (∀ a ∈ F, T a = a) ∧ ‖T‖ ≤ 1 := by
  have := @exists_extension_opNorm_le 𝕜 _ E _ _ _ F F _ _ _ _
    (ContinuousLinearMap.id _ _) {0} (by simp)  (fun _ => 1) (by simp) (by simp) (by simp)
  simp only [ContinuousLinearMap.coe_id', id_eq, Subtype.forall, Set.mem_singleton_iff, forall_eq,
    sub_zero] at this
  rcases this with ⟨T, hT1, hT2⟩
  refine ⟨T, ⟨fun a ha => ?_, hT2⟩⟩
  simp only [hT1 a ha]

noncomputable def OrthComp (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F]
: Submodule 𝕜 E :=
LinearMap.ker (exists_orthproj_of_spherically_complete_space 𝕜 F).choose

theorem isCompl_orthcomp (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
IsCompl F (OrthComp 𝕜 F) := by
  unfold OrthComp
  apply orth_of_orthcomp
  have := (exists_orthproj_of_spherically_complete_space 𝕜 F).choose_spec.1
  intro a ha
  specialize this a ha
  exact SetLike.coe_eq_coe.mp this

theorem sorth_orthcomp (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
(F ⟂ₛ (OrthComp 𝕜 F)) := by
  unfold OrthComp
  let T := (exists_orthproj_of_spherically_complete_space 𝕜 F).choose
  let hT1 := (exists_orthproj_of_spherically_complete_space 𝕜 F).choose_spec.1
  let hT2 := (exists_orthproj_of_spherically_complete_space 𝕜 F).choose_spec.2
  rw [sorth_symm]
  unfold SOrth MOrth
  intro x hx
  simp only [LinearMap.mem_ker] at hx
  refine eq_of_le_of_ge ?_ ?_
  · rw [← dist_zero, dist_comm]
    exact infDist_le_dist_of_mem <| zero_mem F
  · apply (le_infDist (Submodule.nonempty F)).2
    intro y hy
    rw [dist_eq_norm]
    have : ‖y‖ ≤ ‖x - y‖ := by
      have : T (x - y) = -y := by
        simp only [T, map_sub, hx, zero_sub, NegMemClass.coe_neg, neg_inj]
        apply hT1
        exact hy
      rw [← norm_neg, ← this]
      have := (ContinuousLinearMap.opNorm_le_iff zero_le_one).1 hT2 (x - y)
      simpa only [map_sub, AddSubgroupClass.coe_sub, ge_iff_le, AddSubgroupClass.coe_norm, one_mul]
    nth_rw 1 [(by abel : x = (x - y) + y)]
    refine le_trans (iud.norm_add_le_max _ _) ?_
    simp only [this, sup_of_le_left, le_refl]

lemma morth_of_mem_orthComp (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F]
{x : E} (hx : x ∈ OrthComp 𝕜 F) :
(x ⟂ₘ F) := by

  sorry

noncomputable def OrthProj (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
E →L[𝕜] ↥F :=
(exists_orthproj_of_spherically_complete_space 𝕜 F).choose

theorem norm_OrthProj_le_one (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
‖OrthProj 𝕜 F‖ ≤ 1 := by
  unfold OrthProj
  exact (exists_orthproj_of_spherically_complete_space 𝕜 F).choose_spec.2

theorem OrthProj_id (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
∀ a ∈ F, (OrthProj 𝕜 F) a = a := by
  unfold OrthProj
  exact (exists_orthproj_of_spherically_complete_space 𝕜 F).choose_spec.1

theorem orthcomp_eq_ker_OrthProj (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
OrthComp 𝕜 F = LinearMap.ker (OrthProj 𝕜 F) := by
  unfold OrthComp OrthProj
  rfl

theorem orthproj_idempotent (𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [iud : IsUltrametricDist E]
[NormedSpace 𝕜 E]
(F : Submodule 𝕜 E) [SphericallyCompleteSpace F] :
∀ x : E, (OrthProj 𝕜 F) ((OrthProj 𝕜 F) x) = (OrthProj 𝕜 F) x :=
  fun x => SetLike.coe_eq_coe.mp <| OrthProj_id 𝕜 F ((OrthProj 𝕜 F) x) (OrthProj 𝕜 F x).prop

end SphericallyCompleteSpace
