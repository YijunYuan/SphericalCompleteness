import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

open ContinuousLinearMap

namespace SphericallyCompleteSpace

class IsHahnBanachExtendable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
(D : Submodule 𝕜 E)
(F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] : Prop where
  extendable : SphericallyCompleteSpace D ∨ SphericallyCompleteSpace F

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
[SphericallyCompleteSpace F] : IsHahnBanachExtendable D F where
  extendable := Or.inr ‹SphericallyCompleteSpace F›

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
[SphericallyCompleteSpace D] : IsHahnBanachExtendable D F where
  extendable := Or.inl ‹SphericallyCompleteSpace D›

theorem hahn_banach {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(D : Submodule 𝕜 E)
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
[ihbe : IsHahnBanachExtendable D F] (f : D →L[𝕜] F) :
∃ f' : E →L[𝕜] F,
  (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖ := by
  rcases ihbe.extendable with hd | hf
  · use comp f (OrthProj 𝕜 D)
    constructor
    · intro v hv
      rw [comp_apply, (SetLike.coe_eq_coe.mp <| OrthProj_id 𝕜 D v hv : ((OrthProj 𝕜 D) v) = ⟨v,hv⟩)]
    · refine eq_of_le_of_ge ((opNorm_le_iff <| opNorm_nonneg f).mpr fun x => ?_) ?_
      · rw [comp_apply]
        refine le_trans (le_opNorm f _) ?_
        have : ‖(OrthProj 𝕜 D) x‖ ≤ 1 * ‖x‖ :=
          le_of_opNorm_le (OrthProj 𝕜 D) (norm_OrthProj_le_one 𝕜 D) x
        simp only [AddSubgroupClass.coe_norm, one_mul] at this
        exact PosMulMono.mul_le_mul_of_nonneg_left (opNorm_nonneg f) this
      · repeat rw [norm_def]
        apply csInf_le_csInf
        · use ‖f‖
          simp only [lowerBounds, AddSubgroupClass.coe_norm, Subtype.forall, Set.mem_setOf_eq,
            and_imp]
          exact fun a ha h => (opNorm_le_iff ha).mpr fun x ↦ h (↑x) x.prop
        · use ‖(f.comp (OrthProj 𝕜 D))‖
          simp only [coe_comp', Function.comp_apply, Set.mem_setOf_eq,
            norm_nonneg, true_and]
          intro x
          rw [← comp_apply]
          exact le_opNorm (f.comp (OrthProj 𝕜 D)) x
        · intro c hc
          simp only [coe_comp', Function.comp_apply, Set.mem_setOf_eq,
            AddSubgroupClass.coe_norm, Subtype.forall] at *
          refine ⟨hc.1, fun a ha => ?_⟩
          convert hc.2 a
          exact Eq.symm (OrthProj_id 𝕜 D a ha)
  · if hf : f = 0 then
      use 0
      simp only [zero_apply, hf, implies_true, norm_zero, and_self]
    else
    rcases @exists_extension_opNorm_le 𝕜 _ E _ _ _ D F _ _ _ _ f {0}
      (by simp) (fun _ => ‖f‖) (by simp [hf]) (by simp) (by
      simpa using fun a ha => le_opNorm f ⟨a, ha⟩
      ) with ⟨f', hf1, hf2⟩
    use f'
    simp only [Subtype.forall, Set.mem_singleton_iff, forall_eq, sub_zero] at hf2
    refine ⟨fun v hv => hf1 ⟨v, hv⟩, eq_of_le_of_ge hf2 ?_⟩
    repeat rw [norm_def]
    apply csInf_le_csInf
    · use ‖f‖
      simp only [lowerBounds, AddSubgroupClass.coe_norm, Subtype.forall, Set.mem_setOf_eq,
        and_imp]
      exact fun a ha h => (opNorm_le_iff ha).mpr fun x ↦ h (↑x) x.prop
    · use ‖f'‖
      simp only [Set.mem_setOf_eq, norm_nonneg, true_and]
      exact fun x => le_opNorm f' x
    · intro c hc
      simp only [AddSubgroupClass.coe_norm, Subtype.forall, Set.mem_setOf_eq] at *
      refine ⟨hc.1, fun a ha => ?_⟩
      simpa only [← (hf1 a ha).symm] using hc.2 a


end SphericallyCompleteSpace
