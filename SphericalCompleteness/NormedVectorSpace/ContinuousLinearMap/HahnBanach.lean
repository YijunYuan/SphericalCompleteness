/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

/-!
# Non-Archimedean Hahn-Banach

The non-Archimedean Hahn-Banach extension theorem.
-/

@[expose] public section

open ContinuousLinearMap

namespace SphericallyCompleteSpace

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
  (D : Submodule 𝕜 E)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
The **non-Archimedean Hahn–Banach theorem**, spherically complete domain form.

If the source subspace `D` is spherically complete, then any continuous linear map
`f : D →L[𝕜] F` extends to `f' : E →L[𝕜] F` that agrees with `f` on `D` and preserves the operator
norm, `‖f'‖ = ‖f‖`. Here the extension is concrete: `f` is precomposed with the norm-nonincreasing
orthogonal projection `orthProj 𝕜 D` onto `D`, which exists precisely because `D` is spherically
complete.
-/
theorem hahn_banach [hd : SphericallyCompleteSpace D] (f : D →L[𝕜] F) :
    ∃ f' : E →L[𝕜] F, (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖ := by
  use comp f (orthProj 𝕜 D)
  refine ⟨fun v hv ↦ ?_, le_antisymm ?_ ?_⟩
  · rw [comp_apply, (SetLike.coe_eq_coe.mp <| orthProj_id 𝕜 D v hv : ((orthProj 𝕜 D) v) = ⟨v,hv⟩)]
  · exact (opNorm_comp_le f _).trans
      (mul_le_of_le_one_right (norm_nonneg f) (norm_orthProj_le_one 𝕜 D))
  · refine (opNorm_le_iff <| opNorm_nonneg (f.comp (orthProj 𝕜 D))).mpr fun x ↦ ?_
    have hproj' : (orthProj 𝕜 D) (x : E) = x :=
      SetLike.coe_eq_coe.mp (orthProj_id 𝕜 D x x.prop)
    simpa [ContinuousLinearMap.comp_apply, hproj'] using le_opNorm (f.comp (orthProj 𝕜 D)) (x : E)

/--
The **non-Archimedean Hahn–Banach theorem**, spherically complete codomain form.

If the *target* `F` is spherically complete, then any continuous linear map `f : D →L[𝕜] F` from a
submodule `D` extends to `f' : E →L[𝕜] F` agreeing with `f` on `D` and preserving the operator norm,
`‖f'‖ = ‖f‖`. Unlike `hahn_banach`, no completeness assumption is placed on `D`; the extension is
built by iterating the codimension-one step `exists_extension_codimOne` over all of `E`, which is
why spherical completeness is required on the side where the values live. -/
theorem hahn_banach' [IsUltrametricDist F] [hf : SphericallyCompleteSpace F] (f : D →L[𝕜] F) :
    ∃ f' : E →L[𝕜] F, (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖ := by
  if hf : f = 0 then exact ⟨0, ⟨fun v hv ↦ by simp [hf], by simp [hf]⟩⟩
  else
    rcases @exists_extension_opNorm_le 𝕜 _ E _ _ _ D F _ _ _ _ f {0}
      (by simp) (fun _ ↦ ContinuousLinearMap.opNorm f)
      (fun _ ↦ norm_pos_iff.mpr hf)
      (fun U V ↦ by rw [U.2, V.2, sub_zero, norm_zero, max_self]; exact opNorm_nonneg f)
      (fun U a ↦ by rw [U.2]; simp only [zero_apply, sub_zero]; exact le_opNorm f a)
      with ⟨f', hf1, hf2⟩
    use f'
    simp only [Subtype.forall, Set.mem_singleton_iff, forall_eq, sub_zero] at hf2
    refine ⟨fun v hv ↦ hf1 ⟨v, hv⟩, le_antisymm hf2 ?_⟩
    refine (opNorm_le_iff <| opNorm_nonneg f').mpr fun a ↦ ?_
    simpa [AddSubgroupClass.coe_norm, hf1 a] using le_opNorm f' (a : E)

end

end SphericallyCompleteSpace
