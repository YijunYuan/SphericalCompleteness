/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

/-!
# Non-Archimedean Hahn-Banach

The non-Archimedean Hahn-Banach extension theorem.
-/

open ContinuousLinearMap

namespace SphericallyCompleteSpace

/--
Hahn–Banach extension theorem in the ultrametric setting, assuming spherical completeness.

Given a nontrivially normed field `𝕜`, normed `𝕜`-spaces `E` and `F` equipped with an
ultrametric distance, a submodule `D : Submodule 𝕜 E` that is spherically complete
(`SphericallyCompleteSpace D`), and a continuous linear map `f : D →L[𝕜] F`,
this theorem produces an extension `f' : E →L[𝕜] F` such that:

* `f'` agrees with `f` on `D` (via the subtype coercion `⟨v, hv⟩`), and
* the operator norm is preserved: `‖f'‖ = ‖f‖`.

This is a norm-preserving extension result (isometric on operator norm) for continuous
linear maps from a spherically complete subspace in a non-Archimedean (ultrametric) context.
-/
theorem hahn_banach {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(D : Submodule 𝕜 E)
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
[hd : SphericallyCompleteSpace D] (f : D →L[𝕜] F) :
∃ f' : E →L[𝕜] F,
  (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧
    ContinuousLinearMap.opNorm f' = ContinuousLinearMap.opNorm f := by
  use comp f (OrthProj 𝕜 D)
  constructor
  · intro v hv
    rw [comp_apply, (SetLike.coe_eq_coe.mp <| OrthProj_id 𝕜 D v hv : ((OrthProj 𝕜 D) v) = ⟨v,hv⟩)]
  · apply le_antisymm
    · calc ‖f.comp (OrthProj 𝕜 D)‖ ≤ ‖f‖ * ‖OrthProj 𝕜 D‖ := opNorm_comp_le f _
        _ ≤ ‖f‖ * 1 := by gcongr; exact norm_OrthProj_le_one 𝕜 D
        _ = ‖f‖ := mul_one _
    · refine (opNorm_le_iff <| opNorm_nonneg (f.comp (OrthProj 𝕜 D))).mpr fun x => ?_
      have hproj' : (OrthProj 𝕜 D) (x : E) = x :=
        SetLike.coe_eq_coe.mp (OrthProj_id 𝕜 D x x.prop)
      change ‖f x‖ ≤ ‖f.comp (OrthProj 𝕜 D)‖ * ‖(x : E)‖
      simpa [ContinuousLinearMap.comp_apply, hproj'] using le_opNorm (f.comp (OrthProj 𝕜 D)) (x : E)

/--
A Hahn–Banach style extension theorem for continuous linear maps between ultrametric normed spaces.

Given:
* a nontrivially normed field `𝕜`,
* normed `𝕜`-vector spaces `E` and `F` equipped with an ultrametric distance
  (`[IsUltrametricDist E]` and `[IsUltrametricDist F]`),
* a submodule `D : Submodule 𝕜 E`,
* a continuous linear map `f : D →L[𝕜] F`,
* and the assumption that `F` is spherically complete (`[SphericallyCompleteSpace F]`),

this theorem produces a continuous linear map `f' : E →L[𝕜] F` extending `f` from `D` to all of `E`,
and preserving the operator norm: `‖f'‖ = ‖f‖`.

The extension property is stated pointwise: for any `v : E` with `hv : v ∈ D`, we have
`f' v = f ⟨v, hv⟩`.
-/
theorem hahn_banach' {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
(D : Submodule 𝕜 E)
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
[hf : SphericallyCompleteSpace F] (f : D →L[𝕜] F) :
∃ f' : E →L[𝕜] F,
  (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧
    ContinuousLinearMap.opNorm f' = ContinuousLinearMap.opNorm f := by
  if hf : f = 0 then
    use 0
    constructor
    · intro v hv
      simp [hf]
    · rw [hf]
      calc
        ContinuousLinearMap.opNorm (0 : E →L[𝕜] F) = 0 := ContinuousLinearMap.opNorm_zero
        _ = ContinuousLinearMap.opNorm (0 : D →L[𝕜] F) := by
          symm
          exact ContinuousLinearMap.opNorm_zero
  else
    rcases @exists_extension_opNorm_le 𝕜 _ E _ _ _ D F _ _ _ _ f {0}
      (by simp) (fun _ => ContinuousLinearMap.opNorm f)
      (by
        intro U
        refine lt_of_le_of_ne (opNorm_nonneg f) ?_
        intro hop
        apply hf
        ext x
        have hle : ‖f x‖ ≤ ContinuousLinearMap.opNorm f * ‖x‖ := le_opNorm f x
        have hop' : ContinuousLinearMap.opNorm f = 0 := by simpa using hop.symm
        rw [hop', zero_mul] at hle
        exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))
      (by
        intro U V
        have hUV : U.1 = V.1 := congrArg Subtype.val (Subsingleton.elim U V)
        simpa [hUV] using
          (show (0 : ℝ) ≤ max ((fun x ↦ f.opNorm) U) ((fun x ↦ f.opNorm) V) from
            le_trans (opNorm_nonneg f) (le_max_left _ _)))
      (by
        intro U a
        have hU : U.1 = 0 := Set.mem_singleton_iff.mp U.2
        rw [hU]
        simp only [zero_apply, sub_zero]
        exact le_opNorm f a
      ) with ⟨f', hf1, hf2⟩
    use f'
    simp only [Subtype.forall, Set.mem_singleton_iff, forall_eq, sub_zero] at hf2
    refine ⟨fun v hv => hf1 ⟨v, hv⟩, le_antisymm hf2 ?_⟩
    refine (opNorm_le_iff <| opNorm_nonneg f').mpr ?_
    intro a
    have hle := le_opNorm f' (a : E)
    simpa [AddSubgroupClass.coe_norm, hf1 a] using hle

end SphericallyCompleteSpace
