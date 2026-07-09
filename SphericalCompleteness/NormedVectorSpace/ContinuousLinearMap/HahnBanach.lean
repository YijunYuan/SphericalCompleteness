/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

/-!
# Non-Archimedean Hahn–Banach

The non-Archimedean Hahn–Banach extension theorem for continuous linear maps between ultrametric
normed spaces over a nontrivially normed field.

The extension property is packaged as a `Prop`-valued class `IsHahnBanachPair D F`: it holds when
every continuous linear map `f : D →L[𝕜] F` out of the submodule `D` extends to `E →L[𝕜] F` while
agreeing with `f` on `D` and preserving the operator norm. Two sufficient conditions are recorded as
instances:

* the domain `D` is spherically complete, in which case `f` factors through the norm-nonincreasing
  orthogonal projection `orthProj 𝕜 D` onto `D`;
* the codomain `F` is spherically complete, in which case `f` is extended by
  `exists_extension_opNorm_le`, iterating the codimension-one step over all of `E`.

## Main definitions

* `IsHahnBanachPair`: the class asserting that norm-preserving extension holds for every continuous
  linear map `D →L[𝕜] F`.

## Main statements

* `hahn_banach`: the extension theorem obtained from an `IsHahnBanachPair D F` instance.

## References

* A. C. M. van Rooij, *Non-Archimedean Functional Analysis*.

## Tags

Hahn–Banach, non-Archimedean, ultrametric, spherically complete
-/

@[expose] public section

open ContinuousLinearMap

namespace SphericallyCompleteSpace

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
  (D : Submodule 𝕜 E)
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]

/--
`IsHahnBanachPair D F` states that the submodule `D` of `E` and the space `F` satisfy the
non-Archimedean Hahn–Banach extension property: every continuous linear map `f : D →L[𝕜] F` extends
to a continuous linear map `E →L[𝕜] F` that agrees with `f` on `D` and preserves the operator norm.
-/
class IsHahnBanachPair [IsUltrametricDist E] [IsUltrametricDist F] : Prop where
  /-- Every continuous linear map `f : D →L[𝕜] F` extends to `E →L[𝕜] F`, agreeing with `f` on `D`
  and preserving the operator norm. -/
  is_hb : ∀ f : D →L[𝕜] F,
    ∃ f' : E →L[𝕜] F, (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖

/--
The **non-Archimedean Hahn–Banach theorem**.

Whenever `D` and `F` form an `IsHahnBanachPair`, any continuous linear map `f : D →L[𝕜] F` extends
to `f' : E →L[𝕜] F` that agrees with `f` on `D` and preserves the operator norm, `‖f'‖ = ‖f‖`.
-/
theorem hahn_banach [IsHahnBanachPair D F] (f : D →L[𝕜] F) :
    ∃ f' : E →L[𝕜] F, (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖ :=
  IsHahnBanachPair.is_hb f

/--
A spherically complete domain forms an `IsHahnBanachPair`.

If the source subspace `D` is spherically complete, the extension is concrete: `f` is precomposed
with the norm-nonincreasing orthogonal projection `orthProj 𝕜 D` onto `D`, which exists precisely
because `D` is spherically complete.
-/
instance instIsHahnBanachPairOfDomainSphericallyComplete
    [SphericallyCompleteSpace D] : IsHahnBanachPair D F where
  is_hb f := by
    use f.comp (orthProj 𝕜 D)
    refine ⟨fun v hv ↦ ?_, le_antisymm ?_ ?_⟩
    · rw [comp_apply, (SetLike.coe_eq_coe.mp <| orthProj_id 𝕜 D v hv : (orthProj 𝕜 D) v = ⟨v, hv⟩)]
    · exact (opNorm_comp_le f _).trans
        (mul_le_of_le_one_right (norm_nonneg f) (norm_orthProj_le_one 𝕜 D))
    · refine (opNorm_le_iff <| opNorm_nonneg (f.comp (orthProj 𝕜 D))).mpr fun x ↦ ?_
      have hproj : (orthProj 𝕜 D) (x : E) = x :=
        SetLike.coe_eq_coe.mp (orthProj_id 𝕜 D x x.prop)
      simpa [comp_apply, hproj] using le_opNorm (f.comp (orthProj 𝕜 D)) (x : E)

/--
A spherically complete codomain forms an `IsHahnBanachPair`.

If the target `F` is spherically complete, no completeness assumption is placed on `D`; the
extension is built by iterating the codimension-one Hahn–Banach step `exists_extension_codimOne`
over all of `E` through `exists_extension_opNorm_le`, which is why spherical completeness is
required on the side where the values live.
-/
instance instIsHahnBanachPairOfCodomainSphericallyComplete
    [SphericallyCompleteSpace F] : IsHahnBanachPair D F where
  is_hb f := by
    if hf : f = 0 then exact ⟨0, fun v hv ↦ by simp [hf], by simp [hf]⟩
    else
      rcases exists_extension_opNorm_le 𝕜 D f (𝒰 := {0})
        (by simp) (fun _ ↦ opNorm f)
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
