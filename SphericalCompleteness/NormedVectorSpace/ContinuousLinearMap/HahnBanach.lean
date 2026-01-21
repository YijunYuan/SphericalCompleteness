import SphericalCompleteness.NormedVectorSpace.Orthogonal.OrthComp

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
  (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖ := by
  use comp f (OrthProj 𝕜 D)
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
  (∀ v : E, (hv : v ∈ D) → f' v = f ⟨v, hv⟩) ∧ ‖f'‖ = ‖f‖ := by
  if hf : f = 0 then
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
