/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.LinearAlgebra.Projection
public import SphericalCompleteness.External.Ultrametric
public import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.Extension
public import SphericalCompleteness.NormedVectorSpace.Orthogonal.Basic

/-!
# Orthogonal complements

Orthogonal complements and projections in ultrametric normed spaces.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

section
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [iud : IsUltrametricDist E] [NormedSpace 𝕜 E]
  (F : Submodule 𝕜 E) [SphericallyCompleteSpace ↥F]

/--
Existence of a norm-nonincreasing continuous linear projection onto a spherically complete subspace.

Let `𝕜` be a nontrivially normed field and `E` a normed `𝕜`-vector space whose distance is
ultrametric (`IsUltrametricDist E`). For a submodule `F : Submodule 𝕜 E` that is spherically
complete (as a normed space), this theorem produces a continuous linear map
`T : E →L[𝕜] F` such that:

* `T` restricts to the identity on `F` (i.e. `∀ a ∈ F, T a = a`), hence `T` is a retraction onto
`F`;
* `‖T‖ ≤ 1`, so `T` is 1-Lipschitz / nonexpanding with respect to the norm.

In other words, in the ultrametric setting, spherical completeness of `F` ensures the existence of
a bounded linear projection of operator norm at most `1` from `E` onto `F`.
-/
theorem exists_orthProj_of_sphericallyComplete :
    ∃ T : E →L[𝕜] ↥F, (∀ a ∈ F, T a = a) ∧ ‖T‖ ≤ 1 := by
  have := @exists_extension_opNorm_le 𝕜 _ E _ _ _ F ↥F _ _ _ _
    (ContinuousLinearMap.id 𝕜 ↥F) {0} (by simp) (fun _ ↦ 1) (fun _ ↦ by simp)
    (fun U V ↦ by rw [congrArg Subtype.val (Subsingleton.elim U V)]; simp)
    (fun U x ↦ by simp [Set.mem_singleton_iff.mp U.2, one_mul])
  simp only [Subtype.forall, Set.mem_singleton_iff, forall_eq, sub_zero] at this
  rcases this with ⟨T, hT1, hT2⟩
  exact ⟨T, ⟨fun a ha ↦ congrArg Subtype.val (hT1 a ha), hT2⟩⟩

/--
`orthComp 𝕜 F` is the *orthogonal complement* of a submodule `F : Submodule 𝕜 E` in a
normed space over a nontrivially normed field, assuming `E` carries an ultrametric
distance and that `F` is spherically complete.

It is defined as the kernel of an orthogonal projection onto `F` whose existence is
guaranteed by spherical completeness (`exists_orthProj_of_sphericallyComplete`).

In particular, `x ∈ orthComp 𝕜 F` iff the chosen orthogonal projection sends `x` to `0`,
so elements of `orthComp 𝕜 F` are exactly those “orthogonal to `F`” with respect to that
projection.
-/
noncomputable def orthComp
    : Submodule 𝕜 E :=
LinearMap.ker (exists_orthProj_of_sphericallyComplete 𝕜 F).choose.toLinearMap

/--
`isCompl_orthComp` shows that, over a nontrivially normed field `𝕜`, in a normed `𝕜`-vector space
`E` whose distance is ultrametric, any submodule `F` that is spherically complete is complemented by
its orthogonal complement `orthComp 𝕜 F`.

More precisely, it produces an `IsCompl` decomposition:
* every `x : E` can be written as `x = f + g` with `f ∈ F` and `g ∈ orthComp 𝕜 F`, and
* the intersection `F ⊓ orthComp 𝕜 F` is trivial.

This is the ultrametric analogue of the standard orthogonal decomposition result, with spherical
completeness providing the completeness hypothesis needed to construct the complement.
-/
theorem isCompl_orthComp :
    IsCompl F (orthComp 𝕜 F) := by
  unfold orthComp
  refine LinearMap.isCompl_of_proj fun x ↦ ?_
  exact SetLike.coe_eq_coe.mp <|
    (exists_orthProj_of_sphericallyComplete 𝕜 F).choose_spec.1 x x.property

namespace IsOrtho

/--
`F` is *sphere-orthogonal* to its orthogonal complement `orthComp 𝕜 F`.

In a nontrivially normed field `𝕜`, for an ultrametric normed space `E` over `𝕜`,
assuming `F : Submodule 𝕜 E` is spherically complete, this theorem asserts the
orthogonality relation `F ⟂ₛ orthComp 𝕜 F`.
-/
theorem orthComp :
    (F ⟂ₛ (orthComp 𝕜 F)) := by
  unfold SphericallyCompleteSpace.orthComp
  let T := (exists_orthProj_of_sphericallyComplete 𝕜 F).choose
  let hT2 := (exists_orthProj_of_sphericallyComplete 𝕜 F).choose_spec.2
  rw [IsOrtho.symm]
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
        simp only [map_sub, AddSubgroupClass.coe_sub, T]
        simp only [ContinuousLinearMap.coe_coe] at hx
        simp only [hx, ZeroMemClass.coe_zero, zero_sub, neg_inj]
        apply (exists_orthProj_of_sphericallyComplete 𝕜 F).choose_spec.1
        exact (Submodule.mem_toAddSubgroup F).mp hy
      rw [← norm_neg, ← this]
      have := (ContinuousLinearMap.opNorm_le_iff zero_le_one).1 hT2 (x - y)
      simpa only [map_sub, AddSubgroupClass.coe_sub, ge_iff_le, AddSubgroupClass.coe_norm, one_mul]
    nth_rw 1 [(by abel : x = (x - y) + y)]
    refine le_trans (iud.norm_add_le_max _ _) ?_
    simp only [this, sup_of_le_left, le_refl]

end IsOrtho

namespace IsMOrtho

/--
If `x` lies in the orthogonal complement `orthComp 𝕜 F`, then `x` is metrically orthogonal to `F`
(i.e. `x ⟂ₘ F`).

This lemma provides the forward direction from membership in `orthComp` to metric orthogonality,
under the assumptions that `E` is an ultrametric normed space over a nontrivially normed field `𝕜`
and that the submodule `F` is spherically complete.
-/
lemma of_mem_orthComp
    {x : E} (hx : x ∈ orthComp 𝕜 F) :
    (x ⟂ₘ F) :=
  (IsOrtho.symm.1 <| IsOrtho.orthComp 𝕜 F) x hx

end IsMOrtho

/--
`orthProj 𝕜 F` is the (noncomputable) continuous `𝕜`-linear map from `E` to the submodule `F`,
intended to represent the *orthogonal projection* onto `F` in the ultrametric setting.

This definition assumes:
- `𝕜` is a `NontriviallyNormedField`,
- `E` is a normed `𝕜`-vector space equipped with an ultrametric distance (`IsUltrametricDist E`),
- `F` is a `Submodule 𝕜 E` that is spherically complete (`[SphericallyCompleteSpace F]`).

The spherically complete hypothesis is used to ensure existence of best-approximation/projection
data in the non-Archimedean context. The resulting map is packaged as a continuous linear map
`E →L[𝕜] F`.

This definition is marked `noncomputable` because its construction relies on classical choice and
existence results rather than an algorithm.
-/
noncomputable def orthProj :
    E →L[𝕜] ↥F :=
  (exists_orthProj_of_sphericallyComplete 𝕜 F).choose

/--
The orthogonal projection `orthProj 𝕜 F` has operator norm at most `1`.

This is an immediate consequence of the construction of `orthProj` via
`exists_orthProj_of_sphericallyComplete`, which provides a continuous linear
projection onto `F` satisfying `‖T‖ ≤ 1`.
-/
theorem norm_orthProj_le_one :
    ‖orthProj 𝕜 F‖ ≤ 1 :=
  (exists_orthProj_of_sphericallyComplete 𝕜 F).choose_spec.2

/--
`orthProj 𝕜 F` restricts to the identity on the submodule `F`.

Concretely, if `a : E` satisfies `a ∈ F`, then applying the orthogonal projection onto `F`
returns `a`.

This is inherited from the choice of `orthProj` in
`exists_orthProj_of_sphericallyComplete`.
-/
theorem orthProj_id :
    ∀ a ∈ F, (orthProj 𝕜 F) a = a :=
  (exists_orthProj_of_sphericallyComplete 𝕜 F).choose_spec.1

/--
`orthComp 𝕜 F` is definitionally the kernel of the chosen orthogonal projection `orthProj 𝕜 F`.

This lemma is just an unfolding of the noncomputable definitions:
* `orthComp 𝕜 F := ker (exists_orthProj_of_sphericallyComplete 𝕜 F).choose`,
* `orthProj 𝕜 F := (exists_orthProj_of_sphericallyComplete 𝕜 F).choose`.
-/
theorem orthComp_eq_ker_orthProj :
    orthComp 𝕜 F = LinearMap.ker (orthProj 𝕜 F).toLinearMap :=
  rfl

/--
`orthProj 𝕜 F` is idempotent.

More precisely, for every `x : E` we have
`orthProj 𝕜 F (orthProj 𝕜 F x) = orthProj 𝕜 F x`.

This follows from the fact that `orthProj 𝕜 F` restricts to the identity on `F`, and
`orthProj 𝕜 F x` is by definition an element of `F`.
-/
theorem orthProj_idempotent :
    ∀ x : E, (orthProj 𝕜 F) ((orthProj 𝕜 F) x) = (orthProj 𝕜 F) x :=
  fun x ↦ SetLike.coe_eq_coe.mp <| orthProj_id 𝕜 F ((orthProj 𝕜 F) x) (orthProj 𝕜 F x).prop

end

end SphericallyCompleteSpace
