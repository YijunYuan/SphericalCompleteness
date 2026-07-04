/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.NormedVectorSpace.Orthogonal.Defs

/-!
# Orthogonality: basic results

Basic results on (norm) orthogonality in ultrametric normed spaces, building on the definitions
`Orth` (`x ⟂[𝕜] y`), `MOrth` (`x ⟂ₘ F`) and `SOrth` (`F ⟂ₛ G`) from
`SphericalCompleteness.NormedVectorSpace.Orthogonal.Defs`.

## Main statements

* Orthogonality of vectors is symmetric (`Orth.symm`) and admits two reformulations: it coincides
  with **Birkhoff–James orthogonality** (`Orth.iff_birkhoffJames`) and with the ultrametric
  identity "the norm of a linear combination is the maximum of the norms of its terms"
  (`Orth.iff_norm_add_eq_max`).
* All three relations are invariant under nonzero scalar multiplication
  (`Orth.smul_left_iff`, `Orth.smul_right_iff`,
  `MOrth.smul_iff`).
* Metric orthogonality to a subspace is orthogonality to each of its vectors
  (`MOrth.iff_forall_orth`); subspace orthogonality unfolds to orthogonality of all pairs of
  vectors (`SOrth.iff_forall_orth`) and is symmetric (`SOrth.symm`).
* A vector that both lies in `F` and is orthogonal to `F` is zero (`MOrth.eq_zero_of_mem`).
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E]

/-! ### Orthogonality of vectors -/

namespace Orth

/-- Orthogonality of two vectors is symmetric: if `x ⟂[𝕜] y` then `y ⟂[𝕜] x`. This is the
technical direction from which the symmetry equivalence `Orth.symm` is assembled; the argument
uses the strong triangle inequality to rule out any point of `𝕜 ∙ x` approximating `y` better
than `0` does. -/
private lemma of_orth {x y : E}
    (h : x ⟂[𝕜] y) : y ⟂[𝕜] x := by
  unfold SphericallyCompleteSpace.Orth at *
  refine eq_of_le_of_not_lt ?_ ?_
  · have := @infDist_le_dist_of_mem E _ ↑(Submodule.span 𝕜 {x}) y 0 (by simp)
    simpa only [ge_iff_le, dist_zero_right] using this
  · by_contra hc
    rcases (infDist_lt_iff (by use 0; simp)).1 hc with ⟨z, hz1, hz2⟩
    simp only [SetLike.mem_coe] at hz1
    rcases Submodule.mem_span_singleton.1 hz1 with ⟨a, ha⟩
    rw [← ha] at hz2
    if ha' : a = 0 then
      subst ha'
      simp only [zero_smul, dist_zero_right, lt_self_iff_false] at *
    else
    rw [dist_eq_norm] at hz2
    have hax : ‖a • x‖ = ‖y‖ := by
      rw [← norm_neg, neg_sub] at hz2
      rw [(by abel : a • x = a • x - y + y), iud.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hz2),
        max_eq_right hz2.le]
    have : y = a • a⁻¹ • y := (inv_smul_eq_iff₀ ha').mp rfl
    rw [← hax, this, ← smul_sub, norm_smul, norm_smul, norm_sub_rev,
      ← dist_eq_norm, mul_lt_mul_iff_right₀ <| norm_pos_iff.mpr ha'] at hz2
    have := lt_of_le_of_lt (infDist_le_dist_of_mem
      (Submodule.mem_span_singleton.mpr ⟨a⁻¹,rfl⟩)) hz2
    linarith

/-- Orthogonality of vectors is symmetric: `x ⟂[𝕜] y` if and only if `y ⟂[𝕜] x`. Although `Orth`
is defined asymmetrically (as a distance to the line spanned by the second vector), the relation
does not depend on the order of its arguments. -/
lemma symm {x y : E} :
    (x ⟂[𝕜] y) ↔ (y ⟂[𝕜] x) :=
  ⟨of_orth, of_orth⟩

/-- **Birkhoff–James characterization of orthogonality**: `x ⟂[𝕜] y` if and only if `x` is a
best approximation of itself along the line `𝕜 ∙ y`, i.e. `‖x‖ ≤ ‖x + c • y‖` for every scalar
`c`. This rephrases the `infDist`-based definition of `Orth` as a norm-minimality condition. -/
lemma iff_birkhoffJames
    (x y : E) : (x ⟂[𝕜] y) ↔ ∀ c : 𝕜, ‖x‖ ≤ ‖x + c • y‖ := by
  constructor
  · intro h c
    have : x + c • y = x - (-c) • y := by simp only [neg_smul, sub_neg_eq_add]
    rw [← h, this, ← dist_eq_norm]
    refine infDist_le_dist_of_mem ?_
    simp only [neg_smul, SetLike.mem_coe, neg_mem_iff]
    exact Submodule.mem_span_singleton.mpr ⟨c, by simp⟩
  · intro h
    by_contra hc
    replace hc := lt_of_le_of_ne ?_ hc
    · replace hc := (infDist_lt_iff ?_).1 hc
      · rcases hc with ⟨y', hy', hy''⟩
        rcases Submodule.mem_span_singleton.1 hy' with ⟨c, hc⟩
        rw [← hc, dist_eq_norm, sub_eq_add_neg, ← neg_smul] at hy''
        specialize h (-c); linarith
      · use 0; simp only [SetLike.mem_coe, zero_mem]
    · nth_rw 2 [← sub_zero x]
      rw [← dist_eq_norm]
      refine infDist_le_dist_of_mem ?_
      simp only [SetLike.mem_coe, zero_mem]

/-- Orthogonality of vectors is equivalent to the ultrametric "norm of a sum equals the maximum
of the norms" identity on the spanned plane: `x ⟂[𝕜] y` if and only if
`‖α • x + β • y‖ = max ‖α • x‖ ‖β • y‖` for all scalars `α` and `β`. In particular `x` and `y`
then span a plane on which the norm is completely determined by the norms of the two axes. -/
lemma iff_norm_add_eq_max {x y : E} :
    (x ⟂[𝕜] y) ↔ (∀ α β : 𝕜, ‖α • x + β • y‖ = max ‖α • x‖ ‖β • y‖) := by
  constructor
  · intro h a b
    if hab : a = 0 ∨ b = 0 then
      rcases hab with ha | hb
      · simp only [ha, zero_smul, zero_add, norm_zero, norm_nonneg, sup_of_le_right]
      · simp only [hb, zero_smul, add_zero, norm_zero, norm_nonneg, sup_of_le_left]
    else
    push Not at hab
    refine eq_of_le_of_ge (iud.norm_add_le_max _ _) ?_
    apply max_le
    · rw [← sub_neg_eq_add, ← dist_eq_norm]
      refine le_trans ?_ <| infDist_le_dist_of_mem (by
        simp only [neg_mem_iff]
        refine Submodule.mem_span_singleton.mpr ?_
        use b : - (b • y) ∈ 𝕜 ∙ y)
      have := infDist_smul₀ hab.1 (Submodule.span 𝕜 {y} : Set E) x
      rw [Submodule.smul_coe_eq_self hab.1] at this
      rw [this, h, norm_smul]
    · have : a • x + b • y = b • y - - (a • x) := by abel
      rw [this, ← dist_eq_norm]
      refine le_trans ?_ <| infDist_le_dist_of_mem (by
        simp only [neg_mem_iff]
        refine Submodule.mem_span_singleton.mpr ?_
        use a : - (a • x) ∈ 𝕜 ∙ x)
      have := infDist_smul₀ hab.2 (Submodule.span 𝕜 {x} : Set E) y
      rw [Submodule.smul_coe_eq_self hab.2] at this
      rw [this, norm_smul, mul_le_mul_iff_right₀ (norm_pos_iff.mpr hab.2)]
      rw [symm] at h
      simpa only using le_of_eq (Eq.symm h)
  · intro h
    unfold SphericallyCompleteSpace.Orth
    suffices hh : ∀ y' ∈ ↑(Submodule.span 𝕜 {y}), dist x y' ≥ ‖x‖ by
      refine eq_of_le_of_ge ?_ ?_
      · rw [← dist_zero, dist_comm]
        apply infDist_le_dist_of_mem
        simp only [SetLike.mem_coe, zero_mem]
      · rw [infDist_eq_iInf]
        refine (le_ciInf_set_iff ?_ ?_).mpr hh
        · use 0
          simp only [SetLike.mem_coe, zero_mem]
        · use ‖x‖
          simpa only [lowerBounds, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, ge_iff_le] using hh
    intro y' hy'
    rcases Submodule.mem_span_singleton.1 hy' with ⟨s, hs⟩
    rw [← hs, dist_eq_norm, sub_eq_add_neg, ← one_nsmul x,← neg_one_zsmul]
    have : -1 • s • y = (-1 * s) • y := by simp only [Int.reduceNeg, neg_smul, one_smul,
      neg_mul, one_mul]
    rw [this]
    specialize h 1 (-1 * s)
    simp only [Int.reduceNeg, neg_smul, one_smul, neg_mul, one_mul, norm_neg] at *
    simp only [h, le_sup_left]

/-- Orthogonality is preserved by scaling the first vector: if `x ⟂[𝕜] y` then `(a • x) ⟂[𝕜] y`
for every scalar `a` (including `a = 0`, since `0` is orthogonal to everything). -/
theorem smul_left {x y : E}
    (a : 𝕜) : (x ⟂[𝕜] y) → ((a • x) ⟂[𝕜] y) := by
  intro h
  unfold SphericallyCompleteSpace.Orth at *
  if ha : a = 0 then
    subst ha
    simp only [zero_smul, norm_zero]
    refine infDist_zero_of_mem ?_
    simp only [SetLike.mem_coe, zero_mem]
  else
  rw [norm_smul, ← h, ← infDist_smul₀ ha, Submodule.smul_coe_eq_self ha]

/-- For a nonzero scalar `a`, scaling the first vector preserves and reflects orthogonality:
`x ⟂[𝕜] y` if and only if `(a • x) ⟂[𝕜] y`. -/
theorem smul_left_iff {x y : E}
    {a : 𝕜} (ha : a ≠ 0) : (x ⟂[𝕜] y) ↔ ((a • x) ⟂[𝕜] y) := by
  refine ⟨smul_left a, fun h ↦ ?_⟩
  apply smul_left a⁻¹ at h
  rwa [inv_smul_smul₀ ha x] at h

/-- Orthogonality is preserved by scaling the second vector: if `x ⟂[𝕜] y` then `x ⟂[𝕜] (a • y)`
for every scalar `a`. This is the counterpart of `Orth.smul_left` obtained through symmetry. -/
theorem smul_right {x y : E}
    (a : 𝕜) : (x ⟂[𝕜] y) → (x ⟂[𝕜] (a • y)) := by
  intro h
  rw [symm] at *
  exact smul_left a h

/-- For a nonzero scalar `a`, scaling the second vector preserves and reflects orthogonality:
`x ⟂[𝕜] y` if and only if `x ⟂[𝕜] (a • y)`. -/
theorem smul_right_iff {x y : E}
    {a : 𝕜} (ha : a ≠ 0) : (x ⟂[𝕜] y) ↔ (x ⟂[𝕜] (a • y)) := by
  nth_rw 1 [symm]
  nth_rw 2 [symm]
  exact smul_left_iff ha

end Orth

/-! ### Metric orthogonality to a subspace -/

namespace MOrth

/-- Metric orthogonality to a subspace reduces to orthogonality to each of its vectors: `x ⟂ₘ F`
if and only if `x ⟂[𝕜] y` for every `y ∈ F`. This links the subspace notion `MOrth` to the
vector notion `Orth`. -/
lemma iff_forall_orth
    (x : E) (F : Subspace 𝕜 E) :
    (x ⟂ₘ F) ↔ ∀ y ∈ F, (x ⟂[𝕜] y) := by
  constructor
  · intro h y hy
    refine eq_of_le_of_not_lt ?_ ?_
    · simpa only [dist_zero_right] using
        @infDist_le_dist_of_mem E _ _ x 0 (Submodule.zero_mem (Submodule.span 𝕜 {y}))
    · by_contra hc
      rcases (infDist_lt_iff (Submodule.nonempty (Submodule.span 𝕜 {y}))).1 hc with ⟨y', hy'⟩
      exact lt_iff_not_ge.1 hy'.2 <| (le_infDist (Submodule.nonempty F)).1
        (by rw [h]) (by aesop : y' ∈ F)
  · intro h
    refine eq_of_le_of_not_lt ?_ ?_
    · simpa only [dist_zero_right] using infDist_le_dist_of_mem (Submodule.zero_mem F)
    · by_contra hc
      rcases (infDist_lt_iff (Submodule.nonempty F)).1 hc with ⟨y, hy⟩
      exact lt_iff_not_ge.1 hy.2 <|
        (h y hy.1) ▸ (le_infDist (Submodule.nonempty (Submodule.span 𝕜 {y}))).1
          le_rfl (Submodule.mem_span_singleton_self y)

end MOrth

end

namespace MOrth

/-- A vector that both lies in a subspace `F` and is metrically orthogonal to `F` must be zero:
`x ∈ F` and `x ⟂ₘ F` force `x = 0`. Membership makes the distance from `x` to `F` vanish, so
`‖x‖ = 0`.

Unlike the surrounding results this requires the genuine `NormedAddCommGroup E` (rather than only
`SeminormedAddCommGroup E`), since it is where `‖x‖ = 0` is upgraded to `x = 0`. -/
theorem eq_zero_of_mem {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {x : E} {F : Subspace 𝕜 E} : x ∈ F → (x ⟂ₘ F) → x = 0 :=
  fun h1 h2 ↦ norm_eq_zero.mp (infDist_zero_of_mem h1 ▸ h2 : (0 : ℝ) = ‖x‖).symm

end MOrth

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [iud : IsUltrametricDist E]

namespace MOrth

/-- Metric orthogonality to a subspace is preserved by scaling: if `x ⟂ₘ F` then `(a • x) ⟂ₘ F`
for every scalar `a`. -/
theorem smul
    {x : E} {F : Subspace 𝕜 E} (a : 𝕜) :
    (x ⟂ₘ F) → ((a • x) ⟂ₘ F) := by
  intro h
  rw [iff_forall_orth] at *
  intro y hy
  exact Orth.smul_left a (h y hy)

/-- For a nonzero scalar `a`, scaling preserves and reflects metric orthogonality to a subspace:
`x ⟂ₘ F` if and only if `(a • x) ⟂ₘ F`. -/
theorem smul_iff
    {x : E} {F : Subspace 𝕜 E} {a : 𝕜} (ha : a ≠ 0) :
    (x ⟂ₘ F) ↔ ((a • x) ⟂ₘ F) := by
  refine ⟨smul a, fun h ↦ ?_⟩
  apply smul a⁻¹ at h
  rwa [inv_smul_smul₀ ha x] at h

/-- Failure of metric orthogonality is witnessed by a strictly better approximation: `x` is *not*
metrically orthogonal to `F` if and only if some `y ∈ F` satisfies `dist x y < ‖x‖`. This is the
negation of `MOrth` phrased as the existence of a point of `F` closer to `x` than `0` is. -/
theorem not_iff_exists_dist_lt_norm
    {x : E} {F : Subspace 𝕜 E} :
    ¬ (x ⟂ₘ F) ↔ ∃ y ∈ F, dist x y < ‖x‖ := by
  unfold SphericallyCompleteSpace.MOrth
  constructor
  · intro h
    contrapose h
    push Not at h
    exact eq_of_le_of_ge
      (by simpa only [dist_zero_right] using infDist_le_dist_of_mem (by simp : (0 : E) ∈ ↑F))
      ((le_infDist <| Submodule.nonempty F).2 h)
  · intro h
    contrapose h
    push Not
    rw [← h]
    exact fun z hz ↦ infDist_le_dist_of_mem hz

end MOrth

/-! ### Orthogonality of subspaces -/

namespace SOrth

/-- Subspace orthogonality unfolds to orthogonality of all pairs of vectors: `F₁ ⟂ₛ F₂` if and
only if `x ⟂[𝕜] y` for every `x ∈ F₁` and every `y ∈ F₂`. -/
theorem iff_forall_orth
    (F1 F2 : Subspace 𝕜 E) : (F1 ⟂ₛ F2) ↔ ∀ x ∈ F1, ∀ y ∈ F2, (x ⟂[𝕜] y) := by
  simp only [SphericallyCompleteSpace.SOrth, MOrth.iff_forall_orth]

/-- Subspace orthogonality is symmetric: if `F₁ ⟂ₛ F₂` then `F₂ ⟂ₛ F₁`. This is the technical
direction underlying the symmetry equivalence `SOrth.symm`, obtained by swapping the roles of the
two subspaces and applying symmetry of vector orthogonality. -/
private lemma of_sorth
    {F1 F2 : Subspace 𝕜 E} : (F1 ⟂ₛ F2) → (F2 ⟂ₛ F1) := by
  intro h
  simp only [SphericallyCompleteSpace.SOrth, MOrth.iff_forall_orth] at *
  exact fun x hx y hy ↦ Orth.of_orth (h y hy x hx)

/-- Subspace orthogonality is symmetric: `F₁ ⟂ₛ F₂` if and only if `F₂ ⟂ₛ F₁`. Despite the
asymmetric definition of `SOrth` (quantifying over vectors of the first subspace only), the
relation is independent of the order of its arguments. -/
theorem symm
    {F1 F2 : Subspace 𝕜 E} : (F1 ⟂ₛ F2) ↔ (F2 ⟂ₛ F1) :=
  ⟨of_sorth, of_sorth⟩

end SOrth

end

end SphericallyCompleteSpace
