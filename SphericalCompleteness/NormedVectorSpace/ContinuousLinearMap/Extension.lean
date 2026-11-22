/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import SphericalCompleteness.External.Submodule
public import SphericalCompleteness.Metric.Seminormed.Basic
public import SphericalCompleteness.NormedVectorSpace.Basic
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.Ambient
public import SphericalCompleteness.PseudoMetric.Module.Extension

/-!
# The ultrametric Hahn–Banach extension via Zorn's lemma

This file constructs the extension theorem underlying the non-Archimedean Hahn–Banach theorem for
continuous linear maps valued in a spherically complete space over a nontrivially normed field.

Given a continuous linear map `S : D →L[𝕜] F` on a submodule `D` of an ultrametric normed space `E`,
together with a family `𝒰` of continuous linear maps on `E` that approximate `S` on `D` within
tolerances `ε`, the main result `exists_extension_opNorm_le` produces a continuous linear map
`T : E →L[𝕜] F` extending `S` and still lying within the same tolerances of every member of `𝒰`.
Specializing the family `𝒰` recovers the norm-preserving Hahn–Banach extension.

The explicit codimension-one extension sends `d + c • a` to `S d + c • z`, where a compatible
family of balls determines the admissible values of `z`. For the global extension,
`PseudoMetric.exists_linearExtension_of_le_moduli` applies to the functions `r ↦ ε U * r`.
One operator in the family then supplies a bound proving continuity of the extended linear map.

## Main statements

* `exists_extension_codimOne`: the codimension-one Hahn–Banach step.
* `exists_extension_opNorm_le`: the full extension with operator-norm control.

## References

* A. C. M. van Rooij, *Non-Archimedean Functional Analysis*.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/-- The linear equivalence `↥(D + 𝕜∙a) ≃ₗ D × 𝕜` given by the (unique, since `a ∉ D`)
decomposition `x = d + l • a`. -/
noncomputable def spanSupDecomp {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {D : Submodule 𝕜 E} {a : E} (ha : a ∉ D) :
    ↥(D + Submodule.span 𝕜 {a}) ≃ₗ[𝕜] D × 𝕜 :=
  (D.prodEquivSupSpanSingleton ha).symm

/-- The inverse of `spanSupDecomp` sends the coordinates `(d, l)` back to the vector
`d + l • a`. This is the defining computation of the decomposition, phrased as a `simp` lemma so
that downstream proofs can rewrite an element of `D + 𝕜 ∙ a` into its `D`-part plus its
`𝕜 ∙ a`-part. -/
@[simp] lemma spanSupDecomp_symm_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {D : Submodule 𝕜 E} {a : E} (ha : a ∉ D)
    (d : D) (l : 𝕜) : (((spanSupDecomp ha).symm (d, l)) : E) = (d : E) + l • a := rfl

private theorem nnMetric_le_mul_iff_norm_sub_le {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (r : NNReal) (x y : E) (u v : F) :
    (nnMetric F) u v ≤ r * (nnMetric E) x y ↔ ‖u - v‖ ≤ (r : ℝ) * ‖x - y‖ := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, nnMetric_apply, nnMetric_apply, coe_nndist,
    coe_nndist, dist_eq_norm, dist_eq_norm]

private theorem nnMetric_apply_le_max_of_opNorm_le {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (U V : E →L[𝕜] F) (r s : NNReal) (h : ‖U - V‖ ≤ max (r : ℝ) (s : ℝ)) (x : E) :
    (nnMetric F) (U x) (V x) ≤ max (r * (nnMetric E) x 0) (s * (nnMetric E) x 0) := by
  rw [← max_mul_of_nonneg _ _ zero_le, nnMetric_le_mul_iff_norm_sub_le, sub_zero, NNReal.coe_max]
  exact ((U - V).le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

section
variable {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
    [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
    {a : E} (ha1 : a ∉ D)
    {F : Type*} [SeminormedAddCommGroup F]
    [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
    (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
    {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
    (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖)

include hε2 hε3 in
/-- Compatible operator-norm bounds admit a simultaneous value at any vector.
The tolerances may vanish and the family of approximants may be empty. -/
lemma exists_extensionValue_norm_le_of_nonneg (hε : ∀ U, 0 ≤ ε U) :
    ∃ z : F, ∀ (x : D) (U : 𝒰), ‖S x + z - U.val (↑x + a)‖ ≤ ε U * ‖↑x + a‖ := by
  let r (U : 𝒰) : NNReal := ⟨ε U, hε U⟩
  have hr (U : 𝒰) : (r U : ℝ) = ε U := rfl
  obtain ⟨b, hb⟩ := PseudoMetric.exists_linearExtensionValue (nnMetric E) (nnMetric F)
    (fun U : 𝒰 ↦ U.val.toLinearMap) (fun U t ↦ r U * t)
    (fun _ _ _ h ↦ mul_le_mul_of_nonneg_left h zero_le)
    (fun U V ↦ (le_total (r U) (r V)).imp
      (fun h t ↦ mul_le_mul_of_nonneg_right h t.2) (fun h t ↦ mul_le_mul_of_nonneg_right h t.2))
    (fun U V ↦ nnMetric_apply_le_max_of_opNorm_le U.val V.val (r U) (r V) (hε2 U V))
    D S.toLinearMap (fun U x ↦
      (nnMetric_le_mul_iff_norm_sub_le (r U) (x : E) 0 (S x) (U.val x)).mpr
        (by simpa only [sub_zero, Submodule.norm_coe, hr] using hε3 U x)) a
  refine ⟨b, fun x U ↦ ?_⟩
  have h := (nnMetric_le_mul_iff_norm_sub_le (r U) a ((-x : D) : E) b
    (U.val (a - ((-x : D) : E)) + S (-x))).mp (hb U (-x))
  simpa only [ContinuousLinearMap.coe_coe, NegMemClass.coe_neg, map_neg, sub_neg_eq_add,
    ← sub_eq_add_neg, sub_sub_eq_add_sub, add_comm b, add_comm a, hr] using h

-- Retain the codimension-one hypotheses and argument order of the public theorem.
set_option linter.unusedSectionVars false in
include ha1 h𝒰 hε1 hε2 hε3 in
/-- The heart of the codimension-one extension step (van Rooij, *Non-Archimedean Functional
Analysis*, Lemma 4.4). Given a continuous linear `S : D →L[𝕜] F` approximated on `D` by a
compatible family `𝒰` with tolerances `ε`, and a vector `a ∉ D`, spherical completeness of `F`
produces a single value `z0` that plays the role of `S a`: adjoining it keeps every approximation
bound `‖S x + z0 - U (x + a)‖ ≤ ε U * ‖x + a‖` valid on `D + 𝕜 ∙ a`. The witness is extracted from
the nonempty intersection of the family of operator-norm balls. -/
lemma exists_extensionValue_norm_le :
    ∃ z0 : F, ∀ (x : ↥D) (U : ↑𝒰), ‖S x + z0 - U.val (↑x + a)‖ ≤ ε U * ‖↑x + a‖ :=
  exists_extensionValue_norm_le_of_nonneg S hε2 hε3 (fun U ↦ (hε1 U).le)

/-- Homogeneity form of `exists_extensionValue_norm_le`: the approximation bound provided by the
chosen extension value survives scaling of `a` by any `l : 𝕜`, i.e.
`‖S x + l • z0 - U (x + l • a)‖ ≤ ε U * ‖x + l • a‖`. This upgrades the single-vector bound to the
full line `𝕜 ∙ a`, which is what makes the extension well defined on `D + 𝕜 ∙ a`. -/
lemma norm_smul_extensionValue_le :
    ∀ (x : ↥D) (l : 𝕜) (U : ↑𝒰),
    ‖S x + l • (exists_extensionValue_norm_le ha1 S h𝒰 hε1 hε2 hε3).choose - U.val (↑x + l • a)‖ ≤
    ε U * ‖↑x + l • a‖ := by
  intro x l U
  by_cases hl : l = 0
  · simp only [hl, zero_smul, add_zero, map_add]; exact hε3 U x
  · have : x = l • (l⁻¹ • x) := by simp [smul_smul, mul_inv_cancel₀ hl]
    rw [this, S.map_smul, show ↑(l • l⁻¹ • x) + l • a = l • ((l⁻¹ • x) + a) by simp [smul_add]]
    rw [U.val.map_smul, ← smul_add, ← smul_sub, norm_smul, norm_smul, ← mul_assoc, mul_comm (ε U),
      mul_assoc, mul_le_mul_iff_of_pos_left <| norm_pos_iff.mpr hl]
    exact (exists_extensionValue_norm_le ha1 S h𝒰 hε1 hε2 hε3).choose_spec (l⁻¹ • x) U

include ha1 h𝒰 hε1 hε2 hε3 in
/-- The underlying function of the codimension-one extension of `S` to `D + 𝕜 ∙ a`. On the unique
decomposition `m = d + l • a` (with `d ∈ D`, valid because `a ∉ D`) it returns
`S d + l • z0`, where `z0` is the extension value from `exists_extensionValue_norm_le`. Linearity
and boundedness are established separately in `isLinearMap_codimOneExtension` and
`isBoundedLinearMap_codimOneExtension`. -/
noncomputable def codimOneExtension :
    (D + Submodule.span 𝕜 {a}) → F := fun M ↦ by
    have := Submodule.mem_sup.1 M.prop
    let lambda := (Submodule.mem_span_singleton.1 this.choose_spec.2.choose_spec.1).choose
    use S ⟨this.choose, this.choose_spec.1⟩ +
      lambda • (exists_extensionValue_norm_le ha1 S h𝒰 hε1 hε2 hε3).choose

/-- Closed form of `codimOneExtension` in the `spanSupDecomp` coordinates `m ↦ (d, l)`:
its value is `S d + l • z0`, where `z0` is the extension value from
`exists_extensionValue_norm_le`. This is the computational identity that all downstream
linearity, boundedness and approximation proofs rewrite with. -/
lemma codimOneExtension_eq (M : ↥(D + Submodule.span 𝕜 {a})) :
    codimOneExtension ha1 S h𝒰 hε1 hε2 hε3 M =
    S (spanSupDecomp ha1 M).1 +
      (spanSupDecomp ha1 M).2 • (exists_extensionValue_norm_le ha1 S h𝒰 hε1 hε2 hε3).choose := by
  unfold codimOneExtension
  set p := Submodule.mem_sup.1 M.prop with hp
  set l := (Submodule.mem_span_singleton.1 p.choose_spec.2.choose_spec.1).choose with hl
  have ha0 : a ≠ 0 := fun h ↦ ha1 (h ▸ D.zero_mem)
  have hMeq : (M : E) = ((spanSupDecomp ha1 M).1 : E) + (spanSupDecomp ha1 M).2 • a := by
    conv_lhs => rw [← (spanSupDecomp ha1).symm_apply_apply M]
    rw [spanSupDecomp_symm_apply]
  have hpeq : (p.choose : E) + l • a = (M : E) := by
    rw [hl, (Submodule.mem_span_singleton.1 p.choose_spec.2.choose_spec.1).choose_spec,
      p.choose_spec.2.choose_spec.2]
  have hdecomp := Submodule.eq_and_eq_of_add_eq_add_of_notMem ha1
    p.choose p.choose_spec.1 (l • a) (Submodule.mem_span_singleton.2 ⟨l, rfl⟩)
    (spanSupDecomp ha1 M).1 (spanSupDecomp ha1 M).1.2 ((spanSupDecomp ha1 M).2 • a)
    (Submodule.mem_span_singleton.2 ⟨_, rfl⟩) (hpeq.trans hMeq)
  refine congrArg₂ _ (congrArg S (Subtype.ext hdecomp.1)) ?_
  exact congrArg (· • _) (smul_left_injective 𝕜 ha0 hdecomp.2)

/-- The codimension-one extension `codimOneExtension` is `𝕜`-linear. Additivity and homogeneity
both reduce, via `codimOneExtension_eq`, to the linearity of `S` and of scalar multiplication in
the `spanSupDecomp` coordinates. -/
theorem isLinearMap_codimOneExtension :
    IsLinearMap 𝕜 (codimOneExtension ha1 S h𝒰 hε1 hε2 hε3) where
  map_add x1 x2 := by
    simp only [codimOneExtension_eq, map_add, Prod.fst_add, Prod.snd_add, S.map_add, add_smul]
    abel
  map_smul k m := by
    simp only [codimOneExtension_eq, map_smul, Prod.smul_fst, Prod.smul_snd, S.map_smul,
      smul_smul, smul_add, smul_eq_mul]


/-- The codimension-one extension is a bounded linear map: on top of linearity
(`isLinearMap_codimOneExtension`) the ultrametric estimate bounds its value by
`max (ε U₀) ‖U₀‖ * ‖x‖` for a fixed member `U₀` of the family, using the extension bound
`norm_smul_extensionValue_le`. -/
theorem isBoundedLinearMap_codimOneExtension :
    IsBoundedLinearMap 𝕜 (codimOneExtension ha1 S h𝒰 hε1 hε2 hε3) where
  map_add := (isLinearMap_codimOneExtension ha1 S h𝒰 hε1 hε2 hε3).map_add
  map_smul := (isLinearMap_codimOneExtension ha1 S h𝒰 hε1 hε2 hε3).map_smul
  bound := by
    use max (ε ⟨h𝒰.some,h𝒰.some_mem⟩) ‖h𝒰.some‖
    refine ⟨lt_max_of_lt_left <| hε1 _, fun x ↦ ?_⟩
    rw [codimOneExtension_eq]
    set d := (spanSupDecomp ha1 x).1 with hd
    set l := (spanSupDecomp ha1 x).2 with hl
    have hx_eq : (d : E) + l • a = ↑x := by
      rw [hd, hl, ← spanSupDecomp_symm_apply ha1, LinearEquiv.symm_apply_apply]
    have tt := (norm_smul_extensionValue_le ha1 S h𝒰 hε1 hε2 hε3) d l ⟨h𝒰.some, h𝒰.some_mem⟩
    rw [show S d + l • (exists_extensionValue_norm_le ha1 S h𝒰 hε1 hε2 hε3).choose =
      S d + l • (exists_extensionValue_norm_le ha1 S h𝒰 hε1 hε2 hε3).choose
      - h𝒰.some (d + l • a) + h𝒰.some (d + l • a) from by simp only [sub_add_cancel],
      max_mul_of_nonneg _ _ (norm_nonneg x)]
    refine le_trans (iud.norm_add_le_max _ _) (max_le_max ?_ ?_)
    · rw [show ‖x‖ = ‖(d : E) + l • a‖ by rw [hx_eq, ← Submodule.norm_coe]]
      simpa using tt
    · rw [hx_eq]
      exact ContinuousLinearMap.le_opNorm h𝒰.some ↑x

end

/-- **Codimension-one Hahn–Banach step.** Given `S : D →L[𝕜] F` approximated on `D` by a
compatible family `𝒰` (pairwise close in operator norm, each within tolerance `ε U` of `S`), and a
single vector `a ∉ D`, there is a continuous linear extension `T` to `D + 𝕜 ∙ a` that still agrees
with `S` on `D` and stays within the same tolerances: `‖T x - U x‖ ≤ ε U * ‖x‖` for all `U ∈ 𝒰`.
Iterating this one-dimension-at-a-time step (via Zorn) is what yields the full extension
`exists_extension_opNorm_le`, and ultimately non-Archimedean Hahn–Banach. Spherical completeness of
`F` is what makes the single step possible. -/
lemma exists_extension_codimOne
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [SeminormedAddCommGroup E] [iude : IsUltrametricDist E] [NormedSpace 𝕜 E]
    (D : Submodule 𝕜 E)
    (a : E) (ha1 : a ∉ D)
    (F : Type*) [SeminormedAddCommGroup F] [iud : IsUltrametricDist F]
    [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
    (S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
    (ε : ↑𝒰 → ℝ)
    (hε1 : ∀ T : ↑𝒰, 0 < ε T)
    (hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
    (hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
    :
    ∃ (T : (D + Submodule.span 𝕜 {a}) →L[𝕜] F),
    (∀ x : D, T ⟨x.val, by
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    use x
    simp only [x.prop, add_eq_left, exists_eq_right, zero_mem, and_self]
    ⟩ = S x) ∧
    (∀ U : ↑𝒰, ∀ x : E, (hx : x ∈ (D + Submodule.span 𝕜 {a})) → ‖T ⟨x, hx⟩ - U.val x‖ ≤ ε U * ‖x‖)
    := by
  use (isBoundedLinearMap_codimOneExtension ha1 S h𝒰 hε1 hε2 hε3).toContinuousLinearMap
  refine ⟨fun x ↦ ?_, fun U x hx ↦ ?_⟩
  · have hsup : x.val ∈ D + Submodule.span 𝕜 {a} := Submodule.mem_sup_left x.prop
    have hcoord : spanSupDecomp ha1 ⟨x.val, hsup⟩ = (x, 0) := by
      apply (spanSupDecomp ha1).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact Subtype.ext (by rw [spanSupDecomp_symm_apply]; simp)
    change codimOneExtension ha1 S h𝒰 hε1 hε2 hε3 ⟨x.val, hsup⟩ = S x
    rw [codimOneExtension_eq, hcoord]; simp
  · change ‖codimOneExtension ha1 S h𝒰 hε1 hε2 hε3 ⟨x, hx⟩ - U.val x‖ ≤ ε U * ‖x‖
    rw [codimOneExtension_eq]
    simpa [← spanSupDecomp_symm_apply ha1, LinearEquiv.symm_apply_apply] using
      (norm_smul_extensionValue_le ha1 S h𝒰 hε1 hε2 hε3)
        (spanSupDecomp ha1 ⟨x, hx⟩).1 (spanSupDecomp ha1 ⟨x, hx⟩).2 U

/-- Extend a continuous linear map subject to any nonempty compatible family of closed
operator-norm balls. Zero tolerances are allowed. -/
theorem exists_extension_opNorm_le_of_nonneg
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
    (D : Submodule 𝕜 E)
    {F : Type*} [SeminormedAddCommGroup F] [IsUltrametricDist F]
    [NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
    (S : D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
    (ε : ↑𝒰 → ℝ)
    (hε1 : ∀ T : ↑𝒰, 0 ≤ ε T)
    (hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
    (hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
    : ∃ T : E →L[𝕜] F, (∀ x : D, T x = S x) ∧ ∀ U : 𝒰, ‖T - U.val‖ ≤ ε U := by
  let r (U : 𝒰) : NNReal := ⟨ε U, hε1 U⟩
  have hr (U : 𝒰) : (r U : ℝ) = ε U := rfl
  obtain ⟨g, hgf, hg⟩ := PseudoMetric.exists_linearExtension_of_le_moduli (nnMetric E) (nnMetric F)
    (fun U : 𝒰 ↦ U.val.toLinearMap) (fun U t ↦ r U * t)
    (fun _ _ _ h ↦ mul_le_mul_of_nonneg_left h zero_le)
    (fun U V ↦ (le_total (r U) (r V)).imp
      (fun h t ↦ mul_le_mul_of_nonneg_right h t.2) (fun h t ↦ mul_le_mul_of_nonneg_right h t.2))
    (fun _ c {u x} h ↦ by
      simp only [nnMetric_apply, nndist_zero_right, nnNorm_smul] at h ⊢
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left h (show 0 ≤ ‖c‖₊ from zero_le))
    (fun U V ↦ nnMetric_apply_le_max_of_opNorm_le U.val V.val (r U) (r V) (hε2 U V))
    D S.toLinearMap (fun U x ↦
      (nnMetric_le_mul_iff_norm_sub_le (r U) (x : E) 0 (S x) (U.val x)).mpr
        (by simpa only [sub_zero, Submodule.norm_coe, hr] using hε3 U x))
  have hbound (U : 𝒰) (x : E) : ‖g x - U.val x‖ ≤ ε U * ‖x‖ := by
    simpa only [sub_zero, hr] using
      (nnMetric_le_mul_iff_norm_sub_le (r U) x 0 (g x) (U.val x)).mp (hg U x)
  obtain ⟨U, hU⟩ := h𝒰
  let V : 𝒰 := ⟨U, hU⟩
  let T := (g - U.toLinearMap).mkContinuous (ε V) (hbound V) + U
  have hT (x : E) : T x = g x := sub_add_cancel _ _
  refine ⟨T, fun x ↦ (hT x).trans (hgf x), fun W ↦ ?_⟩
  exact (ContinuousLinearMap.opNorm_le_iff (hε1 W)).mpr fun x ↦ by
    change ‖T x - W.val x‖ ≤ ε W * ‖x‖
    rw [hT]
    exact hbound W x

/-- The positive-tolerance formulation of the simultaneous extension theorem. -/
lemma exists_extension_opNorm_le
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
    (D : Submodule 𝕜 E)
    {F : Type*} [SeminormedAddCommGroup F] [IsUltrametricDist F]
    [NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
    (S : D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
    (ε : ↑𝒰 → ℝ)
    (hε1 : ∀ T : ↑𝒰, 0 < ε T)
    (hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
    (hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
    : ∃ T : E →L[𝕜] F, (∀ x : D, T x = S x) ∧ ∀ U : 𝒰, ‖T - U.val‖ ≤ ε U :=
  exists_extension_opNorm_le_of_nonneg 𝕜 D S h𝒰 ε (fun U ↦ (hε1 U).le) hε2 hε3

end SphericallyCompleteSpace
