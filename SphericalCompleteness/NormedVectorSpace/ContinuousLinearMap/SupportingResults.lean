/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import SphericalCompleteness.NormedVectorSpace.Basic
import SphericalCompleteness.External.Submodule
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Supporting results for continuous linear maps

Auxiliary results used in the Hahn-Banach development.
-/

open Metric

namespace SphericallyCompleteSpace

lemma rooij_lemma_4_4_z0 {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
  [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
  {a : E} (ha1 : a ∉ D)
  {F : Type u_3} [SeminormedAddCommGroup F]
  [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
  (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖) :
  ∃ z0 : F, ∀ (x : ↥D) (U : ↑𝒰), ‖S x + z0 - U.val (↑x + a)‖ ≤ ε U * ‖↑x + a‖ := by
  rw [sphericallyCompleteSpace_iff_pairwise_inter_nonempty] at hsc
  let 𝒮 : Set (F × NNReal) := {(U.val x + U.val a - S x,
    ⟨(ε U) * ‖x + a‖, mul_nonneg (le_of_lt (hε1 _)) (norm_nonneg _)⟩) | (x : ↑D) (U : ↑𝒰)}
  have h𝒮ne : 𝒮.Nonempty := by
    use (h𝒰.some 0 + h𝒰.some a - S 0, ⟨(ε ⟨h𝒰.some, h𝒰.some_mem⟩)
      * ‖0 + a‖, mul_nonneg (le_of_lt (hε1 _)) (norm_nonneg _)⟩)
    unfold 𝒮
    use 0, ⟨h𝒰.some, h𝒰.some_mem⟩
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add, sub_zero]
  specialize hsc 𝒮 h𝒮ne
  have h𝒮 : ∀ (w1 w2 : ↑𝒮), (closedBall w1.val.1 w1.val.2 ∩
    closedBall w2.val.1 ↑w2.val.2).Nonempty := by
    intro s1 s2
    wlog h : ε s1.2.out.choose_spec.choose ≤ ε s2.2.out.choose_spec.choose
    · specialize this ha1 S h𝒰 hε1 hε2 hε3 hsc h𝒮ne s2 s1 (le_of_lt <| lt_of_not_ge h)
      rwa [Set.inter_comm]
    · let x := s1.2.out.choose
      let U := s1.2.out.choose_spec.choose
      let hxU := s1.2.out.choose_spec.choose_spec
      let y := s2.2.out.choose
      let V := s2.2.out.choose_spec.choose
      let hyV := s2.2.out.choose_spec.choose_spec
      have : ‖(U.val ↑x + U.val a - S x) - (V.val ↑y + V.val a - S y)‖ ≤
        max ((ε V) * ‖y + a‖) ((ε U) * ‖x + a‖) := by
        have : (U.val ↑x + U.val a - S x) - (V.val ↑y + V.val a - S y) =
          (U.val - V.val) (y + a) - (S (x - y) - U.val (x - y)) := by
          simp
          abel
        rw [this, sub_eq_add_neg]
        refine le_trans (iud.norm_add_le_max _ _) ?_
        rw [norm_neg]
        specialize hε3 U ⟨x.val - y.val, (Submodule.sub_mem_iff_left D y.prop).mpr x.prop⟩
        have : ⟨↑x - ↑y, (Submodule.sub_mem_iff_left D y.prop).mpr x.prop⟩ = x - y:= rfl
        rw [this] at hε3
        have : (x - y).val = x.val - y.val := rfl
        rw [this] at hε3
        specialize hε2 U V
        replace hε2 := mul_le_mul_of_nonneg_right hε2 (norm_nonneg (y + a))
        replace hε2 := le_trans (ContinuousLinearMap.le_opNorm (U.val - V.val) (y + a)) hε2
        refine le_trans (max_le_max hε2 hε3) ?_
        have hmax_bound : max (max (ε U) (ε V) * ‖↑y + a‖) (ε U * ‖x - y‖) ≤
          max ((ε V) * ‖↑y + a‖) (ε U * ‖x - y‖) := by
          refine sup_le_sup_right ?_ (ε U * ‖x - y‖)
          exact mul_le_mul_of_nonneg_right (max_le h <| le_refl (ε V)) (norm_nonneg _)
        refine le_trans hmax_bound ?_
        have hxy_eq : ((x - y : D) : E) = (↑x + a) + -(↑y + a) := by push_cast; abel
        have hnorm_eq : ‖x - y‖ = ‖(x.val + a) + -(y.val + a)‖ := by
          simpa using congrArg (fun z : E => ‖z‖) hxy_eq
        have hnorm_le : ‖x - y‖ ≤ max ‖x.val + a‖ ‖y.val + a‖ := by
          rw [hnorm_eq]
          refine le_trans (iude.norm_add_le_max _ _) ?_
          rw [norm_neg]
        have hmul_le : ε U * ‖x - y‖ ≤ max (ε U * ‖x + a‖) (ε U * ‖y + a‖) := by
          refine le_trans (mul_le_mul_of_nonneg_left hnorm_le (le_of_lt (hε1 U))) ?_
          rw [mul_max_of_nonneg _ _ (le_of_lt (hε1 U))]
        have hy_le : ε U * ‖y + a‖ ≤ ε V * ‖y + a‖ := by
          exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
        calc
          max (ε V * ‖↑y + a‖) (ε U * ‖x - y‖)
              ≤ max (ε V * ‖↑y + a‖) (max (ε U * ‖x + a‖) (ε U * ‖y + a‖)) :=
                by
                  apply max_le
                  · exact le_max_left _ _
                  · exact le_trans hmul_le (le_max_right _ _)
          _ = max (max (ε V * ‖↑y + a‖) (ε U * ‖x + a‖)) (ε U * ‖y + a‖) := by
                rw [max_assoc]
          _ = max (ε V * ‖↑y + a‖) (ε U * ‖x + a‖) := by
                apply max_eq_left
                exact le_trans hy_le (le_max_left _ _)
      rcases le_sup_iff.1 this with hc | hc
      · use U.val ↑x + U.val a - S x
        simp only [Set.mem_inter_iff]
        constructor
        · rw [← hxU]
          unfold U x
          simp only [Subtype.exists, mem_closedBall, dist_self]
          exact Left.mul_nonneg (le_of_lt (hε1 _)) <| norm_nonneg _
        · rw [← dist_eq_norm, ← mem_closedBall] at hc
          rwa [← hyV]
      · use V.val ↑y + V.val a - S y
        simp only [Set.mem_inter_iff]
        constructor
        · rw [← dist_eq_norm, dist_comm, ← mem_closedBall] at hc
          rwa [← hxU]
        · rw [← hyV]
          unfold V y
          simp only [Subtype.exists, mem_closedBall, dist_self]
          exact Left.mul_nonneg (le_of_lt (hε1 _)) <| norm_nonneg _
  specialize hsc h𝒮
  simp only [Set.iInter_coe_set, Set.nonempty_iInter, Set.mem_iInter, mem_closedBall] at hsc
  rcases hsc with ⟨z0, hz0⟩
  use z0
  intro x U
  have : (U.val x + U.val a - S x,
    ⟨ε U * ‖x.val + a‖, mul_nonneg (le_of_lt (hε1 _)) (norm_nonneg _) ⟩) ∈ 𝒮 := by
    use x, U
  specialize hz0 _ this
  simp only at hz0
  rw [dist_eq_norm] at hz0
  have : z0 - (U.val ↑x + U.val a - S x) = S x + z0 - U.val (↑x + a) := by
    simp only [map_add]; abel
  rwa [this] at hz0

lemma rooij_lemma_4_4_z0_prop {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
  [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
  {a : E} (ha1 : a ∉ D)
  {F : Type u_3} [SeminormedAddCommGroup F]
  [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
  (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖) :
  ∀ (x : ↥D) (l : 𝕜) (U : ↑𝒰),
  ‖S x + l • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose - U.val (↑x + l • a)‖ ≤
    ε U * ‖↑x + l • a‖ := by
  intro x l U
  if hl : l = 0 then
    simp only [hl, map_add, Subtype.forall, zero_smul, add_zero]
    exact hε3 U x
  else
  have : x = l • (l⁻¹ • x) := by
    rw [smul_smul, mul_inv_cancel₀ hl]
    exact Eq.symm (MulAction.one_smul x)
  rw [this, S.map_smul]
  have : ↑(l • l⁻¹ • x) + l • a = l • ((l⁻¹ • x) + a) := by
    simp only [SetLike.val_smul, smul_add]
  rw [this, U.val.map_smul, ← smul_add, ← smul_sub, norm_smul, norm_smul, ← mul_assoc]
  nth_rw 3 [mul_comm]
  rw [mul_assoc, mul_le_mul_iff_of_pos_left <| norm_pos_iff.mpr hl]
  exact (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose_spec (l⁻¹ • x) U

noncomputable def rooij_lemma_4_4_T {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
  [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
  {a : E} (ha1 : a ∉ D)
  {F : Type u_3} [SeminormedAddCommGroup F]
  [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
  (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖) :
  (D + Submodule.span 𝕜 {a}) → F := fun M => by
    have := Submodule.mem_sup.1 M.prop
    let lambda := (Submodule.mem_span_singleton.1 this.choose_spec.2.choose_spec.1).choose
    use S ⟨this.choose, this.choose_spec.1⟩ +
      lambda • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose

/-- The linear equivalence `↥(D + 𝕜∙a) ≃ₗ D × 𝕜` given by the (unique, since `a ∉ D`)
decomposition `x = d + l • a`. -/
noncomputable def spanSupDecomp {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {D : Submodule 𝕜 E} {a : E} (ha : a ∉ D) :
    ↥(D + Submodule.span 𝕜 {a}) ≃ₗ[𝕜] D × 𝕜 :=
  have hinj : Function.Injective (D.subtype.coprod (LinearMap.toSpanSingleton 𝕜 E a)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨d, l⟩ hdl
    simp only [LinearMap.coprod_apply, Submodule.subtype_apply,
      LinearMap.toSpanSingleton_apply] at hdl
    rcases eq_or_ne l 0 with hl | hl
    · subst hl; simp only [zero_smul, add_zero] at hdl; simp [Submodule.coe_eq_zero.1 hdl]
    · exact absurd ((neg_eq_of_add_eq_zero_right hdl ▸ D.neg_mem d.2 :
        l • a ∈ D) |> D.smul_mem l⁻¹ |> (by simpa [hl] using ·)) ha
  (LinearEquiv.ofEq _ _ (by rw [Submodule.add_eq_sup, LinearMap.range_coprod,
    Submodule.range_subtype, LinearMap.span_singleton_eq_range])).symm.trans
    (LinearEquiv.ofInjective _ hinj).symm

@[simp] lemma spanSupDecomp_symm_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {D : Submodule 𝕜 E} {a : E} (ha : a ∉ D)
    (d : D) (l : 𝕜) : (((spanSupDecomp ha).symm (d, l)) : E) = (d : E) + l • a := rfl

/-- Value of `rooij_lemma_4_4_T` expressed through the `spanSupDecomp` coordinates: it is the
composition of `S` on the `D`-part with scaling `rooij_lemma_4_4_z0` by the `𝕜`-part. -/
lemma rooij_lemma_4_4_T_eq {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
  [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
  {a : E} (ha1 : a ∉ D)
  {F : Type u_3} [SeminormedAddCommGroup F]
  [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
  (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖) (M : ↥(D + Submodule.span 𝕜 {a})) :
  rooij_lemma_4_4_T ha1 S h𝒰 hε1 hε2 hε3 M =
    S (spanSupDecomp ha1 M).1 +
      (spanSupDecomp ha1 M).2 • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose := by
  unfold rooij_lemma_4_4_T
  set p := Submodule.mem_sup.1 M.prop with hp
  set l := (Submodule.mem_span_singleton.1 p.choose_spec.2.choose_spec.1).choose with hl
  have ha0 : a ≠ 0 := fun h => ha1 (h ▸ D.zero_mem)
  have hMeq : (M : E) = ((spanSupDecomp ha1 M).1 : E) + (spanSupDecomp ha1 M).2 • a := by
    conv_lhs => rw [← (spanSupDecomp ha1).symm_apply_apply M]
    rw [spanSupDecomp_symm_apply]
  have hpeq : (p.choose : E) + l • a = (M : E) := by
    rw [hl, (Submodule.mem_span_singleton.1 p.choose_spec.2.choose_spec.1).choose_spec,
      p.choose_spec.2.choose_spec.2]
  have hdecomp := eq_and_eq_of_add_eq_add_of_not_mem_submodule_span_singleton ha1
    p.choose p.choose_spec.1 (l • a) (Submodule.mem_span_singleton.2 ⟨l, rfl⟩)
    (spanSupDecomp ha1 M).1 (spanSupDecomp ha1 M).1.2 ((spanSupDecomp ha1 M).2 • a)
    (Submodule.mem_span_singleton.2 ⟨_, rfl⟩) (hpeq.trans hMeq)
  refine congrArg₂ _ (congrArg S (Subtype.ext hdecomp.1)) ?_
  exact congrArg (· • _) (smul_left_injective 𝕜 ha0 hdecomp.2)

noncomputable def rooij_lemma_4_4_T_linear {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
  [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
  {a : E} (ha1 : a ∉ D)
  {F : Type u_3} [SeminormedAddCommGroup F]
  [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
  (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖) :
  IsLinearMap 𝕜 (rooij_lemma_4_4_T ha1 S h𝒰 hε1 hε2 hε3) where
  map_add x1 x2 := by
    simp only [rooij_lemma_4_4_T_eq, map_add, Prod.fst_add, Prod.snd_add, S.map_add, add_smul]
    abel
  map_smul k m := by
    simp only [rooij_lemma_4_4_T_eq, map_smul, Prod.smul_fst, Prod.smul_snd, S.map_smul,
      smul_smul, smul_add, smul_eq_mul]


noncomputable def rooij_lemma_4_4_T_boundedlinear {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [SeminormedAddCommGroup E] [iude : IsUltrametricDist E]
  [NormedSpace 𝕜 E] {D : Submodule 𝕜 E}
  {a : E} (ha1 : a ∉ D)
  {F : Type u_3} [SeminormedAddCommGroup F]
  [iud : IsUltrametricDist F] [NormedSpace 𝕜 F] [hsc : SphericallyCompleteSpace F]
  (S : ↥D →L[𝕜] F) {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  {ε : ↑𝒰 → ℝ} (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖) :
  IsBoundedLinearMap 𝕜 (rooij_lemma_4_4_T ha1 S h𝒰 hε1 hε2 hε3) where
  map_add := (rooij_lemma_4_4_T_linear ha1 S h𝒰 hε1 hε2 hε3).map_add
  map_smul := (rooij_lemma_4_4_T_linear ha1 S h𝒰 hε1 hε2 hε3).map_smul
  bound := by
    use max (ε ⟨h𝒰.some,h𝒰.some_mem⟩) ‖h𝒰.some‖
    refine ⟨lt_max_of_lt_left <| hε1 _, fun x => ?_⟩
    rw [rooij_lemma_4_4_T_eq]
    set d := (spanSupDecomp ha1 x).1 with hd
    set l := (spanSupDecomp ha1 x).2 with hl
    have hx_eq : (d : E) + l • a = ↑x := by
      rw [hd, hl, ← spanSupDecomp_symm_apply ha1, LinearEquiv.symm_apply_apply]
    have tt := (rooij_lemma_4_4_z0_prop ha1 S h𝒰 hε1 hε2 hε3) d l ⟨h𝒰.some, h𝒰.some_mem⟩
    rw [show S d + l • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose =
      S d + l • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose
      - h𝒰.some (d + l • a) + h𝒰.some (d + l • a) from by simp only [sub_add_cancel],
      max_mul_of_nonneg _ _ (norm_nonneg x)]
    refine le_trans (iud.norm_add_le_max _ _) (max_le_max ?_ ?_)
    · rw [show ‖x‖ = ‖(d : E) + l • a‖ by rw [hx_eq, Submodule.coe_norm]]
      simpa using tt
    · rw [hx_eq]
      exact ContinuousLinearMap.le_opNorm h𝒰.some ↑x

lemma rooij_lemma_4_4_codim_1
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
  use (rooij_lemma_4_4_T_boundedlinear ha1 S h𝒰 hε1 hε2 hε3).toContinuousLinearMap
  refine ⟨fun x => ?_, fun U x hx => ?_⟩
  · have hsup : x.val ∈ D + Submodule.span 𝕜 {a} := Submodule.mem_sup_left x.prop
    have hcoord : spanSupDecomp ha1 ⟨x.val, hsup⟩ = (x, 0) := by
      apply (spanSupDecomp ha1).symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact Subtype.ext (by rw [spanSupDecomp_symm_apply]; simp)
    change rooij_lemma_4_4_T ha1 S h𝒰 hε1 hε2 hε3 ⟨x.val, hsup⟩ = S x
    rw [rooij_lemma_4_4_T_eq, hcoord]; simp
  · change ‖rooij_lemma_4_4_T ha1 S h𝒰 hε1 hε2 hε3 ⟨x, hx⟩ - U.val x‖ ≤ ε U * ‖x‖
    rw [rooij_lemma_4_4_T_eq]
    have hx_eq : ((spanSupDecomp ha1 ⟨x, hx⟩).1 : E) + (spanSupDecomp ha1 ⟨x, hx⟩).2 • a = x := by
      rw [← spanSupDecomp_symm_apply ha1, LinearEquiv.symm_apply_apply]
    have := (rooij_lemma_4_4_z0_prop ha1 S h𝒰 hε1 hε2 hε3)
      (spanSupDecomp ha1 ⟨x, hx⟩).1 (spanSupDecomp ha1 ⟨x, hx⟩).2 U
    rwa [hx_eq] at this

@[ext]
private structure PartialExtension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(F : Type*) [SeminormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ) where
  M : Submodule 𝕜 E
  hDM : D ≤ M
  T : M →L[𝕜] F
  hT : ∀ x : D, T ⟨x, hDM x.prop⟩ = S x
  hU : ∀ U : ↑𝒰, ∀ x : M, ‖T x- U.val x‖ ≤ (ε U) * ‖x‖

private lemma instNonemptyPartialExtension
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(F : Type*) [SeminormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
(hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
: Nonempty (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε) :=
  Nonempty.intro { M := D, hDM := fun ⦃x⦄ a ↦ a, T := S, hT := by simp, hU := hε3 }

private instance instPartialOrderPartialExtension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(F : Type*) [SeminormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
: PartialOrder (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε) where
  le a b := ∃ hab : a.M ≤ b.M , ∀ x : a.M, b.T ⟨x.val, hab x.prop⟩ = a.T x
  le_refl a := by
    use fun ⦃x⦄ a ↦ a
    simp only [Subtype.coe_eta, implies_true]
  le_trans a b c := by
    rintro ⟨hab, habT⟩ ⟨hbc, hbcT⟩
    use fun ⦃x⦄ a ↦ hbc (hab a)
    intro x
    specialize habT x
    specialize hbcT ⟨x.val, hab x.prop⟩
    rw [hbcT, habT]
  le_antisymm a b:= by
    rintro ⟨hab, habT⟩ ⟨hba, hbaT⟩
    refine PartialExtension.ext ?_ ?_
    · exact Submodule.ext fun x ↦ { mp := fun a_1 ↦ hab a_1, mpr := fun a_1 ↦ hba a_1 }
    · have : a.M = b.M :=
        by rw [Submodule.ext fun x ↦ { mp := fun a_1 ↦ hab a_1, mpr := fun a_1 ↦ hba a_1 }]
      cases a; cases b
      subst this
      simp only [heq_eq_eq]
      ext z
      rw [← habT]

private lemma directed_chain (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [SeminormedAddCommGroup F] [IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)}
  (h𝒰 : 𝒰.Nonempty) (ε : ↑𝒰 → ℝ)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε)) (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P)
  : Directed (fun x1 x2 ↦ x1 ≤ x2) fun p : P ↦ p.val.M := fun a b =>
  (hP.directed a b).imp fun _ h => ⟨h.1.1, h.2.1⟩

private noncomputable def glued_map (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [SeminormedAddCommGroup F] [IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)}
  (h𝒰 : 𝒰.Nonempty) (ε : ↑𝒰 → ℝ)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε))
  (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P) (hhP : P.Nonempty) :
  ↥(iSup (fun p : P ↦ p.val.M)) → F := fun x => by
    haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
    have := (Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
      (by apply directed_chain; repeat assumption)).1 x.2
    exact this.choose.val.T ⟨x.val,this.choose_spec⟩

private def islinearmap_of_glued_map (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [SeminormedAddCommGroup F] [IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)}
  (h𝒰 : 𝒰.Nonempty) (ε : ↑𝒰 → ℝ)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε))
  (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P) (hhP : P.Nonempty) :
  IsLinearMap 𝕜 (glued_map 𝕜 h𝒰 ε P hP hhP) where
    map_add a b := by
      simp only [glued_map]
      haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
      let Mp := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 (a + b).prop).choose
      let hMp := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 (a + b).prop).choose_spec
      let Ma := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 a.prop).choose
      let hMa := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 a.prop).choose_spec
      let Mb := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 b.prop).choose
      let hMb := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 b.prop).choose_spec
      rcases hP.directed Ma Mb with ⟨Mab, hMab1, hMab2⟩
      rcases hP.directed Mp Mab with ⟨Mfinal, hMfinal1, hMfinal2⟩
      simp only [Subtype.coe_le_coe] at hMfinal1 hMfinal2 hMab1 hMab2
      have t1 : Mp.val.T ⟨↑(a+b),hMp⟩ = Mfinal.val.T ⟨↑(a+b), hMfinal1.choose hMp⟩ := by
        rw [hMfinal1.choose_spec ⟨↑(a+b),hMp⟩]
      have t2 : Ma.val.T ⟨↑a, hMa⟩ = Mfinal.val.T ⟨↑a, hMfinal2.choose <| hMab1.choose hMa⟩ := by
        rw [(le_trans hMab1 hMfinal2).choose_spec ⟨↑a, hMa⟩]
      have t3 : Mb.val.T ⟨↑b, hMb⟩ = Mfinal.val.T ⟨↑b, hMfinal2.choose <| hMab2.choose hMb⟩ := by
        rw [(le_trans hMab2 hMfinal2).choose_spec ⟨↑b, hMb⟩]
      rw [t1, t2, t3, ← Mfinal.val.T.map_add]
      simp only [Submodule.coe_add, AddMemClass.mk_add_mk]
    map_smul k a := by
      simp only [glued_map]
      haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
      let Mp := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 (k • a).prop).choose
      let hMp := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 (k • a).prop).choose_spec
      let Ma := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 a.prop).choose
      let hMa := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
        (by apply directed_chain; repeat assumption)).1 a.prop).choose_spec
      rcases hP.directed Ma Mp with ⟨Mfinal, hMfinal1, hMfinal2⟩
      simp only [Subtype.coe_le_coe] at hMfinal1 hMfinal2
      have t1 : Mp.val.T ⟨k • ↑a,hMp⟩ = Mfinal.val.T ⟨k • ↑a, hMfinal2.choose hMp⟩ := by
        rw [hMfinal2.choose_spec ⟨k • ↑a, hMp⟩]
      have t2 : Ma.val.T ⟨↑a, hMa⟩ = Mfinal.val.T ⟨↑a, hMfinal1.choose hMa⟩ := by
        rw [hMfinal1.choose_spec ⟨↑a, hMa⟩]
      simp only [SetLike.val_smul]
      rw [t1, t2, ← Mfinal.val.T.map_smul, SetLike.mk_smul_mk]

private def isboundedlinearmap_of_glued_map (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [SeminormedAddCommGroup F] [iudf : IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F}
  {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  (ε : ↑𝒰 → ℝ) (hε1 : ∀ (T : ↑𝒰), 0 < ε T)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε))
  (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P) (hhP : P.Nonempty) :
  IsBoundedLinearMap 𝕜 (glued_map 𝕜 h𝒰 ε P hP hhP) where
    map_add := (islinearmap_of_glued_map 𝕜 h𝒰 ε P hP hhP).map_add
    map_smul := (islinearmap_of_glued_map 𝕜 h𝒰 ε P hP hhP).map_smul
    bound := by
      use max (ε ⟨h𝒰.some, h𝒰.some_mem⟩) ‖h𝒰.some‖
      constructor
      · simp only [lt_sup_iff]
        exact Or.inl <| by simp only [hε1]
      · intro x
        simp only [glued_map]
        haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
        set Mx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
          (by apply directed_chain; repeat assumption)).1 x.prop).choose
        set hMx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
          (by apply directed_chain; repeat assumption)).1 x.prop).choose_spec
        rw [show (↑Mx : PartialExtension 𝕜 E F S 𝒰 h𝒰 ε).T ⟨↑x, hMx⟩ =
          (↑Mx : PartialExtension 𝕜 E F S 𝒰 h𝒰 ε).T ⟨↑x, hMx⟩ - h𝒰.some x.val + h𝒰.some x.val
          from by simp only [sub_add_cancel]]
        refine le_trans (iudf.norm_add_le_max _ _) ?_
        rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
        apply max_le_max
        · exact le_trans (Mx.val.hU ⟨h𝒰.some, h𝒰.some_mem⟩ ⟨x.val, hMx⟩) le_rfl
        · exact ContinuousLinearMap.le_opNorm h𝒰.some ↑x

private lemma bddAbove_of_chain_of_partial_extension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [SeminormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [SeminormedAddCommGroup F] [IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F}
  {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
  (ε : ↑𝒰 → ℝ) (hε1 : ∀ (T : ↑𝒰), 0 < ε T)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε))
  (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P) (hhP : P.Nonempty) : BddAbove P := by
  use { M := iSup (fun p : P ↦ p.val.M)
        hDM := fun z hz => (Submodule.mem_iSup _).2 <|
          fun N hN => (le_trans hhP.some.hDM <| hN ⟨hhP.some, hhP.some_mem⟩) hz
        T := IsBoundedLinearMap.toContinuousLinearMap _
          (isboundedlinearmap_of_glued_map 𝕜 h𝒰 ε hε1 P hP hhP)
        hT := by
          intro d
          haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
          have : D ≤ iSup (fun p : P ↦ p.val.M) := fun z hz => (Submodule.mem_iSup _).2 <|
            fun N hN => (le_trans hhP.some.hDM <| hN ⟨hhP.some, hhP.some_mem⟩) hz
          let Md := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 <| this d.prop).choose
          let hMd := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 <| this d.prop).choose_spec
          change glued_map 𝕜 h𝒰 ε P hP hhP ⟨↑d, _⟩ = S d
          unfold glued_map
          exact Md.val.hT d
        hU := by
          intro U x
          haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
          let Mx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 x.prop).choose
          let hMx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 x.prop).choose_spec
          change ‖glued_map 𝕜 h𝒰 ε P hP hhP x - U.val x.val‖ ≤ ε U * ‖x‖
          unfold glued_map
          exact Mx.val.hU U ⟨x.val, hMx⟩
      }
  simp only [upperBounds, Set.mem_setOf_eq]
  intro M hM
  unfold LE.le instPartialOrderPartialExtension
  have hM' : M.M ≤ ⨆ (p : ↑P), (↑p : PartialExtension 𝕜 E F S 𝒰 h𝒰 ε).M :=
    fun z hz => Submodule.mem_iSup_of_mem ⟨M,hM⟩ hz
  use hM'
  intro a
  change glued_map 𝕜 h𝒰 ε P hP hhP ⟨↑a, hM' a.prop⟩ = M.T a
  simp only [glued_map]
  haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
  let Ma := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
    (by apply directed_chain; repeat assumption)).1 (hM' a.prop)).choose
  let hMa := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
    (by apply directed_chain; repeat assumption)).1 (hM' a.prop)).choose_spec
  rcases hP.directed Ma ⟨M,hM⟩ with ⟨Mfinal, hMfinal1, hMfinal2⟩
  exact (hMfinal1.choose_spec ⟨↑a, hMa⟩).symm.trans (hMfinal2.choose_spec a)


/--
`exists_extension_opNorm_le` is an extension lemma for continuous linear maps between
ultrametric normed spaces over a nontrivially normed field.

Given:
* a submodule `D : Submodule 𝕜 E`,
* a continuous linear map `S : D →L[𝕜] F`,
* a nonempty family `𝒰 : Set (E →L[𝕜] F)` of continuous linear maps on `E`,
* a radius function `ε : 𝒰 → ℝ` with `0 < ε U` for all `U`,
* a pairwise compatibility bound
  `‖U - V‖ ≤ max (ε U) (ε V)` for all `U V ∈ 𝒰`,
* and a pointwise approximation bound on `D`
  `‖S x - U x‖ ≤ ε U * ‖x‖` for all `U ∈ 𝒰` and `x : D`,

then there exists an extension `T : E →L[𝕜] F` such that:
* `T` agrees with `S` on `D`, and
* for every `U ∈ 𝒰`, the operator norm distance is controlled by the given radius:
  `‖T - U‖ ≤ ε U`.

The spherical completeness assumption on `F` is used to realize the limit/selection
from the compatible family of operator-norm balls.
-/
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
:
∃ (T : E →L[𝕜] F), (∀ x : D, T x = S x) ∧ (∀ U : ↑𝒰, ‖T - U.val‖ ≤ ε U)
 := by
  rcases @zorn_le_nonempty (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε) _
    (instNonemptyPartialExtension 𝕜 E F S 𝒰 h𝒰 ε hε3) (by
    intro P hP hhP
    apply bddAbove_of_chain_of_partial_extension
    repeat assumption
  ) with ⟨W, hW⟩
  have : W.M = ⊤ := by
    by_contra hc
    have : W.M < ⊤ := Ne.lt_top' fun a ↦ hc (id (Eq.symm a))
    rcases Set.exists_of_ssubset this with ⟨a, ha⟩
    rcases rooij_lemma_4_4_codim_1 𝕜 E W.M a ha.2 F W.T 𝒰 h𝒰 ε hε1 hε2 W.hU with ⟨L, hL1, hL2⟩
    let W' : PartialExtension 𝕜 E F S 𝒰 h𝒰 ε :=
      { M := W.M + Submodule.span 𝕜 {a}
        T := L
        hDM := by
          refine le_trans W.hDM ?_
          simp only [Submodule.add_eq_sup, le_sup_left]
        hT := by
          intro x
          specialize hL1 ⟨x, W.hDM x.prop⟩
          rwa [← W.hT x]
        hU := fun U x => hL2 U x.val x.prop
      }
    have : W' > W := by
      apply lt_of_le_of_ne ?_ ?_
      · unfold LE.le instPartialOrderPartialExtension
        use (by
          have : W'.M = W.M + Submodule.span 𝕜 {a} := rfl
          rw [this]
          simp only [Submodule.add_eq_sup, le_sup_left]
        )
      · by_contra hc
        have : W'.M = W.M + Submodule.span 𝕜 {a} := rfl
        replace := this ▸ congrArg PartialExtension.M hc
        simp only [Submodule.add_eq_sup, left_eq_sup, Submodule.span_singleton_le_iff_mem] at this
        exact ha.2 this
    exact (not_le_of_gt this) <| hW <| le_of_lt this
  let f := W.T ∘ (LinearEquiv.ofTop _ this).symm
  have fiblm : IsBoundedLinearMap 𝕜 f := by
    unfold f
    apply IsBoundedLinearMap.comp (ContinuousLinearMap.isBoundedLinearMap W.T)
    refine { toIsLinearMap :=
      { map_add := fun x ↦ congrFun rfl, map_smul := fun c ↦ congrFun rfl }, bound := ⟨1, ?_⟩ }
    exact ⟨by norm_num, fun x => by simp [one_mul]⟩
  use IsBoundedLinearMap.toContinuousLinearMap _ fiblm
  constructor
  · intro D
    change f ↑D = S D
    unfold f
    simp only [Function.comp_apply, LinearEquiv.ofTop_symm_apply]
    exact W.hT D
  · intro U
    have tt : ∀ x : E, ‖(fiblm.toContinuousLinearMap - ↑U) x‖
      = ‖W.T ⟨x, this ▸ Submodule.mem_top⟩ - U.val x‖ := by
      intro x
      simp only [IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap,
        sub_apply, ContinuousLinearMap.coe_mk',
        IsLinearMap.mk'_apply, Function.comp_apply, LinearEquiv.ofTop_symm_apply, f]
    rw [ContinuousLinearMap.opNorm_le_iff <| le_of_lt <| hε1 U]
    exact fun x => tt x ▸ W.hU U ⟨x, this ▸ Submodule.mem_top⟩


end SphericallyCompleteSpace
