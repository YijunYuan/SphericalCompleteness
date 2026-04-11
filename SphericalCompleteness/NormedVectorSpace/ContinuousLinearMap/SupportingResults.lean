import SphericalCompleteness.NormedVectorSpace.Basic
import SphericalCompleteness.External.Submodule

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
  have : 𝒮.Nonempty := by
    use (h𝒰.some 0 + h𝒰.some a - S 0, ⟨(ε ⟨h𝒰.some, h𝒰.some_mem⟩)
      * ‖0 + a‖, mul_nonneg (le_of_lt (hε1 _)) (norm_nonneg _)⟩)
    unfold 𝒮
    use 0, ⟨h𝒰.some, h𝒰.some_mem⟩
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add, sub_zero]
  specialize hsc 𝒮 this
  have h𝒮 : ∀ (w1 w2 : ↑𝒮), (closedBall w1.val.1 w1.val.2 ∩
    closedBall w2.val.1 ↑w2.val.2).Nonempty := by
    intro s1 s2
    wlog h : ε s1.2.out.choose_spec.choose ≤ ε s2.2.out.choose_spec.choose
    · specialize this ha1 S h𝒰 hε1 hε2 hε3 (by assumption)
        hsc s2 s1 (le_of_lt <| lt_of_not_ge h)
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
        have : max (max (ε U) (ε V) * ‖↑y + a‖) (ε U * ‖x - y‖) ≤
          max ((ε V) * ‖↑y + a‖) (ε U * ‖x - y‖) := by
          refine sup_le_sup_right ?_ (ε U * ‖x - y‖)
          exact mul_le_mul_of_nonneg_right (max_le h <| le_refl (ε V)) (norm_nonneg _)
        refine le_trans this ?_
        have : ‖x - y‖ = ‖(x.val + a) + -(y.val + a)‖ := by
          rw [← sub_eq_add_neg]
          simp only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub, add_sub_add_right_eq_sub]
        replace this : ‖x - y‖ ≤ max ‖x.val + a‖ ‖y.val + a‖:= by
          rw [this]
          refine le_trans (iude.norm_add_le_max _ _) ?_
          rw [norm_neg]
        replace := mul_le_mul_of_nonneg_left this <| le_of_lt (hε1 U)
        rw [mul_max_of_nonneg _ _ (le_of_lt (hε1 U))] at this
        refine le_trans (max_le_max_left _ this) ?_
        nth_rw 2 [max_comm]
        rw [← max_assoc]
        nth_rw 2 [max_eq_left]
        exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
      rcases le_sup_iff.1 this with hc | hc
      · use U.val ↑x + U.val a - S x
        simp only [Set.mem_inter_iff]
        constructor
        · rw [← hxU]
          unfold U x
          simp only [Subtype.exists, NNReal.coe_mk, mem_closedBall, dist_self]
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
          simp only [Subtype.exists, NNReal.coe_mk, mem_closedBall, dist_self]
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
    unfold rooij_lemma_4_4_T
    simp only
    have hdecomp := eq_and_eq_of_add_eq_add_of_not_mem_submodule_span_singleton ha1
      (Submodule.mem_sup.1 (x1 + x2).prop).choose
      (Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.1
      (Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.2.choose
      (Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.2.choose_spec.1
      ((Submodule.mem_sup.1 x1.prop).choose + (Submodule.mem_sup.1 x2.prop).choose) (by
      refine Submodule.add_mem D ?_ ?_
      · exact (Submodule.mem_sup.1 x1.prop).choose_spec.1
      · exact (Submodule.mem_sup.1 x2.prop).choose_spec.1)
      ((Submodule.mem_sup.1 x1.prop).choose_spec.2.choose +
        (Submodule.mem_sup.1 x2.prop).choose_spec.2.choose) (by
        refine Submodule.add_mem _ ?_ ?_
        · exact (Submodule.mem_sup.1 x1.prop).choose_spec.2.choose_spec.1
        · exact (Submodule.mem_sup.1 x2.prop).choose_spec.2.choose_spec.1
          ) (by
        rw [add_add_add_comm]
        rw [(Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.2.choose_spec.2]
        rw [(Submodule.mem_sup.1 x1.prop).choose_spec.2.choose_spec.2]
        rw [(Submodule.mem_sup.1 x2.prop).choose_spec.2.choose_spec.2]
        exact rfl
        )
    have hS :
        S ⟨(Submodule.mem_sup.1 (x1 + x2).prop).choose,
          (Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.1⟩ =
        S (⟨(Submodule.mem_sup.1 x1.prop).choose,
            (Submodule.mem_sup.1 x1.prop).choose_spec.1⟩ +
          ⟨(Submodule.mem_sup.1 x2.prop).choose,
            (Submodule.mem_sup.1 x2.prop).choose_spec.1⟩) := by
      exact congrArg S <| Subtype.ext hdecomp.1
    have hsmul :
        (Submodule.mem_span_singleton.1
          (Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.2.choose_spec.1).choose =
        (Submodule.mem_span_singleton.1
          (Submodule.mem_sup.1 x1.prop).choose_spec.2.choose_spec.1).choose +
        (Submodule.mem_span_singleton.1
          (Submodule.mem_sup.1 x2.prop).choose_spec.2.choose_spec.1).choose := by
      have hspan := hdecomp.2
      rw [← (Submodule.mem_span_singleton.1
            (Submodule.mem_sup.1 x1.prop).choose_spec.2.choose_spec.1).choose_spec,
          ← (Submodule.mem_span_singleton.1
            (Submodule.mem_sup.1 x2.prop).choose_spec.2.choose_spec.1).choose_spec,
          ← (Submodule.mem_span_singleton.1
            (Submodule.mem_sup.1 (x1 + x2).prop).choose_spec.2.choose_spec.1).choose_spec,
          ← add_smul] at hspan
      have ha : a ≠ 0 := by
        by_contra hc
        contrapose ha1
        simp only [hc, zero_mem]
      exact smul_left_injective _ ha hspan
    rw [hS, S.map_add, hsmul, add_smul]
    abel
  map_smul k m := by
    unfold rooij_lemma_4_4_T
    simp only
    have := eq_and_eq_of_add_eq_add_of_not_mem_submodule_span_singleton ha1
        (Submodule.mem_sup.1 (k • m).prop).choose
        (Submodule.mem_sup.1 (k • m).prop).choose_spec.1
        (Submodule.mem_sup.1 (k • m).prop).choose_spec.2.choose
        (Submodule.mem_sup.1 (k • m).prop).choose_spec.2.choose_spec.1
        (k • (Submodule.mem_sup.1 m.prop).choose) (by
        refine Submodule.smul_mem D k ?_
        exact (Submodule.mem_sup.1 m.prop).choose_spec.1)
        (k • (Submodule.mem_sup.1 m.prop).choose_spec.2.choose) (by
        refine Submodule.smul_mem _ k ?_
        exact (Submodule.mem_sup.1 m.prop).choose_spec.2.choose_spec.1
        ) (by
        rw [← smul_add]
        rw [(Submodule.mem_sup.1 (k • m).prop).choose_spec.2.choose_spec.2]
        rw [(Submodule.mem_sup.1 m.prop).choose_spec.2.choose_spec.2]
        rfl
        )
    rw [smul_add, ← S.map_smul]
    congr 1
    · congr
      rw [this.1]
    · rw [smul_smul]
      congr
      rw [← (Submodule.mem_span_singleton.1 (Submodule.mem_sup.1
            (k • m).prop).choose_spec.2.choose_spec.1).choose_spec,
          ← (Submodule.mem_span_singleton.1 (Submodule.mem_sup.1
             m.prop).choose_spec.2.choose_spec.1).choose_spec,
          smul_smul] at this
      have ha : a ≠ 0 := by
        by_contra hc
        contrapose ha1
        simp only [hc, zero_mem]
      exact smul_left_injective _ ha this.2

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
    unfold rooij_lemma_4_4_T
    simp only
    set d := (Submodule.mem_sup.1 x.prop).choose
    set hd := (Submodule.mem_sup.1 x.prop).choose_spec.1
    set l := (Submodule.mem_span_singleton.1
      (Submodule.mem_sup.1 x.prop).choose_spec.2.choose_spec.1).choose
    have tt := (rooij_lemma_4_4_z0_prop ha1 S h𝒰 hε1 hε2 hε3) ⟨d, hd⟩ l ⟨h𝒰.some, h𝒰.some_mem⟩
    rw [show S ⟨d, hd⟩ + l • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose =
      S ⟨d, hd⟩ + l • (rooij_lemma_4_4_z0 ha1 S h𝒰 hε1 hε2 hε3).choose
      - h𝒰.some (d + l • a) + h𝒰.some (d + l • a) from by simp only [sub_add_cancel],
      max_mul_of_nonneg _ _ (norm_nonneg x)]
    have hx_eq := (Submodule.mem_sup.1 x.prop).choose_spec.2.choose_spec.2
    rw [← (Submodule.mem_span_singleton.1
      (Submodule.mem_sup.1 x.prop).choose_spec.2.choose_spec.1).choose_spec] at hx_eq
    refine le_trans (iud.norm_add_le_max _ _) ?_
    apply max_le_max
    · convert tt
      simp only [Submodule.add_eq_sup, AddSubgroupClass.coe_norm]
      rw [hx_eq]
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
  constructor
  · intro x
    unfold IsBoundedLinearMap.toContinuousLinearMap IsBoundedLinearMap.toLinearMap
      IsLinearMap.mk' rooij_lemma_4_4_T
    simp only [Submodule.add_eq_sup, map_add, Subtype.forall, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk]
    have : x.val ∈ D + Submodule.span 𝕜 {a} := Submodule.mem_sup_left x.prop
    have t := eq_and_eq_of_add_eq_add_of_not_mem_submodule_span_singleton ha1
      (Submodule.mem_sup.1 this).choose (Submodule.mem_sup.1 this).choose_spec.1
      ((Submodule.mem_span_singleton.1
        (Submodule.mem_sup.1 this).choose_spec.2.choose_spec.1).choose • a)
      ((Submodule.mem_span_singleton.1
        (Submodule.mem_sup.1 this).choose_spec.2.choose_spec.1).choose_spec.symm ▸
        (Submodule.mem_sup.1 this).choose_spec.2.choose_spec.1)
      x.val x.prop 0 (Submodule.zero_mem _)
    specialize t (by
      have := (Submodule.mem_span_singleton.1
        (Submodule.mem_sup.1 this).choose_spec.2.choose_spec.1).choose_spec.symm ▸
        (Submodule.mem_sup.1 this).choose_spec.2.choose_spec.2
      rw [this, add_zero]
      )
    have := (smul_eq_zero_iff_left (by
      contrapose ha1
      simp only [ha1, zero_mem])).1 t.2
    simp only [this, zero_smul, add_zero]
    congr
    exact t.1
  · intro U x hx
    unfold IsBoundedLinearMap.toContinuousLinearMap IsBoundedLinearMap.toLinearMap
      IsLinearMap.mk' rooij_lemma_4_4_T
    have := (rooij_lemma_4_4_z0_prop ha1 S h𝒰 hε1 hε2 hε3) ⟨(Submodule.mem_sup.1 hx).choose,
      (Submodule.mem_sup.1 hx).choose_spec.1⟩ ((Submodule.mem_span_singleton.1
      (Submodule.mem_sup.1 hx).choose_spec.2.choose_spec.1).choose) U
    have t := (Submodule.mem_span_singleton.1
      (Submodule.mem_sup.1 hx).choose_spec.2.choose_spec.1).choose_spec ▸
      (Submodule.mem_sup.1 hx).choose_spec.2.choose_spec.2
    rwa [t] at this

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

private instance instNonemptyPartialExtension
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
  : Directed (fun x1 x2 ↦ x1 ≤ x2) fun p : P ↦ p.val.M := by
  intro a b
  rcases hP.directed a b with ⟨c, hc1, hc2⟩
  use c
  constructor
  · cases hc1; assumption
  · cases hc2; assumption

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
        · simp only [AddSubgroupClass.coe_norm]
          exact ContinuousLinearMap.le_opNorm h𝒰.some ↑x

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
          simp only [IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap,
            ContinuousLinearMap.coe_mk', IsLinearMap.mk'_apply, glued_map]
          haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
          have : D ≤ iSup (fun p : P ↦ p.val.M) := fun z hz => (Submodule.mem_iSup _).2 <|
            fun N hN => (le_trans hhP.some.hDM <| hN ⟨hhP.some, hhP.some_mem⟩) hz
          rw [((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 <| this d.prop).choose.val.hT]
        hU := by
          intro U x
          simp only [IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap,
            ContinuousLinearMap.coe_mk', IsLinearMap.mk'_apply, glued_map,
            AddSubgroupClass.coe_norm]
          haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
          let Mx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 x.prop).choose
          let hMx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
            (by apply directed_chain; repeat assumption)).1 x.prop).choose_spec
          simpa only [ge_iff_le, AddSubgroupClass.coe_norm] using Mx.val.hU U ⟨x.val, hMx⟩
      }
  simp only [upperBounds, Set.mem_setOf_eq]
  intro M hM
  unfold LE.le instPartialOrderPartialExtension
  simp only [Subtype.forall, not_exists, not_forall]
  have hM' : M.M ≤ ⨆ (p : ↑P), (↑p : PartialExtension 𝕜 E F S 𝒰 h𝒰 ε).M :=
    fun z hz => Submodule.mem_iSup_of_mem ⟨M,hM⟩ hz
  use hM'
  intro a ha
  simp only [IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap,
    ContinuousLinearMap.coe_mk', IsLinearMap.mk'_apply, glued_map]
  haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
  let Ma := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
    (by apply directed_chain; repeat assumption)).1 (hM' ha)).choose
  let hMa := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
    (by apply directed_chain; repeat assumption)).1 (hM' ha)).choose_spec
  rcases hP.directed Ma ⟨M,hM⟩ with ⟨Mfinal, hMfinal1, hMfinal2⟩
  rw [← hMfinal1.choose_spec ⟨a, hMa⟩, ← hMfinal2.choose_spec ⟨a, ha⟩]


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
    simp only [zero_lt_one, AddSubgroupClass.coe_norm, LinearEquiv.coe_ofTop_symm_apply, one_mul,
      le_refl, implies_true, and_self]
  use IsBoundedLinearMap.toContinuousLinearMap _ fiblm
  constructor
  · intro D
    simpa only [IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap,
      IsLinearMap.mk', LinearEquiv.ofTop, LinearEquiv.coe_symm_mk', ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply] using W.hT D
  · intro U
    have tt : ∀ x : E, ‖(fiblm.toContinuousLinearMap - ↑U) x‖
      = ‖W.T ⟨x, this ▸ Submodule.mem_top⟩ - U.val x‖ := by
      intro x
      simp only [IsBoundedLinearMap.toContinuousLinearMap, IsBoundedLinearMap.toLinearMap,
        ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_mk', Pi.sub_apply,
        IsLinearMap.mk'_apply, Function.comp_apply, LinearEquiv.ofTop_symm_apply, f]
    rw [ContinuousLinearMap.opNorm_le_iff <| le_of_lt <| hε1 U]
    exact fun x => tt x ▸ W.hU U ⟨x, this ▸ Submodule.mem_top⟩


end SphericallyCompleteSpace
