import SphericalCompleteness.NormedVectorSpace.ContinuousLinearMap.HahnBanach

open Metric

namespace SphericallyCompleteSpace

def IsImmediate {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
{F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
(f : E →ₗᵢ[𝕜] F) : Prop :=
∀ v : F, (v ⟂ₘ LinearMap.range f) → v = 0

noncomputable def LinearIsometry.weakInv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
(f : E →ₗᵢ[𝕜] F) : LinearMap.range f →ₗᵢ[𝕜] E where
  toFun := Function.invFun <| Set.rangeFactorization f
  map_add' x y := by
    have : Function.Injective (Set.rangeFactorization f) := by
      refine Set.rangeFactorization_injective.mpr ?_
      exact LinearIsometry.injective f
    have t := Function.rightInverse_invFun (@Set.rangeFactorization_surjective _ _ f)
    unfold Function.RightInverse Function.LeftInverse at t
    have tx := t x
    have ty := t y
    apply_fun (Set.rangeFactorization f)
    rw [t (x + y)]
    apply_fun Subtype.val
    · simp only [Submodule.coe_add, Set.rangeFactorization_coe, map_add]
      apply_fun Subtype.val at tx ty
      simp only [Set.rangeFactorization_coe] at tx ty
      rw [tx, ty]
    · exact Subtype.val_injective
  map_smul' c x := by
    simp
    apply_fun (Set.rangeFactorization f)
    · apply_fun Subtype.val
      · simp
        have t := Function.rightInverse_invFun (@Set.rangeFactorization_surjective _ _ f)
        unfold Function.RightInverse Function.LeftInverse at t
        have tc := t (c • x)
        have tx := t x
        apply_fun Subtype.val at tc tx
        simp at tc tx
        rw [tc, tx]
      · exact Subtype.val_injective
    · refine Set.rangeFactorization_injective.mpr ?_
      exact LinearIsometry.injective f
  norm_map' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_norm, Subtype.forall,
      LinearMap.mem_range, forall_exists_index]
    intro a x h
    simp only [← h, LinearIsometry.norm_map]
    congr
    have : f x = Set.rangeFactorization f x := by
      simp only [Set.rangeFactorization_coe]
    conv => arg 1; arg 2; arg 1; rw [this]
    exact Function.leftInverse_invFun
      (Set.rangeFactorization_injective.mpr <| LinearIsometry.injective f) x

theorem noname' {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [IsUltrametricDist E] {F : Type u_3} [NormedAddCommGroup F] [inst_5 : NormedSpace 𝕜 F]
  [IsUltrametricDist F] {H : Type u_4} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [IsUltrametricDist H] [SphericallyCompleteSpace H] (f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f)
  (g : E →ₗᵢ[𝕜] H) (h : F →L[𝕜] H)
  (hf2 : ‖h‖ = ‖g.toContinuousLinearMap.comp (LinearIsometry.weakInv f).toContinuousLinearMap‖)
  (hf1 : ∀ (v : F) (x : E) (h_1 : f x = v), h v = g ((LinearIsometry.weakInv f) ⟨v, Exists.intro
    x h_1⟩))
  (this :
    ‖(g.comp (LinearIsometry.weakInv f)).toContinuousLinearMap‖ =
      ‖g.toContinuousLinearMap.comp (LinearIsometry.weakInv f).toContinuousLinearMap‖)
  (v : F) : ‖(↑h : F →ₗ[𝕜] H) v‖ = ‖v‖ := by
  refine eq_of_le_of_ge ?_ ?_
  · suffices hh : ‖h‖ ≤ 1 by
      have := (ContinuousLinearMap.opNorm_le_iff zero_le_one).1 hh v
      simpa only [one_mul]
    rw [hf2]
    apply  (ContinuousLinearMap.opNorm_le_iff zero_le_one).2
    intro x
    have : ‖(LinearIsometry.weakInv f).toContinuousLinearMap x‖ = ‖x‖ := by
      simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
        AddSubgroupClass.coe_norm]
    rw [← this]
    simp only [ContinuousLinearMap.coe_comp', LinearIsometry.coe_toContinuousLinearMap,
      Function.comp_apply, LinearIsometry.norm_map, AddSubgroupClass.coe_norm, one_mul, le_refl]
  · if hv : v = 0 then
      simp [hv]
    else
    simp [IsImmediate] at hf
    specialize hf v
    simp [hv, MOrth] at hf
    replace hf : infDist v ↑(LinearMap.range f) < ‖v‖ := by
      refine lt_of_le_of_ne ?_ hf
      rw [← dist_zero_right v]
      exact infDist_le_dist_of_mem <| zero_mem (LinearMap.range f)
    rcases(infDist_lt_iff <| Submodule.nonempty (LinearMap.range f)).1 hf with ⟨x, hx⟩
    rw [dist_eq_norm] at hx
    have : ‖h x - h v‖ < ‖v‖ := by
      rw [(by simp : h x - h v = h (x - v))]
      refine lt_of_le_of_lt (ContinuousLinearMap.le_opNorm h (x - v)) ?_
      have : ‖h‖ = 1 := by
        have : ‖(g.comp (LinearIsometry.weakInv f)).toContinuousLinearMap‖ = ‖ (g.toContinuousLinearMap).comp (LinearIsometry.weakInv f).toContinuousLinearMap‖ := rfl
        rw [← this] at hf2
        rw [hf2]
        have : Nontrivial ↥(LinearMap.range f) := by

          sorry
        exact LinearIsometry.norm_toContinuousLinearMap _
      rw [this, one_mul, norm_sub_rev]
      exact hx.2
    rw [sub_eq_add_neg] at hx
    -- IsUltrametricDist.norm_eq_of_add_norm_lt_max
    sorry

theorem noname {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]
{H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [IsUltrametricDist H]
[SphericallyCompleteSpace H]
(f : E →ₗᵢ[𝕜] F) (hf : IsImmediate f)
(g : E →ₗᵢ[𝕜] H) :
∃ (h : F →ₗᵢ[𝕜] H), @LinearIsometry.comp 𝕜 𝕜 𝕜 E F H _ _ _ (RingHom.id _)
(RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ h f = g := by
  rcases hahn_banach' _
    (LinearIsometry.comp g (LinearIsometry.weakInv f)).toContinuousLinearMap with ⟨h, hf1, hf2⟩
  simp at hf1
  have : ‖(g.comp (LinearIsometry.weakInv f)).toContinuousLinearMap‖ = ‖ (g.toContinuousLinearMap).comp (LinearIsometry.weakInv f).toContinuousLinearMap‖ := rfl
  rw [this] at hf2
  let h : F →ₗᵢ[𝕜] H := {
    toFun := h.toFun,
    map_add' := h.map_add',
    map_smul' := h.map_smul',
    norm_map' := fun v => noname' f hf g h hf2 hf1 this v
  }
  use h
  ext z
  simp [h]
  have : (LinearIsometry.weakInv f) ⟨f z, LinearMap.mem_range_self f z⟩ = z := by
    unfold LinearIsometry.weakInv
    simp
    have : f z = Set.rangeFactorization f z := by
      simp only [Set.rangeFactorization_coe]
    conv => arg 1; arg 2; arg 1; rw [this]
    exact Function.leftInverse_invFun
      (Set.rangeFactorization_injective.mpr <| LinearIsometry.injective f) z
  rw [hf1 (f z) z rfl, this]

end SphericallyCompleteSpace
