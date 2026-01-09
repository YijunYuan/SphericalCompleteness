import SphericalCompleteness.NormedVectorSpace.Existance
import Mathlib.Algebra.Order.Group.DenselyOrdered

namespace SphericallyCompleteSpace

def sphericallyCompleteExtension {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [IsUltrametricDist 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
  E →ₗᵢ[𝕜] ((lp (fun (_ : ℕ) => E) ⊤)⧸ c₀ 𝕜 (fun (_ : ℕ) => E)) where
  toFun x := by
    have : (fun (_ : ℕ) => x) ∈ (lp (fun (_ : ℕ) => E) ⊤) := by
      simp only [lp, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
      refine Set.mem_setOf.mpr ?_
      refine memℓp_infty ?_
      use ‖x‖
      simp only [upperBounds, Set.range_const, Set.mem_singleton_iff, forall_eq, Set.mem_setOf_eq,
        le_refl]
    exact (QuotientAddGroup.mk' (c₀ 𝕜 (fun x ↦ E)).toAddSubgroup) (⟨fun (_ : ℕ) => x, this⟩)
  map_add' x y := rfl
  map_smul' c x := rfl
  norm_map' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    intro x
    rw [quotient_norm_mk_eq]
    simp only [Submodule.coe_toAddSubgroup]
    refine eq_of_le_of_ge ?_ ?_
    · apply csInf_le
      · use 0
        apply mem_lowerBounds.2
        intro z hz
        rw [Set.mem_image] at hz
        rw [← hz.choose_spec.2]
        exact norm_nonneg _
      · rw [Set.mem_image]
        use 0
        constructor
        · simp only [SetLike.mem_coe, zero_mem]
        · simp only [add_zero]
          rw [lp.norm_eq_ciSup]
          simp only [ciSup_const]
    · apply le_csInf
      · use ‖x‖
        simp only [Set.mem_image, SetLike.mem_coe, Subtype.exists, AddMemClass.mk_add_mk]
        use 0
        refine ⟨zero_mem _, zero_mem _, ?_⟩
        simp only [add_zero]
        rw [lp.norm_eq_ciSup]
        simp only [ciSup_const]
      · intro b hb
        simp only [Set.mem_image, SetLike.mem_coe, Subtype.exists, AddMemClass.mk_add_mk] at hb
        rcases hb with ⟨p, hp, hp', h⟩
        rw [← h]
        apply le_of_forall_pos_sub_le
        intro ε hε
        simp [c₀] at hp'
        rcases hp' ε hε with ⟨N, hN⟩
        refine le_trans (?_: _ ≤ sSup {‖x + p i‖ | i ≥ N}) ?_
        · refine le_csSup_of_le ?_ (?_ : ‖x + p N‖ ∈ _) ?_
          · use b
            rw [← h]
            rw [mem_upperBounds]
            simp only [ge_iff_le, Set.mem_setOf_eq, forall_exists_index, and_imp,
              forall_apply_eq_imp_iff₂]
            intro s hs
            refine le_of_eq_of_le ?_ (lp.norm_apply_le_norm ENNReal.top_ne_zero _ s)
            rfl
          · use N
          · specialize hN N (le_refl N)
            rw [(by abel : x + p N = x - - (p N))]
            refine le_trans ?_ (norm_sub_norm_le _ _)
            rw [norm_neg]
            linarith
        · apply csSup_le
          · use ‖x + p N‖, N
          · intro b hb
            simp only [ge_iff_le, Set.mem_setOf_eq] at hb
            rcases hb with ⟨i, hi, hi'⟩
            rw [← hi']
            refine le_of_eq_of_le ?_ (lp.norm_apply_le_norm ENNReal.top_ne_zero _ i)
            rfl

end SphericallyCompleteSpace
