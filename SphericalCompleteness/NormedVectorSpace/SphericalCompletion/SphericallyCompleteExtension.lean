import SphericalCompleteness.NormedVectorSpace.Existance
import Mathlib.Algebra.Order.Group.DenselyOrdered

namespace SphericallyCompleteSpace

def sphericallyCompleteExtension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
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
        · simp only [add_zero, lp.norm_eq_ciSup, ciSup_const]
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
        simp only [c₀, gt_iff_lt, ge_iff_le, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hp'
        rcases hp' ε hε with ⟨N, hN⟩
        refine le_trans (?_: _ ≤ ‖x + p N‖) ?_
        · specialize hN N (le_refl N)
          rw [← sub_neg_eq_add x (p N)]
          refine le_trans ?_ (norm_sub_norm_le _ _)
          rw [norm_neg]
          linarith
        · exact le_of_eq_of_le (by rfl) (lp.norm_apply_le_norm ENNReal.top_ne_zero _ N)

noncomputable instance (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
   NormedAddCommGroup (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E):= by
  have : IsClosed (↑(c₀ 𝕜 fun x ↦ E).carrier) := by
    apply IsSeqClosed.isClosed
    simp [IsSeqClosed]
    intro seq lim hlim hseq htend
    rw [NormedAddCommGroup.tendsto_atTop] at htend
    intro ε hε
    specialize htend (ε / 2) (by linarith)
    rcases htend with ⟨N, hN⟩
    specialize hN N (le_refl N)
    rw [lp.norm_eq_ciSup] at hN
    specialize hseq N
    simp [c₀] at hseq
    specialize hseq (ε / 2) (by linarith)
    rcases hseq with ⟨M, hM⟩
    use M.max N
    intro n hn
    specialize hM n (by simp_all only
      [gt_iff_lt, AddSubgroupClass.coe_sub, Pi.sub_apply, ge_iff_le, sup_le_iff])
    have := (ciSup_le_iff (by
      use ‖seq N - ⟨lim, hlim⟩‖
      simp only [upperBounds,  Set.mem_range,
        forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
      intro a
      refine lp.norm_apply_le_norm ?_ (seq N - ⟨lim, hlim⟩) a
      exact ENNReal.top_ne_zero
      )).1 (le_of_lt hN) n
    simp at this
    simp
    replace := add_le_add hM this
    rw [norm_sub_rev, add_comm] at this
    simp at this
    refine le_trans ?_ this
    exact norm_le_norm_sub_add _ _
  simp at this
  infer_instance

end SphericallyCompleteSpace
