import SphericalCompleteness.VectorSpace

namespace SphericalCompleteness

lemma lemma_4_4_codim_1
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
(D : Submodule 𝕜 E)
(a : E) (ha1 : a ∉ D) (ha2 : D + Submodule.span 𝕜 {a} = ⊤)
(F : Type*) [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
(hε1 : ∀ T : ↑𝒰, 0 < ε T)
(hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
(hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
:
∃ (T : E →L[𝕜] F), (∀ x : D, T x = S x) ∧ (∀ U : ↑𝒰, ‖T - U.val‖ ≤ ε U)
 := sorry


@[ext]
structure PartialExtension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(F : Type*) [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ) where
  M : Submodule 𝕜 E
  hDM : D ≤ M
  T : M →L[𝕜] F
  hT : ∀ x : D, T ⟨x, hDM x.prop⟩ = S x
  hU : ∀ U : ↑𝒰, ∀ x : M, ‖T x- U.val x‖ ≤ (ε U) * ‖x‖

instance pene (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(F : Type*) [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
(S : D →L[𝕜] F) (𝒰 : Set (E →L[𝕜] F)) (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
(hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
: Nonempty (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε) :=
  Nonempty.intro { M := D, hDM := fun ⦃x⦄ a ↦ a, T := S, hT := by simp, hU := hε3 }

instance (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : Type*) [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
(F : Type*) [NormedAddCommGroup F] [IsUltrametricDist F]
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

theorem directed_chain (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [NormedAddCommGroup F] [IsUltrametricDist F]
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

noncomputable def glued_map (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [NormedAddCommGroup F] [IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)}
  (h𝒰 : 𝒰.Nonempty) (ε : ↑𝒰 → ℝ)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε))
  (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P) (hhP : P.Nonempty) :
  ↥(iSup (fun p : P ↦ p.val.M)) → F := fun x => by
    haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
    have := (Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
      (by apply directed_chain; repeat assumption)).1 x.2
    exact this.choose.val.T ⟨x.val,this.choose_spec⟩

noncomputable def islinearmap_of_glued_map (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [NormedAddCommGroup F] [IsUltrametricDist F]
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

noncomputable def isboundedlinearmap_of_glued_map (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [NormedAddCommGroup F] [iudf : IsUltrametricDist F]
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
      · simp only [lt_sup_iff, norm_pos_iff, ne_eq]
        exact Or.inl <| by simp only [hε1]
      · intro x
        simp only [glued_map]
        haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
        let Mx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
          (by apply directed_chain; repeat assumption)).1 x.prop).choose
        let hMx := ((Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M)
          (by apply directed_chain; repeat assumption)).1 x.prop).choose_spec
        rw [← sub_add_cancel ((↑Mx : PartialExtension 𝕜 E F S 𝒰 h𝒰 ε).T ⟨↑x, hMx⟩) (h𝒰.some x.val)]
        refine le_trans (iudf.norm_add_le_max _ _) ?_
        apply max_le
        · refine le_trans (Mx.val.hU ⟨h𝒰.some, h𝒰.some_mem⟩ ⟨x.val, hMx⟩) ?_
          rw [max_mul_of_nonneg]
          · apply le_max_of_le_left
            simp only [AddSubgroupClass.coe_norm, le_refl]
          · exact norm_nonneg x
        · rw [max_mul_of_nonneg]
          · exact le_max_of_le_right <| ContinuousLinearMap.le_opNorm h𝒰.some ↑x
          · exact norm_nonneg x

theorem bddAbove_of_chain_of_partial_extension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type u_2} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
  {D : Submodule 𝕜 E} {F : Type u_3} [NormedAddCommGroup F] [IsUltrametricDist F]
  [NormedSpace 𝕜 F] [SphericallyCompleteSpace F] {S : ↥D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)}
  (h𝒰 : 𝒰.Nonempty) (ε : ↑𝒰 → ℝ)
  (hε1 : ∀ (T : ↑𝒰), 0 < ε T) (hε2 : ∀ (U V : ↑𝒰), ‖U.val - V.val‖ ≤ max (ε U) (ε V))
  (hε3 : ∀ (U : ↑𝒰) (x : ↥D), ‖S x - U.val ↑x‖ ≤ ε U * ‖x‖)
  (P : Set (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε))
  (hP : IsChain (fun x1 x2 ↦ x1 ≤ x2) P) (hhP : P.Nonempty) : BddAbove P := by
  let Mmax := iSup (fun p : P ↦ p.val.M)
  let fmax : Mmax → F := fun x => by
    haveI : Nonempty ↑P := Set.Nonempty.to_subtype hhP
    have : Directed (fun x1 x2 ↦ x1 ≤ x2) (fun p : P ↦ p.val.M) := by
      intro a b
      rcases hP.directed a b with ⟨c, hc1, hc2⟩
      use c
      constructor
      · cases hc1; assumption
      · cases hc2; assumption
    have := (Submodule.mem_iSup_of_directed (fun p : P ↦ p.val.M) this).1 x.2
    exact this.choose.val.T ⟨x.val,this.choose_spec⟩
  use { M := Mmax
        hDM := by
          unfold Mmax
          intro z hz
          rw [Submodule.mem_iSup]
          intro N hN
          exact (le_trans hhP.some.hDM <| hN ⟨hhP.some, hhP.some_mem⟩) hz
        T := by

          sorry
        hT := sorry
        hU := sorry, }
  sorry


set_option maxHeartbeats 0 in
lemma lemma_4_4
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [NormedSpace 𝕜 E]
{D : Submodule 𝕜 E}
{F : Type*} [NormedAddCommGroup F] [IsUltrametricDist F]
[NormedSpace 𝕜 F] [SphericallyCompleteSpace F]
{S : D →L[𝕜] F} {𝒰 : Set (E →L[𝕜] F)} (h𝒰 : 𝒰.Nonempty)
(ε : ↑𝒰 → ℝ)
(hε1 : ∀ T : ↑𝒰, 0 < ε T)
(hε2 : ∀ U V : ↑𝒰, ‖U.val - V.val‖ ≤ max (ε U) (ε V))
(hε3 : ∀ U : ↑𝒰, ∀ x : D, ‖S x - U.val x‖ ≤ ε U * ‖x‖)
:
∃ (T : E →L[𝕜] F), (∀ x : D, T x = S x) ∧ (∀ U : ↑𝒰, ‖T - U.val‖ ≤ ε U)
 := by
  have := @zorn_le_nonempty (PartialExtension 𝕜 E F S 𝒰 h𝒰 ε) _ (pene 𝕜 E F S 𝒰 h𝒰 ε hε3
    ) (by
    intro P hP hhP
    apply bddAbove_of_chain_of_partial_extension
    repeat assumption
  )
  rcases this with ⟨T, hT⟩
  have : T.M = ⊤ := by
    by_contra hc
    have : T.M < ⊤ := by exact Ne.lt_top' fun a ↦ hc (id (Eq.symm a))
    rcases Set.exists_of_ssubset this with ⟨a, ha⟩
    --have := lemma_4_4_codim_1 𝕜 E T.M a ha.2
    sorry
  let f := this ▸ T.T

  sorry


end SphericalCompleteness

#check Submodule.mem_iSup_of_directed
