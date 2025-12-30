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
    let Mmax := Submodule.span 𝕜 (⋃ (p : P), (p.val.M : Set E))
    #check @IsLinearMap.mk' 𝕜 Mmax F _ _ _ _ _
    use {M := Mmax
         hDM := by
          unfold Mmax
          intro z hz
          exact Submodule.mem_span_of_mem <| Set.mem_iUnion_of_mem
            (Classical.indefiniteDescription (Membership.mem P) hhP) <| hhP.some.hDM hz
         T := by
          #check @ContinuousLinearMap.mk 𝕜 𝕜 _ _ (RingHom.id 𝕜) ↥Mmax _ _ F _ _ _ _
          sorry
         hT := sorry
         hU := sorry, }
    sorry
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

#check StrongDual
