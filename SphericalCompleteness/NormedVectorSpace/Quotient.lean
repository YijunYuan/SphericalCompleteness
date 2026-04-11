import SphericalCompleteness.Basic

open Metric
open Filter


namespace SphericallyCompleteSpace

private lemma lift_to_nearby_element (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Submodule 𝕜 E}
  (un : E ⧸ F) (en : NNReal) (unp1 : E ⧸ F) (h : unp1 ∈ closedBall un en)
  (lun : E) (hlun : (QuotientAddGroup.mk' F.toAddSubgroup) lun = un)
  (ens1 : NNReal) (hens1 : ens1 > en)
   : ∃ lup1 : E, (QuotientAddGroup.mk' F.toAddSubgroup) lup1 = unp1 ∧ ‖lup1 - lun‖ < ens1 := by
  simp only [mem_closedBall] at h
  rw [← hlun, ← QuotientAddGroup.out_eq' unp1, QuotientAddGroup.mk'_apply, dist_eq_norm,
    (by rfl : ((↑(unp1.out) : E ⧸ F.toAddSubgroup) - (↑lun: E ⧸ F.toAddSubgroup) : E ⧸ F)
    = ↑(unp1.out - lun))] at h
  have := quotient_norm_mk_eq F.toAddSubgroup
  simp only [QuotientAddGroup.mk'_apply, Submodule.coe_toAddSubgroup] at this
  rw [this] at h
  rcases (csInf_lt_iff (by
    use 0
    simp only [lowerBounds, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, norm_nonneg, implies_true]
    ) (by simpa only [Set.image_nonempty] using Submodule.nonempty F
    )).1 <| lt_of_le_of_lt h hens1 with ⟨px, hxF, hx⟩
  simp only [Set.mem_image, SetLike.mem_coe] at hxF
  rcases hxF with ⟨x, hxF, hx_eq⟩
  simp only [← hx_eq, NNReal.val_eq_coe] at hx
  use unp1.out + x
  simp only [QuotientAddGroup.mk'_apply, Submodule.mem_toAddSubgroup, hxF,
    QuotientAddGroup.mk_add_of_mem, Quotient.out_eq, true_and]
  refine lt_of_eq_of_lt ?_ hx
  rw [(by grind only : (unp1.out + x) - lun = unp1.out - lun + x)]

private noncomputable def liftSequence (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [IsUltrametricDist E]
  {F : Submodule 𝕜 E} ⦃c : ℕ → E ⧸ F⦄
  ⦃r : ℕ → NNReal⦄ (hr : StrictAnti r) (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
  (t : ℕ) → {x : E // (↑x : E ⧸ F.toAddSubgroup) = c t} := fun n =>
  match n with
  | 0 => ⟨(c 0).out, by simp only [Quotient.out_eq]⟩
  | 1 => ⟨(c 1).out, by simp only [Quotient.out_eq]⟩
  | m + 2 => by
    have := lift_to_nearby_element 𝕜 (c (m + 1)) (r (m + 1)) (c (m + 2)) (by
      specialize hanti (Nat.le_succ (m+1))
      refine hanti ?_
      simp only [Nat.succ_eq_add_one, mem_closedBall, dist_self,
        NNReal.zero_le_coe]) (liftSequence 𝕜 hr hanti (m + 1)).val (by
      simp only [QuotientAddGroup.mk'_apply, (liftSequence 𝕜 hr hanti (m + 1)).prop]
    ) (r m) (hr <| lt_add_one m)
    exact ⟨this.choose, this.choose_spec.1⟩

private lemma liftSequence_prop (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [IsUltrametricDist E]
  {F : Submodule 𝕜 E} ⦃c : ℕ → E ⧸ F⦄
  ⦃r : ℕ → NNReal⦄ (hr : StrictAnti r) (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
  ∀ i' : ℕ, ‖(liftSequence 𝕜 hr hanti (i'+ 2)).val - (liftSequence 𝕜 hr hanti (i' + 1)).val‖ < ↑(r i') := by
  intro i'
  simp only [liftSequence, QuotientAddGroup.mk'_apply]
  exact (lift_to_nearby_element 𝕜 (c (i' + 1)) (r (i' + 1)) (c (i' + 2)) (by
      specialize hanti (Nat.le_succ (i'+1))
      refine hanti ?_
      simp only [Nat.succ_eq_add_one, mem_closedBall, dist_self,
        NNReal.zero_le_coe]) (liftSequence 𝕜 hr hanti (i' + 1)).val (by
      simp only [QuotientAddGroup.mk'_apply, (liftSequence 𝕜 hr hanti (i' + 1)).prop]
    ) (r i') (hr <| lt_add_one i')).choose_spec.2

/--
Establishes spherical completeness of the quotient `E ⧸ F`.

Assumptions:
- `𝕜` is a nontrivially normed field.
- `E` is a seminormed `𝕜`-normed space equipped with an ultrametric distance
  (`IsUltrametricDist E`).
- `E` is spherically complete (`SphericallyCompleteSpace E`).
- `F` is a `𝕜`-submodule of `E`.

Conclusion:
- The quotient space `E ⧸ F`, endowed with the induced seminorm/normed space structure,
  is spherically complete.
-/
theorem Quotient.sphericallyCompleteSpace
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
[iud : IsUltrametricDist E] [scsk : SphericallyCompleteSpace E]
{F : Submodule 𝕜 E} :
SphericallyCompleteSpace (E ⧸ F) := by
  rw [sphericallyCompleteSpace_iff_strictAnti_radius]
  intro c r hr hanti
  let lc : ℕ → E := fun n => (liftSequence 𝕜 hr hanti (n + 2)).val
  let lr : ℕ → NNReal := fun n => r (n + 1)
  have := @scsk.isSphericallyComplete (fun n => (liftSequence 𝕜 hr hanti (n + 2)).val)
    (fun n => r (n + 1)) (by
    refine antitone_nat_of_succ_le fun n => ?_
    intro z hz
    simp only [mem_closedBall] at *
    have := iud.dist_triangle_max z ↑(liftSequence 𝕜 hr hanti (n + 1 + 2)) ↑(liftSequence 𝕜 hr hanti (n + 2))
    refine le_trans this <| sup_le_iff.2 ⟨le_trans hz <| le_of_lt <| hr <| lt_add_one _, ?_⟩
    simp only [dist_eq_norm, le_of_lt <| liftSequence_prop 𝕜 hr hanti (n + 1)]
    )
  simp only [Set.nonempty_iInter] at this
  rcases this with ⟨w, hw⟩
  use (QuotientAddGroup.mk' F.toAddSubgroup) w
  simp only [QuotientAddGroup.mk'_apply, Set.mem_iInter, mem_closedBall]
  intro i
  have := (inferInstance : IsUltrametricDist (E ⧸ F)).dist_triangle_max
    (↑w : E ⧸ F.toAddSubgroup) (c (i + 2)) (c i)
  refine le_trans this <| sup_le_iff.2 ⟨?_, ?_⟩
  · specialize hw i
    simp only [mem_closedBall, dist_eq_norm] at hw
    rw [← (liftSequence 𝕜 hr hanti (i + 2)).prop, dist_eq_norm,
    (by rfl : (↑w - ↑↑(liftSequence 𝕜 hr hanti (i + 2)) : E ⧸ F.toAddSubgroup) =
      ((QuotientAddGroup.mk' F.toAddSubgroup)) (w - ↑(liftSequence 𝕜 hr hanti (i + 2)))),
      quotient_norm_mk_eq F.toAddSubgroup]
    replace := csInf_le (by
      use 0
      simp only [lowerBounds, Submodule.coe_toAddSubgroup, Set.mem_image, SetLike.mem_coe,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, norm_nonneg,
        implies_true]
      ) (by
      use 0
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, zero_mem, add_zero, and_self]
      : ‖w - ↑(liftSequence 𝕜 hr hanti (i + 2))‖ ∈
      ((fun x ↦ ‖w - ↑(liftSequence 𝕜 hr hanti (i + 2)) + x‖) '' ↑F.toAddSubgroup))
    exact le_trans (le_trans this hw) <| le_of_lt <| hr <| lt_add_one i
  · refine (hanti <| Nat.le_add_right i 2) ?_
    simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]

end SphericallyCompleteSpace
