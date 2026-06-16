/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import SphericalCompleteness.Basic

/-!
# Spherical completeness of quotient spaces

This file proves that the quotient `E ⧸ F` of a spherically complete ultrametric normed
space `E` by a submodule `F` is again spherically complete.
-/

open Metric
open Filter


namespace SphericallyCompleteSpace

private lemma lift_to_nearby_element (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Submodule 𝕜 E}
  (un : E ⧸ F.toAddSubgroup) (en : NNReal) (unp1 : E ⧸ F.toAddSubgroup)
    (h : unp1 ∈ closedBall un en)
  (lun : E) (hlun : (QuotientAddGroup.mk' F.toAddSubgroup) lun = un)
  (ens1 : NNReal) (hens1 : ens1 > en)
   : ∃ lup1 : E, (QuotientAddGroup.mk' F.toAddSubgroup) lup1 = unp1 ∧ ‖lup1 - lun‖ < ens1 := by
  simp only [mem_closedBall] at h
  -- h : dist unp1 un ≤ en
  have h_norm : ‖(QuotientAddGroup.mk' F.toAddSubgroup) (unp1.out - lun)‖ ≤ en := by
    calc
      ‖(QuotientAddGroup.mk' F.toAddSubgroup) (unp1.out - lun)‖
          = ‖(QuotientAddGroup.mk' F.toAddSubgroup) unp1.out -
              (QuotientAddGroup.mk' F.toAddSubgroup) lun‖ := by
        simp [(QuotientAddGroup.mk' F.toAddSubgroup).map_sub]
      _ = ‖unp1 - (QuotientAddGroup.mk' F.toAddSubgroup) lun‖ := by
        have h1 : (QuotientAddGroup.mk' F.toAddSubgroup) (unp1.out) = unp1 := by
          calc
            (QuotientAddGroup.mk' F.toAddSubgroup) (unp1.out)
              = (unp1.out : E ⧸ F.toAddSubgroup) := by simp
            _ = unp1 := Quotient.out_eq' unp1
        rw [h1]
      _ = ‖unp1 - un‖ := by rw [hlun]
      _ = dist unp1 un := by rw [dist_eq_norm]
      _ ≤ en := h
  have this := quotient_norm_mk_eq F.toAddSubgroup
  rw [this (unp1.out - lun)] at h_norm
  rcases (csInf_lt_iff (by
    use 0
    simp only [lowerBounds, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, norm_nonneg, implies_true]
    ) (by
      simp only [Set.image_nonempty]
      exact ⟨0, F.zero_mem⟩
    )).1 <| lt_of_le_of_lt h_norm hens1 with ⟨px, hxF, hx⟩
  simp only [Set.mem_image, SetLike.mem_coe] at hxF
  rcases hxF with ⟨x, hxF, hx_eq⟩
  simp only [← hx_eq, NNReal.val_eq_coe] at hx
  use unp1.out + x
  simp only [QuotientAddGroup.mk'_apply, hxF,
    QuotientAddGroup.mk_add_of_mem, Quotient.out_eq', true_and]
  refine lt_of_eq_of_lt ?_ hx
  rw [(by grind only : (unp1.out + x) - lun = unp1.out - lun + x)]

private noncomputable def liftSequence (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [IsUltrametricDist E]
  {F : Submodule 𝕜 E} ⦃c : ℕ → E ⧸ F⦄
  ⦃r : ℕ → NNReal⦄ (hr : StrictAnti r) (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
  (t : ℕ) → {x : E // (↑x : E ⧸ F.toAddSubgroup) = c t} := fun n =>
  match n with
  | 0 => ⟨(c 0).out, Quotient.out_eq' (c 0)⟩
  | 1 => ⟨(c 1).out, Quotient.out_eq' (c 1)⟩
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
  ∀ i' : ℕ, ‖(liftSequence 𝕜 hr hanti (i'+ 2)).val -
             (liftSequence 𝕜 hr hanti (i' + 1)).val‖ < ↑(r i') := by
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
    have := iud.dist_triangle_max z ↑(liftSequence 𝕜 hr hanti (n + 1 + 2))
      ↑(liftSequence 𝕜 hr hanti (n + 2))
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
    -- hw : ‖w - (liftSequence ... (i+2)).val‖ ≤ r (i+1)
    let lc := liftSequence 𝕜 hr hanti (i + 2)
    have htemp : ‖(QuotientAddGroup.mk' F.toAddSubgroup) (w - lc.val)‖ ≤ ↑(r i) := by
      rw [quotient_norm_mk_eq F.toAddSubgroup (w - lc.val)]
      have hbdd : BddBelow ((fun (x : E) => ‖(w - lc.val) + x‖) '' (F.toAddSubgroup : Set E)) := by
        refine ⟨0, ?_⟩
        intro y hy
        simp only [Set.mem_image, SetLike.mem_coe] at hy
        rcases hy with ⟨x, hx, rfl⟩
        exact norm_nonneg _
      have hmem : ‖w - lc.val‖ ∈
        ((fun (x : E) => ‖(w - lc.val) + x‖) '' (F.toAddSubgroup : Set E)) := by
        refine ⟨0, AddSubgroup.zero_mem _, ?_⟩
        simp
      refine le_trans (csInf_le hbdd hmem) ?_
      exact le_trans hw (le_of_lt (hr (lt_add_one i)))
    have hgoal : dist ((↑w : E ⧸ F.toAddSubgroup)) (c (i + 2)) ≤ ↑(r i) := by
      calc
        dist ((↑w : E ⧸ F.toAddSubgroup)) (c (i + 2))
            = dist ((QuotientAddGroup.mk' F.toAddSubgroup) w)
              ((QuotientAddGroup.mk' F.toAddSubgroup) lc.val) := by
          simp [lc.prop]
        _ = ‖(QuotientAddGroup.mk' F.toAddSubgroup) (w - lc.val)‖ := by
          rw [dist_eq_norm, (QuotientAddGroup.mk' F.toAddSubgroup).map_sub]
        _ ≤ ↑(r i) := htemp
    exact hgoal
  · refine (hanti <| Nat.le_add_right i 2) ?_
    simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]

end SphericallyCompleteSpace
