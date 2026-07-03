/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.Basic

/-!
# Spherical completeness of quotient spaces

This file proves that the quotient `E ⧸ F` of a spherically complete ultrametric normed
space `E` by a submodule `F` is again spherically complete.
-/

@[expose] public section

open Metric
open Filter

namespace SphericallyCompleteSpace

private lemma lift_to_nearby_element (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Submodule 𝕜 E}
    (un : E ⧸ F.toAddSubgroup) (en : NNReal) (unp1 : E ⧸ F.toAddSubgroup)
    (h : unp1 ∈ closedBall un en)
    (lun : E) (hlun : (QuotientAddGroup.mk' F.toAddSubgroup) lun = un)
    (ens1 : NNReal) (hens1 : ens1 > en) :
    ∃ lup1 : E, (QuotientAddGroup.mk' F.toAddSubgroup) lup1 = unp1 ∧ ‖lup1 - lun‖ < ens1 := by
  subst hlun
  rw [mem_closedBall, dist_eq_norm] at h
  have hε : (0 : ℝ) < ens1 - ‖unp1 - (QuotientAddGroup.mk' F.toAddSubgroup) lun‖ := by
    have : ‖unp1 - (QuotientAddGroup.mk' F.toAddSubgroup) lun‖ < (ens1 : ℝ) :=
      lt_of_le_of_lt h (by exact_mod_cast hens1)
    linarith
  obtain ⟨m, hm_eq, hm_norm⟩ :=
    Submodule.Quotient.norm_mk_lt (S := F) (unp1 - (QuotientAddGroup.mk' F.toAddSubgroup) lun) hε
  refine ⟨lun + m, ?_, ?_⟩
  · rw [map_add, show (QuotientAddGroup.mk' F.toAddSubgroup) m = Submodule.Quotient.mk m
      from rfl, hm_eq]
    abel
  · rw [add_sub_cancel_left]
    have hms : ‖m‖ < (ens1 : ℝ) := by
      rw [show (ens1 : ℝ) = ‖unp1 - (QuotientAddGroup.mk' F.toAddSubgroup) lun‖ +
        (↑ens1 - ‖unp1 - (QuotientAddGroup.mk' F.toAddSubgroup) lun‖) from by ring]
      exact hm_norm
    exact_mod_cast hms

private noncomputable def liftSequence (𝕜 : Type*) [inst : NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [IsUltrametricDist E]
    {F : Submodule 𝕜 E} ⦃c : ℕ → E ⧸ F⦄
    ⦃r : ℕ → NNReal⦄ (hr : StrictAnti r) (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
    (t : ℕ) → {x : E // (↑x : E ⧸ F.toAddSubgroup) = c t} := fun n ↦
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

private lemma liftSequence_prop (𝕜 : Type*) [inst : NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E]
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
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [iud : IsUltrametricDist E] [scsk : SphericallyCompleteSpace E]
    {F : Submodule 𝕜 E} :
    SphericallyCompleteSpace (E ⧸ F) := by
  rw [sphericallyCompleteSpace_iff_strictAnti_radius]
  intro c r hr hanti
  have := @scsk.isSphericallyComplete (fun n ↦ (liftSequence 𝕜 hr hanti (n + 2)).val)
    (fun n ↦ r (n + 1)) (by
    refine antitone_nat_of_succ_le fun n ↦ ?_
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
    have htemp : ‖(QuotientAddGroup.mk' F.toAddSubgroup) (w - lc.val)‖ ≤ ↑(r i) :=
      (Submodule.Quotient.norm_mk_le (S := F) (w - lc.val)).trans <|
        hw.trans (le_of_lt (hr (lt_add_one i)))
    calc
      dist ((↑w : E ⧸ F.toAddSubgroup)) (c (i + 2))
          = dist ((QuotientAddGroup.mk' F.toAddSubgroup) w)
            ((QuotientAddGroup.mk' F.toAddSubgroup) lc.val) := by
        simp [lc.prop]
      _ = ‖(QuotientAddGroup.mk' F.toAddSubgroup) (w - lc.val)‖ := by
        rw [dist_eq_norm, (QuotientAddGroup.mk' F.toAddSubgroup).map_sub]
      _ ≤ ↑(r i) := htemp
  · refine (hanti <| Nat.le_add_right i 2) ?_
    simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]

end SphericallyCompleteSpace
