import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.LinearAlgebra.Basis.VectorSpace

import SphericalCompleteness.Orthogonal

open Metric
open Filter

instance (𝕜 : Type u_1) [NontriviallyNormedField 𝕜]
{E : Type u_2} [inst_1 : NormedAddCommGroup E]
[NormedSpace 𝕜 E] [iud : IsUltrametricDist E]
{F : Submodule 𝕜 E} : IsUltrametricDist (E ⧸ F) where
  dist_triangle_max := by
    intro a b c
    have := quotient_norm_mk_eq F.toAddSubgroup
    repeat rw [dist_eq_norm]
    have ta := this (a - c).out
    have tb := this (c - b).out
    have tc := this (a - b).out
    simp only [QuotientAddGroup.mk'_apply, Quotient.out_eq, Submodule.coe_toAddSubgroup] at ta tb tc
    have ta' : ∀ a c : E⧸F, (fun x ↦ ‖(a - c).out + x‖) '' ↑F =
      (fun x ↦ ‖a.out -c.out + x‖) '' ↑F := by
      intro a c
      ext z
      constructor
      · intro hz
        simp only [QuotientAddGroup.mk'_apply, Submodule.coe_toAddSubgroup, Set.mem_image,
          SetLike.mem_coe] at *
        rcases hz with ⟨x, hx, hz⟩
        have : (a - c).out - (a.out - c.out) ∈ F := by
          refine (Submodule.Quotient.eq F).mp ?_
          simp only [Submodule.Quotient.mk_out, Submodule.Quotient.mk_sub]
        rw [← hz]
        use Quotient.out (a - c) - (Quotient.out a - Quotient.out c) + x
        constructor
        · exact (Submodule.add_mem_iff_right F this).mpr hx
        · rw [← add_assoc, (by grind only : a.out - c.out + ((a - c).out - (a.out - c.out)) + x =
            (a - c).out + x)]
      · intro hz
        simp at *
        rcases hz with ⟨x, hx, hz⟩
        have : (a.out - c.out) - (a - c).out ∈ F := by
          refine (Submodule.Quotient.eq F).mp ?_
          simp only [Submodule.Quotient.mk_out, Submodule.Quotient.mk_sub]
        rw [← hz]
        use (a.out - c.out) - (a - c).out + x
        constructor
        · exact (Submodule.add_mem_iff_right F this).mpr hx
        · rw [← add_assoc, (by grind only : (a - c).out + (a.out - c.out - (a - c).out) + x
            = a.out - c.out + x)]
    rw [ta'] at ta tb tc
    nth_rw 3 [← dist_eq_norm]
    rw [dist_comm, dist_eq_norm, ta, tb, tc]
    have t :
        sInf (((fun x : E ↦ ‖a.out -c.out + x‖) '' (↑F : Set E)) : Set ℝ) ≤
          sInf (((fun x : E × E ↦
            ‖(a.out -b.out + x.1) - (c.out - b.out + x.2)‖) '' (↑F ×ˢ ↑F)) : Set ℝ) := by
      apply le_csInf
      · simp
        exact Submodule.nonempty F
      · intro b hb
        simp only [Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists] at hb
        rcases hb with ⟨p, q, hp, hq, hh⟩
        apply csInf_le
        · use 0
          simp only [lowerBounds, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, norm_nonneg, implies_true]
        · simp only [Set.mem_image, SetLike.mem_coe]
          use p - q
          constructor
          · exact And.casesOn hp fun left right ↦ sub_mem left right
          · rw [(by grind only : a.out - c.out + (p - q) =
              a.out - b.out + p - (c.out - b.out + q))]
    have : sInf ((fun x ↦ ‖a.out - b.out + x.1 - (c.out - b.out + x.2)‖) '' ↑F ×ˢ ↑F) ≤
      sInf ((fun x ↦ max ‖a.out - b.out + x.1‖ ‖c.out - b.out + x.2‖) '' ↑F ×ˢ ↑F) := by
      rw [le_csInf_iff]
      · intro v hv
        simp only [Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists] at hv
        rcases hv with ⟨p, q, hp, hq⟩
        rw [← hq]
        have : sInf ((fun x ↦ ‖a.out - b.out + x.1 - (c.out - b.out + x.2)‖) '' ↑F ×ˢ ↑F) ≤
          ‖a.out - b.out + p - (c.out - b.out + q)‖ := by
          apply csInf_le (by
            use 0
            simp only [lowerBounds, Set.mem_image, Set.mem_prod,
              SetLike.mem_coe, Prod.exists, forall_exists_index, and_imp, Set.mem_setOf_eq]
            intro _ _ _ _ _ h
            rw [← h]
            exact (norm_nonneg _))
          simp only [Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
          use p, q
        refine le_trans this ?_
        have := iud.norm_add_le_max (a.out - b.out + p) (- (c.out - b.out + q))
        rwa [← sub_eq_add_neg, norm_neg] at this
      · use 0
        simp only [lowerBounds, Set.mem_image, Set.mem_prod, SetLike.mem_coe,
          Prod.exists, forall_exists_index, and_imp, Set.mem_setOf_eq]
        intro _ _ _ _ _ h
        rw [← h]
        simp only [le_sup_iff, norm_nonneg, or_self]
      · simpa only [Set.image_nonempty, Set.prod_nonempty_iff, and_self] using Submodule.nonempty F
    refine le_trans t <| le_trans this ?_
    apply le_of_forall_pos_le_add
    intro ε hε
    rw [← max_add_add_right]
    rcases @exists_lt_of_csInf_lt _ _ _
      (sInf ((fun x ↦ ‖a.out - b.out + x‖) '' ↑F) + ε) (by
        use ‖a.out - b.out‖, 0
        simp only [SetLike.mem_coe, zero_mem, add_zero, and_self]
        : (((fun x ↦ ‖a.out - b.out + x‖) '' ↑F)).Nonempty) (by linarith)
      with ⟨px0, hx0, hx0'⟩
    rcases @exists_lt_of_csInf_lt _ _ _
      (sInf ((fun x ↦ ‖c.out - b.out + x‖) '' ↑F) + ε) (by
        use ‖c.out - b.out‖, 0
        simp only [SetLike.mem_coe, zero_mem, add_zero, and_self]
        : (((fun x ↦ ‖c.out - b.out + x‖) '' ↑F)).Nonempty) (by linarith)
      with ⟨py0, hy0, hy0'⟩
    rcases hx0 with ⟨x0, hox0, hox0'⟩
    rcases hy0 with ⟨y0, hoy0, hoy0'⟩
    refine le_trans ?_ <| max_le_max (le_of_lt hx0') (le_of_lt hy0')
    apply csInf_le
    · use 0
      simp only [lowerBounds, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists,
        forall_exists_index, and_imp, Set.mem_setOf_eq]
      intro _ _ _ _ _ h
      rw [← h]
      simp only [le_sup_iff, norm_nonneg, or_self]
    · use (x0, y0)
      simp only [Set.mem_prod, hox0, hoy0, and_self, hox0', hoy0']


namespace SphericallyCompleteSpace

private lemma hhh (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Submodule 𝕜 E}
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

private noncomputable def hhhh (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [IsUltrametricDist E]
  {F : Submodule 𝕜 E} ⦃c : ℕ → E ⧸ F⦄
  ⦃r : ℕ → NNReal⦄ (hr : StrictAnti r) (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
  (t : ℕ) → {x : E // (↑x : E ⧸ F.toAddSubgroup) = c t} := fun n =>
  match n with
  | 0 => ⟨(c 0).out, by simp only [Quotient.out_eq]⟩
  | 1 => ⟨(c 1).out, by simp only [Quotient.out_eq]⟩
  | m + 2 => by
    have := hhh 𝕜 (c (m + 1)) (r (m + 1)) (c (m + 2)) (by
      specialize hanti (Nat.le_succ (m+1))
      refine hanti ?_
      simp only [Nat.succ_eq_add_one, mem_closedBall, dist_self,
        NNReal.zero_le_coe]) (hhhh 𝕜 hr hanti (m + 1)).val (by
      simp only [QuotientAddGroup.mk'_apply, (hhhh 𝕜 hr hanti (m + 1)).prop]
    ) (r m) (hr <| lt_add_one m)
    exact ⟨this.choose, this.choose_spec.1⟩

private lemma hhhh_prop (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [IsUltrametricDist E]
  {F : Submodule 𝕜 E} ⦃c : ℕ → E ⧸ F⦄
  ⦃r : ℕ → NNReal⦄ (hr : StrictAnti r) (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
  ∀ i' : ℕ, ‖(hhhh 𝕜 hr hanti (i'+ 2)).val - (hhhh 𝕜 hr hanti (i' + 1)).val‖ < ↑(r i') := by
  intro i'
  simp only [hhhh, QuotientAddGroup.mk'_apply]
  exact (hhh 𝕜 (c (i' + 1)) (r (i' + 1)) (c (i' + 2)) (by
      specialize hanti (Nat.le_succ (i'+1))
      refine hanti ?_
      simp only [Nat.succ_eq_add_one, mem_closedBall, dist_self,
        NNReal.zero_le_coe]) (hhhh 𝕜 hr hanti (i' + 1)).val (by
      simp only [QuotientAddGroup.mk'_apply, (hhhh 𝕜 hr hanti (i' + 1)).prop]
    ) (r i') (hr <| lt_add_one i')).choose_spec.2

theorem Quotient.sphericallyCompleteSpace
(𝕜 : Type*) [NontriviallyNormedField 𝕜]
{E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[iud : IsUltrametricDist E] [scsk : SphericallyCompleteSpace E]
{F : Submodule 𝕜 E} :
SphericallyCompleteSpace (E ⧸ F) := by
  rw [sphericallyComplete_iff']
  intro c r hr hanti
  let lc : ℕ → E := fun n => (hhhh 𝕜 hr hanti (n + 2)).val
  let lr : ℕ → NNReal := fun n => r (n + 1)
  have := @scsk.isSphericallyComplete (fun n => (hhhh 𝕜 hr hanti (n + 2)).val)
    (fun n => r (n + 1)) (by
    refine antitone_nat_of_succ_le fun n => ?_
    intro z hz
    simp only [mem_closedBall] at *
    have := iud.dist_triangle_max z ↑(hhhh 𝕜 hr hanti (n + 1 + 2)) ↑(hhhh 𝕜 hr hanti (n + 2))
    refine le_trans this <| sup_le_iff.2 ⟨le_trans hz <| le_of_lt <| hr <| lt_add_one _, ?_⟩
    simp only [dist_eq_norm, le_of_lt <| hhhh_prop 𝕜 hr hanti (n + 1)]
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
    rw [← (hhhh 𝕜 hr hanti (i + 2)).prop, dist_eq_norm,
    (by rfl : (↑w - ↑↑(hhhh 𝕜 hr hanti (i + 2)) : E ⧸ F.toAddSubgroup) =
      ((QuotientAddGroup.mk' F.toAddSubgroup)) (w - ↑(hhhh 𝕜 hr hanti (i + 2)))),
      quotient_norm_mk_eq F.toAddSubgroup]
    replace := csInf_le (by
      use 0
      simp only [lowerBounds, Submodule.coe_toAddSubgroup, Set.mem_image, SetLike.mem_coe,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, norm_nonneg,
        implies_true]
      ) (by
      use 0
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, zero_mem, add_zero, and_self]
      : ‖w - ↑(hhhh 𝕜 hr hanti (i + 2))‖ ∈
      ((fun x ↦ ‖w - ↑(hhhh 𝕜 hr hanti (i + 2)) + x‖) '' ↑F.toAddSubgroup))
    exact le_trans (le_trans this hw) <| le_of_lt <| hr <| lt_add_one i
  · refine (hanti <| Nat.le_add_right i 2) ?_
    simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]

end SphericallyCompleteSpace
