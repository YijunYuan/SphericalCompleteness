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
{F : Submodule 𝕜 E} [inst_4 : IsClosed (F : Set E)] : IsUltrametricDist (E ⧸ F) where
  dist_triangle_max := by
    intro a b c
    have := quotient_norm_mk_eq F.toAddSubgroup
    repeat rw [dist_eq_norm]
    have ta := this (a - c).out
    have tb := this (b - c).out
    have tc := this (a - b).out
    simp at ta tb tc
    have ta' : ∀ a c : E⧸F, (fun x ↦ ‖Quotient.out (a - c) + x‖) '' ↑F =
      (fun x ↦ ‖Quotient.out a - Quotient.out c + x‖) '' ↑F := by
      intro a c
      ext z
      constructor
      · intro hz
        simp at *
        rcases hz with ⟨x, hx, hz⟩
        have : (a - c).out - (a.out - c.out) ∈ F := by
          refine (Submodule.Quotient.eq F).mp ?_
          simp only [Submodule.Quotient.mk_out, Submodule.Quotient.mk_sub]
        rw [← hz]
        use Quotient.out (a - c) - (Quotient.out a - Quotient.out c) + x
        constructor
        · exact (Submodule.add_mem_iff_right F this).mpr hx
        · rw [← add_assoc]
          aesop
      · intro hz
        simp at *
        rcases hz with ⟨x, hx, hz⟩
        have : (a.out - c.out) - (a - c).out ∈ F := by
          refine (Submodule.Quotient.eq F).mp ?_
          simp only [Submodule.Quotient.mk_out, Submodule.Quotient.mk_sub]
        rw [← hz]
        use (a.out - c.out) - Quotient.out (a - c) + x
        constructor
        · exact (Submodule.add_mem_iff_right F this).mpr hx
        · rw [← add_assoc]
          aesop
    rw [ta'] at ta tb tc
    rw [ta, tb, tc]
    have t :
        sInf (((fun x : E ↦ ‖Quotient.out a - Quotient.out c + x‖) '' (↑F : Set E)) : Set ℝ) ≤
          sInf
            (((fun x : E × E ↦ ‖(a.out -b.out + x.1) - (c.out - b.out + x.2)‖) '' (↑F ×ˢ ↑F)) : Set ℝ) := by
      apply le_csInf
      · simp
        exact Submodule.nonempty F
      · intro b hb
        simp at hb
        rcases hb with ⟨p, q, hp, hq, hh⟩
        apply csInf_le
        · use 0
          unfold lowerBounds
          simp only [Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, norm_nonneg, implies_true]
        · simp
          use p - q
          constructor
          · exact And.casesOn hp fun left right ↦ sub_mem left right
          · have : Quotient.out a - Quotient.out c + (p - q) = Quotient.out a - Quotient.out b + p - (Quotient.out c - Quotient.out b + q) := by grind
            rw [this]
    refine le_trans t ?_
    have : sInf ((fun x ↦ ‖Quotient.out a - Quotient.out b + x.1 - (Quotient.out c - Quotient.out b + x.2)‖) '' ↑F ×ˢ ↑F) ≤
      sInf ((fun x ↦ max ‖Quotient.out a - Quotient.out b + x.1‖ ‖Quotient.out c - Quotient.out b + x.2‖) '' ↑F ×ˢ ↑F) := by
      rw [le_csInf_iff]
      · intro v hv
        simp at hv
        rcases hv with ⟨p, q, hp, hq⟩
        rw [← hq]
        have : sInf ((fun x ↦ ‖Quotient.out a - Quotient.out b + x.1 - (Quotient.out c - Quotient.out b + x.2)‖) '' ↑F ×ˢ ↑F) ≤
          ‖Quotient.out a - Quotient.out b + p - (Quotient.out c - Quotient.out b + q)‖ := by
          apply csInf_le (by use 0; unfold lowerBounds; aesop)
          simp
          use p, q
        refine le_trans this ?_
        have := iud.norm_add_le_max (a.out - b.out + p) (- (c.out - b.out + q))
        rwa [← sub_eq_add_neg, norm_neg] at this
      · use 0
        unfold lowerBounds
        aesop
        --sorry
      · simp
        exact Submodule.nonempty F
    refine le_trans this ?_
    apply le_of_forall_pos_le_add
    intro ε hε
-- https://gemini.google.com/share/fbb39311b2b7
    sorry

namespace SphericallyCompleteSpace

theorem Quotient.sphericallyCompleteSpace
(𝕜 : Type*) [NontriviallyNormedField 𝕜] [scsk : SphericallyCompleteSpace 𝕜]
{E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [IsUltrametricDist E]
{F : Submodule 𝕜 E} [IsClosed (F : Set E)] :
SphericallyCompleteSpace (E ⧸ F) := by
  rw [sphericallyComplete_iff']

  sorry

end SphericallyCompleteSpace
