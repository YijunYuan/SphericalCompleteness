import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace

open Metric
open NNReal

theorem diam_le_radius_of_ultrametric {α : Type*}
[PseudoMetricSpace α] [hiud : IsUltrametricDist α]
(z : α) (r : ℝ≥0) :
diam (closedBall z r) ≤ r := by
  apply diam_le_of_forall_dist_le
  · exact r.prop
  · intro x hx y hy
    simp only [closedBall, Set.mem_setOf_eq] at hx hy
    rw [dist_comm] at hy
    have := hiud.dist_triangle_max x z y
    grind only [= max_def]

theorem closedBall_subset_closedBall_of_le_radius_of_nonempty_intersection_of_ultrametric
{α : Type*} [PseudoMetricSpace α] [hiud : IsUltrametricDist α]
{z1 z2 : α} {r1 r2 : ℝ≥0}
(hle : r1 ≤ r2)
(hne : (closedBall z1 r1 ∩ closedBall z2 r2).Nonempty) :
closedBall z1 r1 ⊆ closedBall z2 r2 := by
  intro x hx
  simp only [closedBall, Set.mem_setOf_eq] at hx
  rcases hne with ⟨y, hy1, hy2⟩
  simp only [mem_closedBall] at *
  refine le_trans (hiud.dist_triangle_max x y z2) <| sup_le_iff.2 ⟨?_, hy2⟩
  refine le_trans (hiud.dist_triangle_max x z1 y) <| sup_le_iff.2 ⟨le_trans hx hle, ?_⟩
  simpa only [dist_comm] using le_trans hy1 hle

instance (𝕜 : Type u_1) [NontriviallyNormedField 𝕜]
{E : Type u_2} [inst_1 : SeminormedAddCommGroup E]
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

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
{F : Type*} [SeminormedAddCommGroup F] [iud : IsUltrametricDist F]
[NormedSpace 𝕜 F] :
IsUltrametricDist (E →L[𝕜] F) where
  dist_triangle_max := by
    intro f g h
    repeat rw [dist_eq_norm]
    rw [ContinuousLinearMap.opNorm_le_iff]
    · intro x
      have : ‖(f - h) x‖ = ‖(f - g) x + (g - h) x‖ := by
        simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, sub_add_sub_cancel]
      rw [this, max_mul_of_nonneg _ _ (norm_nonneg _)]
      refine le_trans (iud.norm_add_le_max _ _) <| max_le_max ?_ ?_
      · exact ContinuousLinearMap.le_opNorm (f - g) x
      · exact ContinuousLinearMap.le_opNorm (g - h) x
    · simp only [le_sup_iff, norm_nonneg, or_self]

instance {ι : Type*} {E : ι → Type*} [Nonempty ι] [∀ i, NormedAddCommGroup (E i)]
[iiud : ∀ i, IsUltrametricDist (E i)] :
IsUltrametricDist (lp E ⊤) where
dist_triangle_max a b c := by
  repeat rw [dist_eq_norm, lp.norm_eq_ciSup]
  apply ciSup_le
  intro j
  have : ‖(↑(a - c): (i : ι) → E i) j‖ = ‖a j - c j‖ := rfl
  rw [this, ← dist_eq_norm]
  refine le_trans ((iiud j).dist_triangle_max (a j) (b j) (c j)) ?_
  repeat rw [dist_eq_norm]
  apply max_le_max
  · have : ‖(↑a: (i : ι) → E i) j - (↑b: (i : ι) → E i) j‖ = ‖(↑(a - b) : (i : ι) → E i) j‖ := rfl
    rw [this]
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero
  · have : ‖(↑b: (i : ι) → E i) j - (↑c: (i : ι) → E i) j‖ = ‖(↑(b - c) : (i : ι) → E i) j‖ := rfl
    rw [this]
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero
