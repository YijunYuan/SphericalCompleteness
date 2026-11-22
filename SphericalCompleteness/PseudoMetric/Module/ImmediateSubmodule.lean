/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.LinearAlgebra.Span.Basic
public import SphericalCompleteness.PseudoMetric.Immediate
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# Maximal immediate submodules

Inside a spherically complete ambient module, each submodule admits an immediate,
spherically complete enlargement. The ambient pseudometric may be nonseparated.
-/

@[expose] public section

namespace PseudoMetric

variable {K E Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
variable [Zero Γ] [Add Γ] [LinearOrder Γ] (d : PseudoMetric E Γ)

/-- An intermediate submodule is immediate over `D` if each new vector has an approximation
in `D` strictly better than zero. Translation gives the analogous improvement over every
point of `D`. -/
def IsImmediateSubmodule (D M : Submodule K E) : Prop :=
  D ≤ M ∧ ∀ x ∈ M, x ∉ D → ∃ y ∈ D, d x y < d x 0

theorem isImmediateSubmodule_iff [d.IsAddInvariant] {D M : Submodule K E} :
    d.IsImmediateSubmodule D M ↔
      ∃ h : D ≤ M, (d.comap ((↑) : M → E)).IsImmediate (Submodule.inclusion h) := by
  constructor
  · rintro ⟨hle, h⟩
    refine ⟨hle, fun x hx ↦ ⟨inferInstance, fun z ↦ ?_⟩⟩
    have hnot : (x : E) - z ∉ D := fun hsub ↦
      hx ⟨⟨x, (sub_add_cancel (x : E) z) ▸ D.add_mem hsub z.prop⟩, rfl⟩
    obtain ⟨y, hy, hlt⟩ := h _ (M.sub_mem x.prop (hle z.prop)) hnot
    refine ⟨⟨y + z, D.add_mem hy z.prop⟩, ?_⟩
    change d x (y + z) < d x z
    simpa only [← d.sub_right_eq (x : E) (y + z) z, add_sub_cancel_right, d.sub_zero_eq] using hlt
  · rintro ⟨hle, h⟩
    refine ⟨hle, fun x hx hxD ↦ ?_⟩
    have hout : (⟨x, hx⟩ : M) ∉ Set.range (Submodule.inclusion hle) := by
      rintro ⟨z, hz⟩
      have heq : (z : E) = x := congrArg Subtype.val hz
      exact hxD (heq ▸ z.prop)
    obtain ⟨z, hz⟩ := (h _ hout).2 0
    exact ⟨z, z.prop, hz⟩

/-- The strict approximation test on the range agrees with immediacy of the linear map. -/
theorem isImmediate_iff_range [d.IsAddInvariant] {A : Type*} [AddCommGroup A] [Module K A]
    (i : A →ₗ[K] E) : d.IsImmediate i ↔ d.IsImmediateSubmodule i.range ⊤ := by
  constructor
  · refine fun h ↦ ⟨le_top, fun x _ hx ↦ ?_⟩
    obtain ⟨z, hz⟩ := (h x hx).2 0
    exact ⟨i z, i.mem_range_self z, by simpa only [map_zero] using hz⟩
  · intro h x hx
    refine ⟨inferInstance, fun z ↦ ?_⟩
    have hn : x - i z ∉ i.range := fun hs ↦
      hx (show x ∈ i.range from (sub_add_cancel x (i z)) ▸ i.range.add_mem hs (i.mem_range_self z))
    obtain ⟨_, ⟨y, rfl⟩, hlt⟩ := h.2 _ trivial hn
    refine ⟨y + z, ?_⟩
    rwa [map_add, ← d.sub_right_eq x (i y + i z) (i z), add_sub_cancel_right,
      ← d.sub_zero_eq x (i z)]

/-- Unions of chains of immediate intermediate submodules are immediate. -/
theorem exists_maximal_isImmediateSubmodule (D : Submodule K E) :
    ∃ M, Maximal (d.IsImmediateSubmodule D) M := by
  let A := {M | d.IsImmediateSubmodule D M}
  have hD : D ∈ A := ⟨le_rfl, fun _ hx hn ↦ (hn hx).elim⟩
  obtain ⟨M, _, hM⟩ := zorn_le_nonempty₀ A (by
    intro C hC hchain N hN
    have : Nonempty C := ⟨⟨N, hN⟩⟩
    let U := ⨆ P : C, P.val
    have hle (P : C) : P.val ≤ U := le_iSup (fun P : C ↦ P.val) P
    refine ⟨U, ⟨(hC hN).1.trans (hle ⟨N, hN⟩), fun x hx hnot ↦ ?_⟩, fun P hP ↦ hle ⟨P, hP⟩⟩
    obtain ⟨P, hxP⟩ := (Submodule.mem_iSup_of_directed _ hchain.directed).mp hx
    exact (hC P.prop).2 x hxP hnot) D hD
  exact ⟨M, hM⟩

variable [d.IsAddInvariant] [d.IsSMulMono K]

/-- A maximal immediate intermediate submodule of a spherically complete ambient space is
spherically complete. Adjoining a point with no nearest point would preserve immediacy. -/
theorem isSphericallyComplete_of_maximal_isImmediateSubmodule [d.IsUltra] [d.IsSphericallyComplete]
    {D M : Submodule K E} (h : Maximal (d.IsImmediateSubmodule D) M) :
    (d.comap ((↑) : M → E)).IsSphericallyComplete := by
  apply (d.isSphericallyComplete_subtype_iff_exists_bestApprox (M : Set E) M.nonempty).mpr
  intro a
  by_contra! hbad
  have ha : a ∉ M := fun ha ↦ by
    obtain ⟨z, hz⟩ := hbad ⟨a, ha⟩
    exact (d.refl a ▸ hz).not_ge (d.nonneg_of_ultra a z)
  obtain ⟨hle, himm⟩ := d.isImmediateSubmodule_iff.mp h.prop
  have hnew : d.IsImmediateSubmodule D (M ⊔ (K ∙ a)) := by
    refine ⟨hle.trans le_sup_left, fun x hx hout ↦ ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    by_cases hc : c = 0
    · apply h.prop.2 _ _ hout
      simpa only [hc, zero_smul, add_zero] using hu
    let t : M := ⟨c⁻¹ • (-u), M.smul_mem _ (M.neg_mem hu)⟩
    obtain ⟨z, hz⟩ := hbad t
    let y : M := ⟨c • (z : E) + u, M.add_mem (M.smul_mem _ z.prop) hu⟩
    have hlt : d (u + c • a) y < d (u + c • a) (0 : E) := by
      have ht : c • (t : E) + u = 0 := by simp [t, smul_inv_smul₀ hc]
      rw [add_comm u, ← ht]
      change d (c • a + u) (c • (z : E) + u) < d (c • a + u) (c • (t : E) + u)
      rw [IsAddInvariant.add_right, IsAddInvariant.add_right]
      exact IsSMulMono.smul_dist_lt d hc hz
    obtain ⟨w, hw⟩ := himm.exists_lt_of_lt d (x := (0 : D)) (y := y) hlt
    exact ⟨w, w.prop, hw⟩
  exact ha ((h.le_of_ge hnew le_sup_left) <|
    (show K ∙ a ≤ M ⊔ (K ∙ a) from le_sup_right) (Submodule.mem_span_singleton_self a))

end PseudoMetric
