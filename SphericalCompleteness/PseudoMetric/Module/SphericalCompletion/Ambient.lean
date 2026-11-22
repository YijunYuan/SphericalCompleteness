/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# An ambient module for constructing immediate extensions

A free summand indexed by the power set of `A` supplies a fresh coordinate for every
submodule whose carrier embeds into `A`. Adjoining a vector outside a submodule adds
one independent scalar coordinate.
-/

@[expose] public section

namespace Submodule

variable {K E A : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

/-- A submodule that injects into `A` misses some standard basis vector of a free summand
indexed by the power set of `A`. -/
theorem exists_single_notMem_of_injective
    (M : Submodule K (E × (Set A →₀ K))) {f : M → A} (hf : Function.Injective f) :
    ∃ i : Set A, (0, Finsupp.single i (1 : K)) ∉ M := by
  classical
  by_contra! h
  let g (i : Set A) : M := ⟨(0, Finsupp.single i 1), h i⟩
  apply Function.cantor_injective (f ∘ g) (hf.comp ?_)
  intro i j hij
  exact Finsupp.single_left_injective one_ne_zero (congrArg (fun m : M ↦ m.val.2) hij)

/-- Adjoining an independent vector identifies the enlarged submodule with the old one
and one scalar coordinate. -/
noncomputable def prodEquivSupSpanSingleton (M : Submodule K E) {z : E} (hz : z ∉ M) :
    (M × K) ≃ₗ[K] (M ⊔ K ∙ z : Submodule K E) := by
  let L := M.subtype.coprod (LinearMap.toSpanSingleton K E z)
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨m, c⟩ h
    change (m : E) + c • z = 0 at h
    rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul, add_zero] at h
      simp [Submodule.coe_eq_zero.mp h]
    · have hcz : c • z ∈ M := neg_eq_of_add_eq_zero_right h ▸ M.neg_mem m.prop
      exact (hz (by simpa [hc] using M.smul_mem c⁻¹ hcz)).elim
  exact (LinearEquiv.ofInjective L hL).trans (LinearEquiv.ofEq _ _ (by
    dsimp only [L]
    rw [LinearMap.range_coprod, range_subtype, LinearMap.span_singleton_eq_range]))

@[simp] theorem coe_prodEquivSupSpanSingleton_apply (M : Submodule K E) {z : E} (hz : z ∉ M)
    (m : M) (c : K) : (M.prodEquivSupSpanSingleton hz (m, c) : E) = m + c • z := rfl

end Submodule
