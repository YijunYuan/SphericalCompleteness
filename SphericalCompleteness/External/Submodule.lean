/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Auxiliary submodule lemmas

Supporting lemmas on submodules.
-/

@[expose] public section

namespace Submodule

/--
If `a ∉ D`, then the sum decomposition of an element of the form `d + l`
with `d ∈ D` and `l ∈ span 𝕜 {a}` is unique.

More precisely, for any `d₁ d₂ ∈ D` and any `l₁ l₂ ∈ Submodule.span 𝕜 {a}`,
the equality `d₁ + l₁ = d₂ + l₂` forces `d₁ = d₂` and `l₁ = l₂`.

This expresses that, under the non-membership hypothesis `a ∉ D`, the two
submodules `D` and `span 𝕜 {a}` intersect trivially and the ambient module
behaves like a direct sum along these components (at least with respect to
equality of such decompositions).
-/
lemma eq_and_eq_of_add_eq_add_of_notMem {𝕜 : Type*} [Field 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {D : Submodule 𝕜 V} {a : V} (ha : a ∉ D) :
    ∀ d₁ ∈ D, ∀ l₁ ∈ Submodule.span 𝕜 {a}, ∀ d₂ ∈ D, ∀ l₂ ∈ Submodule.span 𝕜 {a},
      d₁ + l₁ = d₂ + l₂ → d₁ = d₂ ∧ l₁ = l₂ := by
  intro d₁ hd₁ l₁ hl₁ d₂ hd₂ l₂ hl₂ heq
  rw [add_comm, ← sub_eq_sub_iff_add_eq_add] at heq
  have : d₂ - d₁ ∈ Submodule.span 𝕜 {a} := by
    rw [← heq]
    exact (Submodule.sub_mem_iff_left (Submodule.span 𝕜 {a}) hl₂).mpr hl₁
  rcases Submodule.mem_span_singleton.1 this with ⟨r, hr⟩
  if hr' : r = 0 then
    simp only [hr', zero_smul] at hr
    rw [← hr] at heq
    exact ⟨(sub_eq_zero.1 hr.symm).symm, sub_eq_zero.1 heq⟩
  else
  replace hr : a = r⁻¹ • (d₂ - d₁) := by
    rw [← hr]
    exact (eq_inv_smul_iff₀ hr').mpr rfl
  simp only [hr] at ha
  exact absurd (Submodule.smul_mem D r⁻¹ <| (Submodule.sub_mem_iff_left D hd₁).mpr hd₂) ha

/--
If `a : 𝕜` is nonzero, then scalar multiplication by `a` leaves any submodule `M` invariant:
`a • M = M`.

This is the submodule-level expression of the fact that `a` acts as an invertible linear map
(with inverse given by multiplication by `a⁻¹`), so the image of `M` under the action equals `M`
itself.

Parameters:
- `ha : a ≠ 0` ensures `a` is a unit in the field `𝕜`.
- `M : Submodule 𝕜 E` is the submodule being scaled.

Result:
- `a • M = M`.
-/
theorem smul_coe_eq_self {𝕜 : Type*} [Field 𝕜]
    {E : Type*} [AddCommMonoid E] [Module 𝕜 E] {a : 𝕜} (ha : a ≠ 0) (M : Submodule 𝕜 E) :
    (@HSMul.hSMul 𝕜 (Set E) (Set E) (@instHSMul 𝕜 (Set E) Set.smulSet) a ↑M)
      = ↑M := by
  ext z
  refine ⟨?_, fun h ↦ ⟨a⁻¹ • z, SMulMemClass.smul_mem a⁻¹ h, smul_inv_smul₀ ha z⟩⟩
  rintro ⟨c, hc, rfl⟩
  exact SMulMemClass.smul_mem a hc

end Submodule
