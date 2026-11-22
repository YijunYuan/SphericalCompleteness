/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Span.Basic

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
  have h : d₁ - d₂ = l₂ - l₁ := by
    rw [sub_eq_sub_iff_add_eq_add]
    simpa [add_comm] using heq
  have hd : d₁ - d₂ = 0 := (disjoint_def.mp (disjoint_span_singleton_of_notMem ha)) _
    (D.sub_mem hd₁ hd₂) (h.symm ▸ (span 𝕜 {a}).sub_mem hl₂ hl₁)
  exact ⟨sub_eq_zero.mp hd, by simpa [sub_eq_zero.mp hd] using heq⟩

end Submodule
