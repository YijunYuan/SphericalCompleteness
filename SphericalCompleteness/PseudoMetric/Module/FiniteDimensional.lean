/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import SphericalCompleteness.PseudoMetric.Constructions
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# Finite-dimensional spaces with an arbitrary-valued pseudoultrametric

Over a division ring, spherical completeness on every scalar line suffices for spherical
completeness on any finitely generated subspace. Translation invariance and preservation of
distance comparisons by scalar multiplication replace a real-valued norm.
-/

@[expose] public section

namespace PseudoMetric

variable {K E Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]

/-- Spherical completeness on a scalar line can be checked on its parametrization by the
scalar field, even for the zero vector or a line of zero pseudodiameter. -/
theorem isSphericallyComplete_span_singleton_iff [Zero Γ] [Add Γ] [LE Γ]
    (d : PseudoMetric E Γ) (x : E) :
    (d.comap ((↑) : (K ∙ x) → E)).IsSphericallyComplete ↔
      (d.comap (fun a : K ↦ a • x)).IsSphericallyComplete := by
  let f (a : K) : K ∙ x := ⟨a • x, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
    exact ⟨a, Subtype.ext ha⟩
  exact ((d.comap ((↑) : (K ∙ x) → E)).isSphericallyComplete_comap_iff_of_surjective hf).symm

variable [Zero Γ] [Add Γ] [LinearOrder Γ]
variable (d : PseudoMetric E Γ) [d.IsAddInvariant] [d.IsUltra]

/-- The sum of two orthogonal spherically complete subspaces is spherically complete.
Addition preserves the supremum distance even if it has a kernel of zero pseudodiameter. -/
theorem isSphericallyComplete_sup_of_orthogonal (F G : Submodule K E)
    (h : ∀ x ∈ F, d.IsOrthogonalTo x G)
    [(d.comap ((↑) : F → E)).IsSphericallyComplete]
    [(d.comap ((↑) : G → E)).IsSphericallyComplete] :
    (d.comap ((↑) : (F ⊔ G : Submodule K E) → E)).IsSphericallyComplete := by
  let f (z : F × G) : (F ⊔ G : Submodule K E) :=
    ⟨z.1 + z.2, Submodule.add_mem_sup z.1.property z.2.property⟩
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp z.property
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  apply ((d.comap ((↑) : (F ⊔ G : Submodule K E) → E)).isSphericallyComplete_comap_iff_of_surjective
    hf).mp
  apply IsSphericallyComplete.of_prod_eq_sup (d.comap ((↑) : F → E)) (d.comap ((↑) : G → E))
  intro x y
  change d (↑x.1 + ↑x.2) (↑y.1 + ↑y.2) = max (d ↑x.1 ↑y.1) (d ↑x.2 ↑y.2)
  rw [← d.sub_zero_eq, add_sub_add_comm,
    (h _ (F.sub_mem x.1.property y.1.property)).add_eq_max (G.sub_mem x.2.property y.2.property),
    d.sub_zero_eq, d.sub_zero_eq]

/-- Spherical completeness on every scalar line passes to each finitely generated subspace. -/
theorem isSphericallyComplete_of_fg [d.IsSMulMono K]
    (hline : ∀ x : E, (d.comap ((↑) : (K ∙ x) → E)).IsSphericallyComplete)
    (F : Submodule K E) (hF : F.FG) : (d.comap ((↑) : F → E)).IsSphericallyComplete := by
  induction F, hF using Submodule.fg_sup_span_induction with
  | bot =>
    exact (congrArg (fun F : Submodule K E ↦ (d.comap ((↑) : F → E)).IsSphericallyComplete)
      (Submodule.span_zero_singleton (R := K) (M := E))).mp (hline 0)
  | sup F a _ ih =>
    obtain ⟨z, hz⟩ := exists_sub_isOrthogonalTo (d := d) F a
    let x := a - (z : E)
    have heq : F ⊔ (K ∙ a) = (K ∙ x) ⊔ F := by
      have hF : F ≤ F ⊔ (K ∙ a) := le_sup_left
      have hspan : K ∙ a ≤ F ⊔ (K ∙ a) := le_sup_right
      have ha : a ∈ (K ∙ x) ⊔ F :=
        sub_add_cancel a (z : E) ▸
          Submodule.add_mem_sup (Submodule.mem_span_singleton_self x) z.prop
      apply le_antisymm (sup_le le_sup_right ((Submodule.span_singleton_le_iff_mem ..).mpr ha))
      exact sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr
        (Submodule.sub_mem _ (hspan (Submodule.mem_span_singleton_self a))
          (hF z.prop))) le_sup_left
    rw [heq]
    let := hline x
    apply d.isSphericallyComplete_sup_of_orthogonal
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact hz.smul a

/-- A finite-dimensional space is spherically complete if its scalar lines are. -/
theorem isSphericallyComplete_of_finiteDimensional [Module.Finite K E] [d.IsSMulMono K]
    (hline : ∀ x : E, (d.comap ((↑) : (K ∙ x) → E)).IsSphericallyComplete) :
    d.IsSphericallyComplete :=
  (d.isSphericallyComplete_comap_iff_of_surjective
    (show Function.Surjective ((↑) : (⊤ : Submodule K E) → E) from fun x ↦ ⟨⟨x, trivial⟩, rfl⟩)).mp
    (d.isSphericallyComplete_of_fg hline ⊤ Module.Finite.fg_top)

end PseudoMetric
