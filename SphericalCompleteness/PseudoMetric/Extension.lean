/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Order.Preorder.PairwiseChain
public import Mathlib.Order.Zorn
public import SphericalCompleteness.PseudoMetric

/-!
# Nonexpansive extensions into spherically complete pseudoultrametric spaces

A family of closed balls is compatible when the distance between any two centers is bounded
by the larger radius. In a nonempty spherically complete pseudoultrametric space, every such
family has a common point. This gives the single-point extension step for nonexpansive maps.
Consequently, a nonexpansive map into such a space extends from any subset of its domain,
and any nonempty spherically complete subspace admits a nonexpansive retraction.
-/

@[expose] public section

open Set

namespace PseudoMetric

variable {X Y R S : Type*} [Zero R] [Add R] [LinearOrder R]

/-- Compatible distance bounds in a spherically complete pseudoultrametric space have a
simultaneous solution. The nonempty target also allows an empty family of constraints. -/
theorem IsSphericallyComplete.exists_dist_le (e : PseudoMetric Y R) [e.IsUltra]
    [e.IsSphericallyComplete] [Nonempty Y] {ι : Type*} (c : ι → Y) (r : ι → R)
    (h : ∀ i j, e (c i) (c j) ≤ max (r i) (r j)) : ∃ y, ∀ i, e y (c i) ≤ r i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨Classical.arbitrary Y, fun i ↦ isEmptyElim i⟩
  | inr _ =>
    have hr (i : ι) : 0 ≤ r i := by simpa using h i i
    obtain ⟨y, hy⟩ := IsSphericallyComplete.nonempty_iInter_of_pairwise e c r (fun i j ↦ by
      rcases le_total (r i) (r j) with hi | hj
      · exact ⟨c i, e.mem_closedBall_self.mpr (hr i), (h i j).trans_eq (max_eq_right hi)⟩
      · exact ⟨c j, (h j i).trans_eq (max_eq_right hj), e.mem_closedBall_self.mpr (hr j)⟩)
    exact ⟨y, mem_iInter.mp hy⟩

variable (d : PseudoMetric X R) [d.IsUltra]

/-- Extend a map with a prescribed monotone bound on the distances of its images.
The domain and target may have different value types. Agreement on the subset is equality
of points even if the target has distinct points at distance zero. -/
theorem exists_extension_of_le_modulus [Zero S] [Add S] [LinearOrder S]
    (e : PseudoMetric Y S) [e.IsUltra] [Nonempty Y] [e.IsSphericallyComplete]
    (φ : R → S) (hφ : Monotone φ) (hφ₀ : 0 ≤ φ 0)
    (D : Set X) (f : D → Y) (hf : ∀ x y : D, e (f x) (f y) ≤ φ (d x y)) :
    ∃ g : X → Y, (∀ x : D, g x = f x) ∧ ∀ x y, e (g x) (g y) ≤ φ (d x y) := by
  classical
  -- Keep the graphs single-valued, including on zero-distance classes.
  let compatible (p q : X × Y) : Prop := e p.2 q.2 ≤ φ (d p.1 q.1) ∧ (p.1 = q.1 → p.2 = q.2)
  let initial := range (fun x : D ↦ ((x : X), f x))
  have hinit : initial.Pairwise compatible := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact ⟨hf x y, fun h ↦ congrArg f (Subtype.ext h)⟩
  obtain ⟨G, hsub, hmax⟩ := zorn_subset_nonempty {G | G.Pairwise compatible}
    (fun C hC chain _ ↦ ⟨⋃₀ C, chain.pairwise_sUnion.mpr (fun _ h ↦ hC h),
      fun _ ↦ subset_sUnion_of_mem⟩) initial hinit
  have hG {p q : X × Y} (hp : p ∈ G) (hq : q ∈ G) : compatible p q := by
    rcases eq_or_ne p q with rfl | h
    · exact ⟨by simpa using hφ₀, fun _ ↦ rfl⟩
    · exact hmax.prop hp hq h
  have total (x : X) : ∃ y : Y, (x, y) ∈ G := by
    by_contra! h
    obtain ⟨y, hy⟩ := IsSphericallyComplete.exists_dist_le e (fun p : G ↦ p.1.2)
      (fun p ↦ φ (d x p.1.1)) (fun p q ↦ by
        refine (hG p.2 q.2).1.trans ((hφ (IsUltra.le_sup' (d := d) p.1.1 x q.1.1)).trans_eq ?_)
        rw [hφ.map_sup, d.symm p.1.1 x])
    have hnew : (insert (x, y) G).Pairwise compatible := by
      refine pairwise_insert.mpr ⟨hmax.prop, ?_⟩
      intro p hp _
      have hne : x ≠ p.1 := by rintro rfl; exact h p.2 hp
      exact ⟨⟨hy ⟨p, hp⟩, fun eq ↦ (hne eq).elim⟩,
        ⟨by simpa only [e.symm p.2 y, d.symm p.1 x] using hy ⟨p, hp⟩,
          fun eq ↦ (hne eq.symm).elim⟩⟩
    exact h y (hmax.le_of_ge hnew (subset_insert ..) (mem_insert ..))
  choose g hg using total
  exact ⟨g, fun x ↦ (hG (hg x) (hsub (mem_range_self x))).2 rfl,
    fun x y ↦ (hG (hg x) (hg y)).1⟩

/-- A nonexpansive map from a subset extends nonexpansively to the whole space when its
target is nonempty and spherically complete. -/
theorem exists_nonexpansive_extension (e : PseudoMetric Y R) [e.IsUltra] [Nonempty Y]
    [e.IsSphericallyComplete] (D : Set X) (f : D → Y) (hf : ∀ x y : D, e (f x) (f y) ≤ d x y) :
    ∃ g : X → Y, (∀ x : D, g x = f x) ∧ ∀ x y, e (g x) (g y) ≤ d x y :=
  d.exists_extension_of_le_modulus e id monotone_id le_rfl D f hf

/-- A nonempty spherically complete subspace of a pseudoultrametric space is a
nonexpansive retract of the ambient space. -/
theorem exists_nonexpansive_retraction (D : Set X) (hD : D.Nonempty)
    [(d.comap (Subtype.val : D → X)).IsSphericallyComplete] :
    ∃ p : X → D, (∀ x : D, p x = x) ∧ ∀ x y, d (p x) (p y) ≤ d x y := by
  let := hD.to_subtype
  exact d.exists_nonexpansive_extension (d.comap (Subtype.val : D → X)) D id
    (fun _ _ ↦ le_rfl)

/-- A nonexpansive retraction chooses a nearest point for every point of the ambient space. -/
theorem dist_retraction_le {D : Set X} (p : X → D) (hfix : ∀ y : D, p y = y)
    (hp : ∀ x y, d (p x) (p y) ≤ d x y) (x : X) (y : D) : d x (p x) ≤ d x y := by
  refine (IsUltra.le_sup' (d := d) x y (p x)).trans (max_le le_rfl ?_)
  simpa only [hfix, d.symm (y : X) x] using hp (y : X) x

end PseudoMetric
