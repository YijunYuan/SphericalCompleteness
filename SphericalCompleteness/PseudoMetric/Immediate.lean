/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Constructions

/-!
# Immediate extensions of ultrametric spaces

A point outside an immediate image admits approximations from the image and every such
approximation can be strictly improved. Spherical completeness is equivalent to the absence
of proper immediate isometric extensions. A nest with empty intersection supplies an explicit
one-point extension: its distance to an old point is the distance to any member of a ball in
the nest that excludes the old point.
-/

@[expose] public section

open Set Function

namespace PseudoMetric

universe u

variable {X : Type u} {Y R : Type*} [Zero R] [Add R] [LinearOrder R]

/-- An image is immediate if the distances from each point outside it to points of the
image form a nonempty set with no least element. -/
def IsImmediate (e : PseudoMetric Y R) (f : X → Y) : Prop :=
  ∀ y ∉ range f, Nonempty X ∧ ∀ x, ∃ x', e y (f x') < e y (f x)

/-- A strict improvement in an immediate extension can be made in the original image.
The point being approximated may belong to a larger ambient space. -/
theorem IsImmediate.exists_lt_of_lt {Z : Type*} (d : PseudoMetric Z R) [d.IsUltra]
    {g : Y → Z} {f : X → Y} (hf : (d.comap g).IsImmediate f) {z : Z} {y : Y} {x : X}
    (hy : d z (g y) < d z (g (f x))) : ∃ x', d z (g (f x')) < d z (g (f x)) := by
  by_cases h : y ∈ range f
  · obtain ⟨x', rfl⟩ := h
    exact ⟨x', hy⟩
  · obtain ⟨x', hx'⟩ := (hf y h).2 x
    have hle := (IsUltra.le_sup' (d := d) (g y) z (g (f x))).trans <|
      max_le ((d.symm _ _).trans_le hy.le) le_rfl
    exact ⟨x', (IsUltra.le_sup' (d := d) z (g y) (g (f x'))).trans_lt <|
      max_lt hy (hx'.trans_le hle)⟩

/-- Immediate maps compose when the intermediate space carries the pullback distance. -/
theorem IsImmediate.comp {Z : Type*} {d : PseudoMetric Z R} [d.IsUltra] {g : Y → Z} {f : X → Y}
    (hg : d.IsImmediate g) (hf : (d.comap g).IsImmediate f) : d.IsImmediate (g ∘ f) := by
  intro z hz
  by_cases h : z ∈ range g
  · obtain ⟨y, rfl⟩ := h
    apply hf y
    rintro ⟨x, rfl⟩
    exact hz ⟨x, rfl⟩
  · obtain ⟨⟨y⟩, himprove⟩ := hg z h
    refine ⟨?_, fun x ↦ ?_⟩
    · by_cases hy : y ∈ range f
      · exact ⟨hy.choose⟩
      · exact (hf y hy).1
    · obtain ⟨y', hy'⟩ := himprove (f x)
      exact hf.exists_lt_of_lt d hy'

/-- A spherically complete space has no proper immediate isometric extension. Distinct
points at distance zero are allowed in both spaces. -/
theorem IsImmediate.surjective (d : PseudoMetric X R) (e : PseudoMetric Y R)
    [e.IsUltra] [d.IsSphericallyComplete] {f : X → Y} (hf : e.IsImmediate f)
    (hd : ∀ x y, e (f x) (f y) = d x y) : Surjective f := by
  let D := range f
  let g : X → D := rangeFactorization f
  have hg : Surjective g := rangeFactorization_surjective
  have : (e.comap (Subtype.val : D → Y)).IsSphericallyComplete :=
    (d.isSphericallyComplete_iff_of_surjective _ hg hd).mp inferInstance
  intro y
  by_contra hy
  obtain ⟨hne, himprove⟩ := hf y hy
  let := hne
  obtain ⟨z, hz⟩ := e.exists_bestApprox D (range_nonempty f) y
  obtain ⟨x, hx⟩ := hg z
  obtain ⟨x', hx'⟩ := himprove x
  exact hx'.not_ge (by simpa only [← hx, g, rangeFactorization_coe] using hz (g x'))

/-- In a spherically complete ultrametric space a nonempty subset is spherically complete
exactly when each ambient point has a nearest point in the subset. -/
theorem isSphericallyComplete_subtype_iff_exists_bestApprox (d : PseudoMetric X R) [d.IsUltra]
    [d.IsSphericallyComplete] (D : Set X) (hD : D.Nonempty) :
    (d.comap (Subtype.val : D → X)).IsSphericallyComplete ↔
      ∀ x, ∃ y : D, ∀ z : D, d x y ≤ d x z := by
  let e := d.comap (Subtype.val : D → X)
  refine ⟨fun _ ↦ d.exists_bestApprox D hD, fun hbest ↦ e.isSphericallyComplete_iff_pairwise.mpr ?_⟩
  intro S hS hne hpair
  have : Nonempty S := hne.to_subtype
  choose c r hball using fun B : S ↦ hS B.prop
  have hinter (B C : S) : (d.closedBall (c B) (r B) ∩ d.closedBall (c C) (r C)).Nonempty := by
    obtain ⟨z, hzB, hzC⟩ := hpair _ B.prop _ C.prop
    rw [hball B] at hzB
    rw [hball C] at hzC
    exact ⟨z, hzB, hzC⟩
  obtain ⟨x, hx⟩ := IsSphericallyComplete.nonempty_iInter_of_pairwise d (fun i ↦ (c i : X)) r hinter
  obtain ⟨y, hy⟩ := hbest x
  refine ⟨y, mem_sInter.mpr fun B hB ↦ ?_⟩
  let i : S := ⟨B, hB⟩
  change y ∈ i.val
  rw [hball i]
  have hxi : d x (c i) ≤ r i := mem_iInter.mp hx i
  exact (IsUltra.le_sup' (d := d) (y : X) x (c i)).trans <|
    max_le ((d.symm _ _).trans_le ((hy _).trans hxi)) hxi

/-- A nest with empty intersection yields a proper immediate extension by a single point. -/
theorem exists_isImmediate_option_of_not_isSphericallyComplete (d : PseudoMetric X R)
    [d.IsUltra] (h : ¬ d.IsSphericallyComplete) :
    ∃ e : PseudoMetric (Option X) R, e.IsUltra ∧
      (∀ x y, e (some x) (some y) = d x y) ∧ e.IsImmediate some := by
  classical
  have hfail : ¬ d.closedBalls.IsDescendingCompleteFamily := fun hc ↦ h ⟨hc⟩
  unfold Set.IsDescendingCompleteFamily at hfail
  push Not at hfail
  obtain ⟨S, hS, ⟨B₀, hB₀⟩, hn, hchain, hemp⟩ := hfail
  have hmiss (x : X) : ∃ c r, d.closedBall c r ∈ S ∧ x ∉ d.closedBall c r := by
    by_contra! hall
    have hx : x ∈ ⋂₀ S := mem_sInter.mpr fun B hB ↦ by
      obtain ⟨c, r, rfl⟩ := hS hB
      exact hall _ _ hB
    rw [hemp] at hx
    exact hx
  choose c r hmem hnot using hmiss
  let ρ (x : X) := d x (c x)
  have hconst (x z : X) (hz : z ∈ d.closedBall (c x) (r x)) : d x z = ρ x := by
    have hlt : r x < ρ x := lt_of_not_ge (hnot x)
    rw [d.symm x z]
    exact (d.eq_of_lt (x := c x) (y := z) (a := x) (by
      rw [d.symm (c x) z, d.symm (c x) x]
      exact lt_of_le_of_lt hz hlt)).trans (d.symm _ _)
  let δ : Option X → Option X → R
    | none, none => 0
    | some x, none | none, some x => ρ x
    | some x, some y => d x y
  let B : Option X → Set X
    | none => B₀
    | some x => d.closedBall (c x) (r x)
  have hB (a : Option X) : B a ∈ S := by cases a <;> first | exact hB₀ | apply hmem
  have hinter {A B : Set X} (ha : A ∈ S) (hb : B ∈ S) :
      ∃ C ∈ S, C ⊆ A ∧ C ⊆ B := by
    rcases hchain.total ha hb with hab | hba
    · exact ⟨A, ha, Subset.rfl, hab⟩
    · exact ⟨B, hb, hba, Subset.rfl⟩
  have hdist (a b : Option X) (z : X) (ha : z ∈ B a) (hb : z ∈ B b) :
      δ a b = d (a.getD z) (b.getD z) := by
    cases a with
    | none =>
      cases b with
      | none => exact (d.refl z).symm
      | some b => exact ((d.symm _ _).trans (hconst b z hb)).symm
    | some a =>
      cases b with
      | none => exact (hconst a z ha).symm
      | some b => rfl
  have hthree (a b t : Option X) : ∃ z, z ∈ B a ∧ z ∈ B b ∧ z ∈ B t := by
    obtain ⟨C, hc, hca, hcb⟩ := hinter (hB a) (hB b)
    obtain ⟨D, hd, hdc, hdt⟩ := hinter hc (hB t)
    obtain ⟨z, hz⟩ := hn D hd
    exact ⟨z, hca (hdc hz), hcb (hdc hz), hdt hz⟩
  let e : PseudoMetric (Option X) R := {
    toFun := δ
    refl' a := by cases a <;> first | rfl | apply d.refl
    symm' a b := by cases a <;> cases b <;> first | rfl | apply d.symm
    triangle' a b t := by
      obtain ⟨z, ha, hb, ht⟩ := hthree a b t
      rw [hdist a t z ha ht, hdist a b z ha hb, hdist b t z hb ht]
      apply d.triangle }
  refine ⟨e, ⟨fun a b t ↦ ?_⟩, fun _ _ ↦ rfl, ?_⟩
  · obtain ⟨z, ha, hb, ht⟩ := hthree a b t
    change δ a t ≤ δ a b ⊔ δ b t
    rw [hdist a t z ha ht, hdist a b z ha hb, hdist b t z hb ht]
    apply IsUltra.le_sup' (d := d)
  · intro y hy
    cases y with
    | some x => exact (hy ⟨x, rfl⟩).elim
    | none =>
      refine ⟨(hn B₀ hB₀).to_type, fun x ↦ ?_⟩
      obtain ⟨C, hc, hcx, hcc⟩ := hinter (hmem x) (hmem (c x))
      obtain ⟨z, hz⟩ := hn C hc
      refine ⟨c x, ?_⟩
      change ρ (c x) < ρ x
      rw [← hconst (c x) z (hcc hz), d.symm (c x) z]
      exact lt_of_le_of_lt (hcx hz) (lt_of_not_ge (hnot x))

/-- Spherical completeness is equivalent to the surjectivity of every immediate isometric
extension. For the reverse implication it suffices to test extensions in the same universe. -/
theorem isSphericallyComplete_iff_maximallyComplete (d : PseudoMetric X R) [d.IsUltra] :
    d.IsSphericallyComplete ↔ ∀ {Y : Type u} (e : PseudoMetric Y R) [e.IsUltra] (f : X → Y),
      (∀ x y, e (f x) (f y) = d x y) → e.IsImmediate f → Surjective f := by
  constructor
  · intro _ Y e _ f hd hf
    exact hf.surjective d e hd
  · intro h
    by_contra hc
    obtain ⟨e, he, hd, hf⟩ := d.exists_isImmediate_option_of_not_isSphericallyComplete hc
    obtain ⟨x, hx⟩ := h e some hd hf none
    cases hx

end PseudoMetric
