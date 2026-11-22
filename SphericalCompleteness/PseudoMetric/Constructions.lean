/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Fintype.Basic
public import SphericalCompleteness.PseudoMetric

/-!
# Transfer and products of spherically complete pseudometrics

A surjective map preserving distances preserves and reflects spherical completeness.
The supremum pseudometric on a finite product is spherically complete whenever its
factors are. Both results hold for general pseudometrics.
-/

@[expose] public section

open Set Function

namespace PseudoMetric

variable {X Y R : Type*}

private theorem exists_mem_mapped_nest {S : Set (Set X)} {balls : Set (Set Y)}
    (h : balls.IsDescendingCompleteFamily) (g : Set X → Set Y) (hg : Monotone g)
    (hne : S.Nonempty) (hc : IsChain (· ⊆ ·) S)
    (hb : ∀ B ∈ S, g B ∈ balls) (hn : ∀ B ∈ S, (g B).Nonempty) :
    ∃ y, ∀ B ∈ S, y ∈ g B := by
  obtain ⟨y, hy⟩ := h (g '' S) (by rintro _ ⟨B, hB, rfl⟩; exact hb B hB) (hne.image g)
    (by rintro _ ⟨B, hB, rfl⟩; exact hn B hB)
    (hc.image_of_map_rel _ _ g fun _ _ hBC ↦ hg hBC)
  exact ⟨y, fun B hB ↦ mem_sInter.mp hy _ (mem_image_of_mem g hB)⟩

section Transfer

variable [Zero R] [Add R] [LE R]

/-- A surjective pullback preserves and reflects spherical completeness. In particular,
collapsing zero-distance fibers does not affect spherical completeness. -/
theorem isSphericallyComplete_comap_iff_of_surjective (d : PseudoMetric Y R)
    {f : X → Y} (hf : Surjective f) :
    (d.comap f).IsSphericallyComplete ↔ d.IsSphericallyComplete := by
  constructor
  · intro h
    constructor
    intro S hS hne hn hc
    obtain ⟨x, hx⟩ := exists_mem_mapped_nest h.nonempty_sInter (preimage f)
      (fun _ _ ↦ preimage_mono) hne hc (by
        rintro _ hB
        obtain ⟨c, r, rfl⟩ := hS hB
        obtain ⟨x, rfl⟩ := hf c
        exact ⟨x, r, rfl⟩) (fun B hB ↦ (hn B hB).preimage hf)
    exact ⟨f x, mem_sInter.mpr hx⟩
  · intro h
    constructor
    intro S hS hne hn hc
    obtain ⟨y, hy⟩ := exists_mem_mapped_nest h.nonempty_sInter (image f)
      (fun _ _ ↦ image_mono) hne hc (by
        rintro _ hB
        obtain ⟨c, r, rfl⟩ := hS hB
        exact ⟨f c, r, by rw [closedBall_comap, image_preimage_eq _ hf]⟩)
      (fun B hB ↦ (hn B hB).image f)
    obtain ⟨x, rfl⟩ := hf y
    refine ⟨x, mem_sInter.mpr (fun B hB ↦ ?_)⟩
    obtain ⟨c, r, rfl⟩ := hS hB
    simpa only [closedBall_comap, image_preimage_eq _ hf, mem_preimage] using hy _ hB

/-- Surjective distance-preserving maps preserve and reflect spherical completeness. -/
theorem isSphericallyComplete_iff_of_surjective (d : PseudoMetric X R) (e : PseudoMetric Y R)
    {f : X → Y} (hf : Surjective f) (hd : ∀ x y, e (f x) (f y) = d x y) :
    d.IsSphericallyComplete ↔ e.IsSphericallyComplete := by
  have he : e.comap f = d := by ext x y; exact hd x y
  rw [← he]
  exact e.isSphericallyComplete_comap_iff_of_surjective hf

end Transfer

section Product

variable [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d : PseudoMetric X R) (e : PseudoMetric Y R)

/-- Supremum pseudometric on a binary product. -/
def prod : PseudoMetric (X × Y) R := d.comap Prod.fst ⊔ e.comap Prod.snd

@[simp] theorem prod_apply (x y : X × Y) :
    d.prod e x y = d x.1 y.1 ⊔ e x.2 y.2 := rfl

instance [d.IsUltra] [e.IsUltra] : (d.prod e).IsUltra := by
  unfold prod
  infer_instance

theorem closedBall_prod (c : X × Y) (r : R) :
    (d.prod e).closedBall c r = d.closedBall c.1 r ×ˢ e.closedBall c.2 r := by
  ext
  exact sup_le_iff

instance [hd : d.IsSphericallyComplete] [he : e.IsSphericallyComplete] :
    (d.prod e).IsSphericallyComplete where
  nonempty_sInter S hS hne hn hc := by
    have hrect (B) (hB : B ∈ S) :
        ∃ A ∈ d.closedBalls, ∃ C ∈ e.closedBalls, B = A ×ˢ C := by
      obtain ⟨c, r, rfl⟩ := hS hB
      exact ⟨_, d.closedBall_mem_closedBalls .., _, e.closedBall_mem_closedBalls ..,
        closedBall_prod ..⟩
    obtain ⟨x, hx⟩ := exists_mem_mapped_nest hd.nonempty_sInter (image Prod.fst)
      (fun _ _ ↦ image_mono) hne hc (by
        intro B hB
        obtain ⟨A, hA, C, _, rfl⟩ := hrect B hB
        rwa [fst_image_prod _ (hn _ hB).snd]) (fun B hB ↦ (hn B hB).image _)
    obtain ⟨y, hy⟩ := exists_mem_mapped_nest he.nonempty_sInter (image Prod.snd)
      (fun _ _ ↦ image_mono) hne hc (by
        intro B hB
        obtain ⟨A, _, C, hC, rfl⟩ := hrect B hB
        rwa [snd_image_prod (hn _ hB).fst _]) (fun B hB ↦ (hn B hB).image _)
    refine ⟨(x, y), mem_sInter.mpr (fun B hB ↦ ?_)⟩
    obtain ⟨A, _, C, _, rfl⟩ := hrect B hB
    exact ⟨fst_image_prod_subset _ _ (hx _ hB), snd_image_prod_subset _ _ (hy _ hB)⟩

end Product

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
    [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d : ∀ i, PseudoMetric (E i) R)

open Classical in
/-- Supremum pseudometric on a finite dependent product, with value zero for an empty product. -/
noncomputable def pi : PseudoMetric (∀ i, E i) R :=
  if h : (Finset.univ : Finset ι).Nonempty then
    Finset.univ.sup' h fun i ↦ (d i).comap (eval i)
  else ⊥

theorem pi_apply [Nonempty ι] (x y : ∀ i, E i) :
    pi d x y = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ d i (x i) (y i)) := by
  rw [pi, dite_eq_left Finset.univ_nonempty]
  exact Finset.apply_sup'_eq_sup'_comp _ (fun p : PseudoMetric (∀ i, E i) R ↦ p x y) (by simp)

/-- When zero is the bottom value, finite products use the ordinary finite supremum
also for an empty index type. -/
theorem pi_apply_eq_finset_sup [OrderBot R] (hzero : (⊥ : R) = 0) (x y : ∀ i, E i) :
    pi d x y = Finset.univ.sup (fun i ↦ d i (x i) (y i)) := by
  cases isEmpty_or_nonempty ι with
  | inl h => simp [pi, hzero]
  | inr h => rw [pi_apply, Finset.sup'_eq_sup]

instance [∀ i, (d i).IsUltra] : (pi d).IsUltra := by
  unfold pi
  split
  · apply Finset.sup'_induction
    · intro a ha b hb
      infer_instance
    · exact fun i _ ↦ inferInstanceAs ((d i).comap (eval i)).IsUltra
  · infer_instance

theorem closedBall_pi [Nonempty ι] (c : ∀ i, E i) (r : R) :
    (pi d).closedBall c r = univ.pi (fun i ↦ (d i).closedBall (c i) r) := by
  ext x
  simp [pi_apply]

instance [hd : ∀ i, (d i).IsSphericallyComplete] : (pi d).IsSphericallyComplete where
  nonempty_sInter S hS hne hn hc := by
    classical
    cases isEmpty_or_nonempty ι with
    | inl h =>
      refine ⟨isEmptyElim, mem_sInter.mpr (fun B hB ↦ ?_)⟩
      obtain ⟨x, hx⟩ := hn B hB
      exact Subsingleton.elim x isEmptyElim ▸ hx
    | inr h =>
      have hrect (B) (hB : B ∈ S) : ∃ (c : ∀ i, E i) (r : R),
          B = univ.pi (fun i ↦ (d i).closedBall (c i) r) := by
        obtain ⟨c, r, rfl⟩ := hS hB
        exact ⟨c, r, closedBall_pi d c r⟩
      have hproj (i : ι) := exists_mem_mapped_nest (hd i).nonempty_sInter (image (eval i))
        (fun _ _ ↦ image_mono) hne hc (by
          intro B hB
          obtain ⟨c, r, rfl⟩ := hrect B hB
          rw [eval_image_pi (mem_univ i) (hn _ hB)]
          exact (d i).closedBall_mem_closedBalls ..) (fun B hB ↦ (hn B hB).image _)
      choose x hx using hproj
      refine ⟨x, mem_sInter.mpr fun B hB ↦ ?_⟩
      obtain ⟨c, r, rfl⟩ := hrect B hB
      exact mem_univ_pi.mpr fun i ↦
        eval_image_univ_pi_subset (i := i) (t := fun j ↦ (d j).closedBall (c j) r) (hx i _ hB)

end Pi

end PseudoMetric
