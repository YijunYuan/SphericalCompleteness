/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Topology.MetricSpace.BundledFun

/-!
# Spherical completeness for bundled pseudometrics

A bundled `PseudoMetric X R` has a specified value type `R`. We use its closed balls
of every radius and take intersections of arbitrary nonempty nests of nonempty balls.
This permits negative radii and does not require a countability assumption on `R`.

For an ultrametric with linearly ordered values, it suffices to test the balls whose radii
are distances from their centers. This makes the definition invariant under changing the
value type while preserving comparisons of realized distances.
-/

@[expose] public section

open Set

/-- Every nonempty inclusion chain of nonempty members of the family has a common point. -/
def Set.IsDescendingCompleteFamily {X : Type*} (balls : Set (Set X)) : Prop :=
  ∀ S ⊆ balls, S.Nonempty → (∀ B ∈ S, B.Nonempty) → IsChain (· ⊆ ·) S → (⋂₀ S).Nonempty

theorem Set.IsDescendingCompleteFamily.mono {X : Type*} {A B : Set (Set X)}
    (hB : B.IsDescendingCompleteFamily) (hAB : A ⊆ B) : A.IsDescendingCompleteFamily :=
  fun S hS ↦ hB S (hS.trans hAB)

namespace PseudoMetric

variable {X Y R : Type*} [Zero R] [Add R]

section Basic

variable [LE R] (d : PseudoMetric X R)

/-- Closed ball of radius `r` centered at `c` for the bundled pseudometric `d`. -/
def closedBall (c : X) (r : R) : Set X := {x | d x c ≤ r}

@[simp] theorem mem_closedBall {x c : X} {r : R} :
    x ∈ d.closedBall c r ↔ d x c ≤ r := Iff.rfl

@[simp] theorem mem_closedBall_self {c : X} {r : R} : c ∈ d.closedBall c r ↔ 0 ≤ r := by
  rw [mem_closedBall, d.refl]

/-- The family of all closed balls, including balls with unrealized radii. -/
def closedBalls : Set (Set X) := {B | ∃ c r, B = d.closedBall c r}

theorem closedBall_mem_closedBalls (c : X) (r : R) : d.closedBall c r ∈ d.closedBalls :=
  ⟨c, r, rfl⟩

/-- The family of closed balls with an attained radius. -/
def realizedBalls : Set (Set X) := {B | ∃ c x, B = d.closedBall c (d x c)}

theorem realizedBalls_subset_closedBalls : d.realizedBalls ⊆ d.closedBalls := by
  rintro B ⟨c, x, rfl⟩
  exact d.closedBall_mem_closedBalls c (d x c)

/-- Spherical completeness with respect to the bundled pseudometric `d`. -/
class IsSphericallyComplete : Prop where
  /-- Every nonempty nest of nonempty closed balls has nonempty intersection. -/
  nonempty_sInter : d.closedBalls.IsDescendingCompleteFamily

/-- An antitone family of nonempty balls indexed by a nonempty linear order has a common point. -/
theorem IsSphericallyComplete.nonempty_iInter_of_antitone [h : d.IsSphericallyComplete]
    {ι : Type*} [LinearOrder ι] [Nonempty ι] (c : ι → X) (r : ι → R)
    (hr : ∀ i, 0 ≤ r i) (hanti : Antitone fun i ↦ d.closedBall (c i) (r i)) :
    (⋂ i, d.closedBall (c i) (r i)).Nonempty := by
  let B i := d.closedBall (c i) (r i)
  obtain ⟨x, hx⟩ := h.nonempty_sInter (range B)
    (by rintro _ ⟨i, rfl⟩; exact ⟨c i, r i, rfl⟩) (range_nonempty _)
    (by rintro _ ⟨i, rfl⟩; exact ⟨c i, (d.refl _).trans_le (hr i)⟩)
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact (le_total j i).imp (fun h ↦ hanti h) (fun h ↦ hanti h))
  exact ⟨x, mem_iInter.mpr fun i ↦ mem_sInter.mp hx (B i) (mem_range_self i)⟩

/-- Pull back a bundled pseudometric along a function. -/
def comap (f : Y → X) : PseudoMetric Y R where
  toFun x y := d (f x) (f y)
  refl' x := d.refl (f x)
  symm' x y := d.symm (f x) (f y)
  triangle' x y z := d.triangle (f x) (f y) (f z)

@[simp] theorem comap_apply (f : Y → X) (x y : Y) : d.comap f x y = d (f x) (f y) := rfl

theorem closedBall_comap (f : Y → X) (c : Y) (r : R) :
    (d.comap f).closedBall c r = f ⁻¹' d.closedBall (f c) r := rfl

instance [Max R] [d.IsUltra] (f : Y → X) : (d.comap f).IsUltra where
  le_sup' x y z := IsUltra.le_sup' (d := d) (f x) (f y) (f z)

end Basic

section Ultra

variable [SemilatticeSup R] (d : PseudoMetric X R) [d.IsUltra]

/-- The strong triangle inequality implies nonnegativity even when `0` is not a bottom element. -/
theorem nonneg_of_ultra (x y : X) : 0 ≤ d x y := by
  simpa only [d.refl, d.symm y x, sup_idem] using (IsUltra.le_sup' (d := d) x y x)

@[simp] theorem nonempty_closedBall {c : X} {r : R} : (d.closedBall c r).Nonempty ↔ 0 ≤ r := by
  constructor
  · rintro ⟨x, hx⟩
    exact (d.nonneg_of_ultra x c).trans hx
  · exact fun hr ↦ ⟨c, d.mem_closedBall_self.mpr hr⟩

theorem closedBall_subset_of_mem {c e : X} {r s : R} (hc : c ∈ d.closedBall e s)
    (hrs : r ≤ s) : d.closedBall c r ⊆ d.closedBall e s :=
  fun x hx ↦ (IsUltra.le_sup' (d := d) x c e).trans (sup_le (le_trans hx hrs) hc)

/-- In an ultrametric, every point of a closed ball is a center. -/
theorem closedBall_eq_of_mem {c e : X} {r : R} (hc : c ∈ d.closedBall e r) :
    d.closedBall c r = d.closedBall e r :=
  Subset.antisymm (d.closedBall_subset_of_mem hc le_rfl)
    (d.closedBall_subset_of_mem ((d.symm e c).trans_le hc) le_rfl)

/-- If two closed balls meet, the ball of smaller radius is contained in the larger one. -/
theorem closedBall_subset_of_inter {c e : X} {r s : R} (hrs : r ≤ s)
    (h : (d.closedBall c r ∩ d.closedBall e s).Nonempty) :
    d.closedBall c r ⊆ d.closedBall e s := by
  obtain ⟨x, hxc, hxe⟩ := h
  rw [← d.closedBall_eq_of_mem hxc]
  exact d.closedBall_subset_of_mem hxe hrs

end Ultra

section LinearOrder

variable [LinearOrder R] (d : PseudoMetric X R) [d.IsUltra]

/-- In an ultrametric triangle with unequal sides, the two longer sides coincide. -/
theorem eq_of_lt {x y a : X} (h : d x y < d x a) : d y a = d x a := by
  refine le_antisymm ((IsUltra.le_sup' (d := d) y x a).trans
    (max_le ((d.symm _ _).trans_le h.le) le_rfl)) ?_
  exact (le_max_iff.mp (IsUltra.le_sup' (d := d) x y a)).resolve_left h.not_ge

private theorem comparable_of_inter {B C : Set X} (hB : B ∈ d.closedBalls)
    (hC : C ∈ d.closedBalls) (h : (B ∩ C).Nonempty) : B ⊆ C ∨ C ⊆ B := by
  obtain ⟨b, r, rfl⟩ := hB
  obtain ⟨c, s, rfl⟩ := hC
  exact (le_total r s).imp (fun hr ↦ d.closedBall_subset_of_inter hr h)
    (fun hr ↦ d.closedBall_subset_of_inter hr ((inter_comm _ _) ▸ h))

/-- Pairwise intersection of a nonempty family of closed balls suffices in an ultrametric.
The hypothesis includes the pair `B, B`, so every member of the family is nonempty. -/
theorem isSphericallyComplete_iff_pairwise :
    d.IsSphericallyComplete ↔
      ∀ S ⊆ d.closedBalls, S.Nonempty →
        (∀ B ∈ S, ∀ C ∈ S, (B ∩ C).Nonempty) → (⋂₀ S).Nonempty := by
  constructor
  · intro h S hS hne hinter
    apply h.nonempty_sInter S hS hne (fun B hB ↦ (hinter B hB B hB).mono inter_subset_left)
    exact fun _ hB _ hC _ ↦ d.comparable_of_inter (hS hB) (hS hC) (hinter _ hB _ hC)
  · intro h
    constructor
    intro S hS hne hb chain
    apply h S hS hne
    intro B hB C hC
    cases chain.total hB hC with
    | inl hBC => exact (hb B hB).mono fun _ hx ↦ ⟨hx, hBC hx⟩
    | inr hCB => exact (hb C hC).mono fun _ hx ↦ ⟨hCB hx, hx⟩

/-- Indexed form of the intersection principle. Centers and radii may be specified directly. -/
theorem IsSphericallyComplete.nonempty_iInter_of_pairwise [h : d.IsSphericallyComplete]
    {ι : Type*} [Nonempty ι] (c : ι → X) (r : ι → R)
    (hinter : ∀ i j, (d.closedBall (c i) (r i) ∩ d.closedBall (c j) (r j)).Nonempty) :
    (⋂ i, d.closedBall (c i) (r i)).Nonempty := by
  let B i := d.closedBall (c i) (r i)
  obtain ⟨x, hx⟩ := d.isSphericallyComplete_iff_pairwise.mp h (range B)
    (by rintro _ ⟨i, rfl⟩; exact d.closedBall_mem_closedBalls _ _) (range_nonempty _)
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hinter i j)
  exact ⟨x, mem_iInter.mpr fun i ↦ mem_sInter.mp hx (B i) (mem_range_self i)⟩

/-- Between two properly nested nonempty balls lies a ball with an attained radius. -/
theorem exists_realizedBall_between {C B : Set X} (hC : C ∈ d.closedBalls)
    (hB : B ∈ d.closedBalls) (hn : C.Nonempty) (hlt : C ⊂ B) :
    ∃ P ∈ d.realizedBalls, C ⊆ P ∧ P ⊆ B := by
  obtain ⟨c, r, rfl⟩ := hC
  obtain ⟨b, t, rfl⟩ := hB
  obtain ⟨hCB, x, hxB, hxC⟩ := ssubset_iff_exists.mp hlt
  have hct := hCB (d.mem_closedBall_self.mpr (d.nonempty_closedBall.mp hn))
  have hrc : r < d x c := lt_of_not_ge hxC
  have hxc : d x c ≤ t := (IsUltra.le_sup' (d := d) x b c).trans <|
    max_le hxB ((d.symm b c).trans_le hct)
  exact ⟨d.closedBall c (d x c), ⟨c, x, rfl⟩, fun _ hy ↦ le_trans hy hrc.le,
    d.closedBall_subset_of_mem hct hxc⟩

/-- Spherical completeness can be tested on the balls of radii `d x c` about `c`. -/
theorem isSphericallyComplete_iff_realized :
    d.IsSphericallyComplete ↔ d.realizedBalls.IsDescendingCompleteFamily := by
  refine ⟨fun h ↦ h.nonempty_sInter.mono d.realizedBalls_subset_closedBalls, fun h ↦ ⟨?_⟩⟩
  intro s hBs hn ball_nonempty hc
  classical
  by_cases hmin : ∃ C ∈ s, ∀ B ∈ s, C ⊆ B
  · obtain ⟨C, hC, hCB⟩ := hmin
    obtain ⟨x, hx⟩ := ball_nonempty C hC
    exact ⟨x, mem_sInter.mpr (fun B hB ↦ hCB B hB hx)⟩
  push Not at hmin
  -- Form a coinitial nest of realized balls by taking all those containing a member of s.
  let t := {P ∈ d.realizedBalls | ∃ C ∈ s, C ⊆ P}
  have below : ∀ B ∈ s, ∃ P ∈ t, P ⊆ B := by
    intro B hB
    obtain ⟨C, hC, hnBC⟩ := hmin B hB
    have hCB : C ⊂ B := ⟨(hc.total hC hB).resolve_right hnBC, hnBC⟩
    obtain ⟨P, hP, hCP, hPB⟩ :=
      d.exists_realizedBall_between (hBs hC) (hBs hB) (ball_nonempty C hC) hCB
    exact ⟨P, ⟨hP, C, hC, hCP⟩, hPB⟩
  have tchain : IsChain (· ⊆ ·) t := by
    rintro P ⟨hP, C, hC, hCP⟩ Q ⟨hQ, B, hB, hBQ⟩ _
    apply d.comparable_of_inter (d.realizedBalls_subset_closedBalls hP)
      (d.realizedBalls_subset_closedBalls hQ)
    cases hc.total hC hB with
    | inl hCB => exact (ball_nonempty C hC).mono fun _ hx ↦ ⟨hCP hx, hBQ (hCB hx)⟩
    | inr hBC => exact (ball_nonempty B hB).mono fun _ hx ↦ ⟨hCP (hBC hx), hBQ hx⟩
  have tballs : ∀ P ∈ t, P.Nonempty := by
    rintro _ ⟨_, C, hC, hCP⟩
    exact (ball_nonempty C hC).mono hCP
  obtain ⟨B, hB⟩ := hn
  obtain ⟨P, hP, -⟩ := below B hB
  obtain ⟨z, hz⟩ := h t (fun _ hP ↦ hP.1) ⟨P, hP⟩ tballs tchain
  refine ⟨z, mem_sInter.mpr fun B hB ↦ ?_⟩
  obtain ⟨P, hP, hPB⟩ := below B hB
  exact hPB (mem_sInter.mp hz P hP)

/-- In a nonempty spherically complete subset, each point of the ambient space has a
nearest point. Several distinct points may attain the same distance. -/
theorem exists_bestApprox (D : Set X) (hD : D.Nonempty)
    [(d.comap (Subtype.val : D → X)).IsSphericallyComplete] (x : X) :
    ∃ y : D, ∀ z : D, d x y ≤ d x z := by
  let e := d.comap (Subtype.val : D → X)
  let B (z : D) := e.closedBall z (d x z)
  have monoB {p q : D} (hpq : d x p ≤ d x q) : B p ⊆ B q := by
    apply e.closedBall_subset_of_mem _ hpq
    exact (IsUltra.le_sup' (d := d) p x q).trans <|
      max_le ((d.symm (p : X) x).trans_le hpq) le_rfl
  have : Nonempty D := hD.to_subtype
  have ball_nonempty (z : D) : (B z).Nonempty := e.nonempty_closedBall.mpr (d.nonneg_of_ultra x z)
  obtain ⟨y, hy⟩ := IsSphericallyComplete.nonempty_sInter (d := e) (range B)
    (by rintro _ ⟨z, rfl⟩; exact e.closedBall_mem_closedBalls z (d x z)) (range_nonempty _)
    (by rintro _ ⟨z, rfl⟩; exact ball_nonempty z)
    (by rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ _; exact (le_total (d x p) (d x q)).imp monoB monoB)
  refine ⟨y, fun z ↦ (IsUltra.le_sup' (d := d) x z y).trans (max_le le_rfl ?_)⟩
  rw [d.symm (z : X) (y : X)]
  exact mem_sInter.mp hy (B z) (mem_range_self z)

end LinearOrder

end PseudoMetric
