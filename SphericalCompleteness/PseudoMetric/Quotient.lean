/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Order.CompleteLattice.Chain
public import SphericalCompleteness.PseudoMetric.Sequence

/-!
# Spherical completeness of images of pseudoultrametric spaces

A surjection taking each closed ball onto the closed ball of the same radius preserves
spherical completeness for arbitrary linearly ordered radii. For maps that only lift points
at strictly larger radii, a countable coinitiality assumption gives a sequential lifting
argument. The latter applies to quotient seminorms, where the infimum may be unattained.
-/

@[expose] public section

open Set

namespace PseudoMetric

variable {X Y Γ : Type*} [Zero Γ] [Add Γ] [LinearOrder Γ]
  (d : PseudoMetric X Γ) (e : PseudoMetric Y Γ) [d.IsUltra] {f : X → Y}

/-- The strong triangle inequality descends along a nonexpansive surjection that lifts open
balls. Lift both endpoints near one representative of the middle point. -/
theorem isUltra_of_lift_dist_lt (hf : Function.Surjective f)
    (hmap : ∀ x z, e (f x) (f z) ≤ d x z)
    (hlift : ∀ x y r, e y (f x) < r → ∃ z, f z = y ∧ d z x < r) : e.IsUltra := by
  constructor
  intro a b c
  by_contra! h
  obtain ⟨x, rfl⟩ := hf b
  obtain ⟨u, rfl, hu⟩ := hlift x a _ ((le_max_left _ _).trans_lt h)
  obtain ⟨v, rfl, hv⟩ := hlift x c _ (by rw [e.symm c]; exact (le_max_right _ _).trans_lt h)
  exact (hmap u v).not_gt <| (IsUltra.le_sup' (d := d) u x v).trans_lt
    (max_lt hu (by rwa [d.symm x v]))

/-- When the fibers are spherically complete, open-ball lifting improves to closed-ball
lifting. A nearest point in the fiber attains the quotient distance. -/
theorem image_closedBall_of_sphericallyComplete_fibers (hf : Function.Surjective f)
    (hmap : ∀ x z, e (f x) (f z) ≤ d x z)
    (hlift : ∀ x y r, e y (f x) < r → ∃ z, f z = y ∧ d z x < r)
    (hfib : ∀ y : Y, (d.comap (Subtype.val : {z // f z = y} → X)).IsSphericallyComplete)
    (x : X) (r : Γ) : f '' d.closedBall x r = e.closedBall (f x) r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hmap z x).trans hz
  · intro hy
    let F := {z | f z = y}
    have : (d.comap (Subtype.val : F → X)).IsSphericallyComplete := hfib y
    obtain ⟨z, hz⟩ := d.exists_bestApprox F (hf y) x
    refine ⟨z, le_trans ?_ hy, z.prop⟩
    by_contra! h
    obtain ⟨w, hw, hwz⟩ := hlift x y (d z x) h
    have hzw := hz ⟨w, hw⟩
    exact hwz.not_ge <| (d.symm _ _).trans_le (hzw.trans_eq (d.symm x w))

variable [d.IsSphericallyComplete]

/-- Spherical completeness descends along a surjective submetry. The value order can have
arbitrary coinitiality. -/
theorem IsSphericallyComplete.of_image_closedBall (hf : Function.Surjective f)
    (hball : ∀ x r, f '' d.closedBall x r = e.closedBall (f x) r) : e.IsSphericallyComplete := by
  classical
  have : e.IsUltra := isUltra_of_lift_dist_lt d e hf
    (fun x z ↦ by
      change f x ∈ e.closedBall (f z) (d x z)
      rw [← hball]
      exact mem_image_of_mem f (show x ∈ d.closedBall z (d x z) from le_rfl))
    (fun x y r hy ↦ by
      obtain ⟨z, hz, hzy⟩ : y ∈ f '' d.closedBall x (e y (f x)) := by
        rw [hball]
        exact le_rfl
      exact ⟨z, hzy, lt_of_le_of_lt hz hy⟩)
  constructor
  intro S hballs hS hne hchain
  -- Take a maximal nest of source balls whose images belong to the given nest.
  let U := {A : Set X // A ∈ d.closedBalls ∧ f '' A ∈ S}
  have hU : Nonempty U := by
    obtain ⟨B, hB⟩ := hS
    obtain ⟨c, s, rfl⟩ := hballs hB
    obtain ⟨a, rfl⟩ := hf c
    exact ⟨⟨d.closedBall a s, d.closedBall_mem_closedBalls a s, hball a s ▸ hB⟩⟩
  let T := maxChain (fun A B : U ↦ A.val ⊆ B.val)
  have hT : IsMaxChain (fun A B : U ↦ A.val ⊆ B.val) T := maxChain_spec
  obtain ⟨x, hx⟩ := IsSphericallyComplete.nonempty_sInter (d := d) (Subtype.val '' T)
    (by rintro A ⟨u, _, rfl⟩; exact u.prop.1) ((hT.nonempty_iff.mp hU).image _)
    (by rintro A ⟨u, _, rfl⟩; exact (hne _ u.prop.2).of_image)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _
      exact hT.1.total hu hv)
  have hxT (A : U) (hA : A ∈ T) : x ∈ A.val := mem_sInter.mp hx _ ⟨A, hA, rfl⟩
  refine ⟨f x, mem_sInter.mpr fun B hB ↦ ?_⟩
  by_contra hmiss
  obtain ⟨c, s, rfl⟩ := hballs hB
  have hsc : s < e c (f x) := by rw [e.symm]; exact lt_of_not_ge hmiss
  -- Lift the missing center at its exact distance from the common point.
  obtain ⟨z, hzx, hz⟩ : c ∈ f '' d.closedBall x (e c (f x)) := by
    rw [hball]
    exact le_rfl
  let P : U := ⟨d.closedBall z s, d.closedBall_mem_closedBalls z s, by rwa [hball, hz]⟩
  have hsub (A : U) (hA : A ∈ T) : P.val ⊆ A.val := by
    have hxA := hxT A hA
    have hBA := (hchain.total hB A.prop.2).resolve_right
      (fun h ↦ hmiss (h (mem_image_of_mem f hxA)))
    have hcA := hBA (e.mem_closedBall_self.mpr (e.nonempty_closedBall.mp (hne _ hB)))
    obtain ⟨a, t, ha⟩ := A.prop.1
    have hfxA := mem_image_of_mem f hxA
    rw [ha, hball] at hcA hfxA
    have hrt : e c (f x) ≤ t := (IsUltra.le_sup' (d := e) c (f a) (f x)).trans
      (sup_le hcA ((e.symm _ _).trans_le hfxA))
    rw [ha] at hxA ⊢
    rw [← d.closedBall_eq_of_mem hxA]
    exact d.closedBall_subset_of_mem (le_trans hzx hrt) (hsc.le.trans hrt)
  have hPT : P ∈ T := (hT.2 (hT.1.insert fun A hA _ ↦ Or.inl (hsub A hA))
    (subset_insert _ _)).symm ▸ mem_insert P T
  have hfxP := mem_image_of_mem f (hxT P hPT)
  change f x ∈ f '' d.closedBall z s at hfxP
  exact hmiss (by simpa only [hball, hz] using hfxP)

/-- If every nonempty set of radii has a countable coinitial subset, it suffices for a
nonexpansive surjection to lift open balls. This also covers quotients with unattained
distance infima. -/
theorem IsSphericallyComplete.of_lift_dist_lt (hf : Function.Surjective f)
    (hmap : ∀ x z, e (f x) (f z) ≤ d x z)
    (hlift : ∀ x y r, e y (f x) < r → ∃ z, f z = y ∧ d z x < r)
    (hcoin : ∀ s : Set Γ, s.Nonempty → ∃ u : ℕ → s, ∀ r ∈ s, ∃ n, (u n).val ≤ r) :
    e.IsSphericallyComplete := by
  classical
  have : e.IsUltra := isUltra_of_lift_dist_lt d e hf hmap hlift
  apply (e.isSphericallyComplete_iff_strictAnti_radius e.nonneg_of_ultra hcoin).mpr
  intro c r hr hstrict hanti
  have hc (n : ℕ) : c (n + 1) ∈ e.closedBall (c n) (r n) :=
    hanti (Nat.le_succ n) (e.mem_closedBall_self.mpr (hr _))
  -- Lift the next center using the preceding, strictly larger, radius as tolerance.
  let Lift (n : ℕ) := {x : X // f x = c (n + 1)}
  have step (n : ℕ) (x : Lift n) : ∃ z : Lift (n + 1), d z.val x.val ≤ r n := by
    obtain ⟨z, hz, hxz⟩ := hlift x.val (c (n + 2)) (r n) (by
      rw [x.prop]
      exact lt_of_le_of_lt (hc (n + 1)) (hstrict (Nat.lt_succ_self n)))
    exact ⟨⟨z, hz⟩, hxz.le⟩
  choose next hnext using step
  obtain ⟨x₀, hx₀⟩ := hf (c 1)
  let u : (n : ℕ) → Lift n := Nat.rec ⟨x₀, hx₀⟩ next
  obtain ⟨w, hw⟩ := IsSphericallyComplete.nonempty_iInter_of_antitone d
    (fun n ↦ (u n).val) r hr (antitone_nat_of_succ_le fun n ↦
      d.closedBall_subset_of_mem (hnext n (u n)) (hstrict (Nat.lt_succ_self n)).le)
  refine ⟨f w, mem_iInter.mpr fun n ↦ ?_⟩
  apply e.closedBall_subset_of_mem (hc n) (le_refl (r n))
  rw [mem_closedBall, ← (u n).prop]
  exact (hmap _ _).trans (mem_iInter.mp hw n)

end PseudoMetric
