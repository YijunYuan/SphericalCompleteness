/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric.Extension
public import SphericalCompleteness.PseudoMetric.Immediate

/-!
# The spherical completion by maximal nests

A point of the spherical completion is a maximal nest of nonempty closed balls. Two distinct
nests contain disjoint balls, and the distance between the nests is the distance between any
points of those two balls. The original point `x` is represented by all closed balls through
`x`. Points at distance zero give the same nest.
-/

@[expose] public section

open Set Function

namespace PseudoMetric

variable {X R : Type*} [Zero R] [Add R] [LinearOrder R] (d : PseudoMetric X R)

/-- A maximal nonempty family of pairwise intersecting closed balls. For an ultrametric,
such families are nests. -/
def SphericalCompletion :=
  {N : Set (Set X) // Maximal (fun S ↦ S.Nonempty ∧ S ⊆ d.closedBalls ∧
    ∀ A ∈ S, ∀ B ∈ S, (A ∩ B).Nonempty) N}

namespace SphericalCompletion

variable {d} {U V W : SphericalCompletion d}

private lemma meet {A B : Set X} (ha : A ∈ U.val) (hb : B ∈ U.val) : (A ∩ B).Nonempty :=
  U.prop.1.2.2 A ha B hb

private lemma mem_of_meets {A : Set X} (hA : A ∈ d.closedBalls)
    (h : ∀ B ∈ U.val, (A ∩ B).Nonempty) : A ∈ U.val := by
  obtain ⟨B, hB⟩ := U.prop.1.1
  have ha : A.Nonempty := (h B hB).mono inter_subset_left
  apply U.prop.2 (y := insert A U.val) _ (subset_insert ..) (mem_insert ..)
  refine ⟨⟨A, mem_insert ..⟩, insert_subset hA U.prop.1.2.1, ?_⟩
  rintro _ (rfl | hc) _ (rfl | ht)
  · simpa only [inter_self] using ha
  · exact h _ ht
  · simpa only [inter_comm] using h _ hc
  · exact meet hc ht

private lemma mem_of_subset {A B : Set X} (ha : A ∈ U.val) (hb : B ∈ d.closedBalls)
    (hab : A ⊆ B) : B ∈ U.val :=
  mem_of_meets hb fun C hc ↦ (meet ha hc).mono (inter_subset_inter_left C hab)

private lemma exists_disjoint_of_ne (h : U ≠ V) :
    ∃ A ∈ U.val, ∃ B ∈ V.val, Disjoint A B := by
  by_contra! hall
  apply h
  have huv : U.val ⊆ V.val := fun A hA ↦ mem_of_meets (U.prop.1.2.1 hA)
    (fun B hB ↦ not_disjoint_iff_nonempty_inter.mp (hall A hA B hB))
  exact Subtype.ext (Subset.antisymm huv (U.prop.2 V.prop.1 huv))

variable [d.IsUltra]

private lemma constant_on_ball {A : Set X} (ha : A ∈ d.closedBalls) {x p q : X}
    (hx : x ∉ A) (hp : p ∈ A) (hq : q ∈ A) : d x p = d x q := by
  obtain ⟨c, r, rfl⟩ := ha
  have hlt : r < d x c := lt_of_not_ge hx
  have hc (y : X) (hy : y ∈ d.closedBall c r) : d x y = d x c := by
    rw [d.symm x y]
    exact (d.eq_of_lt (x := c) (y := y) (a := x) (by
      rw [d.symm c y, d.symm c x]
      exact lt_of_le_of_lt hy hlt)).trans (d.symm _ _)
  exact (hc p hp).trans (hc q hq).symm

private lemma cross {A B : Set X} (ha : A ∈ d.closedBalls) (hb : B ∈ d.closedBalls)
    (hab : Disjoint A B) {p x q y : X} (hp : p ∈ A) (hx : x ∈ A) (hq : q ∈ B) (hy : y ∈ B) :
    d p q = d x y := by
  calc d p q = d q p := d.symm _ _
    _ = d q x := constant_on_ball ha (fun h ↦ disjoint_left.mp hab h hq) hp hx
    _ = d x q := d.symm _ _
    _ = d x y := constant_on_ball hb (fun h ↦ disjoint_left.mp hab hx h) hq hy

/-- Distinct maximal nests contain disjoint balls separated by a constant distance. -/
theorem exists_gap (huv : U ≠ V) : ∃ r : R, ∃ A ∈ U.val, ∃ B ∈ V.val,
    Disjoint A B ∧ ∀ x ∈ A, ∀ y ∈ B, d x y = r := by
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne huv
  obtain ⟨p, hp, _⟩ := meet ha ha
  obtain ⟨q, hq, _⟩ := meet hb hb
  exact ⟨d p q, A, ha, B, hb, hab, fun _ hx _ hy ↦
    cross (U.prop.1.2.1 ha) (V.prop.1.2.1 hb) hab hx hp hy hq⟩

/-- Distance between maximal nests as measured on a pair of disjoint balls. -/
noncomputable def gap (U V : SphericalCompletion d) : R :=
  open Classical in if h : U = V then 0 else (exists_gap h).choose

@[simp] private lemma gap_self (U : SphericalCompletion d) : gap U U = 0 := dite_eq_left rfl

/-- Disjoint members of two maximal nests determine their distance. -/
theorem gap_eq_of_disjoint {A B : Set X} (ha : A ∈ U.val) (hb : B ∈ V.val)
    (hab : Disjoint A B) {x y : X} (hx : x ∈ A) (hy : y ∈ B) : gap U V = d x y := by
  have huv : U ≠ V := by
    rintro rfl
    exact (not_disjoint_iff_nonempty_inter.mpr (meet ha hb)) hab
  obtain ⟨C, hc, D, hd, _, hv⟩ := (exists_gap huv).choose_spec
  obtain ⟨p, hp, hp'⟩ := meet ha hc
  obtain ⟨q, hq, hq'⟩ := meet hb hd
  exact (dite_eq_right huv).trans ((hv p hp' q hq').symm.trans
    (cross (U.prop.1.2.1 ha) (V.prop.1.2.1 hb) hab hp hx hq hy))

private lemma gap_symm (U V : SphericalCompletion d) : gap U V = gap V U := by
  by_cases huv : U = V
  · rw [huv]
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne huv
  obtain ⟨p, hp, _⟩ := meet ha ha
  obtain ⟨q, hq, _⟩ := meet hb hb
  rw [gap_eq_of_disjoint ha hb hab hp hq, gap_eq_of_disjoint hb ha hab.symm hq hp, d.symm]

private lemma exists_pair (U V : SphericalCompletion d) : ∃ x y, gap U V = d x y := by
  by_cases huv : U = V
  · obtain ⟨A, ha⟩ := U.prop.1.1
    obtain ⟨p, _, _⟩ := meet ha ha
    exact ⟨p, p, by rw [huv, gap_self, d.refl]⟩
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne huv
  obtain ⟨p, hp, _⟩ := meet ha ha
  obtain ⟨q, hq, _⟩ := meet hb hb
  exact ⟨p, q, gap_eq_of_disjoint ha hb hab hp hq⟩

/-- The three distances in a triangle of maximal nests are realized by three original points. -/
private lemma exists_triangle (U V W : SphericalCompletion d) :
    ∃ x y z : X, gap U V = d x y ∧ gap V W = d y z ∧ gap U W = d x z := by
  by_cases huv : U = V
  · subst V
    obtain ⟨x, z, h⟩ := exists_pair U W
    exact ⟨x, x, z, by rw [gap_self, d.refl], h, h⟩
  by_cases hvw : V = W
  · subst W
    obtain ⟨x, y, h⟩ := exists_pair U V
    exact ⟨x, y, y, h, by rw [gap_self, d.refl], h⟩
  by_cases huw : U = W
  · subst W
    obtain ⟨x, y, h⟩ := exists_pair U V
    exact ⟨x, y, x, h, by rw [gap_symm, h, d.symm], by rw [gap_self, d.refl]⟩
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne huv
  obtain ⟨B', hb', C', hc', hbc⟩ := exists_disjoint_of_ne hvw
  obtain ⟨A', ha', C, hc, hac⟩ := exists_disjoint_of_ne huw
  obtain ⟨x, hx, hx'⟩ := meet ha ha'
  obtain ⟨y, hy, hy'⟩ := meet hb hb'
  obtain ⟨z, hz, hz'⟩ := meet hc hc'
  exact ⟨x, y, z, gap_eq_of_disjoint ha hb hab hx hy, gap_eq_of_disjoint hb' hc' hbc hy' hz',
    gap_eq_of_disjoint ha' hc hac hx' hz⟩

end SphericalCompletion

open SphericalCompletion

variable [d.IsUltra]

/-- The pseudometric on maximal nests, valued in the original radius type. -/
noncomputable def sphericalCompletionMetric : PseudoMetric (SphericalCompletion d) R where
  toFun := SphericalCompletion.gap
  refl' := by exact SphericalCompletion.gap_self
  symm' := by exact SphericalCompletion.gap_symm
  triangle' U V W := by
    obtain ⟨x, y, z, hxy, hyz, hxz⟩ := exists_triangle U V W
    rw [hxy, hyz, hxz]
    exact d.triangle x y z

instance : d.sphericalCompletionMetric.IsUltra where
  le_sup' U V W := by
    obtain ⟨x, y, z, hxy, hyz, hxz⟩ := exists_triangle U V W
    change gap U W ≤ gap U V ⊔ gap V W
    rw [hxy, hyz, hxz]
    apply IsUltra.le_sup' (d := d)

/-- The maximal nest consisting of the closed balls that contain a given point. -/
def toSphericalCompletion (x : X) : SphericalCompletion d := by
  let N := {A ∈ d.closedBalls | x ∈ A}
  have hx : d.closedBall x 0 ∈ N :=
    ⟨d.closedBall_mem_closedBalls .., d.mem_closedBall_self.mpr le_rfl⟩
  refine ⟨N, ⟨⟨_, hx⟩, fun _ h ↦ h.1, fun _ ha _ hb ↦ ⟨x, ha.2, hb.2⟩⟩, ?_⟩
  intro M hM hNM B hB
  obtain ⟨c, r, rfl⟩ := hM.2.1 hB
  obtain ⟨z, hzx, hzc⟩ := hM.2.2 _ (hNM hx) _ hB
  refine ⟨d.closedBall_mem_closedBalls .., (IsUltra.le_sup' (d := d) x z c).trans (max_le ?_ hzc)⟩
  exact ((d.symm _ _).trans_le hzx).trans ((d.nonneg_of_ultra z c).trans hzc)

@[simp] theorem mem_toSphericalCompletion {x : X} {A : Set X} :
    A ∈ (d.toSphericalCompletion x).val ↔ A ∈ d.closedBalls ∧ x ∈ A := Iff.rfl

@[simp] theorem sphericalCompletionMetric_toSphericalCompletion (x y : X) :
    d.sphericalCompletionMetric (d.toSphericalCompletion x) (d.toSphericalCompletion y) =
      d x y := by
  by_cases h : d.toSphericalCompletion x = d.toSphericalCompletion y
  · rw [h, PseudoMetric.refl]
    have hx : d.closedBall x 0 ∈ (d.toSphericalCompletion x).val :=
      ⟨d.closedBall_mem_closedBalls .., d.mem_closedBall_self.mpr le_rfl⟩
    rw [h] at hx
    exact le_antisymm (d.nonneg_of_ultra x y) ((d.symm _ _).trans_le hx.2)
  · obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne h
    exact gap_eq_of_disjoint ha hb hab ha.2 hb.2

namespace SphericalCompletion

variable {d}

/-- Given one center nest containing an original ball, the nests through that ball form the
completion ball of the same radius. -/
private lemma mem_iff_gap_le {U V : SphericalCompletion d} {c : X} {r : R}
    (hU : d.closedBall c r ∈ U.val) : d.closedBall c r ∈ V.val ↔ gap V U ≤ r := by
  have hr := d.nonempty_closedBall.mp ((meet hU hU).mono inter_subset_left)
  constructor
  · intro hV
    by_cases heq : V = U
    · simpa only [heq, gap_self] using hr
    obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne heq
    obtain ⟨p, hp, hpc⟩ := meet ha hV
    obtain ⟨q, hq, hqc⟩ := meet hb hU
    rw [gap_eq_of_disjoint ha hb hab hp hq]
    exact (IsUltra.le_sup' (d := d) p c q).trans (max_le hpc ((d.symm _ _).trans_le hqc))
  · intro h
    apply mem_of_meets (d.closedBall_mem_closedBalls ..)
    intro A ha
    by_contra hn
    have hdis := not_disjoint_iff_nonempty_inter.not.mpr hn
    obtain ⟨z, hz, _⟩ := meet ha ha
    have hgap := gap_eq_of_disjoint ha hU (not_not.mp hdis).symm hz (d.mem_closedBall_self.mpr hr)
    exact (disjoint_left.mp (not_not.mp hdis)) ((hgap ▸ h : d z c ≤ r)) hz

private lemma exists_original_ball {U V : SphericalCompletion d} (hne : U ≠ V) :
    ∃ x : X, d.closedBall x (gap U V) ∈ U.val := by
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne hne
  obtain ⟨c, r, rfl⟩ := U.prop.1.2.1 ha
  have hrc := d.nonempty_closedBall.mp ((meet ha ha).mono inter_subset_left)
  obtain ⟨q, hq, _⟩ := meet hb hb
  have hcg := gap_eq_of_disjoint ha hb hab (d.mem_closedBall_self.mpr hrc) hq
  have hlt : r < d q c := lt_of_not_ge fun h ↦ disjoint_left.mp hab h hq
  refine ⟨c, mem_of_subset ha (d.closedBall_mem_closedBalls ..) (fun _ hx ↦ ?_)⟩
  rw [mem_closedBall, hcg, d.symm c q]
  exact le_trans hx hlt.le

omit [d.IsUltra] in
private lemma exists_maximal_nest {N : Set (Set X)} (hne : N.Nonempty) (hb : N ⊆ d.closedBalls)
    (hN : ∀ A ∈ N, ∀ B ∈ N, (A ∩ B).Nonempty) :
    ∃ U : SphericalCompletion d, N ⊆ U.val := by
  let F := {M : Set (Set X) | M.Nonempty ∧ M ⊆ d.closedBalls ∧
    ∀ A ∈ M, ∀ B ∈ M, (A ∩ B).Nonempty}
  have hc (C : Set (Set (Set X))) (hCF : C ⊆ F) (hc : IsChain (· ⊆ ·) C) (hneC : C.Nonempty) :
      ∃ M ∈ F, ∀ S ∈ C, S ⊆ M := by
    obtain ⟨S, hs⟩ := hneC
    refine ⟨⋃₀ C, ⟨(hCF hs).1.mono (subset_sUnion_of_mem hs), ?_, ?_⟩,
      fun _ ↦ subset_sUnion_of_mem⟩
    · rintro A ⟨S, hs, ha⟩
      exact (hCF hs).2.1 ha
    · rintro A ⟨S, hs, ha⟩ B ⟨T, ht, hb⟩
      rcases hc.total hs ht with hst | hts
      · exact (hCF ht).2.2 A (hst ha) B hb
      · exact (hCF hs).2.2 A ha B (hts hb)
  obtain ⟨M, hNM, hm⟩ := zorn_subset_nonempty F hc N ⟨hne, hb, hN⟩
  exact ⟨⟨M, hm⟩, hNM⟩

end SphericalCompletion

instance : d.sphericalCompletionMetric.IsSphericallyComplete := by
  apply d.sphericalCompletionMetric.isSphericallyComplete_iff_pairwise.mpr
  intro S hS hne hpair
  classical
  by_cases hsing : ∃ U : SphericalCompletion d, {U} ∈ S
  · obtain ⟨U, hU⟩ := hsing
    refine ⟨U, mem_sInter.mpr fun B hB ↦ ?_⟩
    obtain ⟨z, hz, hz'⟩ := hpair _ hU B hB
    rwa [mem_singleton_iff.mp hz] at hz'
  have hex (B : S) : ∃ A ∈ d.closedBalls, ∀ U : SphericalCompletion d, U ∈ B.val ↔ A ∈ U.val := by
    obtain ⟨U, r, hball⟩ := hS B.prop
    have hr := d.sphericalCompletionMetric.nonempty_closedBall.mp
      (hball ▸ (hpair B B.prop B B.prop).mono inter_subset_left)
    have hU : U ∈ B.val := hball ▸ d.sphericalCompletionMetric.mem_closedBall_self.mpr hr
    obtain ⟨V, hv, hne⟩ : ∃ V ∈ B.val, V ≠ U := by
      by_contra! hall
      exact hsing ⟨U, (Subset.antisymm (fun V hV ↦ mem_singleton_iff.mpr (hall V hV))
        (singleton_subset_iff.mpr hU)) ▸ B.prop⟩
    obtain ⟨x, hx⟩ := exists_original_ball hne.symm
    have hle : gap U V ≤ r := by
      rw [hball] at hv
      rw [gap_symm]
      exact hv
    have hxr : d.closedBall x r ∈ U.val := mem_of_subset hx (d.closedBall_mem_closedBalls ..)
      (fun _ hp ↦ le_trans hp hle)
    exact ⟨_, d.closedBall_mem_closedBalls x r, fun W ↦
      hball ▸ (mem_iff_gap_le (V := W) hxr).symm⟩
  choose A hA heq using hex
  have : Nonempty S := hne.to_subtype
  obtain ⟨U, hu⟩ := exists_maximal_nest (range_nonempty A)
    (by rintro _ ⟨B, rfl⟩; exact hA B) (by
      rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
      obtain ⟨V, hvB, hvC⟩ := hpair _ B.prop _ C.prop
      exact meet ((heq B V).mp hvB) ((heq C V).mp hvC))
  exact ⟨U, mem_sInter.mpr fun B hB ↦ (heq ⟨B, hB⟩ U).mpr (hu (mem_range_self _))⟩

@[simp] theorem sphericalCompletionMetric_eq_zero_iff {U V : SphericalCompletion d} :
    d.sphericalCompletionMetric U V = 0 ↔ U = V := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ d.sphericalCompletionMetric.refl _⟩
  by_contra hne
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne hne
  obtain ⟨c, r, rfl⟩ := U.prop.1.2.1 ha
  have hr := d.nonempty_closedBall.mp ((meet ha ha).mono inter_subset_left)
  obtain ⟨q, hq, _⟩ := meet hb hb
  have he := gap_eq_of_disjoint ha hb hab (d.mem_closedBall_self.mpr hr) hq
  change gap U V = 0 at h
  have hqc : d q c ≤ r := (d.symm _ _).trans_le ((he.symm.trans h).trans_le hr)
  exact disjoint_left.mp hab hqc hq

@[simp] theorem toSphericalCompletion_eq_iff (x y : X) :
    d.toSphericalCompletion x = d.toSphericalCompletion y ↔ d x y = 0 := by
  rw [← d.sphericalCompletionMetric_eq_zero_iff, sphericalCompletionMetric_toSphericalCompletion]

/-- Two distinct maximal nests have original approximations strictly closer on both sides.
The distance between these approximations is the distance between the nests. -/
theorem exists_strict_approximations {U V : SphericalCompletion d} (hne : U ≠ V) :
    ∃ x y : X, d.sphericalCompletionMetric U (d.toSphericalCompletion x) <
      d.sphericalCompletionMetric U V ∧
      d.sphericalCompletionMetric V (d.toSphericalCompletion y) < d.sphericalCompletionMetric U V ∧
      d x y = d.sphericalCompletionMetric U V := by
  obtain ⟨A, ha, B, hb, hab⟩ := exists_disjoint_of_ne hne
  obtain ⟨x, r, rfl⟩ := U.prop.1.2.1 ha
  obtain ⟨y, s, rfl⟩ := V.prop.1.2.1 hb
  have hr := d.nonempty_closedBall.mp ((meet ha ha).mono inter_subset_left)
  have hs := d.nonempty_closedBall.mp ((meet hb hb).mono inter_subset_left)
  have hx := d.mem_closedBall_self (c := x) |>.mpr hr
  have hy := d.mem_closedBall_self (c := y) |>.mpr hs
  have hgap := gap_eq_of_disjoint ha hb hab hx hy
  refine ⟨x, y, ?_, ?_, hgap.symm⟩
  · change gap U _ < gap U V
    rw [gap_symm U (d.toSphericalCompletion x), hgap, d.symm x y]
    exact ((mem_iff_gap_le (V := d.toSphericalCompletion x) ha).mp
      ⟨d.closedBall_mem_closedBalls .., hx⟩).trans_lt
        (lt_of_not_ge fun h ↦ disjoint_left.mp hab h hy)
  · change gap V _ < gap U V
    rw [gap_symm V (d.toSphericalCompletion y), hgap]
    exact ((mem_iff_gap_le (V := d.toSphericalCompletion y) hb).mp
      ⟨d.closedBall_mem_closedBalls .., hy⟩).trans_lt
        (lt_of_not_ge fun h ↦ disjoint_left.mp hab hx h)

/-- Every subset containing the principal nests has immediate image in the completion. -/
theorem isImmediate_of_range_toSphericalCompletion_subset (D : Set (SphericalCompletion d))
    (hD : range d.toSphericalCompletion ⊆ D) : d.sphericalCompletionMetric.IsImmediate
      (Subtype.val : D → SphericalCompletion d) := by
  intro U hU
  obtain ⟨A, ha⟩ := U.prop.1.1
  obtain ⟨x, _, _⟩ := meet ha ha
  refine ⟨⟨⟨_, hD (mem_range_self x)⟩⟩, fun V ↦ ?_⟩
  obtain ⟨z, _, hz, _, _⟩ := d.exists_strict_approximations
    (show U ≠ V.val from fun he ↦ hU ⟨V, he.symm⟩)
  exact ⟨⟨_, hD (mem_range_self z)⟩, hz⟩

/-- A spherically complete subset containing all principal nests equals the whole completion. -/
theorem eq_univ_of_isSphericallyComplete_of_range_subset (D : Set (SphericalCompletion d))
    (hD : range d.toSphericalCompletion ⊆ D)
    [(d.sphericalCompletionMetric.comap
        (Subtype.val : D → SphericalCompletion d)).IsSphericallyComplete] :
    D = univ := by
  have h := (d.isImmediate_of_range_toSphericalCompletion_subset D hD).surjective
    (d.sphericalCompletionMetric.comap Subtype.val) d.sphericalCompletionMetric (fun _ _ ↦ rfl)
  exact eq_univ_of_forall fun U ↦ (h U).elim fun v hv ↦ hv ▸ v.prop

/-- The original space has immediate image in its maximal-nest completion. -/
theorem isImmediate_toSphericalCompletion :
    d.sphericalCompletionMetric.IsImmediate d.toSphericalCompletion := by
  intro U hU
  obtain ⟨A, ha⟩ := U.prop.1.1
  obtain ⟨p, _, _⟩ := meet ha ha
  refine ⟨⟨p⟩, fun x ↦ ?_⟩
  obtain ⟨z, _, hz, _, _⟩ := d.exists_strict_approximations
    (show U ≠ d.toSphericalCompletion x from fun he ↦ hU ⟨x, he.symm⟩)
  exact ⟨z, hz⟩

/-- A space is spherically complete exactly when all maximal nests come from its points. -/
theorem isSphericallyComplete_iff_surjective_toSphericalCompletion :
    d.IsSphericallyComplete ↔ Surjective d.toSphericalCompletion := by
  refine ⟨fun _ ↦ d.isImmediate_toSphericalCompletion.surjective d d.sphericalCompletionMetric
    d.sphericalCompletionMetric_toSphericalCompletion, fun h ↦ ?_⟩
  exact (d.isSphericallyComplete_iff_of_surjective d.sphericalCompletionMetric h
    d.sphericalCompletionMetric_toSphericalCompletion).mpr inferInstance

/-- A nonexpansive map on the completion is an isometry as soon as it preserves
distances between principal nests. -/
theorem sphericalCompletionMetric_eq_of_nonexpansive {Y : Type*} (e : PseudoMetric Y R)
    [e.IsUltra] (g : SphericalCompletion d → Y)
    (hg : ∀ U V, e (g U) (g V) ≤ d.sphericalCompletionMetric U V)
    (hf : ∀ x y, e (g (d.toSphericalCompletion x)) (g (d.toSphericalCompletion y)) = d x y)
    (U V : SphericalCompletion d) : e (g U) (g V) = d.sphericalCompletionMetric U V := by
  by_cases he : U = V
  · simp [he]
  refine (hg U V).antisymm (le_of_not_gt fun hlt ↦ ?_)
  obtain ⟨x, y, hx, hy, hxy⟩ := d.exists_strict_approximations he
  have hxy' := (IsUltra.le_sup' (d := e) (g (d.toSphericalCompletion x)) (g U)
    (g (d.toSphericalCompletion y))).trans_lt (max_lt
      (((e.symm _ _).trans_le (hg U _)).trans_lt hx)
      ((IsUltra.le_sup' (d := e) (g U) (g V) (g (d.toSphericalCompletion y))).trans_lt
        (max_lt hlt ((hg V _).trans_lt hy))))
  exact (hf x y |>.trans hxy).not_lt hxy'

/-- Weak universal property of the maximal-nest completion. An isometry into a spherically
complete ultrametric space extends to the completion. Agreement as functions requires the
original map to identify points at distance zero, precisely the fibers of the principal map. -/
theorem exists_isometry_from_sphericalCompletion {Y : Type*} (e : PseudoMetric Y R) [e.IsUltra]
    [e.IsSphericallyComplete] (f : X → Y) (hf : ∀ x y, e (f x) (f y) = d x y)
    (hzero : ∀ x y, d x y = 0 → f x = f y) :
    ∃ g : SphericalCompletion d → Y, (∀ x, g (d.toSphericalCompletion x) = f x) ∧
      ∀ U V, e (g U) (g V) = d.sphericalCompletionMetric U V := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h =>
    have : IsEmpty (SphericalCompletion d) := ⟨fun U ↦ by
      obtain ⟨A, ha⟩ := U.prop.1.1
      obtain ⟨x, _⟩ := meet ha ha
      exact h.false x⟩
    exact ⟨isEmptyElim, fun x ↦ isEmptyElim x, fun U ↦ isEmptyElim U⟩
  | inr h =>
    have : Nonempty Y := h.map f
    let D := range d.toSphericalCompletion
    let f₀ (U : D) := f U.prop.choose
    have h₀ (U : D) : d.toSphericalCompletion U.prop.choose = U.val := U.prop.choose_spec
    obtain ⟨g, hg, hle⟩ := d.sphericalCompletionMetric.exists_nonexpansive_extension e D f₀
      (fun U V ↦ by
        change e (f _) (f _) ≤ _
        rw [hf, ← d.sphericalCompletionMetric_toSphericalCompletion, h₀, h₀])
    have hfx (x : X) : g (d.toSphericalCompletion x) = f x := by
      let U : D := ⟨_, mem_range_self x⟩
      exact (hg U).trans (hzero _ _ ((d.toSphericalCompletion_eq_iff _ _).mp (h₀ U)))
    exact ⟨g, hfx, d.sphericalCompletionMetric_eq_of_nonexpansive e g hle
      (fun x y ↦ by rw [hfx, hfx, hf])⟩

/-- A minimal spherically complete extension in which points of the source at distance zero
agree is isometrically equivalent to the maximal-nest completion, over the original space. -/
theorem exists_equiv_of_minimal_sphericallyComplete {Y : Type*} (e : PseudoMetric Y R) [e.IsUltra]
    [e.IsSphericallyComplete] (f : X → Y) (hf : ∀ x y, e (f x) (f y) = d x y)
    (hzero : ∀ x y, d x y = 0 → f x = f y)
    (hmin : ∀ D : Set Y, range f ⊆ D →
      (e.comap (Subtype.val : D → Y)).IsSphericallyComplete → D = univ) :
    ∃ g : SphericalCompletion d ≃ Y, (∀ x, g (d.toSphericalCompletion x) = f x) ∧
      ∀ U V, e (g U) (g V) = d.sphericalCompletionMetric U V := by
  obtain ⟨g, hgf, hg⟩ := d.exists_isometry_from_sphericalCompletion e f hf hzero
  have hinj : Injective g := fun U V h ↦ d.sphericalCompletionMetric_eq_zero_iff.mp
    (by rw [← hg, h, e.refl])
  have hsc : (e.comap (Subtype.val : range g → Y)).IsSphericallyComplete :=
    (d.sphericalCompletionMetric.isSphericallyComplete_iff_of_surjective _
      (rangeFactorization_surjective (f := g)) hg).mp inferInstance
  have hsurj := range_eq_univ.mp <| hmin (range g)
    (by rintro _ ⟨x, rfl⟩; exact ⟨_, hgf x⟩) hsc
  exact ⟨Equiv.ofBijective g ⟨hinj, hsurj⟩, hgf, hg⟩

/-- Every ultrametric admits an injective, immediate, spherically complete extension, even when
distinct points have distance zero. Retain those points by adjoining only the nonprincipal nests.
The extension has the same universe and radius type as the source. -/
theorem exists_sphericallyComplete_immediate_extension {X : Type u} (d : PseudoMetric X R)
    [d.IsUltra] : ∃ (Y : Type u) (e : PseudoMetric Y R) (f : X ↪ Y),
      e.IsUltra ∧ e.IsSphericallyComplete ∧ (∀ x y, e (f x) (f y) = d x y) ∧ e.IsImmediate f := by
  let T := {U : SphericalCompletion d // U ∉ range d.toSphericalCompletion}
  let g : X ⊕ T → SphericalCompletion d := Sum.elim d.toSphericalCompletion Subtype.val
  have hg : Surjective g := by
    intro U
    by_cases h : U ∈ range d.toSphericalCompletion
    · obtain ⟨x, rfl⟩ := h
      exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr ⟨U, h⟩, rfl⟩
  let e := d.sphericalCompletionMetric.comap g
  let f : X ↪ X ⊕ T := ⟨Sum.inl, Sum.inl_injective⟩
  refine ⟨_, e, f, inferInstance,
    (d.sphericalCompletionMetric.isSphericallyComplete_comap_iff_of_surjective hg).mpr
      inferInstance,
    d.sphericalCompletionMetric_toSphericalCompletion, ?_⟩
  intro y hy
  cases y with
  | inl x => exact (hy ⟨x, rfl⟩).elim
  | inr t => exact d.isImmediate_toSphericalCompletion t.val t.prop

end PseudoMetric
