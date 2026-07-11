/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import SphericalCompleteness.Defs

/-!
# Spherical completeness: characterizations

Equivalent characterizations of spherical completeness for ultrametric spaces, together with its
stability under products and the basic examples.

For an ultrametric (pseudo)metric space, spherical completeness can be reformulated as an
intersection property in several equivalent ways: for nested closed balls with *antitone* radii,
for nested closed balls with *strictly decreasing* radii, and for an arbitrary family of closed
balls that merely intersect *pairwise*. These are collected in `tfae`.

The file also shows that spherical completeness passes to binary and finite products, and records
that `PUnit`, `ℂ`, `ℝ` and the `p`-adic numbers `ℚ_[p]` are spherically complete (each being
proper, i.e. having compact closed balls).

## Main statements

* `iff_antitone_radius`, `iff_strictAnti_radius`,
  `iff_pairwise_inter_nonempty`: the three reformulations.
* `tfae`: the reformulations bundled as a `TFAE` list.
* `Prod.sphericallyCompleteSpace`, `Pi.sphericallyCompleteSpace`: stability under products.
-/

@[expose] public section

open Metric
open Filter

namespace SphericallyCompleteSpace

section
variable (α : Type*) [PseudoMetricSpace α] [iud : IsUltrametricDist α]

/--
Characterizes spherical completeness of an ultrametric (pseudo)metric space in terms of
nested closed balls with antitone radii.

In an ultrametric space `α`, `SphericallyCompleteSpace α` is equivalent to the following
intersection property: for every sequence of centers `ci : ℕ → α` and radii
`ri : ℕ → NNReal` such that

* `Antitone ri` (the radii are nonincreasing), and
* `Antitone (fun i ↦ closedBall (ci i) (ri i))` (the closed balls form a nested,
  decreasing chain by inclusion),

the intersection `⋂ i, closedBall (ci i) (ri i)` is nonempty.

This is the standard “Cantor intersection” formulation of spherical completeness for
ultrametric spaces, expressed for sequences indexed by `ℕ`.
-/
theorem iff_antitone_radius :
    SphericallyCompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  refine ⟨fun h ci ri hri hanti ↦ h.nonempty_iInter_of_antitone hanti, fun h ↦ ?_⟩
  · refine { nonempty_iInter_of_antitone := ?_ }
    intro c r hanti
    let r' : ℕ → NNReal := fun n ↦ sInf {r k | k ≤ n}
    have hr'_Antitone : Antitone r' := fun m n hmn ↦
      csInf_le_csInf' ⟨r m, m, le_rfl, rfl⟩ <| by
        rintro a ⟨k, hk, rfl⟩; exact ⟨k, hk.trans hmn, rfl⟩
    have : Antitone fun i ↦ closedBall (c i) ↑(r' i) := by
      refine antitone_nat_of_succ_le fun n ↦ ?_
      intro x hx
      simp only [mem_closedBall, dist_le_coe, r'] at *
      rw [le_csInf_iff''] at *
      · intro b hb
        rcases hb with ⟨k, hk1, hk2⟩
        rw [← hk2]
        specialize hx (r k) ⟨k, ⟨by linarith, rfl⟩⟩
        rw [← dist_le_coe] at *
        refine le_trans (iud.dist_triangle_max x (c (n + 1)) (c n)) <| max_le_iff.2 ⟨hx, ?_⟩
        refine le_trans ?_ <| IsUltrametricDist.diam_le_radius (c k) (r k)
        apply dist_le_diam_of_mem isBounded_closedBall
        · exact hanti (by linarith : k ≤ n + 1) (mem_closedBall_self NNReal.zero_le_coe)
        · exact hanti hk1 (mem_closedBall_self NNReal.zero_le_coe)
      · use r (n + 1), n + 1
      · use r n, n
    specialize h hr'_Antitone this
    simp only [Set.nonempty_iInter, mem_closedBall] at h
    rcases h with ⟨z, hz⟩
    use z
    simp only [Set.mem_iInter, mem_closedBall]
    refine fun i ↦ le_trans (hz i) ?_
    simp only [NNReal.coe_le_coe, r']
    exact csInf_le' ⟨i, le_rfl, rfl⟩

/--
Characterization of spherical completeness in an ultrametric (pseudo)metric space via
nested closed balls with *strictly decreasing* radii.

In an ultrametric space `α`, this theorem states that `SphericallyCompleteSpace α` is
equivalent to the following intersection property:

For any sequence of centers `ci : ℕ → α` and radii `ri : ℕ → NNReal`, if
* `StrictAnti ri` (the radii strictly decrease), and
* `Antitone (fun i ↦ closedBall (ci i) (ri i))` (the closed balls are nested decreasingly),

then the intersection `⋂ i, closedBall (ci i) (ri i)` is nonempty.

This provides a convenient reformulation of spherical completeness when working with
chains of balls indexed by `ℕ` whose radii shrink strictly.
-/
theorem iff_strictAnti_radius :
    SphericallyCompleteSpace α ↔
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    StrictAnti ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty := by
  refine ⟨fun h ci ri hri hanti ↦ h.nonempty_iInter_of_antitone hanti, ?_⟩
  · rw [iff_antitone_radius α]
    intro h ci ri hri hanti
    rcases eventually_stable_or_exists_strictAnti_of_antitone hri with hc | hc
    · rcases hc with ⟨N, hN⟩
      use (ci N)
      simp only [Set.mem_iInter]
      intro i
      if hiN : i ≤ N then
        exact hanti hiN (mem_closedBall_self NNReal.zero_le_coe)
      else
        simp only [not_le] at hiN
        rw [mem_closedBall, dist_comm,← mem_closedBall, hN i (by linarith)]
        exact hanti (by linarith : N ≤ i) (mem_closedBall_self NNReal.zero_le_coe)
    · rcases hc with ⟨φ, hφ1, hφ2⟩
      have := @h (ci ∘ φ) (ri ∘ φ) hφ2
        (antitone_nat_of_succ_le fun n ↦ hanti <| le_of_lt <| hφ1 (by linarith : n < n + 1))
      simp only [Function.comp_apply, Set.nonempty_iInter] at this
      rcases this with ⟨z, hz⟩
      use z
      simp only [Set.mem_iInter]
      exact fun i ↦ hanti hφ1.le_apply <| hz i

end

/--
From a nonempty family `S` of centre/radius pairs whose radii never attain their infimum, one can
always find a strictly smaller admissible radius.

Concretely, if every `w ∈ S` has radius strictly above `sInf {w.2 | w ∈ S}`, then for each `n : ℕ`
and each chosen element `s : S` there is a radius `b` occurring in `S` with
`b < min (sInf {radii} + 1 / 2 ^ n) s.2`. The `1 / 2 ^ n` term forces `b` towards the infimum as
`n` grows, while the `s.2` term keeps `b` below the current radius; this is the key step used to
build a strictly shrinking chain of balls in `countableChainOfBall`.
-/
private lemma smaller_radius {α : Type*} [PseudoMetricSpace α]
    {S : Set (α × NNReal)} [hS : Nonempty ↑S]
    (hw : (∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2)) :
    ∀ (n : ℕ) (s : ↑S), ∃ b ∈ {x | ∃ w ∈ S, w.2 = x},
    b < min (sInf {x | ∃ w ∈ S, w.2 = x} + 1 / 2 ^ n) s.val.2 := by
  intro m s
  exact ((csInf_lt_iff (by simp) (by
      use hS.some.val.2
      simp only [Prod.exists, exists_eq_right, Set.mem_setOf_eq]
      use hS.some.1.1
      simp only [Prod.mk.eta, Subtype.coe_prop]
      : {x | ∃ w ∈ S, w.2 = x}.Nonempty)).1 (by
      simp only [Prod.exists, exists_eq_right, one_div, lt_inf_iff, lt_add_iff_pos_right, inv_pos,
        Nat.ofNat_pos, pow_pos, true_and]
      simpa only [Prod.exists, exists_eq_right] using hw
        s.val s.prop
      : sInf {x | ∃ w ∈ S, w.2 = x} <
      min (sInf {x | ∃ w ∈ S, w.2 = x} + 1 / 2 ^ m)
        s.val.2))

/--
Recursively selects a sequence in `S` whose radii shrink towards `sInf {radii}`.

Assuming the radii of the family `S` never reach their infimum (`hw`), this builds a function
`ℕ → S` where the `n`-th term is chosen, via `smaller_radius`, to have radius strictly below both
`sInf {radii} + 1 / 2 ^ n` and the radius of the previous term. Together with
`antitone_of_countableChainOfBall` and `cofinal_of_countableChainOfBall`, this countable chain
reduces the pairwise-intersection characterization of spherical completeness to the definitional
one for `ℕ`-indexed nested balls.
-/
private noncomputable def countableChainOfBall {α : Type*}
    [PseudoMetricSpace α]
    {S : Set (α × NNReal)} [hS : Nonempty S]
    (hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2) : ℕ → ↑S := fun n ↦
  match n with
  | 0 => ⟨(smaller_radius hw 0 hS.some).choose_spec.1.out.choose,
     (smaller_radius hw 0 hS.some).choose_spec.1.out.choose_spec.1⟩
  | m + 1 =>
    ⟨(smaller_radius hw (m + 1) (countableChainOfBall hw m)).choose_spec.1.out.choose,
     (smaller_radius hw (m + 1) (countableChainOfBall hw m)).choose_spec.1.out.choose_spec.1⟩

/--
The closed balls along `countableChainOfBall` form a nested (antitone) chain.

If any two balls of the family `S` intersect (`hS'`), then in the ultrametric setting each ball of
the chain is contained in its predecessor, because a ball of smaller radius that meets a larger one
is contained in it. This supplies the antitone hypothesis needed to apply spherical completeness to
the chain.
-/
private lemma antitone_of_countableChainOfBall {α : Type*}
    [PseudoMetricSpace α] [iud : IsUltrametricDist α]
    [SphericallyCompleteSpace α]
    {S : Set (α × NNReal)} [hS : Nonempty S]
    (hS' : ∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty)
    (hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2) :
    Antitone (fun n ↦ closedBall
    (countableChainOfBall hw n).val.1
    (countableChainOfBall hw n).val.2) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  apply IsUltrametricDist.closedBall_subset_closedBall_of_le_radius_of_nonempty_inter
  · conv => arg 1; unfold countableChainOfBall
    rw [((smaller_radius hw (n + 1)
      (countableChainOfBall hw n))).choose_spec.1.out.choose_spec.2]
    refine le_trans (le_of_lt ((smaller_radius hw (n + 1)
      (countableChainOfBall hw n))).choose_spec.2) ?_
    simp only [inf_le_right]
  · apply hS'

/--
The chain `countableChainOfBall` is cofinal among the balls of `S`.

For every `s ∈ S` there is an index `n` with
`closedBall (chain n).1 (chain n).2 ⊆ closedBall s.1 s.2`: since the chain radii converge to
`sInf {radii}` (strictly below `s.2` by `hw`), some chain ball has radius below `s.2`, and pairwise
intersection (`hS'`) then forces containment. Consequently a point common to the whole chain lies
in every ball of `S`, which is what turns the chain's nonempty intersection into the pairwise
characterization of spherical completeness.
-/
private lemma cofinal_of_countableChainOfBall {α : Type*}
    [PseudoMetricSpace α] [IsUltrametricDist α]
    [SphericallyCompleteSpace α]
    {S : Set (α × NNReal)} [hS : Nonempty S]
    (hS' : ∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty)
    (hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2) : ∀ s ∈ S, ∃ n : ℕ, closedBall
    (countableChainOfBall hw n).val.1
    (countableChainOfBall hw n).val.2 ⊆ closedBall s.1 s.2 := by
  intro s hs
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one (tsub_pos_of_lt (hw s hs)) (by norm_num : (1 / 2 : NNReal) < 1)
  replace hn := lt_tsub_iff_left.mp (by rwa [div_pow, one_pow] at hn)
  use n
  apply IsUltrametricDist.closedBall_subset_closedBall_of_le_radius_of_nonempty_inter
  · refine le_of_lt <| lt_of_le_of_lt ?_ hn
    conv => arg 1; unfold countableChainOfBall
    cases n
    · rw [(smaller_radius hw 0 hS.some).choose_spec.1.out.choose_spec.2]
      exact le_of_lt <| lt_of_lt_of_le (smaller_radius hw 0 hS.some).choose_spec.2 inf_le_left
    · expose_names
      rw [(smaller_radius hw (n + 1)
        (countableChainOfBall hw n)).choose_spec.1.out.choose_spec.2]
      exact le_of_lt <| lt_of_lt_of_le (smaller_radius hw (n + 1)
        (countableChainOfBall hw n)).choose_spec.2 inf_le_left
  · exact hS' (countableChainOfBall hw n) ⟨s, hs⟩

section
variable (α : Type*) [PseudoMetricSpace α] [iud : IsUltrametricDist α]

/--
Characterization of spherical completeness using only pairwise intersection of closed balls.

Let `α` be a pseudo-metric space whose distance is ultrametric (`[IsUltrametricDist α]`).
This theorem states that `α` is spherically complete if and only if the following
finite-intersection-type condition holds:

For every nonempty family `S : Set (α × NNReal)` of centers and radii, if any two closed balls
from the family intersect (i.e. for all `w1 w2 : S`, the set
`closedBall w1.1 w1.2 ∩ closedBall w2.1 w2.2` is nonempty), then the intersection of the entire
family is nonempty:
`(⋂ w : S, closedBall w.1 w.2).Nonempty`.

In contrast to the usual definition of spherical completeness (often phrased in terms of chains
of nested balls), this formulation replaces nesting by a pairwise intersection hypothesis,
which is sufficient in the ultrametric setting.
-/
theorem iff_pairwise_inter_nonempty :
    SphericallyCompleteSpace α ↔ (
    ∀ S : Set (α × NNReal), S.Nonempty →
    (∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty) →
    (⋂ w : ↑S, closedBall w.val.1 w.val.2).Nonempty) := by
  refine ⟨fun h S hSne h'↦ ?_, fun h ↦ { nonempty_iInter_of_antitone := ?_ }⟩
  · if hw : ∃ w ∈ S, w.2 = sInf {w.2 | w ∈ S} then
      rcases hw with ⟨w, hwS, hwr⟩
      have : ∀ w' ∈ S, closedBall w.1 w.2 ⊆ closedBall w'.1 w'.2 := by
        intro w' hw'
        apply IsUltrametricDist.closedBall_subset_closedBall_of_le_radius_of_nonempty_inter
        · rw [hwr]
          refine csInf_le' ?_
          simp only [Prod.exists, exists_eq_right, Set.mem_setOf_eq]
          use w'.1
        · exact h' ⟨w,hwS⟩ ⟨w',hw'⟩
      use w.1
      simp only [Set.iInter_coe_set, Set.mem_iInter]
      exact fun v hv ↦ this v hv (mem_closedBall_self NNReal.zero_le_coe)
    else
      push Not at hw
      replace hw : ∀ w ∈ S, sInf {x | ∃ w ∈ S, w.2 = x} < w.2 := by
        refine fun w hw' ↦ lt_of_le_of_ne (csInf_le' ?_) <| Ne.symm <| hw w hw'
        simp only [Prod.exists, exists_eq_right, Set.mem_setOf_eq]
        use w.1
      haveI := Set.Nonempty.to_subtype hSne
      rcases h.nonempty_iInter_of_antitone (antitone_of_countableChainOfBall h' hw) with ⟨u, hu⟩
      use u
      simp only [Set.mem_iInter] at *
      intro s
      rcases cofinal_of_countableChainOfBall h' hw s s.prop with ⟨n, hn⟩
      exact hn <| hu n
  · intro c r hanti
    specialize h {(c i, r i) | (i : ℕ)} (by
      use (c 0, r 0), 0
      ) (by
      intro w1 w2
      rcases w1.prop with ⟨i1, hi1⟩
      rcases w2.prop with ⟨i2, hi2⟩
      simp only [Set.mem_setOf_eq, ← hi1, ← hi2]
      rcases le_total i1 i2 with hi | hi
      · rw [Set.inter_eq_self_of_subset_right <| hanti hi]
        exact nonempty_closedBall.mpr NNReal.zero_le_coe
      · rw [Set.inter_eq_self_of_subset_left <| hanti hi]
        exact nonempty_closedBall.mpr NNReal.zero_le_coe)
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.nonempty_iInter] at h
    rcases h with ⟨z, hz⟩
    exact ⟨z, Set.mem_iInter.2 <| fun i ↦ hz ⟨(c i, r i), i, rfl⟩⟩

open List in
/--
The equivalent characterizations of spherical completeness, bundled as a `TFAE` list.

For an ultrametric pseudometric space the following are equivalent:
1. `SphericallyCompleteSpace α` (every nested family of closed balls meets);
2. the intersection property for nested balls with *antitone* radii;
3. the intersection property for nested balls with *strictly decreasing* radii;
4. the pairwise-intersection property for an arbitrary family of closed balls.

This packages `iff_antitone_radius`,
`iff_strictAnti_radius` and
`iff_pairwise_inter_nonempty` into a single statement, so that any one
form can be obtained from any other via `List.TFAE.out`.
-/
theorem tfae :
    TFAE [
    SphericallyCompleteSpace α,
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    Antitone ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty,
    ∀ ⦃ci : ℕ → α⦄, ∀ ⦃ri : ℕ → NNReal⦄,
    StrictAnti ri →
    Antitone (fun i ↦ closedBall (ci i) (ri i)) → (⋂ i, closedBall (ci i) (ri i)).Nonempty,
    ∀ S : Set (α × NNReal), S.Nonempty →
    (∀ w1 w2 : ↑S, (closedBall w1.val.1 w1.val.2 ∩ closedBall w2.val.1 w2.val.2).Nonempty) →
    (⋂ w : ↑S, closedBall w.val.1 w.val.2).Nonempty
    ] := by
  tfae_have 1 ↔ 2 := iff_antitone_radius α
  tfae_have 1 ↔ 3 := iff_strictAnti_radius α
  tfae_have 1 ↔ 4 := iff_pairwise_inter_nonempty α
  tfae_finish

end

/--
`SphericallyCompleteSpace` is stable under binary products.

This instance equips `E × F` with a `SphericallyCompleteSpace` structure assuming both
factors `E` and `F` are spherically complete pseudo-metric spaces.
-/
instance _root_.Prod.sphericallyCompleteSpace {E F : Type*}
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    [hse : SphericallyCompleteSpace E] [hsf : SphericallyCompleteSpace F] :
    SphericallyCompleteSpace (E × F) where
  nonempty_iInter_of_antitone := by
    intro ci ri hanti
    have hE : Antitone (fun i ↦ closedBall (ci i).1 (ri i)) := fun m n hmn x hx ↦ by
      have h2 := hanti hmn (show (x, (ci n).2) ∈ closedBall (ci n) (ri n) by
        simpa [Prod.dist_eq, sup_le_iff, mem_closedBall] using hx)
      simp only [mem_closedBall, Prod.dist_eq, sup_le_iff] at h2 ⊢
      exact h2.1
    have hF : Antitone (fun i ↦ closedBall (ci i).2 (ri i)) := fun m n hmn x hx ↦ by
      have h2 := hanti hmn (show ((ci n).1, x) ∈ closedBall (ci n) (ri n) by
        simpa [Prod.dist_eq, sup_le_iff, mem_closedBall] using hx)
      simp only [mem_closedBall, Prod.dist_eq, sup_le_iff] at h2 ⊢
      exact h2.2
    replace hE := hse.nonempty_iInter_of_antitone hE
    replace hF := hsf.nonempty_iInter_of_antitone hF
    simp only [Set.nonempty_iInter, mem_closedBall, Prod.exists] at *
    obtain ⟨xE, hxE⟩ := hE
    obtain ⟨xF, hxF⟩ := hF
    use xE, xF
    intro n
    simpa only [Prod.dist_eq, sup_le_iff] using ⟨hxE n, hxF n⟩

open Classical in
/--
A finite product of spherically complete pseudometric spaces is spherically complete.

More precisely, if `ι` is a finite index type and each component space `E i` is a
`PseudoMetricSpace` equipped with an instance of `SphericallyCompleteSpace`, then the
dependent function space `∀ i, E i` inherits a `SphericallyCompleteSpace` structure
(with the usual `Pi` pseudometric structure coming from the components).

This instance is intended for use with finite products; the `Fintype ι` assumption is
essential in typical proofs of spherical completeness for `Pi`-types.
-/
instance _root_.Pi.sphericallyCompleteSpace {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, PseudoMetricSpace (E i)]
    [hh : ∀ i, SphericallyCompleteSpace (E i)] :
    SphericallyCompleteSpace (∀ i, E i) where
  nonempty_iInter_of_antitone := by
    intro ci ri hanti
    have hE : ∀ i, Antitone (fun n ↦ closedBall (ci n i) (ri n)) := by
      intro i m n hmn
      simp only [Set.le_eq_subset]
      specialize hanti hmn
      simp only [Set.le_eq_subset] at hanti
      rw [closedBall_pi, closedBall_pi] at hanti
      · intro z hz
        let Z : ((i : ι) → E i) := fun (j : ι) ↦ if hij : j = i then hij ▸ z else (ci n j)
        have : Z ∈ (Set.univ.pi fun b ↦ closedBall (ci n b) ↑(ri n)) := by
          simp only [Z, Set.mem_pi, Set.mem_univ]
          intro j _
          if hij : j = i then
            simp only [hij, ↓reduceDIte]
            cases hij
            simpa only [mem_closedBall, dist_le_coe] using hz
          else
            simp only [hij, ↓reduceDIte, mem_closedBall, dist_self, NNReal.zero_le_coe]
        specialize hanti this
        simp only [Set.mem_pi, Set.mem_univ, forall_const] at hanti
        specialize hanti i
        unfold Z at hanti
        simpa only [↓reduceDIte] using hanti
      · exact (ri m).prop
      · exact (ri n).prop
    use fun i ↦ ((hh i).nonempty_iInter_of_antitone (hE i)).choose
    simp only [Set.mem_iInter]
    intro i
    rw [closedBall_pi]
    · simp only [Set.mem_pi, Set.mem_univ, forall_const]
      intro j
      exact Set.mem_iInter.1 ((hh j).nonempty_iInter_of_antitone (hE j)).choose_spec i
    · exact (ri i).prop

/-- The one-point space `PUnit` is spherically complete. Being trivially proper (its closed balls
are compact), it inherits spherical completeness from
`instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpacePUnit : SphericallyCompleteSpace PUnit := inferInstance

/-- The complex numbers `ℂ` are spherically complete. As a finite-dimensional normed field `ℂ` is
proper (closed balls are compact), so spherical completeness follows from
`instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpaceComplex : SphericallyCompleteSpace ℂ := inferInstance

/-- The real numbers `ℝ` are spherically complete. Being locally compact, hence proper, `ℝ` inherits
spherical completeness from `instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpaceReal : SphericallyCompleteSpace ℝ := inferInstance

/-- For a prime `p`, the field of `p`-adic numbers `ℚ_[p]` is spherically complete. `ℚ_[p]` is
locally compact, hence proper, so its closed balls are compact and spherical completeness follows
from `instSphericallyCompleteSpaceOfProperSpace`. -/
instance instSphericallyCompleteSpacePadic {p : ℕ} [Fact (Nat.Prime p)] :
    SphericallyCompleteSpace (ℚ_[p]) := inferInstance

end SphericallyCompleteSpace
