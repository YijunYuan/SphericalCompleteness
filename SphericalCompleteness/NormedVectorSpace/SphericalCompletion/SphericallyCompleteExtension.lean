/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Order.Group.DenselyOrdered
public import SphericalCompleteness.External.Ultrametric
public import SphericalCompleteness.NormedVectorSpace.Basic
public import SphericalCompleteness.NormedVectorSpace.Quotient

/-!
# Spherically complete extensions

This file exhibits, for an arbitrary normed `𝕜`-vector space `E`, a linear isometric embedding of
`E` into a *spherically complete* ultrametric normed space. This is the starting point of the
spherical completion construction: it realises every normed space inside a spherically complete one,
so that a maximal immediate extension can subsequently be carved out.

The ambient spherically complete space is a quotient of an `ℓ∞`-type space. Given a family of
ultrametric normed spaces `E : ℕ → Type*`, the space `lp E ⊤` of bounded sequences carries the
submodule `c₀ 𝕜 E` of sequences tending to `0` in norm, and the quotient `lp E ⊤ ⧸ c₀ 𝕜 E` is shown
to be spherically complete (`sphericallyCompleteSpace_lp_quotient_c₀`). Specialising to the constant
family `fun _ ↦ E`, the constant-sequence map `x ↦ [x, x, …]` gives the desired embedding
`sphericallyCompleteExtension 𝕜 E`.

## Main definitions

* `c₀ 𝕜 E` — the submodule of null sequences inside `lp E ⊤`.
* `sphericallyCompleteExtension 𝕜 E` — the isometric embedding of `E` into `lp E ⊤ ⧸ c₀ 𝕜 E`.

## Main statements

* `sphericallyCompleteSpace_lp_quotient_c₀` — the quotient `lp E ⊤ ⧸ c₀ 𝕜 E` is spherically
  complete.
-/

@[expose] public section

open Metric

namespace SphericallyCompleteSpace

/-!
## The submodule `c₀`

In the `ℓ∞`-type space `lp E ⊤`, the submodule `c₀ 𝕜 E` consists of those bounded
sequences `f` with values in `E n` that *tend to `0` in norm*, i.e.

`∀ ε > 0, ∃ N, ∀ n ≥ N, ‖f n‖ ≤ ε`.

This is the natural analogue of the classical Banach space `c₀` of scalar-valued
sequences, but for a family of normed spaces `E : ℕ → Type*`.
-/

/-- The submodule `c₀ 𝕜 E` of `lp E ⊤` consisting of the bounded sequences that tend to `0` in
norm: `∀ ε > 0, ∃ N, ∀ n ≥ N, ‖f n‖ ≤ ε`. Quotienting `lp E ⊤` by `c₀` glues together sequences
with the same asymptotic behaviour; this quotient is the spherically complete space into which
`sphericallyCompleteExtension` embeds an arbitrary normed space. -/
def c₀ (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : Submodule 𝕜 ↥(lp E ⊤) where
  carrier := {f : lp E ⊤ | ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, ‖f n‖ ≤ ε}
  add_mem' := by
    intro a b ha hb
    simp only [ge_iff_le, Set.mem_setOf_eq, AddSubgroup.coe_add] at *
    intro ε hε
    rcases ha (ε / 2) (by linarith) with ⟨Na, hNa⟩
    rcases hb (ε / 2) (by linarith) with ⟨Nb, hNb⟩
    use Na + Nb
    intro n hn
    specialize hNa n (by linarith)
    specialize hNb n (by linarith)
    refine le_trans (norm_add_le _ _) ?_
    linarith
  zero_mem' := fun e he ↦ ⟨0, fun n _ ↦ by simp [he.le]⟩
  smul_mem' := by
    intro c x hx
    if hc : c = 0 then
      simp only [gt_iff_lt, ge_iff_le, hc, zero_smul, Set.mem_setOf_eq, ZeroMemClass.coe_zero]
      exact fun e he ↦ ⟨0, fun n _ ↦ by simp [he.le]⟩
    else
    simp only [gt_iff_lt, ge_iff_le, Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply] at *
    intro ε hε
    rcases hx (ε / ‖c‖) (by
      simp_all only [norm_pos_iff, ne_eq, not_false_eq_true, div_pos_iff_of_pos_left]
      ) with ⟨N, hN⟩
    use N
    intro n hn
    rw [norm_smul]
    exact (le_mul_inv_iff₀' <| norm_pos_iff.mpr hc).mp <| hN n hn

/-- Inductive step for lifting a nested family of balls to coherent representatives. Given a
strictly decreasing radius sequence `r`, an antitone family of closed balls
`closedBall (c i) (r i)` in the quotient `lp E ⊤ ⧸ c₀ 𝕜 E`, and a representative `aip1` of the
center `c (i + 1)`, this produces a representative `aip2` of the next center `c (i + 2)` whose
distance to `aip1` is controlled: `‖aip2 - aip1‖ < r i`. Iterating this step (see
`quotientMkSection`) yields a sequence of lifts whose successive differences shrink like `r`, which
is what lets a diagonal sequence be assembled in `lp E ⊤`. -/
private lemma exists_norm_sub_lt {𝕜 : Type*} [inst : NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
    [∀ (i : ℕ), IsUltrametricDist (E i)]
    {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i))
    (i : ℕ) (aip1 : ↥(lp E ⊤)) (hai : (QuotientAddGroup.mk' _) aip1 = c (i + 1)) :
    ∃ (aip2 : ↥(lp E ⊤)), (QuotientAddGroup.mk' _) aip2 = c (i + 2) ∧
    ‖aip2 - aip1‖ < ↑(r i) := by
  have : ‖c (i + 2) - c (i + 1)‖ < ↑(r i) := by
    refine lt_of_le_of_lt ?_ <| hsr <| Nat.lt_add_one i
    rw [← dist_eq_norm, ← mem_closedBall]
    refine (hanti (Nat.le_succ (i + 1))) ?_
    simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
  have hnorm :
      ‖(QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ((c (i + 2) - c (i + 1)).out)‖ < ↑(r i) := by
    have hout :
        (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ((c (i + 2) - c (i + 1)).out) =
          c (i + 2) - c (i + 1) := Quotient.out_eq' _
    rw [hout]
    exact this
  rw [quotient_norm_mk_eq (c₀ 𝕜 E).toAddSubgroup ((c (i + 2) - c (i + 1)).out)] at hnorm
  rw [csInf_lt_iff] at hnorm
  · rcases hnorm with ⟨unp1, hlun, hens1⟩
    rw [Set.mem_image] at hlun
    rcases hlun with ⟨lun, hlun, hlun_eq⟩
    rw [← hlun_eq] at hens1
    use (c (i + 2) - c (i + 1)).out + lun + aip1
    constructor
    · let q1 : ↥(lp E ⊤) ⧸ (c₀ 𝕜 E).toAddSubgroup := c (i + 2)
      let q2 : ↥(lp E ⊤) ⧸ (c₀ 𝕜 E).toAddSubgroup := c (i + 1)
      have hai' : (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) aip1 = q2 := hai
      have hout :
          (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup)
              ((c (i + 2) - c (i + 1)).out) = q1 - q2 := by
        change (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ((c (i + 2) - c (i + 1)).out) =
          (c (i + 2) - c (i + 1) : ↥(lp E ⊤) ⧸ (c₀ 𝕜 E).toAddSubgroup)
        exact Quotient.out_eq' _
      have hmk :
          (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ((c (i + 2) - c (i + 1)).out + lun + aip1) =
            (q1 - q2) +
              (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) lun +
              (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) aip1 := by
        calc
          (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ((c (i + 2) - c (i + 1)).out + lun + aip1)
              = (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ((c (i + 2) - c (i + 1)).out) +
                  (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) lun +
                  (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) aip1 := by
                    simp [add_assoc]
          _ = (q1 - q2) +
                (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) lun +
                (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) aip1 := by rw [hout]
      have hlun' : (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) lun = 0 :=
        (QuotientAddGroup.eq_zero_iff lun).mpr hlun
      rw [hmk, hlun', hai']
      abel
    · simp only [add_sub_cancel_right, hens1]
  · use 0
    refine mem_lowerBounds.mpr ?_
    intro x hx
    simp only [Set.mem_image, SetLike.mem_coe, Subtype.exists] at hx
    rw [← hx.choose_spec.choose_spec.2]
    exact lp.norm_nonneg' _
  · exact Set.Nonempty.of_subtype

/-- A coherent choice of representatives for a nested family of balls in the quotient
`lp E ⊤ ⧸ c₀ 𝕜 E`. For each index `k`, `quotientMkSection E hsr hanti k` is an element of `lp E ⊤`
whose class modulo `c₀ 𝕜 E` is the center `c k`. The representatives for `k = 0, 1` are arbitrary
`Quotient.out` lifts, and each subsequent representative is chosen by `exists_norm_sub_lt` so that
its distance to the previous one is smaller than `r (k - 2)`. This recursively defined section is
the source of the diagonal sequence used to prove spherical completeness of the quotient. -/
private noncomputable def quotientMkSection {𝕜 : Type*} [inst : NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
    [∀ (i : ℕ), IsUltrametricDist (E i)]
    {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i)) :
    (k : ℕ) → {z : ↥(lp E ⊤) // (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) z = c k} := fun n ↦
  match n with
  | 0 => ⟨(c 0).out, Quotient.out_eq' (c 0)⟩
  | 1 => ⟨(c 1).out, Quotient.out_eq' (c 1)⟩
  | m + 2 =>
      ⟨(exists_norm_sub_lt E hsr hanti m
            (quotientMkSection E hsr hanti (m + 1)).val
            (quotientMkSection E hsr hanti (m + 1)).prop).choose,
        (exists_norm_sub_lt E hsr hanti m
            (quotientMkSection E hsr hanti (m + 1)).val
            (quotientMkSection E hsr hanti (m + 1)).prop).choose_spec.1⟩

/-- The two defining properties of `quotientMkSection`, packaged together. For every index `i`:

* `(quotientMkSection E hsr hanti i)` really is a representative of the center `c i`, i.e. its class
  in `lp E ⊤ ⧸ c₀ 𝕜 E` is `c i`; and
* consecutive representatives are close, `‖section (i + 2) - section (i + 1)‖ < r i`.

These are read off directly from the recursive construction and the guarantee provided by
`exists_norm_sub_lt`. -/
private lemma mk_eq_and_norm_sub_lt {𝕜 : Type*} [inst : NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
    [∀ (i : ℕ), IsUltrametricDist (E i)]
    {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i))
    : ∀ i : ℕ,
      (QuotientAddGroup.mk' _) (quotientMkSection E hsr hanti i).1 = c i ∧
        ‖(quotientMkSection E hsr hanti (i + 2)).1 -
        (quotientMkSection E hsr hanti (i + 1)).1‖ < ↑(r i) := by
  intro m
  refine ⟨(quotientMkSection E hsr hanti m).prop, ?_⟩
  simp only [QuotientAddGroup.mk'_apply, quotientMkSection]
  exact
    (exists_norm_sub_lt E hsr hanti m
          (quotientMkSection E hsr hanti (m + 1)).val
          (quotientMkSection E hsr hanti (m + 1)).prop).choose_spec.2

/-- A uniform bound on the diagonal entries of the representatives `quotientMkSection`. For every
`n`, the `n`-th coordinate of the `n`-th representative is bounded, in the ultrametric sense, by
`max ‖section 0‖ (max ‖section 1‖ (r 0))`, independently of `n`. This uniform bound is exactly what
guarantees that the diagonal sequence `fun n ↦ (quotientMkSection E hsr hanti n).val n` is bounded
and hence defines an element of `lp E ⊤`. The proof telescopes `section n - section 1` through the
consecutive differences controlled by `mk_eq_and_norm_sub_lt` and uses the strong (ultrametric)
triangle inequality. -/
private lemma quotientMkSection_norm_apply_self_le_max {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
    [iiud : ∀ (i : ℕ), IsUltrametricDist (E i)]
    ⦃c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E⦄ ⦃r : ℕ → NNReal⦄ (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
    ∀ (n : ℕ), ‖((quotientMkSection E hsr hanti n).val : (i : ℕ) → E i) n‖ ≤
    max ‖(quotientMkSection E hsr hanti 0).val‖
    (max ‖(quotientMkSection E hsr hanti 1).val‖ ↑(r 0)) := by
  intro n
  have : ‖((quotientMkSection E hsr hanti n).val: (i : ℕ) → E i) n‖ ≤
    ‖(quotientMkSection E hsr hanti n).val‖ := by
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero
  refine le_trans this ?_
  if hn : n = 0 then
    rw [hn]
    simp only [le_sup_left]
  else
  apply le_max_of_le_right
  have : (quotientMkSection E hsr hanti n).val =
    (quotientMkSection E hsr hanti n).val - (quotientMkSection E hsr hanti 1).val +
    (quotientMkSection E hsr hanti 1).val := by abel
  rw [this, add_comm]
  refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _) ?_
  apply max_le_max (le_refl _)
  induction n with
  | zero =>
    simp only [not_true_eq_false] at hn
  | succ m ih =>
    if hm : m = 0 then
      rw [hm]
      simp only [QuotientAddGroup.mk'_apply, Nat.reduceAdd, sub_self, norm_zero, NNReal.zero_le_coe]
    else
    simp only [QuotientAddGroup.mk'_apply, hm, not_false_eq_true, sub_add_cancel,
      forall_const] at ih
    specialize ih (by apply lp.norm_apply_le_norm ENNReal.top_ne_zero)
    rw [← sub_add_sub_cancel _ (quotientMkSection E hsr hanti m).val _]
    refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _) ?_
    refine max_le (le_trans (le_of_lt ?_) <| hsr.antitone <| Nat.zero_le (m - 1)) ih
    have := (mk_eq_and_norm_sub_lt E hsr hanti (m - 1)).2
    rwa [(by omega : m - 1 + 2 = m + 1), (by omega : m - 1 + 1 = m)] at this

/-- An eventual coordinatewise bound descends to a bound on the quotient norm. If `A : lp E ⊤`
satisfies `‖A n‖ ≤ C` for all `n ≥ N` (with `C > 0`), then the norm of its class in
`lp E ⊤ ⧸ c₀ 𝕜 E` is at most `C`. The point is that the finitely many early coordinates `n < N`,
which are unconstrained, can be cancelled by subtracting a suitable null sequence in `c₀ 𝕜 E`, so
they do not affect the quotient norm; the remaining coordinates already obey the bound `C`. This is
the estimate used to show the assembled diagonal element lies in every ball of the nested family. -/
lemma quotient_norm_mk_le_of_eventually_norm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
    [∀ (i : ℕ), IsUltrametricDist (E i)]
    (A : lp E ⊤) (C : ℝ) (hC : C > 0)
    (N : ℕ) (hN : ∀ n ≥ N, ‖A n‖ ≤ C)
    :
    ‖(QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) A‖ ≤ C
    := by
  rw [quotient_norm_mk_eq]
  let u : ∀ i, E i := fun i ↦
    if _ : i < N then - (A i)
    else 0
  have hu_mem1 : ↑(u) ∈ lp E ⊤ := by
    simp only [dite_eq_ite, u]
    apply memℓp_infty
    use (memℓp_infty_iff.1 A.prop).some
    have := mem_upperBounds.1 (memℓp_infty_iff.1 A.prop).some_mem
    apply mem_upperBounds.2
    intro z hz
    simp only [Set.mem_range] at hz
    rcases hz with ⟨i, hi⟩
    rw [← hi]
    by_cases hiN : i < N
    · simpa only [hiN, ↓reduceIte, norm_neg] using this ‖A i‖ (by simp)
    · simpa only [hiN, ↓reduceIte, norm_zero] using
      le_trans (norm_nonneg _) <| this ‖A 0‖ (by simp)
  have hu_mem2 : ⟨u, hu_mem1⟩ ∈ (c₀ 𝕜 E) := by
    simp only [c₀, gt_iff_lt, ge_iff_le, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    intro ε hε
    use N
    intro n hn
    simpa only [dite_eq_ite, Nat.not_lt.mpr hn, ↓reduceIte, norm_zero, u] using le_of_lt hε
  have : sInf ((fun x ↦ ‖A + x‖) '' ↑(c₀ 𝕜 E).toAddSubgroup) ≤ ‖A + ⟨u, hu_mem1⟩‖ := by
    apply csInf_le
    · refine ⟨0, mem_lowerBounds.2 <| fun x hx ↦ ?_⟩
      simp only [Submodule.coe_toAddSubgroup, Set.mem_image, SetLike.mem_coe, Subtype.exists] at hx
      rw [← hx.choose_spec.choose_spec.2]
      exact norm_nonneg _
    · rw [Set.mem_image]
      exact ⟨⟨u, hu_mem1⟩, ⟨hu_mem2, rfl⟩⟩
  refine le_trans this ?_
  rw [lp.norm_eq_ciSup]
  refine ciSup_le <| fun k ↦ ?_
  simp only [dite_eq_ite, AddSubgroup.coe_add, u]
  if hk : k < N then
    simp [if_pos hk, hC.le]
  else
    simpa [if_neg hk] using hN k (Nat.le_of_not_lt hk)

/--
The quotient `lp E ⊤ ⧸ c₀ 𝕜 E` is spherically complete whenever each `E i` is ultrametric.

This is the concrete source of spherically complete spaces used to build spherical completions:
`lp E ⊤` is the `ℓ∞`-type space of bounded sequences, and killing the null sequences `c₀ 𝕜 E`
makes nested families of closed balls meet. Given such a family, one lifts it to representatives
in `lp E ⊤` (via `quotientMkSection`), assembles a diagonal candidate sequence, and checks it lies
in every ball using the ultrametric estimates and a `c₀`-correction.
-/
instance sphericallyCompleteSpace_lp_quotient_c₀ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] [∀ i, IsUltrametricDist (E i)] :
    SphericallyCompleteSpace ((lp E ⊤)⧸ c₀ 𝕜 E) := by
  rw [iff_strictAnti_radius]
  intro c r hsr hanti
  let f : ∀ i, E i := fun i ↦ (quotientMkSection E hsr hanti i).val i
  have hf_mem : ↑(f) ∈ lp E ⊤ := by
    simp only [lp, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, f]
    refine memℓp_infty <| bddAbove_def.mpr ?_
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    use max ‖(quotientMkSection E hsr hanti 0).val‖
      (max ‖(quotientMkSection E hsr hanti 1).val‖ (r 0))
    exact fun n ↦ quotientMkSection_norm_apply_self_le_max E hsr hanti n
  let x : (lp E ⊤) ⧸ c₀ 𝕜 E :=
    (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ⟨f, hf_mem⟩
  use x
  have : ∀ n ≥ 1, ‖x - c (n + 1)‖ ≤ r n := by
    unfold x
    intro n hn
    rw [← (mk_eq_and_norm_sub_lt E hsr hanti (n + 1)).1]
    change ‖(QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup)
      (⟨f, hf_mem⟩ - ↑(quotientMkSection E hsr hanti (n + 1)))‖ ≤ ↑(r n)
    have := @quotient_norm_mk_le_of_eventually_norm_le 𝕜 _ E _ _ _
      (⟨f, hf_mem⟩ - ↑(quotientMkSection E hsr hanti (n + 1))) (r n).val ?_ (n + 1) ?_
    · exact this
    · exact lt_of_le_of_lt (r (n + 1)).prop <| hsr <| lt_add_one n
    · intro m hm
      simp only [QuotientAddGroup.mk'_apply, AddSubgroupClass.coe_sub,
        NNReal.val_eq_coe, f]
      have h : ‖(quotientMkSection E hsr hanti m).val -
        (quotientMkSection E hsr hanti (n + 1)).val‖
        ≤ (r n).val := by
        induction m with
        | zero => linarith
        | succ k hk =>
          if hkn : k = n then
            rw [hkn]
            simp only [QuotientAddGroup.mk'_apply, sub_self, norm_zero, NNReal.val_eq_coe,
              NNReal.zero_le_coe]
          else
          specialize hk (by omega)
          rw [← sub_add_sub_cancel _ (quotientMkSection E hsr hanti k).val _]
          refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _) ?_
          apply max_le ?_ hk
          have := (mk_eq_and_norm_sub_lt E hsr hanti (k - 1)).2
          rw [(by omega : k - 1 + 2 = k + 1), (by omega : k - 1 + 1 = k)] at this
          exact le_of_lt <| lt_of_lt_of_le this <| hsr.antitone <| by omega
      refine le_trans ?_ h
      simpa [f] using lp.norm_apply_le_norm ENNReal.top_ne_zero
        ((quotientMkSection E hsr hanti m).val -
          (quotientMkSection E hsr hanti (n + 1)).val) m
  simp only [Set.mem_iInter]
  suffices h : ∀ i ≥ 1, x ∈ closedBall (c i) (r i) by
    exact fun i ↦ (hanti <| Nat.le_add_right i 1) <| h (i + 1) (Nat.le_add_left 1 i)
  intro i hi
  specialize this i hi
  rw [mem_closedBall, dist_eq_norm, ← sub_add_sub_cancel _ (c (i + 1)) _]
  refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤ ⧸ c₀ 𝕜 E)).norm_add_le_max _ _) ?_
  apply max_le this
  rw [← dist_eq_norm, ← mem_closedBall]
  refine (hanti (Nat.le_succ i)) ?_
  simp only [Nat.succ_eq_add_one, mem_closedBall, dist_self, NNReal.zero_le_coe]

/-- A linear isometric embedding of an arbitrary normed `𝕜`-space `E` into a spherically complete
space, namely the constant-sequence map `x ↦ [x, x, x, …]` into `lp (fun _ ↦ E) ⊤ ⧸ c₀ 𝕜 _`.
It is an isometry because the quotient norm of a constant sequence equals `‖x‖`. This realises
every normed space inside a spherically complete one, the first step in constructing the
`SphericalCompletion`. -/
noncomputable def sphericallyCompleteExtension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    E →ₗᵢ[𝕜] ((lp (fun (_ : ℕ) ↦ E) ⊤)⧸ c₀ 𝕜 (fun (_ : ℕ) ↦ E)) where
  toFun x := by
    refine (QuotientAddGroup.mk' (c₀ 𝕜 (fun x ↦ E)).toAddSubgroup) (⟨fun (_ : ℕ) ↦ x, ?_⟩)
    refine memℓp_infty ⟨‖x‖, ?_⟩
    simp only [upperBounds, Set.range_const, Set.mem_singleton_iff, forall_eq, Set.mem_setOf_eq,
      le_refl]
  map_add' x y := rfl
  map_smul' c x := rfl
  norm_map' := by
    intro x
    have hv : (fun (_ : ℕ) ↦ x) ∈ lp (fun (_ : ℕ) ↦ E) ⊤ :=
      memℓp_infty ⟨‖x‖, by
        simp only [upperBounds, Set.range_const, Set.mem_singleton_iff, forall_eq,
          Set.mem_setOf_eq, le_refl]⟩
    let v : lp (fun (_ : ℕ) ↦ E) ⊤ := ⟨fun (_ : ℕ) ↦ x, hv⟩
    change ‖(QuotientAddGroup.mk' (c₀ 𝕜 fun _ ↦ E).toAddSubgroup) v‖ = ‖x‖
    have hvnorm : ‖v‖ = ‖x‖ := by
      rw [lp.norm_eq_ciSup]
      change (⨆ _ : ℕ, ‖x‖) = ‖x‖
      simp
    refine le_antisymm ?_ ?_
    · refine le_trans (Submodule.Quotient.norm_mk_le (S := c₀ 𝕜 fun _ ↦ E) v) ?_
      exact hvnorm.le
    · rw [quotient_norm_mk_eq (c₀ 𝕜 fun _ ↦ E).toAddSubgroup v]
      apply le_csInf
      · refine ⟨‖x‖, ?_⟩
        simp only [Set.mem_image, Submodule.coe_toAddSubgroup, SetLike.mem_coe, Subtype.exists]
        refine ⟨0, zero_mem _, zero_mem _, ?_⟩
        change ‖v + 0‖ = ‖x‖
        rw [add_zero]; exact hvnorm
      · intro b hb
        simp only [Submodule.coe_toAddSubgroup, Set.mem_image, SetLike.mem_coe,
          Subtype.exists] at hb
        rcases hb with ⟨p, hp, hp', h⟩
        rw [← h]
        apply le_of_forall_pos_sub_le
        intro ε hε
        simp only [c₀, gt_iff_lt, ge_iff_le, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hp'
        rcases hp' ε hε with ⟨N, hN⟩
        refine le_trans (?_: _ ≤ ‖x + p N‖) ?_
        · specialize hN N (le_refl N)
          rw [← sub_neg_eq_add x (p N)]
          refine le_trans ?_ (norm_sub_norm_le _ _)
          rw [norm_neg]
          linarith
        · exact lp.norm_apply_le_norm ENNReal.top_ne_zero (v + ⟨p, hp⟩) N

/-- The `NormedAddCommGroup` structure on the quotient `lp (fun _ ↦ E) ⊤ ⧸ c₀ 𝕜 (fun _ ↦ E)`.

A quotient by a submodule only carries a genuine *norm* (rather than a mere seminorm) once the
submodule is topologically closed. This instance supplies the missing ingredient: it proves that the
null-sequence submodule `c₀ 𝕜 (fun _ ↦ E)` is a closed subset of `lp (fun _ ↦ E) ⊤` (via
`IsSeqClosed.isClosed`, using an `ε/2` argument on the `ℓ∞` norm), and then lets typeclass inference
upgrade the quotient seminorm to a `NormedAddCommGroup`. This is what makes
`sphericallyCompleteExtension 𝕜 E` land in a normed—not merely seminormed—space. -/
noncomputable instance (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedAddCommGroup (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) := by
  have : IsClosed (↑(c₀ 𝕜 fun x ↦ E).carrier) := by
    apply IsSeqClosed.isClosed
    simp only [IsSeqClosed, Submodule.carrier_eq_coe, SetLike.mem_coe, Subtype.forall]
    intro seq lim hlim hseq htend
    rw [NormedAddCommGroup.tendsto_atTop] at htend
    intro ε hε
    specialize htend (ε / 2) (by linarith)
    rcases htend with ⟨N, hN⟩
    specialize hN N (le_refl N)
    rw [lp.norm_eq_ciSup] at hN
    specialize hseq N
    simp only [c₀, gt_iff_lt, ge_iff_le, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hseq
    specialize hseq (ε / 2) (by linarith)
    rcases hseq with ⟨M, hM⟩
    use M.max N
    intro n hn
    specialize hM n (by simp_all only
      [gt_iff_lt, AddSubgroupClass.coe_sub, ge_iff_le, sup_le_iff])
    have := (ciSup_le_iff (by
      use ‖seq N - ⟨lim, hlim⟩‖
      simp only [upperBounds,  Set.mem_range,
        forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
      intro a
      refine lp.norm_apply_le_norm ?_ (seq N - ⟨lim, hlim⟩) a
      exact ENNReal.top_ne_zero
      )).1 (le_of_lt hN) n
    simp only [AddSubgroupClass.coe_sub] at this
    replace := add_le_add hM this
    have htriangle : ‖lim n‖ ≤ ‖seq N n - lim n‖ + ‖seq N n‖ := by
      calc
        ‖lim n‖ = ‖(lim n - seq N n) + seq N n‖ := by abel_nf
        _ ≤ ‖lim n - seq N n‖ + ‖seq N n‖ := norm_add_le _ _
        _ = ‖seq N n - lim n‖ + ‖seq N n‖ := by rw [norm_sub_rev]
    have hsum : ‖seq N n - lim n‖ + ‖seq N n‖ ≤ ε := by
      simpa [add_comm, add_left_comm, add_assoc, add_halves] using this
    exact le_trans htriangle hsum
  simp only [Submodule.carrier_eq_coe] at this
  infer_instance

/-- Every non-Archimedean (ultrametric) nontrivially normed field `𝕜` embeds into a spherically
complete Banach space over itself: the quotient `lp (fun _ ↦ 𝕜) ⊤ ⧸ c₀ 𝕜 (fun _ ↦ 𝕜)` is
`SphericallyCompleteSpace`. This is the constant-scalar-family specialisation of
`sphericallyCompleteSpace_lp_quotient_c₀`, recorded as an instance so that spherical completeness of
this concrete space is available to typeclass inference. -/
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] :
    SphericallyCompleteSpace ((lp (fun _ ↦ 𝕜) ⊤)⧸ c₀ 𝕜 (fun _ ↦ 𝕜)) := by
  simpa only using sphericallyCompleteSpace_lp_quotient_c₀ (fun _ ↦ 𝕜)

end SphericallyCompleteSpace
