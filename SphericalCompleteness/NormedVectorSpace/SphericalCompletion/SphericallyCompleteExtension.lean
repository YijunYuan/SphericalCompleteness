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
`canonicalSphericallyCompleteExtension 𝕜 E`.

## Main definitions

* `c₀ 𝕜 E` — the submodule of null sequences inside `lp E ⊤`.
* `canonicalSphericallyCompleteExtension 𝕜 E` — the isometric embedding of `E` into
  `lp E ⊤ ⧸ c₀ 𝕜 E`.

## Main statements

* `sphericallyCompleteSpace_lp_quotient_c₀` — the quotient `lp E ⊤ ⧸ c₀ 𝕜 E` is spherically
  complete.
-/

@[expose] public section

open Metric Filter Topology

namespace SphericallyCompleteSpace

/-!
## The submodule `c₀`

In the `ℓ∞`-type space `lp E ⊤`, the submodule `c₀ 𝕜 E` consists of those bounded
sequences `f` with values in `E n` that *tend to `0` in norm*, i.e.

`Tendsto (fun n ↦ ‖f n‖) atTop (𝓝 0)`.

This is the natural analogue of the classical Banach space `c₀` of scalar-valued
sequences, but for a family of normed spaces `E : ℕ → Type*`.
-/

/-- The submodule `c₀ 𝕜 E` of `lp E ⊤` consisting of the bounded sequences that tend to `0` in
norm: `Tendsto (fun n ↦ ‖f n‖) atTop (𝓝 0)`. Quotienting `lp E ⊤` by `c₀` glues together sequences
with the same asymptotic behaviour; this quotient is the spherically complete space into which
`canonicalSphericallyCompleteExtension` embeds an arbitrary normed space. -/
def c₀ (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] : Submodule 𝕜 ↥(lp E ⊤) where
  carrier := {f : lp E ⊤ | Tendsto (fun n ↦ ‖f n‖) atTop (𝓝 0)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at *
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ norm_add_le _ _) ?_
    simpa using ha.add hb
  zero_mem' := by
    simpa only [Set.mem_setOf_eq, lp.coeFn_zero, Pi.zero_apply, norm_zero] using tendsto_const_nhds
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, norm_smul] at *
    simpa using hx.const_mul ‖c‖

/-- Inductive step for lifting a nested family of balls to coherent representatives. Given a
strictly decreasing radius sequence `r`, an antitone family of closed balls
`closedBall (c i) (r i)` in the quotient `lp E ⊤ ⧸ c₀ 𝕜 E`, and a representative `aip1` of the
center `c (i + 1)`, this produces a representative `aip2` of the next center `c (i + 2)` whose
distance to `aip1` is controlled: `‖aip2 - aip1‖ < r i`. Iterating this step (see
`quotientMkSection`) yields a sequence of lifts whose successive differences shrink like `r`, which
is what lets a diagonal sequence be assembled in `lp E ⊤`. -/
private lemma exists_norm_sub_lt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
    [∀ (i : ℕ), IsUltrametricDist (E i)]
    {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i))
    (i : ℕ) (aip1 : ↥(lp E ⊤)) (hai : (QuotientAddGroup.mk' _) aip1 = c (i + 1)) :
    ∃ (aip2 : ↥(lp E ⊤)), (QuotientAddGroup.mk' _) aip2 = c (i + 2) ∧
    ‖aip2 - aip1‖ < ↑(r i) := by
  have hlt : ‖c (i + 2) - c (i + 1)‖ < ↑(r i) := by
    refine lt_of_le_of_lt ?_ <| hsr <| Nat.lt_add_one i
    rw [← dist_eq_norm, ← mem_closedBall]
    refine (hanti (Nat.le_succ (i + 1))) ?_
    simp only [mem_closedBall, dist_self, NNReal.zero_le_coe]
  -- A representative `m` of the small difference `c (i + 2) - c (i + 1)` has norm `< r i`; shifting
  -- the known lift `aip1` of `c (i + 1)` by `m` yields the desired lift `aip2 := m + aip1`.
  obtain ⟨m, hm, hmlt⟩ := QuotientAddGroup.norm_lt_iff.1 hlt
  refine ⟨m + aip1, ?_, ?_⟩
  · rw [map_add, hai, QuotientAddGroup.mk'_apply, hm]
    abel
  · simpa only [add_sub_cancel_right] using hmlt

/-- A coherent choice of representatives for a nested family of balls in the quotient
`lp E ⊤ ⧸ c₀ 𝕜 E`. For each index `k`, `quotientMkSection E hsr hanti k` is an element of `lp E ⊤`
whose class modulo `c₀ 𝕜 E` is the center `c k`. The representatives for `k = 0, 1` are arbitrary
`Quotient.out` lifts, and each subsequent representative is chosen by `exists_norm_sub_lt` so that
its distance to the previous one is smaller than `r (k - 2)`. This recursively defined section is
the source of the diagonal sequence used to prove spherical completeness of the quotient. -/
private noncomputable def quotientMkSection {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [∀ i, IsUltrametricDist (E i)]

/-- The two defining properties of `quotientMkSection`, packaged together. For every index `i`:

* `(quotientMkSection E hsr hanti i)` really is a representative of the center `c i`, i.e. its class
  in `lp E ⊤ ⧸ c₀ 𝕜 E` is `c i`; and
* consecutive representatives are close, `‖section (i + 2) - section (i + 1)‖ < r i`.

These are read off directly from the recursive construction and the guarantee provided by
`exists_norm_sub_lt`. -/
private lemma mk_eq_and_norm_sub_lt
    {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i))
    : ∀ i : ℕ,
      (QuotientAddGroup.mk' _) (quotientMkSection E hsr hanti i).1 = c i ∧
        ‖(quotientMkSection E hsr hanti (i + 2)).1 -
        (quotientMkSection E hsr hanti (i + 1)).1‖ < ↑(r i) := by
  refine fun m ↦ ⟨(quotientMkSection E hsr hanti m).prop, ?_⟩
  simp only [QuotientAddGroup.mk'_apply, quotientMkSection]
  exact
    (exists_norm_sub_lt E hsr hanti m
          (quotientMkSection E hsr hanti (m + 1)).val
          (quotientMkSection E hsr hanti (m + 1)).prop).choose_spec.2

/-- A telescoping bound on the representatives `quotientMkSection`. For `1 ≤ a ≤ b`, the difference
between the `b`-th and `a`-th representatives is controlled by the radius `r (a - 1)`:
`‖section b - section a‖ ≤ r (a - 1)`. This follows by telescoping `section b - section a` through
the consecutive differences (each `< r (·)`, from `mk_eq_and_norm_sub_lt`) and applying the strong
(ultrametric) triangle inequality together with the antitonicity of `r`. It is the common engine
behind both the uniform diagonal bound (`quotientMkSection_norm_apply_self_le_max`) and the
`c₀`-descent estimate in `sphericallyCompleteSpace_lp_quotient_c₀`. -/
private lemma norm_quotientMkSection_sub_le
    {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i)) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(quotientMkSection E hsr hanti b).val - (quotientMkSection E hsr hanti a).val‖ ≤
      ↑(r (a - 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak ih =>
    rw [← sub_add_sub_cancel _ (quotientMkSection E hsr hanti k).val _]
    refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _)
      (max_le ?_ ih)
    have hcons := (mk_eq_and_norm_sub_lt E hsr hanti (k - 1)).2
    rw [(by omega : k - 1 + 2 = k + 1), (by omega : k - 1 + 1 = k)] at hcons
    exact le_of_lt <| lt_of_lt_of_le hcons <| hsr.antitone <| by omega

/-- A uniform bound on the diagonal entries of the representatives `quotientMkSection`. For every
`n`, the `n`-th coordinate of the `n`-th representative is bounded, in the ultrametric sense, by
`max ‖section 0‖ (max ‖section 1‖ (r 0))`, independently of `n`. This uniform bound is exactly what
guarantees that the diagonal sequence `fun n ↦ (quotientMkSection E hsr hanti n).val n` is bounded
and hence defines an element of `lp E ⊤`. For `n ≥ 1` it follows by writing `section n` as
`(section n - section 1) + section 1` and bounding the difference via
`norm_quotientMkSection_sub_le`. -/
private lemma quotientMkSection_norm_apply_self_le_max
    ⦃c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E⦄ ⦃r : ℕ → NNReal⦄ (hsr : StrictAnti r)
    (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
    ∀ (n : ℕ), ‖((quotientMkSection E hsr hanti n).val : (i : ℕ) → E i) n‖ ≤
    max ‖(quotientMkSection E hsr hanti 0).val‖
    (max ‖(quotientMkSection E hsr hanti 1).val‖ ↑(r 0)) := by
  intro n
  refine le_trans (lp.norm_apply_le_norm ENNReal.top_ne_zero _ n) ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn]; exact le_sup_left
  refine le_max_of_le_right ?_
  rw [show (quotientMkSection E hsr hanti n).val =
    (quotientMkSection E hsr hanti n).val - (quotientMkSection E hsr hanti 1).val +
    (quotientMkSection E hsr hanti 1).val by abel]
  refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _)
    (max_le (le_max_of_le_right ?_) le_sup_left)
  simpa using norm_quotientMkSection_sub_le E hsr hanti le_rfl hn

/--
The quotient `lp E ⊤ ⧸ c₀ 𝕜 E` is spherically complete whenever each `E i` is ultrametric.

This is the concrete source of spherically complete spaces used to build spherical completions:
`lp E ⊤` is the `ℓ∞`-type space of bounded sequences, and killing the null sequences `c₀ 𝕜 E`
makes nested families of closed balls meet. Given such a family, one lifts it to representatives
in `lp E ⊤` (via `quotientMkSection`), assembles a diagonal candidate sequence, and checks it lies
in every ball using the ultrametric estimates and a `c₀`-correction.
-/
instance sphericallyCompleteSpace_lp_quotient_c₀ :
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
    set A : lp E ⊤ := ⟨f, hf_mem⟩ - ↑(quotientMkSection E hsr hanti (n + 1)) with hA_def
    -- The `m`-th coordinate of `A` is bounded by `r n` for every `m ≥ n + 1`, since it is dominated
    -- by `‖section m - section (n + 1)‖ ≤ r n` (`norm_quotientMkSection_sub_le`).
    have hev : ∀ m ≥ n + 1, ‖A m‖ ≤ (r n : ℝ) := by
      intro m hm
      rw [hA_def]
      simp only [QuotientAddGroup.mk'_apply, AddSubgroupClass.coe_sub, f]
      refine le_trans ?_ (by simpa using norm_quotientMkSection_sub_le E hsr hanti n.succ_pos hm)
      simpa [f] using lp.norm_apply_le_norm ENNReal.top_ne_zero
        ((quotientMkSection E hsr hanti m).val -
          (quotientMkSection E hsr hanti (n + 1)).val) m
    -- The eventual coordinatewise bound descends to the quotient norm: the finitely many early
    -- coordinates `m < n + 1` are cancelled by subtracting the null sequence `u ∈ c₀ 𝕜 E`, and the
    -- remaining coordinates already obey the bound `r n`.
    have hC0 : (0 : ℝ) ≤ (r n : ℝ) := le_trans (norm_nonneg _) (hev (n + 1) le_rfl)
    let u : ∀ i, E i := fun i ↦ if _ : i < n + 1 then - (A i) else 0
    have hu_mem1 : ↑(u) ∈ lp E ⊤ := by
      refine memℓp_infty ⟨‖A‖, ?_⟩
      rw [mem_upperBounds]
      rintro z ⟨i, rfl⟩
      by_cases hiN : i < n + 1 <;> simp only [u, hiN, ↓reduceDIte, norm_neg, norm_zero]
      · exact lp.norm_apply_le_norm ENNReal.top_ne_zero A i
      · exact norm_nonneg _
    let U : lp E ⊤ := ⟨u, hu_mem1⟩
    have hu_mem2 : U ∈ (c₀ 𝕜 E) := by
      refine tendsto_const_nhds.congr' <| Filter.eventually_atTop.2 ⟨n + 1, fun m hm ↦ ?_⟩
      simp only [dite_eq_ite, Nat.not_lt.mpr hm, ↓reduceIte, norm_zero, U, u]
    -- `A` and its `c₀`-correction `A + U` represent the same class, so `‖mk' A‖ = ‖mk' (A + U)‖ ≤
    -- ‖A + U‖`; and `A + U` is bounded by `r n` at every coordinate.
    have hAeq : (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) A =
        (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) (A + U) := by
      have hU0 : (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) U = 0 :=
        (QuotientAddGroup.eq_zero_iff U).2 ((Submodule.mem_toAddSubgroup _).2 hu_mem2)
      rw [map_add, hU0, add_zero]
    rw [hAeq]
    refine le_trans QuotientAddGroup.norm_mk_le_norm ?_
    rw [lp.norm_eq_ciSup]
    refine ciSup_le <| fun k ↦ ?_
    simp only [dite_eq_ite, AddSubgroup.coe_add, U, u]
    if hk : k ≤ n then
      simp [if_pos hk, hC0]
    else
      simpa [if_neg hk] using hev k (by omega)
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

end

/-- A linear isometric embedding of an arbitrary normed `𝕜`-space `E` into a spherically complete
space, namely the constant-sequence map `x ↦ [x, x, x, …]` into `lp (fun _ ↦ E) ⊤ ⧸ c₀ 𝕜 _`.
It is an isometry because the quotient norm of a constant sequence equals `‖x‖`. This realises
every normed space inside a spherically complete one — the first step in constructing a spherical
completion of `E`, from which a maximal immediate extension is subsequently carved out (see
`SphericallyCompleteSpace.IsImmediate.exists_maximal_immediateExtensionSubmodule`). -/
noncomputable def canonicalSphericallyCompleteExtension (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    E →ₗᵢ[𝕜] ((lp (fun (_ : ℕ) ↦ E) ⊤)⧸ c₀ 𝕜 (fun (_ : ℕ) ↦ E)) where
  toFun x := by
    refine (QuotientAddGroup.mk' _) (⟨fun (_ : ℕ) ↦ x, memℓp_infty ⟨‖x‖, ?_⟩⟩)
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
    · exact le_trans (Submodule.Quotient.norm_mk_le (S := c₀ 𝕜 fun _ ↦ E) v) hvnorm.le
    · rw [QuotientAddGroup.le_norm_iff]
      intro m hm
      -- Any representative `m` of `mk v` differs from `v` by an element of `c₀`, so its coordinates
      -- `m n` tend to `v n = x`; hence `‖m n‖ → ‖x‖`, and each `‖m n‖ ≤ ‖m‖`, forcing `‖x‖ ≤ ‖m‖`.
      have hmem : m - v ∈ c₀ 𝕜 fun _ ↦ E := QuotientAddGroup.eq_iff_sub_mem.1 hm
      have key : Tendsto (fun n ↦ ‖(m : ∀ _ : ℕ, E) n‖) atTop (𝓝 ‖x‖) := by
        have hvn : ∀ n, ((v : lp (fun _ ↦ E) ⊤) : ∀ _, E) n = x := fun _ ↦ rfl
        have hconv : Tendsto (fun n ↦ (m : ∀ _ : ℕ, E) n) atTop (𝓝 x) := by
          have hsub := tendsto_zero_iff_norm_tendsto_zero.2 hmem
          simp only [lp.coeFn_sub] at hsub
          simpa only [Pi.sub_apply, hvn, sub_add_cancel, zero_add] using
            hsub.add (tendsto_const_nhds (x := x))
        simpa using hconv.norm
      exact le_of_tendsto' key
        (fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero m n)

/-- The `NormedAddCommGroup` structure on the quotient `lp (fun _ ↦ E) ⊤ ⧸ c₀ 𝕜 (fun _ ↦ E)`.

A quotient by a submodule only carries a genuine *norm* (rather than a mere seminorm) once the
submodule is topologically closed. This instance supplies the missing ingredient: it proves that the
null-sequence submodule `c₀ 𝕜 (fun _ ↦ E)` is a closed subset of `lp (fun _ ↦ E) ⊤` (via
`IsSeqClosed.isClosed`, using an `ε/2` argument on the `ℓ∞` norm), and then lets typeclass inference
upgrade the quotient seminorm to a `NormedAddCommGroup`. This is what makes
`canonicalSphericallyCompleteExtension 𝕜 E` land in a normed—not merely seminormed—space. -/
noncomputable instance normedAddCommGroup_lp_quotient_c₀ (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedAddCommGroup (↥(lp (fun _ ↦ E) ⊤) ⧸ c₀ 𝕜 fun _ ↦ E) := by
  have : IsClosed (↑(c₀ 𝕜 fun x ↦ E).carrier) := by
    apply IsSeqClosed.isClosed
    simp only [IsSeqClosed, Submodule.carrier_eq_coe, SetLike.mem_coe, Subtype.forall]
    intro seq lim hlim hseq htend
    -- `seq n → ⟨lim, hlim⟩` in the `ℓ∞` norm forces the coordinate norms `‖seq n ·‖` to converge
    -- *uniformly* to `‖lim ·‖`; a uniform limit of null sequences is again null, so `lim ∈ c₀`.
    have huniform : TendstoUniformly (fun n k ↦ ‖(seq n) k‖)
        (fun k ↦ ‖(⟨lim, hlim⟩ : lp (fun _ ↦ E) ⊤) k‖) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [eventually_atTop.2 (Metric.tendsto_atTop.1 htend ε hε)] with n hn k
      calc dist ‖(⟨lim, hlim⟩ : lp (fun _ ↦ E) ⊤) k‖ ‖(seq n) k‖
            ≤ ‖(⟨lim, hlim⟩ : lp (fun _ ↦ E) ⊤) k - seq n k‖ := by
              rw [Real.dist_eq]; exact abs_norm_sub_norm_le _ _
        _ ≤ ‖(⟨lim, hlim⟩ : lp (fun _ ↦ E) ⊤) - seq n‖ := by
              have := lp.norm_apply_le_norm ENNReal.top_ne_zero
                ((⟨lim, hlim⟩ : lp (fun _ ↦ E) ⊤) - seq n) k
              rwa [lp.coeFn_sub, Pi.sub_apply] at this
        _ = dist (seq n) ⟨lim, hlim⟩ := by rw [dist_eq_norm, norm_sub_rev]
        _ < ε := hn
    exact huniform.tendsto_of_eventually_tendsto (Eventually.of_forall hseq) tendsto_const_nhds
  simp only [Submodule.carrier_eq_coe] at this
  infer_instance

/-- Every non-Archimedean (ultrametric) nontrivially normed field `𝕜` embeds into a spherically
complete Banach space over itself: the quotient `lp (fun _ ↦ 𝕜) ⊤ ⧸ c₀ 𝕜 (fun _ ↦ 𝕜)` is
`SphericallyCompleteSpace`. This is the constant-scalar-family specialisation of
`sphericallyCompleteSpace_lp_quotient_c₀`, recorded as an instance so that spherical completeness of
this concrete space is available to typeclass inference. -/
instance sphericallyCompleteSpace_lp_quotient_c₀_self
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] :
    SphericallyCompleteSpace ((lp (fun _ ↦ 𝕜) ⊤)⧸ c₀ 𝕜 (fun _ ↦ 𝕜)) := by
  simpa only using sphericallyCompleteSpace_lp_quotient_c₀ (fun _ ↦ 𝕜)

end SphericallyCompleteSpace
