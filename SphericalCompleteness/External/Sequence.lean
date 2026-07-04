/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Common

/-!
# Subsequence extraction

Subsequence selection principles used in descending-chain arguments.
-/

@[expose] public section

/--
The index sequence backing `eventually_stable_or_exists_strictAnti_of_antitone`.

Given an antitone `f : ℕ → α` together with the non-stabilization hypothesis
`h : ∀ N, ∃ n ≥ N, f n ≠ f N`, this recursively builds an index map `φ : ℕ → ℕ`: set `φ 0 = 0`, and
let `φ (m + 1)` be a chosen index `n ≥ φ m` with `f n ≠ f (φ m)`. Since `f` is antitone, `n ≥ φ m`
gives `f n ≤ f (φ m)`, so in fact `f n < f (φ m)` and `n > φ m`; hence `φ` is strictly increasing
and `f ∘ φ` is strictly decreasing.
-/
private noncomputable def extractStrictAntiSubseq {α : Type*} [PartialOrder α]
    {f : ℕ → α} (hanti : Antitone f) (h : ∀ (N : ℕ), ∃ n ≥ N, f n ≠ f N) : ℕ → ℕ := fun n ↦
  match n with
  | 0 => 0
  | Nat.succ m => (h (extractStrictAntiSubseq hanti h m)).choose

/--
For an antitone (monotone decreasing) sequence `f : ℕ → α` in a partial order, this theorem gives a
dichotomy:

* either `f` is **eventually stable**: there exists an index `N` such that `f n = f N` for all
  `n ≥ N`;
* or there exists a **strictly increasing subsequence** `φ : ℕ → ℕ` such that `f ∘ φ` is
  **strictly decreasing** (`StrictAnti`).

This is useful for extracting a strictly decreasing subsequence from a non-stabilizing antitone
sequence, a common step in arguments about descending chains and related completeness properties.
-/
theorem eventually_stable_or_exists_strictAnti_of_antitone {α : Type*} [PartialOrder α]
    {f : ℕ → α} (hanti : Antitone f) :
    (∃ N : ℕ, ∀ n ≥ N, f n = f N) ∨ (∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (f ∘ φ)) := by
  if h : ∃ N, ∀ n ≥ N, f n = f N then
    exact Or.inl h
  else
    right
    push Not at h
    refine ⟨extractStrictAntiSubseq hanti h, ?_, ?_⟩
    · refine strictMono_nat_of_lt_succ <| fun n ↦ ?_
      simp only [extractStrictAntiSubseq]
      have := (h (extractStrictAntiSubseq hanti h n)).choose_spec
      exact lt_of_le_of_ne this.1 fun hc ↦ this.2 (hc ▸ rfl)
    · refine strictAnti_nat_of_succ_lt <| fun n ↦ lt_of_le_of_ne ?_ ?_
      · refine hanti ?_
        simp only [extractStrictAntiSubseq]
        exact (h (extractStrictAntiSubseq hanti h n)).choose_spec.1
      · exact (h (extractStrictAntiSubseq hanti h n)).choose_spec.2

/--
The index sequence backing `exists_injective_subseq_of_finite_duplication`.

Given `seq : ℕ → α` whose values duplicate only finitely often, encoded as
`hseq : ∀ n, ∃ N, ∀ i > N, seq n ≠ seq i`, this recursively builds an index map `φ : ℕ → ℕ`: set
`φ 0 = 0`, and `φ (n + 1) = max (φ n + 1) (N + 1)`, where `N` is a threshold past which `seq (φ n)`
never recurs. The `φ n + 1` term keeps `φ` strictly increasing, while exceeding `N` forces
`seq (φ n)` to differ from every later selected value, making `seq ∘ φ` injective.
-/
private noncomputable def extractInjectiveSubseq {α : Type*} (seq : ℕ → α)
    (hseq : ∀ n : ℕ, ∃ N, ∀ i > N, seq n ≠ seq i) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (extractInjectiveSubseq seq hseq n + 1)
    ((hseq (extractInjectiveSubseq seq hseq n)).choose + 1)

/--
Given a sequence `seq : ℕ → α` with *finite duplication*—i.e. for every index `n` there is a
threshold `N` after which the value `seq n` never appears again—this theorem extracts an injective
subsequence.

More precisely, assuming
`hseq : ∀ n, ∃ N, ∀ i > N, seq n ≠ seq i`,
it constructs a strictly increasing map `φ : ℕ → ℕ` such that the composed subsequence
`seq ∘ φ` is injective.

This can be viewed as a subsequence selection principle: under the hypothesis that each value in
the sequence occurs only finitely many times, one can choose indices increasing in `ℕ` so that all
selected values are pairwise distinct.
-/
theorem exists_injective_subseq_of_finite_duplication {α : Type*} (seq : ℕ → α)
    (hseq : ∀ n : ℕ, ∃ N, ∀ i > N, seq n ≠ seq i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (seq ∘ φ) := by
  use extractInjectiveSubseq seq hseq
  have hsm : StrictMono (extractInjectiveSubseq seq hseq) := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    simp only [extractInjectiveSubseq, gt_iff_lt, ne_eq]
    grind only [= max_def]
  refine ⟨hsm, Function.Injective.of_lt_imp_ne fun m n hmn ↦ ?_⟩
  simp only [Function.comp_apply, ne_eq]
  suffices hh : extractInjectiveSubseq seq hseq n >
    (hseq (extractInjectiveSubseq seq hseq m)).choose by
    exact (hseq (extractInjectiveSubseq seq hseq m)).choose_spec _ hh
  refine lt_of_lt_of_le ?_ (hsm.monotone hmn)
  simp only [extractInjectiveSubseq]
  grind only [= max_def]
