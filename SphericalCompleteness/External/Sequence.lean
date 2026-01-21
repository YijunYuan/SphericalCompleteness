import Mathlib.Tactic

private noncomputable def esoesoa {α : Type u_1} [inst : PartialOrder α]
  {f : ℕ → α} (hanti : Antitone f) (h : ∀ (N : ℕ), ∃ n ≥ N, f n ≠ f N) : ℕ → ℕ := fun n =>
  match n with
  | 0 => 0
  | Nat.succ m => (h (esoesoa hanti h m)).choose

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
theorem eventually_stable_or_exists_strictanti_of_antitone {α : Type*} [PartialOrder α]
  {f : ℕ → α} (hanti : Antitone f) :
  (∃ N : ℕ, ∀ n ≥ N, f n = f N) ∨ (∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (f ∘ φ)) := by
  if h : ∃ N, ∀ n ≥ N, f n = f N then
    exact Or.inl h
  else
    right
    push_neg at h
    use esoesoa hanti h
    constructor
    · refine strictMono_nat_of_lt_succ <| fun n => ?_
      simp only [esoesoa]
      have := (esoesoa._proof_2 hanti h n).choose_spec
      refine lt_of_le_of_ne this.1 ?_
      by_contra hc
      rw [← hc] at this
      simp only [ge_iff_le, le_refl, ne_eq, not_true_eq_false, and_false] at this
    · refine strictAnti_nat_of_succ_lt <| fun n => lt_of_le_of_ne ?_ ?_
      · refine hanti ?_
        simp only [esoesoa]
        exact (esoesoa._proof_2 hanti h n).choose_spec.1
      · by_contra hc
        simp only [Function.comp_apply, esoesoa, ge_iff_le, ne_eq] at hc
        exact (esoesoa._proof_2 hanti h n).choose_spec.2 hc

private noncomputable def ebsofd {α : Type*} (seq : ℕ → α)
(hseq : ∀ n : ℕ, ∃ N, ∀ i > N, seq n ≠ seq i) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      max (ebsofd seq hseq n + 1)  ((hseq (ebsofd seq hseq n)).choose + 1)

/-!
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
theorem exists_bijective_subseq_of_finite_duplication {α : Type*} (seq : ℕ → α)
(hseq : ∀ n : ℕ, ∃ N, ∀ i > N, seq n ≠ seq i) :
∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (seq ∘ φ) := by
  use ebsofd seq hseq
  have hsm : StrictMono (ebsofd seq hseq) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    simp only [ebsofd, gt_iff_lt, ne_eq]
    grind only [= max_def]
  refine ⟨hsm, injective_of_lt_imp_ne fun m n hmn => ?_⟩
  simp only [Function.comp_apply, ne_eq]
  suffices hh : ebsofd seq hseq n > (hseq (ebsofd seq hseq m)).choose by
    exact (hseq (ebsofd seq hseq m)).choose_spec _ hh
  refine lt_of_lt_of_le ?_ (hsm.monotone hmn)
  simp only [ebsofd]
  grind only [= max_def]
