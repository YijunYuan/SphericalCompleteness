import Mathlib.Tactic

noncomputable def esoesoa {α : Type u_1} [inst : PartialOrder α]
  {f : ℕ → α} (hanti : Antitone f) (h : ∀ (N : ℕ), ∃ n ≥ N, f n ≠ f N) : ℕ → ℕ := fun n =>
  match n with
  | 0 => 0
  | Nat.succ m => (h (esoesoa hanti h m)).choose

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
