/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import SphericalCompleteness.PseudoMetric

/-!
# Testing spherical completeness with sequences

A sequence suffices when each nonempty set of radii has a countable coinitial subset.
The proofs use symmetry of the distance and apply even without the strong triangle inequality.
-/

@[expose] public section

open Set

namespace PseudoMetric

variable {X Γ : Type*} [Zero Γ] [Add Γ] [LinearOrder Γ] (d : PseudoMetric X Γ)

/-- Take the smallest of the first `n + 1` members of a sequence in a chain. -/
private theorem exists_antitone_refinement {S : Set (Set X)} (h : IsChain (· ⊆ ·) S)
    (u : ℕ → S) : ∃ v : ℕ → S, Antitone (fun n ↦ (v n : Set X)) ∧ ∀ n, (v n : Set X) ⊆ u n := by
  classical
  let v : ℕ → S := Nat.rec (u 0) fun n a ↦ if (u (n + 1)).val ⊆ a.val then u (n + 1) else a
  refine ⟨v, antitone_nat_of_succ_le (fun n ↦ ?_), fun n ↦ ?_⟩
  · change (if (u (n + 1)).val ⊆ (v n).val then u (n + 1) else v n).val ⊆ _
    split <;> simp_all
  · cases n with
    | zero => exact Subset.rfl
    | succ n =>
      change (if (u (n + 1)).val ⊆ (v n).val then u (n + 1) else v n).val ⊆ _
      split
      · exact Subset.rfl
      · exact (h.total (u _).prop (v _).prop).resolve_left ‹_›

/-- Countable coinitiality of every nonempty set of radii reduces the arbitrary nest
condition to decreasing sequences of balls with nonnegative radii. -/
theorem isSphericallyComplete_iff_antitone_sequence (hd : ∀ x y, 0 ≤ d x y)
    (hcoin : ∀ s : Set Γ, s.Nonempty → ∃ u : ℕ → s, ∀ r ∈ s, ∃ n, (u n).val ≤ r) :
    d.IsSphericallyComplete ↔
      ∀ (c : ℕ → X) (r : ℕ → Γ), (∀ n, 0 ≤ r n) →
        Antitone (fun n ↦ d.closedBall (c n) (r n)) → (⋂ n, d.closedBall (c n) (r n)).Nonempty := by
  classical
  refine ⟨fun _ ↦ IsSphericallyComplete.nonempty_iInter_of_antitone d, fun hseq ↦ ⟨?_⟩⟩
  intro S hballs hne hnonempty chain
  have : Nonempty S := hne.to_subtype
  choose c r hcr using fun B : S ↦ hballs B.prop
  have hr (B : S) : 0 ≤ r B := by
    obtain ⟨w, hw⟩ := hnonempty B B.prop
    rw [hcr] at hw
    exact (hd w (c B)).trans hw
  have hc (B : S) : c B ∈ B.val := by rw [hcr]; exact (d.refl _).trans_le (hr B)
  by_contra hempty
  -- Each center is excluded by a smaller ball in the nest.
  have hex (B : S) : ∃ C : S, c B ∉ C.val := by
    by_contra! hall
    exact hempty ⟨c B, mem_sInter.mpr fun C hC ↦ hall ⟨C, hC⟩⟩
  choose smaller hmiss using hex
  have hsub (B : S) : (smaller B : Set X) ⊆ B :=
    (chain.total (smaller B).prop B.prop).resolve_right (fun h ↦ hmiss B (h (hc B)))
  obtain ⟨radii, hcoin'⟩ := hcoin (range r) (range_nonempty _)
  choose u hu using fun n ↦ (radii n).prop
  obtain ⟨v, hv, hvu⟩ := exists_antitone_refinement chain (fun n ↦ smaller (u n))
  obtain ⟨z, hz⟩ := hseq (fun n ↦ c (v n)) (fun n ↦ r (v n)) (fun n ↦ hr _) (by
    simpa only [← hcr] using hv)
  apply hempty
  refine ⟨z, mem_sInter.mpr fun B hB ↦ ?_⟩
  let b : S := ⟨B, hB⟩
  obtain ⟨n, hn⟩ := hcoin' (r b) (mem_range_self b)
  -- If B lay inside the smaller ball, symmetry and the radius bound would put
  -- the excluded center back in it.
  have hsm : (smaller (u n) : Set X) ⊆ b := by
    apply (chain.total (smaller (u n)).prop b.prop).resolve_right
    intro h
    have ha := hsub (u n) (h (hc b))
    rw [hcr] at ha
    have hmem : c (u n) ∈ b.val := by
      rw [hcr, mem_closedBall, d.symm]
      exact le_trans ha ((hu n).trans_le hn)
    exact hmiss _ (h hmem)
  exact hsm (hvu n (by simpa only [hcr] using mem_iInter.mp hz n))

/-- A nested sequence with empty intersection has a cofinal subsequence with strictly
decreasing radii. This test uses only symmetry and the countable coinitiality of radii. -/
theorem isSphericallyComplete_iff_strictAnti_radius (hd : ∀ x y, 0 ≤ d x y)
    (hcoin : ∀ s : Set Γ, s.Nonempty → ∃ u : ℕ → s, ∀ r ∈ s, ∃ n, (u n).val ≤ r) :
    d.IsSphericallyComplete ↔
      ∀ (c : ℕ → X) (r : ℕ → Γ), (∀ n, 0 ≤ r n) → StrictAnti r →
        Antitone (fun n ↦ d.closedBall (c n) (r n)) → (⋂ n, d.closedBall (c n) (r n)).Nonempty := by
  rw [d.isSphericallyComplete_iff_antitone_sequence hd hcoin]
  refine ⟨fun h c r hr _ ↦ h c r hr, fun h c r hr hanti ↦ ?_⟩
  classical
  by_contra hnone
  have hcenter (n : ℕ) : c n ∈ d.closedBall (c n) (r n) := (d.refl _).trans_le (hr n)
  have hex (n : ℕ) : ∃ m, c n ∉ d.closedBall (c m) (r m) := by
    by_contra! hall
    exact hnone ⟨c n, mem_iInter.mpr hall⟩
  choose next hmiss using hex
  have hlt (n : ℕ) : n < next n :=
    lt_of_not_ge fun hmn ↦ hmiss n (hanti hmn (hcenter n))
  have hrad (n : ℕ) : r (next n) < r n := by
    have hdist : d (c n) (c (next n)) ≤ r n :=
      (d.symm _ _).trans_le (hanti (hlt n).le (hcenter _))
    exact (lt_of_not_ge (hmiss n)).trans_le hdist
  let u : ℕ → ℕ := Nat.rec 0 fun _ i ↦ next i
  have hmono : StrictMono u := strictMono_nat_of_lt_succ fun n ↦ hlt (u n)
  have hantiRad : StrictAnti (r ∘ u) := strictAnti_nat_of_succ_lt fun n ↦ hrad (u n)
  obtain ⟨x, hx⟩ := h (c ∘ u) (r ∘ u) (fun n ↦ hr _) hantiRad (hanti.comp_monotone hmono.monotone)
  exact hnone ⟨x, mem_iInter.mpr fun i ↦ hanti (hmono.id_le i) (mem_iInter.mp hx i)⟩

end PseudoMetric
