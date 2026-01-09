import SphericalCompleteness.NormedVectorSpace.Basic
import SphericalCompleteness.NormedVectorSpace.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace

open Metric

namespace SphericallyCompleteSpace

noncomputable instance {ι : Type*} {E : ι → Type*}
[∀ i, NormedAddCommGroup (E i)] :
NormedAddCommGroup ↥(lp E ⊤) := inferInstance

instance {ι : Type*} {E : ι → Type*} [Nonempty ι] [∀ i, NormedAddCommGroup (E i)]
[iiud : ∀ i, IsUltrametricDist (E i)] :
IsUltrametricDist (lp E ⊤) where
dist_triangle_max a b c := by
  repeat rw [dist_eq_norm, lp.norm_eq_ciSup]
  apply ciSup_le
  intro j
  have : ‖(↑(a - c): (i : ι) → E i) j‖ = ‖a j - c j‖ := rfl
  rw [this, ← dist_eq_norm]
  refine le_trans ((iiud j).dist_triangle_max (a j) (b j) (c j)) ?_
  repeat rw [dist_eq_norm]
  apply max_le_max
  · have : ‖(↑a: (i : ι) → E i) j - (↑b: (i : ι) → E i) j‖ = ‖(↑(a - b) : (i : ι) → E i) j‖ := rfl
    rw [this]
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero
  · have : ‖(↑b: (i : ι) → E i) j - (↑c: (i : ι) → E i) j‖ = ‖(↑(b - c) : (i : ι) → E i) j‖ := rfl
    rw [this]
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero

def c₀ (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
[∀ i, NormedSpace 𝕜 (E i)] : Submodule 𝕜 ↥(lp E ⊤) where
  carrier := {f : lp E ⊤ | ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, ‖f n‖ ≤ ε}
  add_mem' := by
    intro a b ha hb
    simp only [ge_iff_le, Set.mem_setOf_eq, AddSubgroup.coe_add, Pi.add_apply] at *
    intro ε hε
    rcases ha (ε / 2) (by linarith) with ⟨Na, hNa⟩
    rcases hb (ε / 2) (by linarith) with ⟨Nb, hNb⟩
    use Na + Nb
    intro n hn
    specialize hNa n (by linarith)
    specialize hNb n (by linarith)
    refine le_trans (norm_add_le _ _) ?_
    linarith
  zero_mem' := by
    simp
    intro e he
    use 0
    simpa using le_of_lt he
  smul_mem' := by
    intro c x hx
    if hc : c = 0 then
      simp [hc]
      intro e he
      use 0
      simpa using le_of_lt he
    else
    simp at *
    intro ε hε
    rcases hx (ε / ‖c‖) (by
      simp_all only [norm_pos_iff, ne_eq, not_false_eq_true, div_pos_iff_of_pos_left]
      ) with ⟨N, hN⟩
    use N
    intro n hn
    rw [norm_smul]
    exact (le_mul_inv_iff₀' <| norm_pos_iff.mpr hc).mp <| hN n hn

private lemma exists_norm_sub_lt {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
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
  have tt := quotient_norm_mk_eq (c₀ 𝕜 E).toAddSubgroup
  specialize tt (c (i + 2) - c (i + 1)).out
  simp only [QuotientAddGroup.mk'_apply, Quotient.out_eq, Submodule.coe_toAddSubgroup] at tt
  simp only [tt] at this
  rw [csInf_lt_iff] at this
  · rcases this with ⟨unp1, hlun, hens1⟩
    rw [Set.mem_image] at hlun
    rcases hlun with ⟨lun, hlun, hlun_eq⟩
    rw [← hlun_eq] at hens1
    use (c (i + 2) - c (i + 1)).out + lun + aip1
    constructor
    · have : (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup)
        ((c (i + 2) - c (i + 1)).out + lun + aip1) =
      (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup)
        (c (i + 2) - c (i + 1)).out +
      (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) lun +
      (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) aip1 := by
        simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk_add, Quotient.out_eq]
      simp only [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk_add, Quotient.out_eq]
      have : (↑aip1 : ↥(lp E ⊤) ⧸ (c₀ 𝕜 E).toAddSubgroup) = c (i + 1) := hai
      rw [(QuotientAddGroup.eq_zero_iff lun).mpr hlun, this]
      abel
    · simp only [add_sub_cancel_right, hens1]
  · use 0
    refine mem_lowerBounds.mpr ?_
    intro x hx
    simp only [Set.mem_image, SetLike.mem_coe, Subtype.exists] at hx
    rw [← hx.choose_spec.choose_spec.2]
    exact lp.norm_nonneg' _
  · exact Set.Nonempty.of_subtype

private noncomputable def quotient_mk_section {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
  [∀ (i : ℕ), IsUltrametricDist (E i)]
  {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
  (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i)) :
  (k : ℕ) → {z : ↥(lp E ⊤) // (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) z = c k} := fun n =>
  match n with
  | 0 => ⟨(c 0).out, by simp⟩
  | 1 => ⟨(c 1).out, by simp⟩
  | m + 2 =>
      ⟨(exists_norm_sub_lt E hsr hanti m
            (quotient_mk_section E hsr hanti (m + 1)).val
            (quotient_mk_section E hsr hanti (m + 1)).prop).choose,
        (exists_norm_sub_lt E hsr hanti m
            (quotient_mk_section E hsr hanti (m + 1)).val
            (quotient_mk_section E hsr hanti (m + 1)).prop).choose_spec.1⟩

private lemma mk_eq_and_norm_sub_lt {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
  [∀ (i : ℕ), IsUltrametricDist (E i)]
  {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
  (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i))
  : ∀ i : ℕ,
      (QuotientAddGroup.mk' _) (quotient_mk_section E hsr hanti i).1 = c i ∧
        ‖(quotient_mk_section E hsr hanti (i + 2)).1 -
        (quotient_mk_section E hsr hanti (i + 1)).1‖ < ↑(r i) := by
  intro m
  constructor
  · exact (quotient_mk_section E hsr hanti m).prop
  · simp only [QuotientAddGroup.mk'_apply, quotient_mk_section]
    exact
      (exists_norm_sub_lt E hsr hanti m
            (quotient_mk_section E hsr hanti (m + 1)).val
            (quotient_mk_section E hsr hanti (m + 1)).prop).choose_spec.2

private lemma quotient_mk_section_norm_apply_self_le_max {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
  [iiud : ∀ (i : ℕ), IsUltrametricDist (E i)]
  ⦃c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E⦄ ⦃r : ℕ → NNReal⦄ (hsr : StrictAnti r)
  (hanti : Antitone fun i ↦ closedBall (c i) ↑(r i)) :
  ∀ (n : ℕ), ‖((quotient_mk_section E hsr hanti n).val : (i : ℕ) → E i) n‖ ≤
    max ‖(quotient_mk_section E hsr hanti 0).val‖
    (max ‖(quotient_mk_section E hsr hanti 1).val‖ ↑(r 0)) := by
  intro n
  have : ‖((quotient_mk_section E hsr hanti n).val: (i : ℕ) → E i) n‖ ≤
    ‖(quotient_mk_section E hsr hanti n).val‖ := by
    apply lp.norm_apply_le_norm ENNReal.top_ne_zero
  refine le_trans this ?_
  if hn : n = 0 then
    rw [hn]
    simp only [le_sup_left]
  else
  apply le_max_of_le_right
  have : (quotient_mk_section E hsr hanti n).val =
    (quotient_mk_section E hsr hanti n).val - (quotient_mk_section E hsr hanti 1).val +
    (quotient_mk_section E hsr hanti 1).val := by abel
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
    rw [← sub_add_sub_cancel _ (quotient_mk_section E hsr hanti m).val _]
    refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _) ?_
    refine max_le (le_trans (le_of_lt ?_) <| hsr.antitone <| Nat.zero_le (m - 1)) ih
    have := (mk_eq_and_norm_sub_lt E hsr hanti (m - 1)).2
    rwa [(by omega : m - 1 + 2 = m + 1), (by omega : m - 1 + 1 = m)] at this

lemma quotient_norm_mk_le_of_eventually_norm_le {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
  [∀ (i : ℕ), IsUltrametricDist (E i)]
  (A : lp E ⊤) (C : ℝ) (hC : C > 0)
  (N : ℕ) (hN : ∀ n ≥ N, ‖A n‖ ≤ C)
  :
  ‖(QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) A‖ ≤ C
   := by
  rw [quotient_norm_mk_eq]
  let u : ∀ i, E i := fun i =>
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
    · refine ⟨0, mem_lowerBounds.2 <| fun x hx => ?_⟩
      simp only [Submodule.coe_toAddSubgroup, Set.mem_image, SetLike.mem_coe, Subtype.exists] at hx
      rw [← hx.choose_spec.choose_spec.2]
      exact norm_nonneg _
    · rw [Set.mem_image]
      exact ⟨⟨u, hu_mem1⟩, ⟨hu_mem2, rfl⟩⟩
  refine le_trans this ?_
  rw [lp.norm_eq_ciSup]
  refine ciSup_le <| fun k => ?_
  simp only [dite_eq_ite, AddSubgroup.coe_add, Pi.add_apply, u]
  if hk : k < N then
    simpa only [if_pos hk, add_neg_cancel, norm_zero] using le_of_lt hC
  else
    simpa only [if_neg hk, add_zero] using hN k <| Nat.le_of_not_lt hk

theorem sphericallyCompleteSpace_lp_quotient_c₀ {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
[∀ i, NormedSpace 𝕜 (E i)] [∀ i, IsUltrametricDist (E i)] :
SphericallyCompleteSpace ((lp E ⊤)⧸ c₀ 𝕜 E) := by
  rw [sphericallyComplete_iff']
  intro c r hsr hanti
  let f : ∀ i, E i := fun i => (quotient_mk_section E hsr hanti i).val i
  have hf_mem : ↑(f) ∈ lp E ⊤ := by
    simp only [lp, QuotientAddGroup.mk'_apply, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, f]
    refine memℓp_infty <| bddAbove_def.mpr ?_
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    use max ‖(quotient_mk_section E hsr hanti 0).val‖
      (max ‖(quotient_mk_section E hsr hanti 1).val‖ (r 0))
    exact fun n => quotient_mk_section_norm_apply_self_le_max E hsr hanti n
  let x : (lp E ⊤) ⧸ c₀ 𝕜 E :=
    (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ⟨f, hf_mem⟩
  use x
  have : ∀ n ≥ 1, ‖x - c (n + 1)‖ ≤ r n := by
    unfold x
    intro n hn
    rw [← (mk_eq_and_norm_sub_lt E hsr hanti (n + 1)).1]
    have : (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ⟨f, hf_mem⟩ - (QuotientAddGroup.mk'
      (c₀ 𝕜 E).toAddSubgroup) ↑(quotient_mk_section E hsr hanti (n + 1)) = (QuotientAddGroup.mk'
      (c₀ 𝕜 E).toAddSubgroup) (⟨f, hf_mem⟩ - (quotient_mk_section E hsr hanti (n + 1)).val) := rfl
    rw [this]
    have := @quotient_norm_mk_le_of_eventually_norm_le 𝕜 _ E _ _ _
      (⟨f, hf_mem⟩ - ↑(quotient_mk_section E hsr hanti (n + 1))) (r n).val ?_ (n + 1) ?_
    · exact this
    · exact lt_of_le_of_lt (r (n + 1)).prop <| hsr <| lt_add_one n
    · intro m hm
      simp only [QuotientAddGroup.mk'_apply, AddSubgroupClass.coe_sub, Pi.sub_apply,
        NNReal.val_eq_coe, f]
      have h : ‖(quotient_mk_section E hsr hanti m).val -
        (quotient_mk_section E hsr hanti (n + 1)).val‖
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
          rw [← sub_add_sub_cancel _ (quotient_mk_section E hsr hanti k).val _]
          refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤)).norm_add_le_max _ _) ?_
          apply max_le ?_ hk
          have := (mk_eq_and_norm_sub_lt E hsr hanti (k - 1)).2
          rw [(by omega : k - 1 + 2 = k + 1), (by omega : k - 1 + 1 = k)] at this
          exact le_of_lt <| lt_of_lt_of_le this <| hsr.antitone <| by omega
      refine le_trans ?_ h
      have : (↑(quotient_mk_section E hsr hanti m).val : (i : ℕ) → E i)  m -
        ((quotient_mk_section E hsr hanti (n + 1)).val : (i : ℕ) → E i) m =
        (↑((quotient_mk_section E hsr hanti m).val -
        (quotient_mk_section E hsr hanti (n + 1)).val) : (i : ℕ) → E i) m := rfl
      rw [this]
      apply lp.norm_apply_le_norm ENNReal.top_ne_zero
  simp only [Set.mem_iInter]
  suffices h : ∀ i ≥ 1, x ∈ closedBall (c i) (r i) by
    exact fun i => (hanti <| Nat.le_add_right i 1) <| h (i + 1) (Nat.le_add_left 1 i)
  intro i hi
  specialize this i hi
  rw [mem_closedBall, dist_eq_norm, ← sub_add_sub_cancel _ (c (i + 1)) _]
  refine le_trans ((inferInstance : IsUltrametricDist (lp E ⊤ ⧸ c₀ 𝕜 E)).norm_add_le_max _ _) ?_
  apply max_le this
  rw [← dist_eq_norm, ← mem_closedBall]
  refine (hanti (Nat.le_succ i)) ?_
  simp only [Nat.succ_eq_add_one, mem_closedBall, dist_self, NNReal.zero_le_coe]

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] :
SphericallyCompleteSpace ((lp (fun _ => 𝕜) ⊤)⧸ c₀ 𝕜 (fun _ => 𝕜))
:= sphericallyCompleteSpace_lp_quotient_c₀ (fun _ => 𝕜)

end SphericallyCompleteSpace
