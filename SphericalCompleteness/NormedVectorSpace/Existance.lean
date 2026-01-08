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
    refine @le_ciSup ℝ ι _ (fun i ↦ ‖(↑(a - b) : (i : ι) → E i) i‖) ?_ j
    rw [← memℓp_infty_iff]
    exact lp.memℓp (a - b)
  · have : ‖(↑b: (i : ι) → E i) j - (↑c: (i : ι) → E i) j‖ = ‖(↑(b - c) : (i : ι) → E i) j‖ := rfl
    rw [this]
    refine @le_ciSup ℝ ι _ (fun i ↦ ‖(↑(b - c) : (i : ι) → E i) i‖) ?_ j
    rw [← memℓp_infty_iff]
    exact lp.memℓp (b - c)

def c₀ (𝕜 : Type*) [NontriviallyNormedField 𝕜]
(E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
[∀ i, NormedSpace 𝕜 (E i)] : Submodule 𝕜 ↥(lp E ⊤) where
  carrier := {f : lp E ⊤ | ∃ ε : ℝ, ∃ N : ℕ, ∀ n ≥ N, ‖f n‖ ≤ ε}
  add_mem' := by
    intro a b ha hb
    simp only [ge_iff_le, Set.mem_setOf_eq, AddSubgroup.coe_add, Pi.add_apply] at *
    rcases ha with ⟨εa, Na, ha'⟩
    rcases hb with ⟨εb, Nb, hb'⟩
    use εa + εb, max Na Nb
    intro n gn
    refine norm_add_le_of_le ?_ ?_
    · exact ha' n <| le_of_max_le_left gn
    · exact hb' n <| le_of_max_le_right gn
  zero_mem' := by
    use 0
    simp only [ge_iff_le, ZeroMemClass.coe_zero, Pi.zero_apply, norm_zero, le_refl, implies_true,
      exists_const]
  smul_mem' := by
    intro c x hx
    simp at *
    rcases hx with ⟨ε, N, h'⟩
    use ‖c‖ * ε, N
    intro n hn
    specialize h' n hn
    rw [norm_smul]
    if hc : c = 0 then
      simp only [hc, norm_zero, zero_mul, le_refl]
    else
    have : ‖c‖ > 0 := norm_pos_iff.mpr hc
    simp_all only [gt_iff_lt, norm_pos_iff, ne_eq, not_false_eq_true, mul_le_mul_iff_right₀]

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

private noncomputable def sb {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
  [∀ (i : ℕ), IsUltrametricDist (E i)]
  {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
  (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i)) :
  (k : ℕ) → {z : ↥(lp E ⊤)// (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) z = c k} := fun n =>
  match n with
  |0 => ⟨(c 0).out, by simp⟩
  |1 => ⟨(c 1).out, by simp⟩
  |m + 2 => ⟨(exists_norm_sub_lt E hsr hanti m
      (sb E hsr hanti (m + 1)).val (sb E hsr hanti (m + 1)).prop).choose,
      (exists_norm_sub_lt E hsr hanti m
      (sb E hsr hanti (m + 1)).val (sb E hsr hanti (m + 1)).prop).choose_spec.1⟩

private lemma sb_prop {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
  (E : ℕ → Type u_2) [(i : ℕ) → NormedAddCommGroup (E i)] [(i : ℕ) → NormedSpace 𝕜 (E i)]
  [∀ (i : ℕ), IsUltrametricDist (E i)]
  {c : ℕ → ↥(lp E ⊤) ⧸ c₀ 𝕜 E} {r : ℕ → NNReal} (hsr : StrictAnti r)
  (hanti : Antitone fun i ↦ Metric.closedBall (c i) ↑(r i))
  : ∀ i : ℕ,
   (QuotientAddGroup.mk' _) (sb E hsr hanti i).1 = c i ∧
    ‖(sb E hsr hanti (i + 2)).1 - (sb E hsr hanti (i + 1)).1‖ < ↑(r i) := by
  intro m
  constructor
  · exact (sb E hsr hanti m).prop
  · simp only [QuotientAddGroup.mk'_apply, sb]
    exact (exists_norm_sub_lt E hsr hanti m
      (sb E hsr hanti (m + 1)).val (sb E hsr hanti (m + 1)).prop).choose_spec.2

theorem eeee {𝕜 : Type*} [NontriviallyNormedField 𝕜]
(E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)]
[∀ i, NormedSpace 𝕜 (E i)] [∀ i, IsUltrametricDist (E i)] :
SphericallyCompleteSpace ((lp E ⊤)⧸ c₀ 𝕜 E) := by
  rw [sphericallyComplete_iff']
  intro c r hsr hanti
  let f : ∀ i, E i := fun i => (sb E hsr hanti i).val i
  have hf_mem : ↑(f) ∈ lp E ⊤ := by
    simp [lp, f]
    refine memℓp_infty ?_

    sorry
  use (QuotientAddGroup.mk' (c₀ 𝕜 E).toAddSubgroup) ⟨f, hf_mem⟩
  sorry

end SphericallyCompleteSpace
