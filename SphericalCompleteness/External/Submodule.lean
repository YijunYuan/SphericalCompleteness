import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Field.Defs

lemma eq_and_eq_of_add_eq_add_of_not_mem_submodule_span_singleton {𝕜 : Type*} [Field 𝕜]
{V : Type*} [AddCommGroup V] [Module 𝕜 V]
{D : Submodule 𝕜 V} {a : V} (ha : a ∉ D) :
∀ d1 ∈ D, ∀ la1 ∈ Submodule.span 𝕜 {a}, ∀ d2 ∈ D, ∀ la2 ∈ Submodule.span 𝕜 {a},
  d1 + la1 = d2 + la2 → d1 = d2 ∧ la1 = la2 := by
  intro d1 hd1 la1 hla1 d2 hd2 la2 hla2 heq
  rw [add_comm, ← sub_eq_sub_iff_add_eq_add] at heq
  have : d2 - d1 ∈ Submodule.span 𝕜 {a} := by
    rw [← heq]
    exact (Submodule.sub_mem_iff_left (Submodule.span 𝕜 {a}) hla2).mpr hla1
  rcases Submodule.mem_span_singleton.1 this with ⟨r, hr⟩
  if hr' : r = 0 then
    simp only [hr', zero_smul] at hr
    rw [← hr] at heq
    constructor
    · exact Eq.symm <| sub_eq_zero.1 <| hr.symm
    · rwa [sub_eq_zero] at heq
  else
  replace hr : a = r⁻¹ • (d2 - d1) := by
    rw [← hr]
    exact (eq_inv_smul_iff₀ hr').mpr rfl
  simp only [hr] at ha
  exfalso
  exact ha <| Submodule.smul_mem D r⁻¹ <| (Submodule.sub_mem_iff_left D hd1).mpr hd2

theorem smul_submodule_eq_self {𝕜 : Type*} [Field 𝕜]
  {E : Type*} [AddCommMonoid E] [Module 𝕜 E] {a : 𝕜} (ha : a ≠ 0) (M : Submodule 𝕜 E) :
  (@HSMul.hSMul 𝕜 (Set E) (Set E) (@instHSMul 𝕜 (Set E) Set.smulSet) a ↑M)
    = ↑M := by
  ext z
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases Set.mem_smul_set.1 h with ⟨c, hc1, hc2⟩
    rw [← hc2]
    exact SMulMemClass.smul_mem a hc1
  · exact Set.mem_smul_set.mpr ⟨a⁻¹ • z, ⟨SMulMemClass.smul_mem a⁻¹ h, smul_inv_smul₀ ha z⟩⟩
