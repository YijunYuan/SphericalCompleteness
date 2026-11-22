/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.TransferInstance
public import SphericalCompleteness.PseudoMetric.AddGroup.ImmediateCardinal
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.Ambient
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.Basic
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.Chain
public import SphericalCompleteness.PseudoMetric.Module.SphericalCompletion.OneDimensional

/-!
# Existence of immediate spherically complete linear extensions

Embed the given module into a direct sum with a sufficiently large free module. An incomplete
immediate stage admits a one-dimensional immediate extension. The cardinal bound on each stage
leaves a free coordinate available for adjoining that vector. Hence a maximal stage is
spherically complete.
-/

@[expose] public section

open Function Set

namespace PseudoMetric

universe u v w

namespace LinearSphericalCompletion

variable {K E V Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V] [Zero Γ] [Add Γ] [LinearOrder Γ]
  (d : PseudoMetric E Γ) (j : E →ₗ[K] V)

private theorem addInvariant_comap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (e : PseudoMetric B Γ) [e.IsAddInvariant] (f : A →ₗ[K] B) :
    (e.comap f).IsAddInvariant where
  add_right x y a := by simp only [comap_apply, map_add, IsAddInvariant.add_right]

private theorem smulMono_comap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (e : PseudoMetric B Γ) [e.IsSMulMono K] (f : A →ₗ[K] B) :
    (e.comap f).IsSMulMono K where
  smul_le c x y h := by
    simp only [comap_apply, map_smul, map_zero] at h ⊢
    exact IsSMulMono.smul_le (d := e) c h

private noncomputable def initial [d.IsUltra] [d.IsAddInvariant] [d.IsSMulMono K]
    (hj : Injective j) : Stage d j := by
  let e := LinearEquiv.ofInjective j hj
  exact {
    dom := j.range
    contains := LinearMap.mem_range_self j
    dist := d.comap e.symm.toLinearMap
    ultra := inferInstance
    addInvariant := addInvariant_comap d e.symm.toLinearMap
    smulMono := smulMono_comap d e.symm.toLinearMap
    agrees := fun x y ↦ congrArg₂ d (e.symm_apply_apply x) (e.symm_apply_apply y)
    immediate := fun x hx ↦ (hx (j.surjective_rangeRestrict x)).elim }

/-- Enlarge an incomplete stage by one independent vector in the ambient space. -/
private theorem exists_proper_extension (P : Stage d j) (hP : ¬ P.dist.IsSphericallyComplete)
    {z : V} (hz : z ∉ P.dom) : ∃ Q : Stage d j, P.Extends Q ∧ ¬ Q.Extends P := by
  let := P.ultra
  let := P.addInvariant
  let := P.smulMono
  obtain ⟨e, _, _, he, ha, hs, hold, himm, _⟩ :=
    P.dist.exists_isImmediate_linear_extension_of_not_isSphericallyComplete K hP
  let D := P.dom ⊔ K ∙ z
  let hD : P.dom ≤ D := le_sup_left
  let inc := Submodule.inclusion hD
  let L := P.dom.prodEquivSupSpanSingleton hz
  let q := e.comap L.symm.toLinearMap
  have coord (x : P.dom) : L.symm (inc x) = (x, 0) := by
    apply L.injective
    rw [L.apply_symm_apply]
    apply Subtype.ext
    simp only [L, Submodule.coe_prodEquivSupSpanSingleton_apply, zero_smul, add_zero]
    rfl
  have hagree (x y : P.dom) : q (inc x) (inc y) = P.dist x y := by
    change e (L.symm (inc x)) (L.symm (inc y)) = _
    rw [coord, coord, hold]
  have hinc : q.IsImmediate inc := by
    intro y hy
    have hy' : L.symm y ∉ range (LinearMap.inl K P.dom K) := by
      rintro ⟨x, hx⟩
      exact hy ⟨x, L.symm.injective ((coord x).trans hx)⟩
    obtain ⟨hne, h⟩ := himm (L.symm y) hy'
    refine ⟨hne, fun x ↦ ?_⟩
    obtain ⟨a, ha⟩ := h x
    refine ⟨a, ?_⟩
    simpa only [q, comap_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, coord] using ha
  have hcomap : q.comap inc = P.dist := by ext x y; exact hagree x y
  have hbase : (q.comap inc).IsImmediate P.embedding := hcomap ▸ P.immediate
  let Q : Stage d j := {
    dom := D
    contains := fun x ↦ hD (P.contains x)
    dist := q
    ultra := inferInstanceAs (e.comap L.symm.toLinearMap).IsUltra
    addInvariant := addInvariant_comap e L.symm.toLinearMap
    smulMono := smulMono_comap e L.symm.toLinearMap
    agrees := fun x y ↦ (hagree (P.embedding x) (P.embedding y)).trans (P.agrees x y)
    immediate := hinc.comp hbase }
  exact ⟨Q, ⟨hD, hagree⟩, fun h ↦ hz (h.choose (Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self z)))⟩

end LinearSphericalCompletion

open LinearSphericalCompletion in
/-- Every module with a translation-invariant pseudoultrametric whose scalar action preserves
comparisons embeds linearly and isometrically into a spherically complete immediate extension. -/
theorem exists_linearSphericalCompletion {E : Type u} {Γ : Type w} [Zero Γ] [Add Γ] [LinearOrder Γ]
    (d : PseudoMetric E Γ) (K : Type v) [DivisionRing K] [AddCommGroup E] [Module K E]
    [d.IsUltra] [d.IsAddInvariant] [d.IsSMulMono K] :
    ∃ (F : Type (max u w)) (_ : AddCommGroup F) (_ : Module K F) (e : PseudoMetric F Γ)
      (i : E →ₗ[K] F), e.IsUltra ∧ e.IsAddInvariant ∧ e.IsSMulMono K ∧
      d.IsLinearSphericalCompletion e i := by
  classical
  let A := E × (Γ → E)
  let j := LinearMap.inl K E (Set A →₀ K)
  obtain ⟨P, hmax⟩ := Stage.exists_maximal (initial d j LinearMap.inl_injective)
  let := P.ultra
  let := P.addInvariant
  have hinj : Injective P.embedding := fun _ _ h ↦ LinearMap.inl_injective (congrArg Subtype.val h)
  obtain ⟨f, hf⟩ := P.immediate.exists_injective_prod_fun P.dist ⟨0, P.embedding.map_zero⟩
  have hsc : P.dist.IsSphericallyComplete := by
    by_contra hP
    obtain ⟨z, hz⟩ := P.dom.exists_single_notMem_of_injective hf
    obtain ⟨Q, hQ, hne⟩ := exists_proper_extension d j P hP hz
    exact hne (hmax Q hQ)
  -- Realize the extension in the universes of the original points and distance values.
  let b := (Equiv.ofInjective f hf).symm
  let : AddCommGroup (range f) := b.addCommGroup
  let : Module K (range f) := b.addEquiv.module K
  let L := b.addEquiv.linearEquiv K
  let g := L.symm.toLinearMap.comp P.embedding
  let e := P.dist.comap L.toLinearMap
  let := P.smulMono
  have hg (x : E) : L (g x) = P.embedding x := L.apply_symm_apply _
  refine ⟨range f, inferInstance, inferInstance, e, g, inferInstanceAs
    (P.dist.comap L.toLinearMap).IsUltra, addInvariant_comap P.dist _, smulMono_comap P.dist _,
    (P.dist.isSphericallyComplete_comap_iff_of_surjective L.surjective).mpr hsc,
    L.symm.injective.comp hinj, fun x y ↦ ?_, fun y hy ↦ ?_⟩
  · change P.dist (L (g x)) (L (g y)) = d x y
    rw [hg, hg]
    exact P.agrees x y
  · have hy' : L y ∉ range P.embedding := by
      rintro ⟨x, hx⟩
      exact hy ⟨x, L.injective ((hg x).trans hx)⟩
    obtain ⟨hn, hbetter⟩ := P.immediate (L y) hy'
    refine ⟨hn, fun x ↦ ?_⟩
    obtain ⟨z, hz⟩ := hbetter x
    exact ⟨z, by change P.dist _ (L (g z)) < P.dist _ (L (g x)); rwa [hg, hg]⟩

end PseudoMetric
