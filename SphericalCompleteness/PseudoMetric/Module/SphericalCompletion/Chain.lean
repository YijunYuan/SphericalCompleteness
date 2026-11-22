/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Order.Zorn
public import SphericalCompleteness.PseudoMetric.Immediate
public import SphericalCompleteness.PseudoMetric.Module.Basic

/-!
# Unions of chains of immediate linear extensions

The ambient space carries only a module structure. Each stage puts a distance on one
submodule. A chain of stages induces a well-defined distance on their union.
-/

@[expose] public section

namespace PseudoMetric.LinearSphericalCompletion

variable {K E V Γ : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [AddCommGroup V] [Module K V] [Zero Γ] [Add Γ] [LinearOrder Γ]

/-- A distance on an intermediate submodule giving an immediate extension of the base. -/
structure Stage (d : PseudoMetric E Γ) (j : E →ₗ[K] V) where
  dom : Submodule K V
  contains : ∀ x, j x ∈ dom
  dist : PseudoMetric dom Γ
  ultra : dist.IsUltra
  addInvariant : dist.IsAddInvariant
  smulMono : dist.IsSMulMono K
  agrees : ∀ x y : E, dist ⟨j x, contains x⟩ ⟨j y, contains y⟩ = d x y
  immediate : dist.IsImmediate (fun x : E ↦ (⟨j x, contains x⟩ : dom))

namespace Stage

variable {d : PseudoMetric E Γ} {j : E →ₗ[K] V}

/-- The original linear map with codomain restricted to one stage. -/
def embedding (P : Stage d j) : E →ₗ[K] P.dom := j.codRestrict P.dom P.contains

/-- The larger stage preserves all the distances on the smaller one. -/
def Extends (P Q : Stage d j) : Prop :=
  ∃ h : P.dom ≤ Q.dom, ∀ x y : P.dom, Q.dist (Submodule.inclusion h x) (Submodule.inclusion h y) =
    P.dist x y

private local instance : Std.Refl (Extends (d := d) (j := j)) where
  refl _ := ⟨le_rfl, fun _ _ ↦ rfl⟩

private theorem Extends.trans {P Q T : Stage d j} (hPQ : P.Extends Q) (hQT : Q.Extends T) :
    P.Extends T := by
  obtain ⟨hp, hpq⟩ := hPQ
  obtain ⟨hq, hqt⟩ := hQT
  exact ⟨hp.trans hq, fun x y ↦ (hqt (Submodule.inclusion hp x) (Submodule.inclusion hp y)).trans
    (hpq x y)⟩

private theorem chain_upperBound (C : Set (Stage d j)) (hc : IsChain Extends C) (hne : C.Nonempty) :
    ∃ Q : Stage d j, ∀ P ∈ C, P.Extends Q := by
  classical
  have : Nonempty C := hne.to_subtype
  let U := ⨆ P : C, P.val.dom
  have hle (P : C) : P.val.dom ≤ U := le_iSup (fun P : C ↦ P.val.dom) P
  have dir : Directed (· ≤ ·) (fun P : C ↦ P.val.dom) := by
    intro P Q
    rcases hc.total P.prop Q.prop with h | h
    · exact ⟨Q, h.choose, le_rfl⟩
    · exact ⟨P, le_rfl, h.choose⟩
  have stage (x : U) : ∃ P : C, (x : V) ∈ P.val.dom :=
    (Submodule.mem_iSup_of_directed _ dir).mp x.prop
  let gauge (x : U) : Γ := (stage x).choose.val.dist ⟨x, (stage x).choose_spec⟩ 0
  have gauge_eq (P : C) (x : U) (hx : (x : V) ∈ P.val.dom) :
      gauge x = P.val.dist ⟨x, hx⟩ 0 := by
    let Q := (stage x).choose
    have hxQ : (x : V) ∈ Q.val.dom := (stage x).choose_spec
    rcases hc.total Q.prop P.prop with h | h
    · exact (h.choose_spec ⟨x, hxQ⟩ 0).symm
    · exact h.choose_spec ⟨x, hx⟩ 0
  let delta (x y : U) : Γ := gauge (x - y)
  have eqOn (P : C) {x y : U} (hx : (x : V) ∈ P.val.dom) (hy : (y : V) ∈ P.val.dom) :
      delta x y = P.val.dist ⟨x, hx⟩ ⟨y, hy⟩ := by
    let := P.val.addInvariant
    exact (gauge_eq P (x - y) (P.val.dom.sub_mem hx hy)).trans
      (P.val.dist.sub_zero_eq ⟨x, hx⟩ ⟨y, hy⟩)
  have cover (x y z : U) :
      ∃ P : C, (x : V) ∈ P.val.dom ∧ (y : V) ∈ P.val.dom ∧ (z : V) ∈ P.val.dom := by
    obtain ⟨P, hx⟩ := stage x
    obtain ⟨Q, hy⟩ := stage y
    obtain ⟨T, hz⟩ := stage z
    obtain ⟨L, hp, hq⟩ := dir P Q
    obtain ⟨A, hl, ht⟩ := dir L T
    exact ⟨A, hl (hp hx), hl (hq hy), ht hz⟩
  let e : PseudoMetric U Γ := {
    toFun := delta
    refl' := fun x ↦ (eqOn _ (stage x).choose_spec (stage x).choose_spec).trans
      ((stage x).choose.val.dist.refl _)
    symm' := by
      intro x y
      obtain ⟨P, hx, hy, _⟩ := cover x y y
      exact (eqOn P hx hy).trans <| (P.val.dist.symm _ _).trans (eqOn P hy hx).symm
    triangle' := by
      intro x y z
      obtain ⟨P, hx, hy, hz⟩ := cover x y z
      rw [eqOn P hx hy, eqOn P hy hz, eqOn P hx hz]
      exact P.val.dist.triangle .. }
  have contains (x : E) : j x ∈ U :=
    hle ⟨hne.choose, hne.choose_spec⟩ (hne.choose.contains x)
  let Q : Stage d j := {
    dom := U
    contains := contains
    dist := e
    ultra := ⟨fun x y z ↦ by
      obtain ⟨P, hx, hy, hz⟩ := cover x y z
      change delta x z ≤ delta x y ⊔ delta y z
      rw [eqOn P hx hy, eqOn P hy hz, eqOn P hx hz]
      exact P.val.ultra.le_sup' ..⟩
    addInvariant := ⟨fun x y a ↦ by
      change gauge (x + a - (y + a)) = gauge (x - y)
      rw [add_sub_add_right_eq_sub]⟩
    smulMono := ⟨fun a {x y} h ↦ by
      obtain ⟨P, hx, hy, _⟩ := cover x y y
      change delta x 0 ≤ delta y 0 at h
      change delta (a • x) 0 ≤ delta (a • y) 0
      rw [eqOn P hx P.val.dom.zero_mem, eqOn P hy P.val.dom.zero_mem] at h
      rw [eqOn P (P.val.dom.smul_mem a hx) P.val.dom.zero_mem,
        eqOn P (P.val.dom.smul_mem a hy) P.val.dom.zero_mem]
      exact P.val.smulMono.smul_le a h⟩
    agrees := fun x y ↦
      (eqOn ⟨hne.choose, hne.choose_spec⟩ (hne.choose.contains x) (hne.choose.contains y)).trans
        (hne.choose.agrees x y)
    immediate := by
      intro x hx
      obtain ⟨P, hxP⟩ := stage x
      have hout : (⟨x, hxP⟩ : P.val.dom) ∉ Set.range P.val.embedding := by
        rintro ⟨z, hz⟩
        have hv : j z = (x : V) := congrArg (fun w : P.val.dom ↦ (w : V)) hz
        exact hx ⟨z, Subtype.ext hv⟩
      obtain ⟨hn, hi⟩ := P.val.immediate _ hout
      refine ⟨hn, fun a ↦ ?_⟩
      obtain ⟨b, hb⟩ := hi a
      refine ⟨b, ?_⟩
      change delta x _ < delta x _
      rwa [eqOn P hxP (P.val.contains b), eqOn P hxP (P.val.contains a)] }
  exact ⟨Q, fun P hP ↦ ⟨hle ⟨P, hP⟩, fun x y ↦ eqOn ⟨P, hP⟩ x.prop y.prop⟩⟩

/-- A fixed ambient module admits a maximal extension of the distance on the base. -/
theorem exists_maximal (start : Stage d j) :
    ∃ P : Stage d j, ∀ Q : Stage d j, P.Extends Q → Q.Extends P := by
  let : Nonempty (Stage d j) := ⟨start⟩
  exact exists_maximal_of_nonempty_chains_bounded chain_upperBound Extends.trans

end Stage

end PseudoMetric.LinearSphericalCompletion
