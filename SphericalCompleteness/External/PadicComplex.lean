import SphericalCompleteness.External.PadicAlgCl
import SphericalCompleteness.External.DenselyNormedField

open PadicAlgCl
open Polynomial
open PadicComplex

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable instance instDenselyNormedFieldPadicComplex : DenselyNormedField ℂ_[p] :=
  inferInstance

instance instSeparableSpacePadicComplex : TopologicalSpace.SeparableSpace ℂ_[p] := inferInstance

--theorem cnmd : NonUnitalSeminormedRing.toSeminormedAddCommGroup.toNorm = (instNormedField p).toNorm := by sorry

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜]
[IsUltrametricDist 𝕜] :
  @IsUltrametricDist (UniformSpace.Completion 𝕜)
  UniformSpace.Completion.instMetricSpace.toDist where
  dist_triangle_max x y z := by
    have := @UniformSpace.Completion.denseRange_coe 𝕜 _
    apply le_of_forall_pos_lt_add
    intro ε hε
    rcases Metric.mem_closure_iff.1 (this x) (ε / 4) (by linarith) with ⟨x'', hx'1, hx'2⟩
    simp at hx'1
    rcases hx'1 with ⟨x', hx'⟩
    rw [← hx'] at hx'2
    rcases Metric.mem_closure_iff.1 (this y) (ε / 4) (by linarith) with ⟨y'', hy'1, hy'2⟩
    simp at hy'1
    rcases hy'1 with ⟨y', hy'⟩
    rw [← hy'] at hy'2
    rcases Metric.mem_closure_iff.1 (this z) (ε / 4) (by linarith) with ⟨z'', hz'1, hz'2⟩
    simp at hz'1
    rcases hz'1 with ⟨z', hz'⟩
    rw [← hz'] at hz'2
    clear hx' x'' hy' y'' hz' z''
    have t1 := dist_triangle x ↑x' z
    have t2 := dist_triangle ↑x' ↑z' z
    have : dist x z < dist (↑x' : UniformSpace.Completion 𝕜) ↑z' + ε / 4 + ε / 4 := by
      rw [dist_comm] at hz'2
      linarith
    refine lt_trans this ?_
    have t3 := dist_triangle_max x' y' z'
    rw [← UniformSpace.Completion.dist_eq] at t3
    nth_rw 2 [← UniformSpace.Completion.dist_eq] at t3
    nth_rw 3 [← UniformSpace.Completion.dist_eq] at t3
    have t4 := dist_triangle ↑x' x ↑y'
    nth_rw 2 [dist_comm] at t4
    have t5 := dist_triangle x y ↑y'
    have t6 := dist_triangle ↑y' y ↑z'
    nth_rw 2 [dist_comm] at t6
    have t7 := dist_triangle y z ↑z'
    nth_rw 3 [(by linarith : ε = ε / 4 + ε / 4 + ε / 4 + ε / 4)]
    have t8 : max (dist x y) (dist y z) + (ε / 4 + ε / 4 + ε / 4 + ε / 4) = max (dist x y) (dist y z) + (ε / 4 + ε / 4) + ε / 4 + ε / 4 := by linarith
    rw [t8, max_add]
    nth_rw 1 [add_assoc]
    nth_rw 1 [add_assoc]
    simp only [add_lt_add_iff_right]
    refine lt_of_le_of_lt t3 ?_
    sorry

instance : @IsUltrametricDist ℂ_[p] UniformSpace.Completion.instMetricSpace.toDist := inferInstance
