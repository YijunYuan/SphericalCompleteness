import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.Normed.Module.Completion

noncomputable instance instDenselyNormedFieldCompletionOfCompletion
{α : Type*} [hdnf : DenselyNormedField α] [CompletableTopField α] :
DenselyNormedField (UniformSpace.Completion α) where
  __ : NormedField (UniformSpace.Completion α) := inferInstance
  lt_norm_lt x y hx hxy := by
    rcases hdnf.lt_norm_lt x y hx hxy with ⟨z, hz⟩
    use z
    simp only [UniformSpace.Completion.norm_coe, hz, and_self]
