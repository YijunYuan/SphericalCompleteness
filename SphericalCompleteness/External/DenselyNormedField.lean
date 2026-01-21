import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Analysis.Normed.Module.Completion

/--
Instantiates `DenselyNormedField` on `UniformSpace.Completion α`.

Assuming `α` is a densely normed field and also a `CompletableTopField`, its uniform
completion inherits a compatible `DenselyNormedField` structure. This allows one to
use the standard API for densely normed fields (e.g. density of the norm range, lemmas
about balls, and approximation arguments) directly on `UniformSpace.Completion α`.

This instance is marked `noncomputable` because the completion and its induced
structures are not definitional/computational in general.
-/
noncomputable instance instDenselyNormedFieldCompletionOfCompletion
{α : Type*} [hdnf : DenselyNormedField α] [CompletableTopField α] :
DenselyNormedField (UniformSpace.Completion α) where
  __ : NormedField (UniformSpace.Completion α) := inferInstance
  lt_norm_lt x y hx hxy := by
    rcases hdnf.lt_norm_lt x y hx hxy with ⟨z, hz⟩
    use z
    simp only [UniformSpace.Completion.norm_coe, hz, and_self]
