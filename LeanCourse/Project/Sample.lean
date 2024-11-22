import Mathlib

/- Fredholm Operators over a fixed field enable notation. -/
open Function Set Classical

noncomputable section

/-Remark: During the project, I would like to work in the field ℝ. I am not familiar
with functional analysis over other normed fields. But, In the definition I can still
consider general normed fields-/
class FredholmOperators
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →L[𝕜] F) [CompleteSpace F] [CompleteSpace E] : Prop :=
  (finite_dimensional_kernel : FiniteDimensional 𝕜 (LinearMap.ker f))
  (closed_range : IsClosed (LinearMap.range f:Set F))
  (finite_dimensional_cokernel : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (f)))

namespace FredholmOperators
/-- Kernel of a Fredholm operator -/
def ker {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →L[𝕜] F) : Submodule 𝕜 E :=LinearMap.ker f

/-- Range of a Fredholm operator -/
def range {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →L[𝕜] F) : Submodule 𝕜 F :=LinearMap.range f

/-- Cokernel of a Fredholm operator -/
def coker {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →L[𝕜] F) :Module 𝕜 (F ⧸ LinearMap.range (f)) :=
    Submodule.Quotient.module (LinearMap.range f)

end FredholmOperators
end

section
/-Remark: Let T : X → Y be a operator so that the range admits a closed
complementary subspace. Then the range of T is closed.-/
lemma RangeClosedIfAdmint
