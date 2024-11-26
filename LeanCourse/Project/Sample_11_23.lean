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
def ran {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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
/-Lemma: Let T : X → Y be a operator so that the range admits a closed
complementary subspace. Then the range of T is closed.-/

lemma RangeClosedIfAdmittingRangeClosedCompletement
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F) [CompleteSpace F] [CompleteSpace E]
  (h : ∃ C : Subspace ℝ F, IsClosed (C : Set F) ∧
      ∀ y : F, ∃ u c : F,
        u ∈ LinearMap.range f ∧
        c ∈ C ∧ u + c = y ∧
        ∀ u' c' : F,
          u' ∈ LinearMap.range f ∧ c' ∈ C ∧ u' + c' = y → u' = u ∧ c' = c) :
  IsClosed (LinearMap.range f : Set F):= by
    sorry

/-Theorem: If T : X → Y is a bounded invertible operator then for all
p : X → Y with sufficiently small norm T + p is also invertible.-/
theorem BoundedInvertibleOperatorPlusεIsInvertible
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F)[CompleteSpace E] [CompleteSpace F]
  (hT_inv : ∃ f_inv : F →L[ℝ] E, f.comp f_inv = ContinuousLinearMap.id ℝ F ∧ f_inv.comp f = ContinuousLinearMap.id ℝ E)
  (p : E →L[ℝ] F) (hp_small : ‖p‖ < ‖f‖)/-I am not sure if ‖f‖ works here, maybe replace it with something else-/
  :∃ S_inv : F →L[ℝ] E, (f + p).comp S_inv = ContinuousLinearMap.id ℝ F ∧ S_inv.comp (f + p) = ContinuousLinearMap.id ℝ E :=sorry

/-(Riesz Theorem): The unit ball B in a Banach space X is compact if and
only if B is finite dimensional.-/
/-Omitted. Since Riesz Theorem is already in mathlib-/

/-Lemma: The following are equivalent:
1. ker(T) is finite dimensional and Ran(T) is closed.
2. Every bounded sequence {xᵢ} ⊂ X with T xᵢ convergent has a convergent
subsequence.-/

lemma FinDimKerAndClosedRanCriterion
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]:
  ∀(f : E →L[ℝ] F),
    (FiniteDimensional ℝ  (LinearMap.ker f)) ∧ IsClosed (LinearMap.range f:Set F) ↔
    (∀ (x_seq : ℕ → E) (h_bounded : ∃ C, ∀ n, ‖x_seq n‖ ≤ C),
      (h_convergent : ∃ y : F, Filter.Tendsto (λ n↦ f (x_seq n)) Filter.atTop (nhds y)) →
      ∃ x_subseq : ℕ → E, ∃ φ : ℕ → ℕ,
        x_subseq=x_seq ∘ φ ∧
        StrictMono φ ∧
        ∃ y : E, Filter.Tendsto (x_subseq) Filter.atTop (nhds (y))) :=sorry



end
