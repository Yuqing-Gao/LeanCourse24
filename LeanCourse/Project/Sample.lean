import Mathlib

/- Fredholm Operators over a fixed field enable notation. -/
open Function Set Classical LinearMap ContinuousLinearMap Submodule

section

/-Remark: During the project, we would like to work in the field ℝ. we are not familiar
with functional analysis over other normed fields. But, In the definition we can still
consider general normed fields-/
class FredholmOperators
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] [CompleteSpace E]
  (f : E →L[𝕜] F) : Prop :=
    (finite_dimensional_kernel : FiniteDimensional 𝕜 (LinearMap.ker f))
    (closed_range : IsClosed (LinearMap.range f:Set F))
    (finite_dimensional_cokernel : FiniteDimensional 𝕜 (F ⧸ LinearMap.range (f)))

/-- Fred(X, Y) is the set of Fredholm operators between X and Y -/
def Fred
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F] :
  Set (E →L[𝕜] F) :={ f | FredholmOperators f }

namespace FredholmOperators
/-- Kernel of a Fredholm operator -/
def ker {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] [CompleteSpace E]
  (f : E →L[𝕜] F): Submodule 𝕜 E :=
    LinearMap.ker f

/-- Range of a Fredholm operator -/
def ran {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] [CompleteSpace E]
  (f : E →L[𝕜] F): Submodule 𝕜 F :=
    LinearMap.range f

/-- Cokernel of a Fredholm operator -/
def coker {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] [CompleteSpace E]
  (f : E →L[𝕜] F) :Module 𝕜 (F ⧸ LinearMap.range (f)) :=
    Submodule.Quotient.module (LinearMap.range f)

noncomputable def ind {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] [CompleteSpace E]
  (f : E →L[𝕜] F) [FredholmOperators f] : ℤ :=
      Module.finrank 𝕜 (ker f) - Module.finrank 𝕜 (F ⧸ ran f)
      /-The Module.finrank is non-computable-/
end FredholmOperators

/-Lemma: Let T : X → Y be a operator so that the range admits a closed
complementary subspace. Then the range of T is closed.-/
lemma RangeClosedIfAdmittingRangeClosedCompletement
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F) [CompleteSpace F] [CompleteSpace E]
  (h : ∃ C : Subspace ℝ F, IsClosed (C : Set F) ∧ IsCompl (LinearMap.range f) C):
  IsClosed (LinearMap.range f : Set F):=by
    -- Extract the closed complement `C` and its properties
    obtain ⟨C, hC_closed, hC_compl⟩ := h
    -- Since `C` is a closed submodule of `F`, it inherits a complete normed space structure
    haveI : NormedAddCommGroup C := Submodule.normedAddCommGroup C
    haveI : NormedSpace ℝ C := Submodule.normedSpace C
    haveI : CompleteSpace C := IsClosed.completeSpace_coe hC_closed
    -- The kernel of `f` is closed because `f` is continuous, So the quotient is well-behaved
    have : IsClosed (LinearMap.ker f : Set E) := ContinuousLinearMap.isClosed_ker f
    -- Consider the quotient space `Ē = E / ker f`
    let E_bar := E ⧸ LinearMap.ker f
    haveI : NormedAddCommGroup E_bar :=Submodule.Quotient.normedAddCommGroup (LinearMap.ker f)
    haveI : NormedSpace ℝ E_bar := Submodule.Quotient.normedSpace (LinearMap.ker f) ℝ
    haveI : CompleteSpace E_bar := Submodule.Quotient.completeSpace (LinearMap.ker f)
    -- Define the induced map `f̄ : Ē → F`
    /- Remark 1. We couldn't believe that we don't have a direct lift method for ContinuousLinearMap QAQ. We have to firstly
    translate a ContinuousLinearMap into a BoundedLinearMap, use BoundedLinearMap.lift and then translate
    back. Also this is not the end of story, since in this case the resulting morphism is not defined
    directly via universal property(like using NormedAddGroupHom.lift), so in the rest of the proof we have to
    check element-wisely to get something we want, e.g the resulting morphism has the same range as the original
    morphism and it's injective... This brings many unnecessay workloads.
    -/
    let  f_bar_l':NormedAddGroupHom E F:=by
      use f.toFun
      simp
      obtain ⟨M,⟨hM₁,hM₂⟩⟩:=(ContinuousLinearMap.isBoundedLinearMap f).bound
      use M
      exact hM₂
    have hf:∀ s ∈ Submodule.toAddSubgroup (LinearMap.ker f), f_bar_l' s = 0:=by
      simp
      exact fun s a ↦ a
    let f_bar_l : NormedAddGroupHom (E ⧸ LinearMap.ker f) F :=NormedAddGroupHom.lift (Submodule.toAddSubgroup (LinearMap.ker f) :AddSubgroup E) (f_bar_l': NormedAddGroupHom E F) hf
    let f_bar : E_bar →L[ℝ] F:={
      toFun:=f_bar_l.toFun
      map_add':=by
        simp
      map_smul':=by
        simp
        intro m x
        induction x using Quotient.ind; rename_i x
        have h₁:∀x:E, f_bar_l ⟦x⟧=f x:=by exact fun x ↦ rfl
        have h₂:∀x:E, (⟦x⟧:E_bar)=Submodule.Quotient.mk x:=by exact fun x ↦ rfl
        rw [h₂]
        have h₃:Submodule.Quotient.mk (m • x)=m • (Submodule.Quotient.mk x):=Submodule.Quotient.mk_smul (LinearMap.ker f) m x
        rw[←h₃,←h₂,←h₂,h₁,h₁]
        exact ContinuousLinearMap.map_smul_of_tower f m x}
    -- range f = range f_bar
    have hrange: LinearMap.range f=LinearMap.range f_bar:=by
      sorry /-Check this by picking elements f_bar([x]) from the range, omitted until we have time. See remark 1-/
    have hinjectivity: Injective f.toFun:=by
      sorry /-Also clear from the constrcution, ommitted until we have time. See remark 1-/
    rw[hrange] at hC_compl
    rw[hrange]


/-Theorem: If T : X → Y is a bounded invertible operator then for all
p : X → Y with sufficiently small norm T + p is also invertible.-/
theorem BoundedInvertibleOperatorPlusεIsInvertible
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F)[CompleteSpace E] [CompleteSpace F]
  (hT_inv : ∃ f_inv : F →L[ℝ] E, f.comp f_inv = ContinuousLinearMap.id ℝ F ∧ f_inv.comp f = ContinuousLinearMap.id ℝ E)
  :∃ε :ℝ ,ε>0 ∧
  ∀ (p:E →L[ℝ] F) ,‖p‖ < ε →
    ∃ S_inv : F →L[ℝ] E,(f + p).comp S_inv = ContinuousLinearMap.id ℝ F ∧
    S_inv.comp (f + p) = ContinuousLinearMap.id ℝ E :=sorry

/-(Riesz Theorem): The unit ball B in a Banach space X is compact if and
only if B is finite dimensional.-/
/-Omitted. Since Riesz Theorem is already in mathlib-/

/-Lemma: The following are equivalent:
1. ker(T) is finite dimensional and Ran(T) is closed.
2. Every bounded sequence {xᵢ} ⊆ X with Txᵢ convergent has a convergent
subsequence.-/
lemma FinDimKerAndClosedRanCriterion
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]:
  ∀(f : E →L[ℝ] F),
    (FiniteDimensional ℝ  (LinearMap.ker f)) ∧ IsClosed (LinearMap.range f:Set F)↔
    (∀ (x_seq : ℕ → E) (h_bounded : ∃ C, ∀ n, ‖x_seq n‖ ≤ C),
      (h_convergent : ∃ y : F, Filter.Tendsto (λ n↦ f (x_seq n)) Filter.atTop (nhds y))→
      ∃ x_subseq : ℕ → E, ∃ φ : ℕ → ℕ,
        x_subseq=x_seq ∘ φ ∧
        StrictMono φ ∧
        ∃ y : E, Filter.Tendsto (x_subseq) Filter.atTop (nhds (y))) :=sorry

/-Theorem: Fred(X,Y) is a open subset of B(X,Y)-/
theorem OpennessFredholm
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]:
  IsOpen ((Fred E F):Set (E →L[ℝ] F))
  :=sorry

/-Theorem: the index is a locally constant function on Fred(X, Y)-/
theorem IndexLocallyConstantFredholm
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]
  (f : (E →L[ℝ] F)) [FredholmOperators f]:
  ∃ (U : Set (E →L[ℝ] F)), IsOpen U ∧ f ∈ U ∧
  (∀g[FredholmOperators g], g∈ U→ FredholmOperators.ind f = FredholmOperators.ind g ):=sorry

/-Lemma: Let T : X → Y be a Fredholm map and p : X → Y a linear map.
If p has sufficiently small norm then there are isomorphisms i: X'⊕ K → X and
j: Y → X'⊕C so that j◦(T + p)◦i is the diag(id_{X'} q) for some q: K → C -/
lemma DecompositionOfFredholmPlusε
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (f : (E →L[ℝ] F)) [FredholmOperators f]:
  ∃(ε:ℝ),ε>0∧ ∀(p:E→L[ℝ] F),‖p‖<ε →
    ∃ (E' : Type*) ,∃_:NormedAddCommGroup E' ,∃_:NormedSpace ℝ E',
    ∃ (K : Type*) ,∃_:NormedAddCommGroup K ,∃_:NormedSpace ℝ K,
    ∃ (C : Type*) ,∃_:NormedAddCommGroup C ,∃_:NormedSpace ℝ C,
    ∃ (i :  (E'× K)≃L[ℝ] E), ∃(j: F≃L[ℝ] E'×C), ∃ q:K →L[ℝ] C,
      j∘ (f + p) ∘ i = λ⟨a,b⟩↦⟨a,q b⟩:=by sorry
end
