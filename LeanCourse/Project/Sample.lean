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
  IsClosed (LinearMap.range f : Set F):= by
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
    let f_bar_l':NormedAddGroupHom E F := by
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
    have hrange: LinearMap.range f=LinearMap.range f_bar := by
      /-Check this by picking elements f_bar([x]) from the range, omitted until we have time. See remark 1-/
      sorry
    have hinjectivity: Injective f.toFun:=by
      /-Also clear from the constrcution, ommitted until we have time. See remark 1-/
      sorry
    rw[hrange] at hC_compl
    rw[hrange]
    -- define a morphism S: E_bar ⨁ C→ F, which we will show to be an isomorphism
    let S: E_bar × C →L[ℝ] F:={
      toFun:=λ⟨a,b⟩ ↦ (f_bar a) + b
      map_add':=by
        intro x y
        simp
        abel
      map_smul':=by
        intro m ⟨a,b⟩
        simp
    }
    -- S is an bijective continuous linear map. Here is where we apply the assumpption about C
    rw[isCompl_iff] at hC_compl
    obtain ⟨hC_compl_inj,hC_compl_sur⟩:=hC_compl
    have hSinjective: Injective S:=by
      by_contra hninjS
      unfold Injective  at hninjS
      push_neg at hninjS
      obtain ⟨⟨a₁,a₂⟩,⟨b₁,b₂⟩,hfab,hab⟩:=hninjS
      unfold S at hfab
      simp at hfab
      unfold Disjoint at hC_compl_inj
      /-Here is trivial, f_bar a₁ - f_bar b₁ belongs to both C and range f_bar.
      Now invoke hC_compl_inj and the injectivity of f_bar we get a₁=b₁, a₂=b₂, from which we deduce
      a contradiction-/
      sorry
    have hSsurjective: Surjective S:=by
      unfold Codisjoint at hC_compl_sur
      /-Much simpler than hSinjective, we just apply hC_compl_sur to range S-/
      sorry

    /- Now we apply open mapping theorem to S to show it's a isomorphism in the category of Banach spaces.
    Then the closed subset E_bar of E_bar ⨁ C under this homeomorphism S should corresponds to a closed subset
    in F, namely the range f_bar =range f-/




-- 可逆性
def IsInvertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →L[ℝ] F) : Prop :=
  ∃ inv : F →L[ℝ] E, f.comp inv = ContinuousLinearMap.id ℝ F ∧ inv.comp f = ContinuousLinearMap.id ℝ E

-- 获取逆算子
noncomputable def get_inv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (hf : IsInvertible f) : F →L[ℝ] E := Classical.choose hf

-- 逆算子性质
lemma get_inv_spec {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (hf : IsInvertible f) :
    f.comp (get_inv hf) = ContinuousLinearMap.id ℝ F ∧ (get_inv hf).comp f = ContinuousLinearMap.id ℝ E := Classical.choose_spec hf

-- 复合算子可逆
lemma IsInvertible.comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F →L[ℝ] G} {g : E →L[ℝ] F}
    (hf : IsInvertible f) (hg : IsInvertible g) :
    IsInvertible (f.comp g) := by
  let f_inv := get_inv hf
  let g_inv := get_inv hg
  have ⟨hf_left, hf_right⟩ := get_inv_spec hf
  have ⟨hg_left, hg_right⟩ := get_inv_spec hg
  use g_inv.comp f_inv
  constructor
  · -- 左逆
    rw [ContinuousLinearMap.comp_assoc]
    conv => left; right; rw [← ContinuousLinearMap.comp_assoc, hg_left]; simp
    exact hf_left
  · -- 右逆
    rw [ContinuousLinearMap.comp_assoc]
    conv => left; right; rw [← ContinuousLinearMap.comp_assoc, hf_right]; simp
    exact hg_right

-- 复合算子的范数估计
#check ContinuousLinearMap.opNorm_comp_le

-- 如果存在可逆映射，那么codomain不是平凡的
lemma exists_of_invertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (hf : IsInvertible f) :
    ∃ y : F, y ≠ 0 := by
      by_contra FisTrivial
      push_neg at FisTrivial
      let f_inv := get_inv hf
      have ⟨hleft, hright⟩ := get_inv_spec hf
      have f_zero : ∀ x : E, f x = 0 := by
        intro x
        exact FisTrivial (f x)
      have comp_zero : f_inv.comp f = 0 := by
        ext x
        simp [ContinuousLinearMap.comp_apply, f_zero]
      rw [comp_zero] at hright
      contrapose! hright
      rw [← ContinuousLinearMap.one_def]
      by_contra h01

      sorry

-- 逆算子的范数是正的
lemma inv_norm_pos {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (hf : IsInvertible f) :
    ‖get_inv hf‖ ≠ 0 := by
  intro h
  -- 如果范数为0，那么这个算子必然是0算子
  have h1 : get_inv hf = 0 := by
    simp only [ContinuousLinearMap.ext_iff]
    intro x
    have := le_trans ((get_inv hf).le_opNorm x) (by rw [h, zero_mul])
    rw [norm_le_zero_iff] at this
    exact this
  -- 但这与逆算子的性质矛盾，0算子不可能是恒等映射
  have := (get_inv_spec hf).1  -- f.comp (get_inv hf) = id
  rw [h1] at this
  simp at this
  have : (0 : F →L[ℝ] F) ≠ ContinuousLinearMap.id ℝ F := by
    intro h2
    have ⟨y, hy⟩ := exists_of_invertible hf
    have : (0 : F →L[ℝ] F) y = y := by
      rw [h2]
      rfl
    rw [ContinuousLinearMap.zero_apply] at this
    exact hy this.symm
  contradiction

-- neumann 级数收敛
#check tsum_geometric_nnreal
#check tsum_coe_mul_geometric_of_norm_lt_one

/-Theorem: If T : X → Y is a bounded invertible operator then for all
p : X → Y with sufficiently small norm T + p is also invertible.-/
theorem BoundedInvertibleOperatorPlusεIsInvertible
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F) [CompleteSpace E] [CompleteSpace F]
  (hf : IsInvertible f) :
  ∃ (ε : ℝ), ε > 0 ∧ ∀ (p : E →L[ℝ] F), ‖p‖ < ε → IsInvertible (f + p) := by
    have ⟨hf_left, hf_right⟩ := get_inv_spec hf
    let f_inv := get_inv hf
    suffices specialcase : ∃ ε₁ > 0, ∀ (q : E →L[ℝ] E), ‖q‖ < ε₁ → @IsInvertible E E _ _ _ _ (ContinuousLinearMap.id ℝ E + q)
    · obtain ⟨ε₁, hε₁_pos, h⟩ := specialcase
      use ε₁ / ‖f_inv‖
      constructor
      · refine div_pos hε₁_pos ?h.left.hb
        unfold f_inv
        exact Ne.lt_of_le (Ne.symm (inv_norm_pos hf)) (norm_nonneg f_inv)
      · intro p hp
        let q := f_inv.comp p
        have q_small : ‖q‖ < ε₁ := by
          unfold q
          have := ContinuousLinearMap.opNorm_comp_le f_inv p
          calc ‖f_inv.comp p‖
            ≤ ‖f_inv‖ * ‖p‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ < ‖f_inv‖ * (ε₁/‖f_inv‖) := by
            gcongr
            unfold f_inv
            exact Ne.lt_of_le (Ne.symm (inv_norm_pos hf)) (norm_nonneg f_inv)
          _ = ε₁ := by
            field_simp
            refine mul_div_cancel_left₀ ε₁ ?ha
            exact inv_norm_pos hf
        have h_mid := h q q_small
        have decomp : f + p = f.comp (ContinuousLinearMap.id ℝ E + q) := by
          ext x
          simp only [ContinuousLinearMap.add_apply]
          apply Eq.symm
          calc f ((ContinuousLinearMap.id ℝ E + q) x)
              = f (x + (f_inv (p x))) := by rfl
            _ = f x + p x := by
              rw [ContinuousLinearMap.map_add]
              simp
              have := ContinuousLinearMap.comp_apply f f_inv (p x)
              rw [← this, hf_left]
              simp
        have : IsInvertible (f.comp (ContinuousLinearMap.id ℝ E + q)) := IsInvertible.comp hf h_mid
        rw [← decomp] at this
        exact this
    · -- ⊢ ∃ ε₁ > 0, ∀ (q : E →L[ℝ] E), ‖q‖ < ε₁ → IsInvertible (ContinuousLinearMap.id ℝ E + q)
      sorry

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
