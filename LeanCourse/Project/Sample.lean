import Mathlib
import Mathlib.Topology.Basic

/- Fredholm Operators over a fixed field enable notation. -/
open Function Set Classical LinearMap ContinuousLinearMap Submodule

section ContinuousLinearMap
/-This section contains some auxiliary definitions and lemmas-/
def ContinuousLinearMap.coker {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →L[𝕜] F) : Module 𝕜 (F ⧸ LinearMap.range (f)) :=
    Submodule.Quotient.module (LinearMap.range f)
end ContinuousLinearMap

section FredholmOperatorsDef

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

/-Lemma: A continous linear map f:E →L[ℝ] F induces a continous linear map
f_bar:E/ker(f) →L[R] F-/
noncomputable def QuotientOfContinuousLinearMap
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F): E ⧸ (LinearMap.ker f) →L[ℝ] F:=by
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
    let f_bar : E ⧸ (LinearMap.ker f) →L[ℝ] F:={
      toFun:=f_bar_l.toFun
      map_add':=by
        simp
      map_smul':=by
        simp
        intro m x
        induction x using Quotient.ind; rename_i x
        have h₁:∀x:E, f_bar_l ⟦x⟧=f x:=by exact fun x ↦ rfl
        have h₂:∀x:E, (⟦x⟧:E ⧸ (LinearMap.ker f))=Submodule.Quotient.mk x:=by exact fun x ↦ rfl
        rw [h₂]
        have h₃:Submodule.Quotient.mk (m • x)=m • (Submodule.Quotient.mk x):=Submodule.Quotient.mk_smul (LinearMap.ker f) m x
        rw[←h₃,←h₂,←h₂,h₁,h₁]
        exact ContinuousLinearMap.map_smul_of_tower f m x}
    use f_bar
    continuity

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
    letI : NormedAddCommGroup C := Submodule.normedAddCommGroup C
    letI : NormedSpace ℝ C := Submodule.normedSpace C
    letI : CompleteSpace C := IsClosed.completeSpace_coe hC_closed
    -- The kernel of `f` is closed because `f` is continuous, So the quotient is well-behaved
    have : IsClosed (LinearMap.ker f : Set E) := ContinuousLinearMap.isClosed_ker f
    -- Consider the quotient space `Ē = E / ker f`
    let E_bar := E ⧸ LinearMap.ker f
    letI : NormedAddCommGroup E_bar :=Submodule.Quotient.normedAddCommGroup (LinearMap.ker f)
    letI : NormedSpace ℝ E_bar := Submodule.Quotient.normedSpace (LinearMap.ker f) ℝ
    letI : CompleteSpace E_bar := Submodule.Quotient.completeSpace (LinearMap.ker f)
    -- Define the induced map `f̄ : Ē → F`
    let f_bar : E_bar →L[ℝ] F:=QuotientOfContinuousLinearMap f
    -- range f = range f_bar
    have hrange: LinearMap.range f=LinearMap.range f_bar := by
      /-Check this by picking elements f_bar([x]) from the range, omitted until we have time.-/
      sorry
    have hinjectivity: Injective f.toFun:=by
      /-Also clear from the constrcution, ommitted until we have time.-/
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
    have hSBijective:Bijective S:=by
      exact ⟨hSinjective,hSsurjective⟩
    let S':= (Equiv.ofBijective S hSBijective)
    have h₁S':Continuous ⇑S':=by
      have hSS':⇑S'=⇑S:=by rfl
      rw[hSS']
      exact ContinuousLinearMap.continuous S
    /-apply the open mapping theorem to show S is open-/
    have h₂S':IsOpenMap ⇑S':=by
      have hSS':⇑S'=⇑S:=by rfl
      rw[hSS']
      apply ContinuousLinearMap.isOpenMap S hSsurjective
    /-continous open bijective map is homeomorphism-/
    let s:=Homeomorph.homeomorphOfContinuousOpen S' h₁S' h₂S'
    /-We have a homeomorphism s between E_bar⨁C and F, now range f is closed because under this
    homeomorphism E_bar⨁0 is closed-/
    sorry


-- Invertibility
def IsInvertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →L[ℝ] F) : Prop :=
  ∃ inv : F →L[ℝ] E, f.comp inv = ContinuousLinearMap.id ℝ F ∧ inv.comp f = ContinuousLinearMap.id ℝ E

-- Define the inverse operator
noncomputable def get_inv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (hf : IsInvertible f) : F →L[ℝ] E := Classical.choose hf

-- The property of inverse operator
lemma get_inv_spec {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (hf : IsInvertible f) :
    f.comp (get_inv hf) = ContinuousLinearMap.id ℝ F ∧ (get_inv hf).comp f = ContinuousLinearMap.id ℝ E := Classical.choose_spec hf

-- The composition of operators is invertible
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
  · -- left inverse
    rw [ContinuousLinearMap.comp_assoc]
    conv => left; right; rw [← ContinuousLinearMap.comp_assoc, hg_left]; simp
    exact hf_left
  · -- right inverse
    rw [ContinuousLinearMap.comp_assoc]
    conv => left; right; rw [← ContinuousLinearMap.comp_assoc, hf_right]; simp
    exact hg_right

-- id 可逆
lemma Isinvertible.id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  : IsInvertible (ContinuousLinearMap.id ℝ E) := by
  rw [IsInvertible]
  let inv := ContinuousLinearMap.id ℝ E
  use inv
  simp

-- Codomain is not trivial if there exists inverse operator
lemma exists_of_invertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial E] {f : E →L[ℝ] F}
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
      exact zero_ne_one' (E →L[ℝ] E)

-- 逆算子的范数是正的
lemma inv_norm_pos {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial E] {f : E →L[ℝ] F}
    (hf : IsInvertible f) :
    ‖get_inv hf‖ ≠ 0 := by
  intro h
  -- If norm of a operator is 0, then it's trivial
  have h1 : get_inv hf = 0 := by
    simp only [ContinuousLinearMap.ext_iff]
    intro x
    have := le_trans ((get_inv hf).le_opNorm x) (by rw [h, zero_mul])
    rw [norm_le_zero_iff] at this
    exact this
  -- 0 operator is not identity
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

-- neumann 级数收敛（算子版本）
open Filter
open Topology

lemma ContinuousLinearMap.tendsto_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E →L[ℝ] E} {f : ℕ → E →L[ℝ] E} {g : E →L[ℝ] E}
  (h : Tendsto f atTop (𝓝 g)) :
  Tendsto (F.comp ∘ f) atTop (𝓝 (F.comp g)) := by
  by_cases hF: F = 0
  · simp [hF]
    rw [Metric.tendsto_atTop]
    intro ε hε
    use 0
    intro n _
    simp only [Function.comp_apply]
    have h1 : ∀ n, (0 : E →L[ℝ] E).comp (f n) = 0 := by
      intro n
      ext x
      simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_apply]
    simp [h1, hε]
  push_neg at hF
  rw [Metric.tendsto_atTop]
  intro ε hε
  have F_norm_pos : 0 < ‖F‖ := norm_pos_iff.mpr hF
  let ε' := ε / ‖F‖
  have ε'_pos : 0 < ε' := div_pos hε F_norm_pos
  rcases Metric.tendsto_atTop.mp h ε' ε'_pos with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  calc ‖F.comp (f n) - F.comp g‖ = ‖F.comp (f n - g)‖ := by rw [ContinuousLinearMap.comp_sub]
    _ ≤ ‖F‖ * ‖f n - g‖ := by apply ContinuousLinearMap.opNorm_comp_le
    _ < ‖F‖ * (ε / ‖F‖) := by exact mul_lt_mul_of_pos_left hN F_norm_pos
    _ = ε := by ring_nf; field_simp [F_norm_pos.ne']

lemma ContinuousLinearMap.tendsto_comp_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E →L[ℝ] E} {f : ℕ → E →L[ℝ] E} {g : E →L[ℝ] E}
  (h : Tendsto f atTop (𝓝 g)) :
  Tendsto (λ n => (f n).comp F) atTop (𝓝 (g.comp F)) := by
  by_cases hF: F = 0
  · simp [hF]
  push_neg at hF
  rw [Metric.tendsto_atTop]
  intro ε hε
  have F_norm_pos : 0 < ‖F‖ := norm_pos_iff.mpr hF
  let ε' := ε / ‖F‖
  have ε'_pos : 0 < ε' := div_pos hε F_norm_pos
  rcases Metric.tendsto_atTop.mp h ε' ε'_pos with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  calc ‖(f n).comp F - g.comp F‖ = ‖(f n - g).comp F‖ := by rw [ContinuousLinearMap.sub_comp]
    _ ≤ ‖f n - g‖ * ‖F‖ := by exact opNorm_comp_le (f n - g) F
    _ < (ε / ‖F‖) * ‖F‖ := by exact mul_lt_mul_of_pos_right hN F_norm_pos
    _ = ε := by ring_nf; field_simp [F_norm_pos.ne']

lemma ContinuousLinearMap.tendsto_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : ℕ → E →L[ℝ] E} {f' g' : E →L[ℝ] E}
  (hf : Tendsto f atTop (𝓝 f')) (hg : Tendsto g atTop (𝓝 g')) :
  Tendsto (λ n => f n - g n) atTop (𝓝 (f' - g')) := by
  rw [@Metric.tendsto_atTop] at hf hg ⊢
  intro ε hε
  let ε' := ε/2
  obtain ⟨N₁, hN₁⟩ := hf ε' (by positivity)
  obtain ⟨N₂, hN₂⟩ := hg ε' (by positivity)
  let N := max N₁ N₂
  use N

  intro n hn
  specialize hN₁ n (by exact le_trans (le_max_left _ _) hn)
  specialize hN₂ n (by exact le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm] at hN₁ hN₂

  calc ‖(f n - g n) - (f' - g')‖
      = ‖(f n - f') - (g n - g')‖ := by rw [@sub_sub_sub_comm]
    _ ≤ ‖f n - f'‖ + ‖g n - g'‖ := by apply norm_sub_le
    _ < ε' + ε' := by exact add_lt_add hN₁ hN₂
    _ = ε := by ring

lemma Finset.sum_zero_eq_add_sum_one_nat {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ)
  (h: 0 < k):
  ∑ x in Finset.Ico 0 k, f x = f 0 + ∑ x in Finset.Ico 1 k, f x := by
  have h1 : Ico 0 k = insert 0 (Ico 1 k) := by exact Eq.symm (Nat.Ico_insert_succ_left h)
  have h2 : 0 ∉ Ico 1 k := by simp [Finset.mem_Ico]
  rw [h1, Finset.sum_insert h2]

lemma sum_power_diff_eq_id_sub_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →L[ℝ] E) (k : ℕ):
  ∑ i in Finset.range k, (T^i - T^(i+1)) = ContinuousLinearMap.id ℝ E - T^k := by
  by_cases hk: k = 0
  · simp [hk]
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  push_neg at hk
  have : 0 < k := by exact Nat.zero_lt_of_ne_zero hk
  calc ∑ i in Finset.range k, (T^i - T^(i+1))
    = ∑ i in Finset.range k, T^i - ∑ i in Finset.range k, T^(i+1) := by apply Finset.sum_sub_distrib
    _ = (∑ i in Finset.range k, T^i) - (∑ j in Finset.range k, T^(j+1)) := by
      congr
    _ = T^0 + (∑ i in Finset.Ico 1 k, T^i) - (∑ j in Finset.Ico 1 (k+1), T^j) := by
      rw [Finset.range_eq_Ico, Finset.sum_zero_eq_add_sum_one_nat]
      · simp; rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add' (fun x => T^x) 0 k 1
      · exact this
    _ = T^0 + (∑ i in Finset.Ico 1 k, T^i) - ((∑ j in Finset.Ico 1 k, T^j) + T^k) := by
      simp
      rw [Finset.sum_Ico_succ_top]; exact this
    _ = T^0 - T^k := by
      rw [add_sub_assoc]; simp; exact Mathlib.Tactic.RingNF.add_neg 1 (T ^ k)
    _ = ContinuousLinearMap.id ℝ E - T^k := by
      rfl

lemma neumann_series_invertible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : E →L[ℝ] E} (hT : ‖T‖ < 1) (h_T_nonzero : ‖T‖ ≠ 0) :
  IsInvertible (ContinuousLinearMap.id ℝ E - T) := by
  unfold IsInvertible
  let Sk : ℕ → E →L[ℝ] E := λ k ↦ ∑ i in Finset.range (k), T^i
  have cauchy_Sk : CauchySeq Sk := by
    let θ := ‖T‖
    have θ_lt_1 : θ < 1 := hT
    have pow_bound : ∀ n : ℕ, ‖T^n‖ ≤ θ^n := by
      unfold θ
      intro n
      induction' n with d hd
      · simp only [pow_zero]
        rw [@one_def]
        exact norm_id_le
      · calc ‖T^(d+1)‖
            = ‖T * T^d‖ := by rw [@npow_add]; simp; rw [@pow_mul_comm']
          _ ≤ ‖T‖ * ‖T^d‖ := by exact NormedRing.norm_mul T (T ^ d)
          _ ≤ ‖T‖ * ‖T‖^d := by refine mul_le_mul_of_nonneg_left hd ?a0; exact ContinuousLinearMap.opNorm_nonneg T
          _ = θ^(d+1) := by exact Eq.symm (pow_succ' θ d)
    rw [@Metric.cauchySeq_iff]
    intro ε hε
    have h1 : 1 - θ > 0 := by linarith [θ_lt_1]
    let k₀ := Nat.ceil ((Real.log (ε) + Real.log (1-θ))/ Real.log (θ)) + 1 -- k₀ should be chosen properly
    use k₀
    intro l hl k hk
    rw [dist_eq_norm]
    unfold Sk
    -- 讨论k和l的大小
    by_cases hkl: k ≤ l
    have : ∑ i ∈ Finset.range l, T ^ i - ∑ i ∈ Finset.range k, T ^ i = ∑ i ∈ Finset.Ico k l, T ^ i := Eq.symm (Finset.sum_Ico_eq_sub (HPow.hPow T) hkl)
    calc ‖∑ i ∈ Finset.range l, T ^ i - ∑ i ∈ Finset.range k, T ^ i‖
        = ‖∑ i ∈ Finset.Ico k l, T ^ i‖ := by rw [this]
      _ ≤ ∑ i ∈ Finset.Ico k l, ‖T ^ i‖ := by
        induction Finset.Ico k l using Finset.induction with
        | empty => simp
        | @insert a s hs ih =>
          field_simp
          calc ‖T^a + ∑ i in s, T^i‖
              ≤ ‖T^a‖ + ‖∑ i in s, T^i‖ := ContinuousLinearMap.opNorm_add_le _ _
            _ ≤ ‖T^a‖ + ∑ i in s, ‖T^i‖ := by gcongr
      _ ≤ ∑ i ∈ Finset.Ico k l, θ^i := by exact Finset.sum_le_sum fun i a ↦ pow_bound i
      _ ≤ θ^(k)/(1-θ) := geom_sum_Ico_le_of_lt_one (ContinuousLinearMap.opNorm_nonneg T) hT
      _ < ε := by
        have h_log_neg : Real.log θ < 0 := by rw [← @Real.exp_lt_one_iff, Real.exp_log_eq_abs h_T_nonzero]; simp; exact hT
        have h_denom_pos : 1 - θ > 0 := by linarith [θ_lt_1]
        have h_theta_pos : θ > 0 := by unfold θ; exact (LE.le.gt_iff_ne (norm_nonneg T)).mpr h_T_nonzero
        have h_num_pos : θ ^ k > 0 := by exact pow_pos h_theta_pos k
        suffices: Real.log (θ^k / (1 - θ)) < Real.log ε
        · apply (Real.log_lt_log_iff (div_pos h_num_pos h_denom_pos) hε).mp
          exact this
        rw [Real.log_div]
        · simp only [Real.log_pow]
          rw [@sub_lt_iff_lt_add']
          suffices: ↑k > (Real.log ε + Real.log (1 - θ)) / Real.log θ
          · -- 除以一个小于零的数后变号
            calc ↑k * Real.log θ
                < ((Real.log ε + Real.log (1 - θ)) / Real.log θ) * Real.log θ := mul_lt_mul_of_neg_right this h_log_neg
              _ = Real.log ε + Real.log (1 - θ) := by
                refine div_mul_cancel₀ (Real.log ε + Real.log (1 - θ)) ?h1
                exact Ne.symm (ne_of_gt h_log_neg)
              _ = Real.log (1 - θ) + Real.log ε := by rw [add_comm]
          · have h0: ↑k > ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ := by
              calc ↑k
                  ≥ ↑k₀ := Nat.cast_le.mpr hk
                _ = ↑(⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ + 1) := rfl
                _ = ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ + 1 := by simp
                _ > ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ := by exact lt_add_one ⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊
            suffices: ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ ≥ (Real.log ε + Real.log (1 - θ)) / Real.log θ
            · exact Nat.lt_of_ceil_lt hk
            · exact Nat.le_ceil ((Real.log ε + Real.log (1 - θ)) / Real.log θ)
        · linarith
        · linarith
    -- when l < k it's similar
    · push_neg at hkl
      -- swap the position of k and l
      calc ‖∑ i ∈ Finset.range l, T ^ i - ∑ i ∈ Finset.range k, T ^ i‖
        = ‖-(∑ i ∈ Finset.range k, T ^ i - ∑ i ∈ Finset.range l, T ^ i)‖ := by rw [neg_sub]
        _ = ‖∑ i ∈ Finset.range k, T ^ i - ∑ i ∈ Finset.range l, T ^ i‖ := by rw [norm_neg]
        _ = ‖∑ i ∈ Finset.Ico l k, T ^ i‖ := by rw [Eq.symm (Finset.sum_Ico_eq_sub (HPow.hPow T) (le_of_lt hkl))]
        -- then it's similar with what we've done when k ≤ l
        _ ≤ ∑ i ∈ Finset.Ico l k, ‖T ^ i‖ := by
          induction Finset.Ico l k using Finset.induction with
          | empty => simp
          | @insert a s hs ih =>
            field_simp
            calc ‖T^a + ∑ i in s, T^i‖
                ≤ ‖T^a‖ + ‖∑ i in s, T^i‖ := ContinuousLinearMap.opNorm_add_le _ _
              _ ≤ ‖T^a‖ + ∑ i in s, ‖T^i‖ := by gcongr
        _ ≤ ∑ i ∈ Finset.Ico l k, θ^i := by exact Finset.sum_le_sum fun i a ↦ pow_bound i
        _ ≤ θ^(l)/(1-θ) := geom_sum_Ico_le_of_lt_one (ContinuousLinearMap.opNorm_nonneg T) hT
        _ < ε := by
          -- next we do the totally same thing as before
          have h_log_neg : Real.log θ < 0 := by rw [← @Real.exp_lt_one_iff, Real.exp_log_eq_abs h_T_nonzero]; simp; exact hT
          have h_denom_pos : 1 - θ > 0 := by linarith [θ_lt_1]
          have h_theta_pos : θ > 0 := by unfold θ; exact (LE.le.gt_iff_ne (norm_nonneg T)).mpr h_T_nonzero
          have h_num_pos : θ ^ l > 0 := by exact pow_pos h_theta_pos l
          suffices: Real.log (θ^l / (1 - θ)) < Real.log ε
          · apply (Real.log_lt_log_iff (div_pos h_num_pos h_denom_pos) hε).mp
            exact this
          rw [Real.log_div]
          · simp only [Real.log_pow]
            rw [@sub_lt_iff_lt_add']
            suffices: ↑l > (Real.log ε + Real.log (1 - θ)) / Real.log θ
            · calc ↑l * Real.log θ
                  < ((Real.log ε + Real.log (1 - θ)) / Real.log θ) * Real.log θ := mul_lt_mul_of_neg_right this h_log_neg
                _ = Real.log ε + Real.log (1 - θ) := by
                  refine div_mul_cancel₀ (Real.log ε + Real.log (1 - θ)) ?h2
                  exact Ne.symm (ne_of_gt h_log_neg)
                _ = Real.log (1 - θ) + Real.log ε := by rw [add_comm]
            · have h0: ↑l > ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ := by
                calc ↑l
                    ≥ ↑k₀ := Nat.cast_le.mpr hl
                  _ = ↑(⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ + 1) := rfl
                  _ = ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ + 1 := by simp
                  _ > ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ := by exact lt_add_one ⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊
              suffices: ↑⌈(Real.log ε + Real.log (1 - θ)) / Real.log θ⌉₊ ≥ (Real.log ε + Real.log (1 - θ)) / Real.log θ
              · exact Nat.lt_of_ceil_lt hl
              · exact Nat.le_ceil ((Real.log ε + Real.log (1 - θ)) / Real.log θ)
          · linarith
          · linarith
  have := cauchySeq_tendsto_of_complete cauchy_Sk
  rcases this with ⟨S, hS⟩
  use S
  constructor
  · -- （Id - T）S = Id
    have h_left : Tendsto (λ k => ∑ i in Finset.range k, (T^i - T^(i+1))) atTop (𝓝 ((ContinuousLinearMap.id ℝ E - T).comp S)) := by
      have: ∀ k, ∑ i ∈ Finset.range k, (T ^ i - T ^ (i + 1)) = (ContinuousLinearMap.id ℝ E - T).comp (Sk k) := by
        intro k
        calc ∑ i ∈ Finset.range k, (T ^ i - T ^ (i + 1))
            = ∑ i ∈ Finset.range k, T^i - ∑ i ∈ Finset.range k, T^(i+1) := by rw [Finset.sum_sub_distrib]
          _ = Sk k - T * Sk k := by unfold Sk; simp; rw [Finset.mul_sum]; congr with i x; refine Eq.symm (DFunLike.congr ?e_f.h.h.h₁ rfl); exact Eq.symm (pow_succ' T i)
          _ = (ContinuousLinearMap.id ℝ E - T).comp (Sk k) := by rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]; simp; rfl
      simp [this]
      -- now we have the goal: ⊢ Tendsto (fun k ↦ Sk k - T.comp (Sk k)) atTop (𝓝 (S - T.comp S))
      have h2 : Tendsto (T.comp ∘ Sk) atTop (𝓝 (T.comp S)) := ContinuousLinearMap.tendsto_comp hS
      exact ContinuousLinearMap.tendsto_sub hS h2
    have h_right : Tendsto (λ k => ∑ i in Finset.range k, (T^i - T^(i+1))) atTop (𝓝 (ContinuousLinearMap.id ℝ E)) := by
      have: ∀ k, ∑ i in Finset.range k, (T^i - T^(i+1)) = ContinuousLinearMap.id ℝ E - T^k := by intro k; exact sum_power_diff_eq_id_sub_pow T k
      simp [this]
      have h2 : Tendsto (fun k ↦ T ^ k) atTop (𝓝 (0)) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hT
      have hId : Tendsto (fun _ : ℕ => (1 : E →L[ℝ] E)) atTop (𝓝 1) := by exact tendsto_const_nhds
      have h : Tendsto (fun k ↦ ContinuousLinearMap.id ℝ E - T ^ k) atTop (𝓝 (1 - 0)) := by apply ContinuousLinearMap.tendsto_sub hId h2
      have: Tendsto (fun k ↦ ContinuousLinearMap.id ℝ E - T ^ k) atTop (𝓝 (ContinuousLinearMap.id ℝ E)) := by
        convert ContinuousLinearMap.tendsto_sub hId h2; simp; rfl
      exact this
    exact tendsto_nhds_unique h_left h_right
  · -- S (Id - T) = Id is nearly the same as above
    have h_left : Tendsto (λ k => ∑ i in Finset.range k, (T^i - T^(i+1))) atTop (𝓝 (S.comp (ContinuousLinearMap.id ℝ E - T))) := by
      have: ∀ k, ∑ i ∈ Finset.range k, (T ^ i - T ^ (i + 1)) = (Sk k).comp (ContinuousLinearMap.id ℝ E - T) := by
        intro k
        calc ∑ i ∈ Finset.range k, (T ^ i - T ^ (i + 1))
            = ∑ i ∈ Finset.range k, T^i - ∑ i ∈ Finset.range k, T^(i+1) := by rw [Finset.sum_sub_distrib]
          _ = Sk k - T * Sk k := by unfold Sk; simp; rw [Finset.mul_sum]; congr with i x; refine Eq.symm (DFunLike.congr ?e_f.h.h.h₂ rfl); exact Eq.symm (pow_succ' T i)
          _ = Sk k - Sk k * T := by unfold Sk; simp; rw [Finset.mul_sum, Finset.sum_mul]; congr with i x; refine DFunLike.congr ?e_f.h.h.h₃ rfl; exact Eq.symm (pow_mul_comm' T i)
          _ = (Sk k).comp (ContinuousLinearMap.id ℝ E - T) := by rw [ContinuousLinearMap.comp_sub]; simp; rfl
      simp [this]
      have h2 : Tendsto (fun k => (Sk k).comp T) atTop (𝓝 (S.comp T)) := ContinuousLinearMap.tendsto_comp_right hS
      exact ContinuousLinearMap.tendsto_sub hS h2
    have h_right : Tendsto (λ k => ∑ i in Finset.range k, (T^i - T^(i+1))) atTop (𝓝 (ContinuousLinearMap.id ℝ E)) := by
      have: ∀ k, ∑ i in Finset.range k, (T^i - T^(i+1)) = ContinuousLinearMap.id ℝ E - T^k := by intro k; exact sum_power_diff_eq_id_sub_pow T k
      simp [this]
      have h2 : Tendsto (fun k ↦ T ^ k) atTop (𝓝 (0)) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hT
      have hId : Tendsto (fun _ : ℕ => (1 : E →L[ℝ] E)) atTop (𝓝 1) := by exact tendsto_const_nhds
      have h : Tendsto (fun k ↦ ContinuousLinearMap.id ℝ E - T ^ k) atTop (𝓝 (1 - 0)) := by apply ContinuousLinearMap.tendsto_sub hId h2
      have: Tendsto (fun k ↦ ContinuousLinearMap.id ℝ E - T ^ k) atTop (𝓝 (ContinuousLinearMap.id ℝ E)) := by
        convert ContinuousLinearMap.tendsto_sub hId h2; simp; rfl
      exact this
    exact tendsto_nhds_unique h_left h_right


/-Theorem: If T : X → Y is a bounded invertible operator then for all
p : X → Y with sufficiently small norm T + p is also invertible.-/
theorem BoundedInvertibleOperatorPlusεIsInvertible
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : E →L[ℝ] F) [CompleteSpace E] [Nontrivial E] [CompleteSpace F]
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
      use 1
      constructor
      · linarith
      intro p hp
      by_cases hpzero: ‖p‖ = 0  -- when p = 0 it's to prove identity is invertible
      · have: p = 0 := by exact (opNorm_zero_iff p).mp hpzero
        rw [this]
        simp
        exact Isinvertible.id
      have hp_neg : ‖-p‖ < 1 := by rw [norm_neg]; exact hp
      unfold IsInvertible
      simp
      conv => congr; rw [← neg_neg p]
      have neumann := neumann_series_invertible hp_neg
      unfold IsInvertible at neumann
      have : ∀ inv : E →L[ℝ] E, (ContinuousLinearMap.id ℝ E - -p).comp inv = inv + (- -p).comp inv := by
        intro inv
        rw [ContinuousLinearMap.sub_comp]
        simp
      have neg_p_ne_zero: ‖-p‖ ≠ 0 := by push_neg at hpzero; rw [← norm_neg p] at hpzero; exact hpzero
      rcases neumann neg_p_ne_zero with ⟨inv, hinv⟩
      rw [this inv] at hinv
      have : ∀ inv : E →L[ℝ] E, inv.comp (ContinuousLinearMap.id ℝ E - -p) = inv + inv.comp (- -p) := by
        intro inv
        rw [ContinuousLinearMap.comp_sub]
        simp
      rw [this inv] at hinv
      exact ⟨inv, hinv⟩

/- Let X be a Banach space and let T ∈ L(X) be compact.
Then A := Id − T is a Fredholm operator with index zero. -/
instance id_minus_compact_T_is_Fredholm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (T : X →L[ℝ] X) (hT : IsCompactOperator T) :
  FredholmOperators (ContinuousLinearMap.id ℝ X - T) where
  finite_dimensional_kernel := by
    let K := ker (ContinuousLinearMap.id ℝ X - T)
    let B := Metric.closedBall (0 : K) 1
    suffices : IsCompact B
    exact FiniteDimensional.of_isCompact_closedBall₀ (by norm_num) this
  closed_range := by
    sorry
  finite_dimensional_cokernel := by
    sorry

theorem id_minus_compact_T_index_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  (T : X →L[ℝ] X) (hT : IsCompactOperator T) (hF : FredholmOperators (ContinuousLinearMap.id ℝ X - T)) :
  FredholmOperators.ind (ContinuousLinearMap.id ℝ X - T) = 0 := by
  sorry

/-(Riesz Theorem): The unit ball B in a Banach space X is compact if and
only if B is finite dimensional.-/
/-Omitted. Riesz Theorem is already in mathlib-/

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
end FredholmOperatorsDef

#check RangeClosedIfAdmittingRangeClosedCompletement
/-The following lemma is about how to extract the norm ‖x‖ of x∈X from |ρ(x)|, where X is a Banach
space and ρ∈X*:=Hom(X,k).
Lemma: ∀x∈X,‖x‖=sup{|ρ(x)|,ρ∈Hom(X,k)}-/
lemma Norm_Dual_Characterization
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (x:E): ‖x‖ = sSup { ‖ρ x‖|ρ ∈ {ρ: (NormedSpace.Dual ℝ E) | ‖ρ‖ = (1:ℝ) } }:=by sorry

section
/-Lemma: if T is a bounded linear operator, then so is T*
Mathlib has similar lemmas, although only formalized for Hilbert spaces.
But the conclusion actually holds more generally for Banach spaces.
-/
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

def ContinuousLinearAdjoint (T:X→L[ℝ] Y):NormedSpace.Dual ℝ Y→L[ℝ] NormedSpace.Dual ℝ X:={
  toFun:=λ ρ↦{
    toFun:=λ x↦ρ (T x)
    map_add':=λ x₁ x₂↦by simp
    map_smul':=λ c x↦by simp
    cont:=by
      simp
      have :(fun x ↦ ρ (T x))=fun x ↦ (ρ∘T) x:=rfl
      rw[this]
      refine Continuous.comp ?hg ?hf
      exact ContinuousLinearMap.continuous ρ
      exact ContinuousLinearMap.continuous T
  }
  map_add':=by exact fun x y ↦ rfl
  map_smul':=by exact fun m x ↦ rfl
  cont:=by
    simp
    letI:NormedSpace ℝ (NormedSpace.Dual ℝ Y):=NormedSpace.instDual ℝ Y
    letI:NormedSpace ℝ (NormedSpace.Dual ℝ X):=NormedSpace.instDual ℝ X
    apply @IsBoundedLinearMap.continuous ℝ _ _ _ _
    exact isBoundedLinearMap_comp_right T
}

/-If T has closed range then Coker(T)*=ker(T*)-/
def CokerDualEqualKerAdjointWhenRangeClosed(T:X→L[ℝ]Y)
  (hT_closed:IsClosed (range T)):
    let Coker := Y ⧸ LinearMap.range T
  /- We need instances ensuring Coker is normed ℝ vector spaces to talk about
Normed spaces dual over ℝ-/
    letI : IsClosed (LinearMap.range T : Set Y) := hT_closed
    letI : NormedAddCommGroup Coker := Submodule.Quotient.normedAddCommGroup (LinearMap.range T)
    letI : NormedSpace ℝ Coker := Submodule.Quotient.normedSpace (LinearMap.range T) ℝ
    NormedSpace.Dual ℝ Coker ≃ₗ[ℝ] ker (ContinuousLinearAdjoint T) := sorry


end
