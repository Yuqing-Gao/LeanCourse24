import LeanCourse.Common
open Function Set Ideal Polynomial Classical
open Matrix hiding mul_smul
noncomputable section





/-
# Practical remarks
* Assignment 7 will be posted tonight. It is due on 26.11. Upload it to eCampus.
  From now on, the assignments will be smaller, so that you have time to start on your project.
-/

/- # Last Week -/

/-
Last time we discussed some Lean internals and group theory:
* universes, coercions, subtypes
* additive vs multiplicative notations
* monoids, groups, subgroups, homomorphisms, quotients
-/

/- # This week

Ring theory and linear algebra
-/

/- # Rings -/

/- Lean uses `Ring` and `CommRing` for rings and commutative rings. -/
example : CommRing ℤ := by infer_instance

/- Also important are *semirings*, which are rings without postulating negation. -/
example : CommSemiring ℕ := by infer_instance

/- A field (German: Körper) is a nontrivial commutative ring with inverses. -/
example : Field ℚ := by infer_instance


/- Many classes only take a type as argument,
others are predicates that take another class as argument -/
#check Field
#check EuclideanDomain

#check IsDomain
#check IsField
#check UniqueFactorizationMonoid


/- In Mathlib, many lemmas about multiplication are stated in two ways:
* For Group-like structures
* For Ring-like structures (with an absorbing element 0).
-/

#check mul_div_cancel_right -- group-like
#check mul_div_cancel_right₀ -- ring-like

#check mul_le_mul_left' -- group-like
#check mul_le_mul_left -- ring-like
#check mul_le_mul_of_nonneg_left -- ring-like

/- Use Loogle to find lemmas you want.

`MonoidWithZero` and `GroupWithZero` capture the
multiplicative structure of a ring or a field
-/

-- #loogle _ * _ < _ * _ ↔ _
#check mul_lt_mul_left
-- #loogle ?a * _ < ?a * _ ↔ _
#loogle _ * 0 = 0

#check MonoidWithZero
#check GroupWithZero




/- Note that the tactics for computation in a
`Ring` and `CommRing` is `noncomm_ring` resp. `ring`.-/
example {R : Type*} [CommRing R] (x y : R) :
    (x - y)^2 = x^2 - 2*x*y + y^2 := by ring

example {R : Type*} [Semiring R] (x y : R) :
    (x + y)^2 = x^2 + x*y + y*x + y^2 := by noncomm_ring

/- The binomial theorem.
The natural number `Nat.choose n m` is coerced to an element of `R`
using `Nat.cast`. -/
example {R : Type*} [CommRing R] (x y : R) (n : ℕ) : (x + y) ^ n =
    ∑ m in Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m := by
  exact?






/- We have a predicate `IsUnit` stating
whether an element of the ring is a unit. -/
example {R : Type*} [CommRing R] (x : R) :
    IsUnit x ↔ ∃ y, x * y = 1 := by exact?


/- We can write `Rˣ` for the units of a ring
(i.e. the elements with a multiplicative inverse). -/
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x
example (x : ℤˣ) : (x : ℤ) = 1 ∨ (x : ℤ) = -1 := by sorry

example {R : Type*} [Ring R] : Group Rˣ := by infer_instance




/- We write ring homomorphisms with `→+*`. -/
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y ∧ f (x * y) = f x * f y ∧
    f 1 = 1 ∧ f 0 = 0 :=
  ⟨f.map_add x y, f.map_mul x y, f.map_one, f.map_zero⟩


/- A subring is a subset of `R`
that is an additive subgroup and multiplicative submonoid.

As subgroups, subrings are bundled as a set with closure properties.
They are only moderately useful, since we cannot quotient a ring by a subring. -/
example {R : Type*} [Ring R] (S : Subring R) : Ring S := by infer_instance

example {R : Type*} [Ring R] : CompleteLattice (Subring R) := by
  infer_instance



/- ## Ideals -/


section Ring
-- Ideals are bundled: I : Ideal R
-- [unbundled would be (I : Set R) (hI : IsIdeal I) ]
variable {R : Type*} [CommRing R] {I J : Ideal R}

/- Ideals are additive subgroups that are closed under arbitary multiplication. -/
example {x y : R} (hy : y ∈ I) : x * y ∈ I :=
  I.mul_mem_left x hy

example {x y : R} (hx : x ∈ I) : x * y ∈ I :=
  I.mul_mem_right y hx



/- There are various operations on ideals. -/
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ I ⊓ J := mul_le_inf

example : CompleteLattice (Ideal R) := by infer_instance
example : Semiring (Ideal R) := by infer_instance




/- We write `Ideal.span s` for the smallest ideal containing `s`.
In particular, `Ideal.span {a}` is the principal ideal generated by `a`. -/


/- Exercise: use Loogle to find relevant lemmas. -/
example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by
  rw [← Ideal.span_union, span_gcd]
  simp
  rw [@span_pair_comm]


/- Exercise: use Loogle to find relevant lemmas. -/
example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by sorry


example (n m : ℤ) : span {n} * span {m} = span {n * m} := by
  exact?



/- We can quotient a ring by an ideal. -/

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

variable {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsPrime] in
#synth IsDomain (R ⧸ I)

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsMaximal] :
    Field (R ⧸ I) :=
  Quotient.field I



/- The Chinese remainder theorem can be stated
for ideals in a commutative ring. -/

example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (f : ι → Ideal R) (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) :
    (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i := by
  exact?

/- Note that we re-use the generic definition of `IsCoprime` here. -/
#print IsCoprime

/- From this we can easily get the traditional version for `ℤ/nℤ`. -/

example (n : ℕ) : Ring (ZMod n) := by infer_instance

example {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* ∀ i, ZMod (a i) :=
  ZMod.prodEquivPi a ha



example {R : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] (I : Ideal R) :
    ∃ x : R, I = span {x} := by exact?




/- # Algebras and polynomials -/

variable {A : Type*} [Semiring A] [Algebra R A]

/- An (associative unital) *algebra*  `A` over a ring `R`
is a semiring `A` equipped with a ring homomorphism `R →+* A`
whose image commutes with every element of `A`. -/
example : R →+* A := algebraMap R A

example (r : R) (a : A) :
    algebraMap R A r * a = a * algebraMap R A r :=
  Algebra.commutes r a

/- We can also denote `algebraMap R A r * a`
using scalar multiplication as `r • a`. -/
example (r : R) (a : A) : r • a = algebraMap R A r * a := Algebra.smul_def r a




/- An important algebra is the polynomial ring `R[X]` or `Polynomial R`.
We can write `X` or `Polynomial.X` for the polynoial variable. -/

example : Algebra R R[X] := by infer_instance

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) : R[X] :=
  X - C r

/- `C` is registered as a ring homomorphism. -/
#check C

example {R : Type*} [CommRing R] (r : R) :
    (X + C r) * (X - C r) = X^2 - C (r ^ 2) := by {
  ring
  simp?
  }



/- You can access coefficients using `Polynomial.coeff` -/

example {R : Type*} [CommRing R] (r : R) :
  (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X^2 + 2*X + C 3 : R[X]).coeff 1 = 2 := by simp

/- Defining the degree of a polynomial leads to a choice:
what is the degree of the `0` polynomial? -/
#check natDegree (R := R)
#check degree (R := R)
example : natDegree (R := R) 0 = 0 := rfl

/- `WithBot ℕ` can be seen as `ℕ ∪ {-∞}`, except that `-∞` is denoted `⊥`. -/
example : degree (R := R) 0 = ⊥ := rfl

example [IsDomain R] (p q : R[X]) :
    degree (p * q) = degree p + degree q := by
  exact degree_mul

example [IsDomain R] (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q := by
  refine natDegree_mul hp hq



/- `compute_degree!` and `monicity!` can automate some proofs. -/

example [Nontrivial R] (p : R) :
    degree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  compute_degree!

example [IsDomain R] (p : R) :
    natDegree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  compute_degree!

example [IsDomain R] (p : R) :
    Monic (X ^ 3 + C p * X ^ 2 + 2 * X - 4) := by
  monicity!




/- We can evaluate polynomials using `Polynomial.eval`. -/

#check eval (R := R)
example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := P.eval x

example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := eval x P

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

/- If `P : R[X]`, then we often want to evaluate `P` in algebras over `R`.
E.g. we want to say that `X ^ 2 - 2 : ℤ[X]` has a root in `ℝ` -/
#check aeval (R := R) (A := A)

example : ∃ (x : ℝ), aeval x (X ^ 2 - 2 : ℤ[X]) = 0 := by {
  use √2
  simp [aeval]
  }



end Ring







/- # Fields

Lean's library contains various results field theory and Galois theory. -/

section Field

#check Algebra
/- If `K` and `L` are both fields, then `[Algebra K L]`
states exactly that `L` is a field extension of `K`. -/


variable {K L : Type*} [Field K] [Field L] [Algebra K L]


/- Here are some important notions in field theory. -/

/- `IntermediateField K L` is the type of field subfields of
`L` that contain `K`, i.e. `S : IntermediateField K L`
is stating we have a tower of fields `L / S / K`. -/
#check IntermediateField

/- `IsSplittingField K L f` states that `L` is the splitting field of
polynomial `f`, i.e. `f` can be written as a product of linear polynomials
in `L`, but not in any subfield of `L` (containing `K`). -/
#check IsSplittingField

/- In an algebraically closed field every polynomial has a root. -/
#synth IsAlgClosed ℂ

/- A Field extension is a Galois extension if it is separable and normal. -/
#check IsGalois

/- A number field is a finite field extension of `ℚ` -/
#check NumberField

/- An element `x` in a field extension `L` is algebraic over `K` if it
the root of a nonzero polynomial over `K`. -/
example {x : L} (hx : IsAlgebraic K x) : aeval x (minpoly K x) = 0 := by
  rw [minpoly.aeval]


end Field






section LinearAlgebra

/- # Modules and vector spaces

Most results in linear algebra are not formulated in terms of vector spaces,
but instead they are generalized to modules over a (semi)ring.
To state that `V` is a vector space over `K`, we actually use the word `Module`.
Note that we have to separately state that `(V, +)` is a group.
Scalar multiplication is written with `•` (\smul). -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

example (k : K) (v : V) : -k • v = k • -v := by
  rw [neg_smul, smul_neg]

/- Beware: every group also has a scalar multiplication w.r.t.
`ℕ` and `ℤ`, and the following lemmas relate this to the
scalar multiplication of `K`. -/

example (v : V) : (2 : K) • v = (2 : ℕ) • v :=
  Nat.cast_smul_eq_nsmul K 2 v
example (v : V) : (2 : ℤ) • v = (2 : K) • v := by
  simp [← Int.cast_smul_eq_zsmul K 2 v]


/- A module `M` over a ring `R` is an abelian group `(M, +)`
together with a scalar multiplication `R → M → M`
with appropriate associativity and distributivity laws. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (r : R) (x y : M) : r • (x + y) = r • x + r • y := by exact?
example (r s : R) (x : M) : (r + s) • x = r • x + s • x := by exact?
example (r s : R) (x : M) : (r * s) • x = r • s • x := by exact?
example (x : M) : (0 : R) • x = 0 := by exact?
example (x : M) : (1 : R) • x = x := by exact?
example (r : R) : r • (0 : M) = 0 := by exact?

/- As usual, we have submodules and quotients -/
example (S : Submodule R M) : Module R S := by infer_instance
example (S : Submodule R M) : Module R (M ⧸ S) := by infer_instance


/- We have linear maps `M →ₗ[R] N` between modules.
We have to write `R` explicitly in this notation.

For example, in complex analysis there is an important difference
between `ℝ`-linear maps and `ℂ`-linear maps -/
variable {N N' : Type*}
  [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

/- `N × N'` is a biproduct: it is both the
product and coproduct of the modules `N` and `N'`. -/
example (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
  M →ₗ[R] N × N' where
    toFun := fun m ↦ (f m, g m)
    map_add' := by simp
    map_smul' := by simp

example : M →ₗ[R] M × N := LinearMap.inl R M N
example : N →ₗ[R] M × N := LinearMap.inr R M N
example : M × N →ₗ[R] M := LinearMap.fst R M N
example : M × N →ₗ[R] N := LinearMap.snd R M N


/- Linear maps themselves form a module over `R`
(requires that `R` is a commutative ring) -/
example : Module R (M →ₗ[R] N) := by infer_instance

/- If you want to use an operation that is linear in multiple arguments,
you can write it as a bundled morphism into the type of bundled morphisms. -/
#check LinearMap.lsmul R M
example (r : R) (m : M) : LinearMap.lsmul R M r m = r • m := by rfl
example (f : M →ₗ[R] N →ₗ[R] N') : N →ₗ[R] M →ₗ[R] N' := f.flip





/- Matrices are defined in Mathlib, but generally we prefer to work
abstractly with vector spaces (or modules) without choosing a basis.
Things are often easier when stated using linear maps than with matrices. -/
#check Matrix

example {m n : Type*} (M : Matrix m n M) : Mᵀᵀ = M := rfl

-- the type of (m × n) - matrixes

example (m n : ℕ) : Type := Matrix (Fin m) (Fin n) ℝ

/- We use `ι → ℝ` to denote `ℝ^n` if `ι` has `n` elements.
However, it is nicer to work over an abstract (finite-dimensional)
vector space. -/
example {ι : Type*} (v : ι → ℝ) : v + v = 2 • v := by rw [two_smul]
example {n : ℕ} (v : Fin n → ℝ) : v + v = 2 • v := by rw [two_smul]
example {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (v : V) : v + v = 2 • v := by rw [two_smul]

/- `Module.finrank` gives the dimension of a vector space. -/
#check Module.finrank R M
#check Module.rank R M

/- `Basis ι R M` is a structure of a basis of a vector space.
It is given by an equivalence of `M` with `ι →₀ R`, which is the
(infinitary) coproduct of copies of `R`, vectors indexed by `ι`,
where only finitely many entries are nonzero. -/
example {ι : Type*} (b : Basis ι R M) : M ≃ₗ[R] ι →₀ R := b.repr
example {ι : Type*} [Fintype ι] (b : Basis ι K V) :
  V ≃ₗ[K] ι → K := by exact?


example {ι : Type*} (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)


section product

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/- We can also take a (infinitary) product of modules.
This is given by the `Π`-type or dependent function type in Lean.
-/
example : Module R (Π i : ι, M i) := by infer_instance

example (f : Π i, M i) (i : ι) : M i := f i

example (f : Π i, M i) (i₀ : ι) (x : M i₀) :
  Π i, M i := fun j : ι ↦ Function.update f i₀ x j

example (r : R) (f : Π i, M i) (i : ι) :
  (r • f) i = r • f i := by simp

example (r : R) (f : Π i, M i) (i₀ : ι) (x : M i₀) :
    r • Function.update f i₀ x = Function.update (r • f) i₀ (r • x) := by {
  sorry
  }

end product

end LinearAlgebra
