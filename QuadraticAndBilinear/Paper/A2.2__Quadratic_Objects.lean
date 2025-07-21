--import Bilinear_and_Quadratic_Forms_paper.A0__Preliminaries

/-
A0__Preliminaries.lean
-/


import Mathlib
import Mathlib.Data.Fintype.Basic
-- import Mathlib.Data.MvPolynomial.Basic



-- Setup the R-modules used in the paper
-- This block is correct and sets the context for the whole file.
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

#check R
#check M
#check N
#check M × M → N



-- Enable diagnostic comments
--set_option diagnostics true

-- Allow unused variables without a warning
set_option linter.unusedVariables false

-- to control threshold for reporting counters
set_option diagnostics.threshold 10




-- ===========================================================
-- ===========================================================
-- ===========================================================

/-
A2.1__Linear_and_Bilinear_Objects.lean
-/



/-
Definition 2.1 (Linear Maps). Given two R-modules M and N for some commutative ring R, we say that a function L : M ! N is an R-linear map if it has the following properties:
1. L(am) = aL(m) (degree 1),
2. L(m + m′) = L(m) + L(m′) (additivity),
for all a ∈ R and all m, m′ ∈ M.
-/

-- Use the original, simple definition.
def IsRLinearMap (L : M → N) : Prop :=
  (∀ (a₁ : R) (m₁ : M), L (a₁ • m₁) = a₁ • (L (m₁))) ∧
  (∀ (m₁ m₁' : M), L (m₁ + m₁') = L (m₁) + L (m₁))



/-
Definition 2.2 (Bilinear Maps). Given two R-modules M and N for some commutative ring R, we say that a function B : M × M ! N is an R-bilinear map if it has the following properties:
1. B(a1m1, a2m2) = a1a2B(m1, m2) (degree 1),
2. B(m1 + m′1, m2) = B(m1, m2) + B(m′1, m2) (additivity in first argument),
3. B(m1, m2 + m′2) = B(m1, m2) + B(m1, m′2) (additivity in second argument),
for all a1, a2 ∈ R and all m1, m2, m′1, m′2 ∈ M.
-/

-- Use the original, simple definition.
def IsRBilinearMap (B : M × M → N) : Prop :=
  (∀ (a₁ a₂ : R) (m₁ m₂ : M), B (a₁ • m₁, a₂ • m₂) = (a₁ * a₂) • B (m₁, m₂)) ∧
  (∀ (m₁ m₁' m₂ : M), B (m₁ + m₁', m₂) = B (m₁, m₂) + B (m₁', m₂)) ∧
  (∀ (m₁ m₂ m₂' : M), B (m₁, m₂ + m₂') = B (m₁, m₂) + B (m₁, m₂'))



/-
Definition 2.3 (Diagonal Bilinear Maps).
Suppose M and N are R-modules for some commutative ring R,
B : M × M ! N is an R-bilinear map, and G ⊆ M is a totally ordered set
of R-module generators of M. Then we say that B is diagonal (with respect to G) if

g = g′ ==> B ( g , g ′ ) = 0 .

We further say that B is diagonalizable if there exists some totally ordered set G ⊆ M of R-module
generators of M so that B is diagonal with respect to G.
-/

def IsDiagonalBilinearMap (B : M →ₗ[R] M →ₗ[R] N) (G : Set M)
    (h_gen : Submodule.span R G = ⊤) [h_ord : LinearOrder ↥G] : Prop :=
  ∀ g g' : ↥G, g ≠ g' → B g g' = 0

def IsDiagonalizableBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ (G : Set M) (h_gen : Submodule.span R G = ⊤),
    ∃ (_ : LinearOrder ↥G), IsDiagonalBilinearMap B G h_gen



/-
Definition 2.4 (Upper-triangular Bilinear Maps).
Suppose M and N are R-modules for some commutative ring R,
B : M × M --> N is an R-bilinear map,
and G ⊆ M is a totally ordered set of R-module generators of M.
Then we say that B is upper-triangular (with respect to G) if

  B ( g , g ′ ) ̸ = 0 =⇒ g ≤ g ′ ,

and strictly upper-triangular (with respect to G) if

  B ( g , g ′ ) ̸ = 0 =⇒ g < g ′ ,

We further say that B is upper-triangularizable (resp. strictly upper-triangularizable)
if there exists some totally ordered set G ⊆ M of R-module generators of M so that
B is upper- triangular (resp. strictly upper-triangular) with respect to G.
-/

def IsUpperTriangularBilinearMap (B : M →ₗ[R] M →ₗ[R] N) (G : Set M)
    (h_gen : Submodule.span R G = ⊤) [h_ord : LinearOrder ↥G] : Prop :=
  ∀ g g' : ↥G, B g g' ≠ 0 → g ≤ g'


def IsStrictlyUpperTriangularBilinearMap (B : M →ₗ[R] M →ₗ[R] N) (G : Set M)
    (h_gen : Submodule.span R G = ⊤) [h_ord : LinearOrder ↥G] : Prop :=
  ∀ g g' : ↥G, B g g' ≠ 0 → g < g'


def IsUpperTriangularizableBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ (G : Set M) (h_gen : Submodule.span R G = ⊤),
    ∃ (_ : LinearOrder ↥G), IsUpperTriangularBilinearMap B G h_gen


def IsStrictlyUpperTriangularizableBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ (G : Set M) (h_gen : Submodule.span R G = ⊤),
    ∃ (_ : LinearOrder ↥G), IsStrictlyUpperTriangularBilinearMap B G h_gen




/-
Remark 2.5 (Lower-triangular conditions).
One could similarly instead define notions of lower- triangular,
strictly lower-triangular and lower-triangularizable,
and strictly lower-triangularizable for bilinear forms,
and use these for the discussion.
We have made the arbitrary choice to use “upper-” definitions
based on our preference for the < relation over the > relation.
-/

def IsLowerTriangularBilinearMap (B : M →ₗ[R] M →ₗ[R] N) (G : Set M)
    (h_gen : Submodule.span R G = ⊤) [h_ord : LinearOrder ↥G] : Prop :=
  ∀ g g' : ↥G, B g g' ≠ 0 → g' ≤ g

def IsStrictlyLowerTriangularBilinearMap (B : M →ₗ[R] M →ₗ[R] N) (G : Set M)
    (h_gen : Submodule.span R G = ⊤) [h_ord : LinearOrder ↥G] : Prop :=
  ∀ g g' : ↥G, B g g' ≠ 0 → g' < g

def IsLowerTriangularizableBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ (G : Set M) (h_gen : Submodule.span R G = ⊤),
    ∃ (_ : LinearOrder ↥G), IsLowerTriangularBilinearMap B G h_gen

def IsStrictlyLowerTriangularizableBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ (G : Set M) (h_gen : Submodule.span R G = ⊤),
    ∃ (_ : LinearOrder ↥G), IsStrictlyLowerTriangularBilinearMap B G h_gen



/-
UNLABELLED DEFINTION -- TO ADD AS A DEFINTION
It will also be useful to understand how a bilinear form B behaves
with respect to the non-trivial permutation
σ : M × M ! M × M defined by σ(m1, m2) := (m2, m1),
motivating the following definitions.
-/

def nonTrivialPermutation (B : M →ₗ[R] M →ₗ[R] N) : M →ₗ[R] M →ₗ[R] N :=
  LinearMap.mk₂ R (fun m₁ m₂ => B m₂ m₁)
    (fun m₁ m₂ m₃ => by simp)
    (fun r m₁ m₂ => by simp)
    (fun m₁ m₂ m₃ => by simp [B.map_add])
    (fun r m₁ m₂ => by simp [B.map_smul])




/-
Definition 2.6 (Symmetric and Skew-Symmetric Bilinear Maps). Suppose M and N are R-modules for some commutative ring R, B : M × M ! N is an R-bilinear map. Then we say that B is symmetric (resp. skew-symmetric) if
B(m1, m2) = B(m2, m1) (resp. B(m1,m2) = −B(m2,m1)) for all m1,m2 ∈ M.
-/


/-!
### Symmetric and Skew-Symmetric Bilinear Maps
-/

/-- A bilinear map `B` is **symmetric** if `B(m₁, m₂) = B(m₂, m₁)` for all `m₁, m₂`. -/
def IsSymmetricBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  B = nonTrivialPermutation B

/-- A bilinear map `B` is **skew-symmetric** if `B(m₁, m₂) = -B(m₂, m₁)` for all `m₁, m₂`. -/
def IsSkewSymmetricBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  B = - (nonTrivialPermutation B)




/-
Remark 2.7 (Symmetrized and Symmetrizations of Bilinear forms). We can also define the notion of a bilinear form B being symmetrized (resp. skew-symmetrized) if it can be written as
B = B′ + B′ ◦ σ
(resp. B = B′ − B′ ◦ σ) for some bilinear form B′. Similarly, we can define the symmetrization (resp. skew-symmetrization) of a bilinear form B′ as the bilinear form B := B′ + B′ ◦ σ (resp. B := B′ − B′ ◦ σ).
-/

/-!
### Symmetrized Bilinear Maps
-/

/-- The **symmetrization** of a bilinear map `B` is `B + flip B`. -/
def symmetrization (B : M →ₗ[R] M →ₗ[R] N) : M →ₗ[R] M →ₗ[R] N :=
  B + nonTrivialPermutation B

/-- The **skew-symmetrization** of a bilinear map `B` is `B - flip B`. -/
def skewSymmetrization (B : M →ₗ[R] M →ₗ[R] N) : M →ₗ[R] M →ₗ[R] N :=
  B - nonTrivialPermutation B

/-- A bilinear map `B` is **symmetrized** if it is the symmetrization of some map `B'`. -/
def IsSymmetrizedBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ B' : M →ₗ[R] M →ₗ[R] N, B = symmetrization B'

/-- A bilinear map `B` is **skew-symmetrized** if it is the skew-symmetrization of some map `B'`. -/
def IsSkewSymmetrizedBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∃ B' : M →ₗ[R] M →ₗ[R] N, B = skewSymmetrization B'





/-
UNLABELLED DEFINTION -- TO ADD AS A DEFINTION
... the diagonal map ∆ : M ! M × M is defined by ∆(m) := (m, m).
-/
-- import Mathlib.Algebra.Module.LinearMap
def diagonalMap (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : M →ₗ[R] M × M :=
{ -- Use record syntax for defining the LinearMap
  toFun     := fun m => (m, m),
  map_add'  := by
    -- Goal: ∀ (x y : M), (x + y, x + y) = (x, x) + (y, y)
    intros x y -- Explicitly introduce variables
    -- simp can now easily prove the goal using component-wise addition on M × M
    simp,
  map_smul' := by
    -- Goal: ∀ (r : R) (x : M), (r • x, r • x) = r • (x, x)
    intros r x -- Explicitly introduce variables
    -- simp can now prove the goal using component-wise scalar multiplication
    simp
}




/-
Definition 2.8 (Alternating Bilinear Maps).
Suppose M and N are R-modules for some commutative ring R, B : M × M ! N is an R-bilinear map.
Then we say that B is alternating if
B(m, m) = 0
for all m ∈ M.
-/


/-!
### Alternating Bilinear Maps
-/

/--
A bilinear map `B` is **alternating** if `B(m, m) = 0` for all `m`.
This corresponds to the condition that the diagonal evaluation `B ∘ Δ` vanishes,
where `Δ : M → M × M` is the diagonal map `Δ(m) = (m, m)`.
-/
def IsAlternatingBilinearMap (B : M →ₗ[R] M →ₗ[R] N) : Prop :=
  ∀ m : M, B m m = 0




-- ===========================================================
-- ===========================================================
-- ===========================================================

/-
A2.2__Quadratic_objects.lean
-/



/-
Definition 2.9 (Quadratic Maps).
Given two R-modules M and N for some commutative ring R,
we say that a function Q : M ! N is an R-quadratic map
if there exists some associated R-bilinear map B_Q : M × M -> N
so that the following two properties hold:
  1. Q(am) = a^2 * Q(m) (degree 2),
  2. Q(m + m′) = Q(m) + Q(m′) + B_Q(m, m′) (quadratic additivity),
for all a ∈ R and all m,m′ ∈ M.
-/


-- FIX: The @ call now has the correct argument order.
def IsRQuadraticMap (Q : M → N) : Prop :=
  ∃ (B_Q : M × M → N), @IsRBilinearMap R _ M _ _ N _ _ B_Q ∧
    (∀ (a : R) (m : M), Q (a • m) = (a * a) • (Q m)) ∧
    (∀ (m m' : M), Q (m + m') = Q m + Q m' + B_Q (m, m'))



/-
Remark 2.11 (The Polarization identity and the Polar map). The R-bilinear map BQ := Q ◦ Σ − Q ◦ π1 − Q ◦ π2 associated to an R-quadratic map Q is often called the polar map of Q. It is uniquely defined by the quadratic additivity condition
Q(m + m′) = Q(m) + Q(m′) + BQ(m, m′), which is often referred to as the polarization identity.
-/



/-!
### Quadratic Maps and Polarization
-/

/--
The **polar map** `polar Q` associated with a function `Q : M → N` is defined by
`polar Q m₁ m₂ := Q (m₁ + m₂) - Q m₁ - Q m₂`.
-/
def polar (Q : M → N) (m₁ m₂ : M) : N := Q (m₁ + m₂) - Q m₁ - Q m₂

/--
The **polarization identity** states `Q(m₁ + m₂) = Q m₁ + Q m₂ + polar Q m₁ m₂`.
This is true by definition of the polar map.
-/
theorem polarization_identity (Q : M → N) (m₁ m₂ : M) :
    Q (m₁ + m₂) = Q m₁ + Q m₂ + polar Q m₁ m₂ := by
  simp [polar]

/-
A function `Q : M → N` is an **R-quadratic map** if its associated polar map is
an R-bilinear map.
-/

/-
def IsQuadraticMap (Q : M → N) : Prop :=
  (∀ m₂ : M, IsLinearMap R (fun m₁ => polar Q m₁ m₂)) ∧
  (∀ m₁ : M, IsLinearMap R (fun m₂ => polar Q m₁ m₂))
-/

/-
If `Q` is a quadratic map, its polar map can be bundled as a bilinear map `M →ₗ[R] M →ₗ[R] N`.
-/
-- Assuming a definition for polar: def polar (Q : M → N) (m₁ m₂ : M) : N := Q (m₁ + m₂) - Q m₁ - Q m₂
-- Also assuming your bilinear map type (M →[N] M →[N] N) is built with a constructor like LinearMap.mk₂


/--
A function `Q` is a quadratic map if its polar form is additive in each variable.
The required lemmas are the fields of this class.
-/
class IsQuadraticMap (Q : M → N) : Prop where
  /-- A quadratic map sends zero to zero. -/
  map_zero : Q 0 = 0
  /-- The polar form of Q is additive in the first variable. -/
  polar_add_left : ∀ m₁ m₂ m₃ : M, polar Q (m₁ + m₂) m₃ = polar Q m₁ m₃ + polar Q m₂ m₃
  /-- The polar form of Q is additive in the second variable. -/
  polar_add_right : ∀ m₁ m₂ m₃ : M, polar Q m₁ (m₂ + m₃) = polar Q m₁ m₂ + polar Q m₁ m₃


/--
Constructs the bilinear map associated with a quadratic map `Q`.
It's a group homomorphism from `M` to the group of homomorphisms `(M →+ N)`.
-/
def polarBilinear (Q : M → N) [hQ : IsQuadraticMap Q] : M →+ (M →+ N) :=
{ toFun := fun m₁ =>
    { toFun   := polar Q m₁,
      -- FIX: Add the missing 'map_zero' proof for the inner homomorphism.
      map_zero' := by
        simp [polar, hQ.map_zero],
      map_add' := by
        intros m₂ m₃
        exact hQ.polar_add_right m₁ m₂ m₃ },
  -- FIX: Add the missing 'map_zero' proof for the outer homomorphism.
  map_zero' := by
    -- We prove that `polarBilinear Q 0` is the zero homomorphism.
    ext m₂
    simp [polar, hQ.map_zero],
  map_add' := by
    intros m₁ m₂
    ext m₃
    -- FIX: Complete the proof using the lemma from hQ.
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_mk]
    exact hQ.polar_add_left m₁ m₂ m₃ }











/-
Definition 2.12 (Diagonal Quadratic Maps). Given two R-modules M and N for some commuta- tive ring R, an R-quadratic map Q : M ! N, and a set G ⊆ M of R-module generators of M, we say Q is diagonal (with respect to G)
Q(g + g′) = Q(g) + Q(g′)
for all g,g′ ∈ G. We further say that Q is diagonalizable if there exists some set G ⊆ M of
R-module generators of M so that Q is diagonal with respect to G.
-/


/-!
### Diagonal Quadratic Maps
-/

/--
A quadratic map `Q` is **diagonal** with respect to a set of generators `G` if
`Q(g + g') = Q(g) + Q(g')` for all `g, g' ∈ G`. This is equivalent to the
polar map `polar Q` vanishing on pairs of elements from `G`.
-/
def IsDiagonalQuadraticMap (Q : M → N) (G : Set M) (h_gen : Submodule.span R G = ⊤) : Prop :=
  ∀ g g' : ↥G, polar Q g g' = 0

/--
A quadratic map `Q` is **diagonalizable** if there exists a set of `R`-module
generators `G` for `M` such that `Q` is diagonal with respect to `G`.
-/
def IsDiagonalizableQuadraticMap (Q : M → N) : Prop :=
  ∃ (G : Set M) (h_gen : Submodule.span R G = ⊤), IsDiagonalQuadraticMap Q G h_gen









/-
Definition 2.13 (Quadratic Forms). Given a commutative ring R, we say that an (R-)quadratic form is a degree 2 homogeneous polynomial with coefficients in R (i.e. a homogeneous degree 2 element Q in the polynomial algebra R[S] for some given set S).
-/

/-
Definition 2.14 (Diagonal Quadratic Forms). Given a commutative ring R and an R-quadratic form Q ∈ R[S] for some given set S, we say that Q is diagonal if
Q(s + s′) = Q(s) + Q(s′)
for all s, s′ ∈ S. We further say that Q is diagonalizable if there exists some subset S′ ⊆ R[S] and
an R-algebra isomorphism φ : R[S′] !∼ R[S] so that the quadratic form Q ◦ φ ∈ R[S′] is diagonal.
-/



/-!
### Quadratic Forms
-/

open MvPolynomial

/--
An (R-)quadratic form is a degree 2 homogeneous polynomial with coefficients in R.
-/
def IsQuadraticForm {S : Type*} (Q : MvPolynomial S R) : Prop :=
  IsHomogeneous Q 2

/--
A quadratic form `Q ∈ R[S]` is **diagonal** if all its monomials are of the
form `c * (X s)^2` for some `s ∈ S`, i.e., it has no cross-terms.
This means that for any monomial `m` in the support of `Q`, the support of `m`
as a function from `S` to `ℕ` has at most one element.
-/
def IsDiagonalQuadraticForm {S : Type*} (Q : MvPolynomial S R) : Prop :=
  ∀ m ∈ Q.support, m.support.card ≤ 1

/--
A quadratic form `Q` is **diagonalizable** if there exists an `R`-algebra
automorphism `φ` of `R[S]` that transforms `Q` into a diagonal form.
This corresponds to a linear change of variables.
-/
def IsDiagonalizableQuadraticForm {S : Type*} (Q : MvPolynomial S R) : Prop :=
  ∃ (φ : MvPolynomial S R ≃ₐ[R] MvPolynomial S R), IsDiagonalQuadraticForm (φ Q)










/-
Definition 2.16 (Quadratic maps induced by Quadratic forms).
Given a commutative ring R, a quadratic form Q ∈ R[S]
for some finite set S with cardinality n := #S,
and a total ordering τ> on S, we define the quadratic map
Qe : Rn ! R induced by Q (and τ<) by setting
n!n! Q Xri·⃗ei :=Q Xri·φ(i) ,
i=1 i=1
where φ : {1, · · · n} ! S is the unique order-preserving bijection carrying < to τ .
-/


/-!
### Quadratic Maps from Quadratic Forms
-/

--
-- The new definition using a matrix instead of a polynomial
--
def mapFromQuadraticForm (S : Type*) [Fintype S]
  -- Instead of a polynomial Q, we take its coefficient matrix A
  (A : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) R) :
  -- The output signature is the same as before
  (Fin (Fintype.card S) → R) → R :=
  -- The body implements vᵀ * A * v
  fun v => dotProduct v (Matrix.mulVec A v)


theorem mapFromQuadraticForm_is_quadratic {S : Type*} [Fintype S]
  (A : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) R) :
  IsQuadraticMap (mapFromQuadraticForm S A) := by
  constructor

  -- 1. Proof that mapFromQuadraticForm S A 0 = 0
  case map_zero =>
    simp [mapFromQuadraticForm, Matrix.mulVec_zero, dotProduct_zero]

  -- 2. Proof of additivity in the first argument of the polar form
  case polar_add_left =>
    intros m₁ m₂ m₃
    dsimp [polar, mapFromQuadraticForm]
    -- FIX: Use the correct lemma names for dot product linearity.
    simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add]
    abel

  -- 3. Proof of additivity in the second argument of the polar form
  case polar_add_right =>
    intros m₁ m₂ m₃
    dsimp [polar, mapFromQuadraticForm]
    -- FIX: Use the correct lemma names for dot product linearity.
    simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add]
    abel



/-
Remark 2.17 (Two induced quadratic maps).
Our choice of a (unique) induced quadratic map associated to
a quadratic form is based on our preference for using the > relation
mentioned in Remark 2.5. A preference for the < relation would
in general give a different induced quadratic map.
-/
