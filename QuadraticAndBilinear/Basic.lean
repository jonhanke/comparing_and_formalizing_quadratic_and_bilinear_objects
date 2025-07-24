import Mathlib
import QuadraticAndBilinear.ForMathlib.LinearAlgebra.QuadraticForm.Basic
import QuadraticAndBilinear.ForMathlib.LinearAlgebra.QuadraticForm.DFinsupp
import QuadraticAndBilinear.ForMathlib.LinearAlgebra.BilinearMap


-- Some basics

variable {R M N : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

-- defn:linear_maps
example (L : M →ₗ[R] N) (a : R) (m : M) : L (a • m) = a • L m := map_smul L a m

-- defn:alternating_bilinear_maps
example (B : M →ₗ[R] M →ₗ[R] N) : B.IsAlt ↔ ∀ m, B m m = 0 := Iff.rfl

-- defn:quadratic_maps
example (Q : QuadraticMap R M N) (a : R) (m : M) : Q (a • m) = (a * a) • Q m := Q.map_smul a m

open scoped DirectSum

variable {ι : Type*} {Mᵢ : ι → Type*}
variable [DecidableEq ι]  [(i : ι) → AddCommGroup (Mᵢ i)] [(i : ι) → Module R (Mᵢ i)]

-- defn:direct_sums_of_quadratic_maps
def QuadraticMap.directSum [DecidableEq ι] :
    (Π i, QuadraticMap R (Mᵢ i) N) →ₗ[R] QuadraticMap R (⨁ i, Mᵢ i) N :=
  QuadraticMap.dfinsupp

@[simp]
theorem QuadraticMap.directSum_of (i : ι) (Q : QuadraticMap R (Mᵢ i) N) :
    QuadraticMap.directSum (Pi.single i Q) = Q.comp (DirectSum.component _ _ _ i) :=
  QuadraticMap.dfinsupp_piSingle _ _


@[simp]
theorem QuadraticMap.directSum_apply_of
      (Q : ⨁ i, QuadraticMap R (Mᵢ i) N) (i : ι) (m : Mᵢ i) :
    QuadraticMap.directSum Q (DirectSum.of _ i m) = Q i m :=
  QuadraticMap.dfinsupp_apply_single _ _ _

/-- Two quadratic maps from a direct sum agree if they agree:
1. On the diagonal
2. Off the diagonal

We could require `i < j` in `offDiag`, but as `polarBilin` is symmetric it's not very useful.
-/
theorem QuadraticMap.directSum_ext'
    {Q₁ Q₂ : QuadraticMap R (⨁ i, Mᵢ i) N}
    (diag : ∀ i m, Q₁ (.of _ i m) = Q₂ (.of _ i m))
    (offDiag : ∀ i j, i ≠ j → ∀ m n,
      Q₁.polarBilin (.of _ i m) (.of _ j n) = Q₂.polarBilin (.of _ i m) (.of _ j n)) :
    Q₁ = Q₂ := by
  ext m
  classical
  rw [← m.sum_support_of, QuadraticMap.map_sum, QuadraticMap.map_sum]
  simp_rw [diag]
  congr! 2 with ⟨⟨i, j⟩⟩ h
  rw [Finset.mem_filter] at h
  refine offDiag _ _ h.2 _ _


-- The `ext` paper explains a little why _this_ is the one tagged `ext` not the above.
@[ext]
theorem QuadraticMap.dfinsupp_ext [LinearOrder ι]
    {Q₁ Q₂ : QuadraticMap R (Π₀ i, Mᵢ i) N}
    (diag : ∀ i, Q₁.comp (DFinsupp.lsingle i) = Q₂.comp (DFinsupp.lsingle i))
    (upperTri : ∀ i j, i ≠ j →
      Q₁.polarBilin.compl₁₂ (DFinsupp.lsingle i) (DFinsupp.lsingle j) =
      Q₂.polarBilin.compl₁₂ (DFinsupp.lsingle i) (DFinsupp.lsingle j)) :
    Q₁ = Q₂ :=
  QuadraticMap.directSum_ext'
    (fun i => DFunLike.congr_fun <| diag i)
    (fun i j hij m n => DFunLike.congr_fun (DFunLike.congr_fun (upperTri i j hij) m) n)



variable (R) in
@[simps -fullyApplied]
def extendZero {P : ι → Prop} [DecidablePred P] :
    ((i : { i : ι // P i}) → Mᵢ i.val) →ₗ[R] Π i, Mᵢ i where
  toFun x := fun i => if h : P i then x ⟨_, h⟩ else 0
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

-- note the families are infinite not finite!
def QuadraticMap.dfinsuppTriangle [LinearOrder ι] :
    ((Π i, QuadraticMap R (Mᵢ i) N) ×
      (Π ij : {p : ι × ι // p.1 < p.2}, Mᵢ ij.val.1 →ₗ[R] Mᵢ ij.val.2 →ₗ[R] N)) ≃ₗ[R]
      QuadraticMap R (Π₀ i, Mᵢ i) N :=
  .ofLinear
    -- the forward map
    (LinearMap.coprod
      QuadraticMap.dfinsupp
      (LinearMap.BilinMap.toQuadraticMapLinearMap R R (⨁ i, Mᵢ i) ∘ₗ
        LinearMap.dfinsupp₂ ∘ₗ (LinearEquiv.piCurry R _).toLinearMap ∘ₗ
          (LinearEquiv.piCongrLeft R
            (fun i => Mᵢ i.fst →ₗ[R] Mᵢ i.snd →ₗ[R] N) (Equiv.sigmaEquivProd ι ι).symm).toLinearMap ∘ₗ
              extendZero R
                (Mᵢ := fun ij => Mᵢ ij.1 →ₗ[R] Mᵢ ij.2 →ₗ[R] N)
                (P := fun ij : ι × ι => ij.1 < ij.2) ))
    -- the reverse map
    (LinearMap.prod
      (LinearMap.pi fun i => QuadraticMap.compL (R := R) (DFinsupp.lsingle i))
      (LinearMap.pi fun ij =>
        LinearMap.lcompl₁₂ R (DFinsupp.lsingle ij.val.1) (DFinsupp.lsingle ij.val.2) ∘ₗ
          QuadraticMap.polarBilinHom))
    -- proof they are inverses
    (by
      ext Q i j hij : 2 <;> dsimp
      · ext mi
        dsimp
        simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
          Equiv.piCongrLeft', LinearMap.BilinMap.toQuadraticMapLinearMap]
        unfold Sigma.curry
        dsimp
        -- something is going wrong with `dsimp` here
        erw [LinearMap.coe_mk]
        dsimp
        erw [DFinsupp.sumZeroHom_single, LinearMap.coe_mk]
        sorry
      · ext mi mj
        dsimp
        sorry)
    (by
      ext i Qi : 4 <;> dsimp
      · ext j mj
        dsimp
        sorry
      · ext jk mj mk
        dsimp
        sorry
      · ext j mj
        dsimp
        sorry
      · ext jk mj mk
        dsimp
        sorry)


-- The `ext` paper explains a little why _this_ is the one tagged `ext` not the above.
@[ext]
theorem QuadraticMap.directSum_ext [LinearOrder ι]
    {Q₁ Q₂ : QuadraticMap R (⨁ i, Mᵢ i) N}
    (diag : ∀ i, Q₁.comp (DirectSum.lof R _ Mᵢ i) = Q₂.comp (DirectSum.lof R _ Mᵢ i))
    (upperTri : ∀ i j, i ≠ j →
      Q₁.polarBilin.compl₁₂ (DirectSum.lof R ι Mᵢ i) (DirectSum.lof R ι Mᵢ j) =
      Q₂.polarBilin.compl₁₂ (DirectSum.lof R ι Mᵢ i) (DirectSum.lof R ι Mᵢ j)) :
    Q₁ = Q₂ :=
  QuadraticMap.dfinsupp_ext diag upperTri

-- note the families are infinite not finite!
def QuadraticMap.directSumTriangle [LinearOrder ι] :
    ((Π i, QuadraticMap R (Mᵢ i) N) ×
      (Π ij : {p : ι × ι // p.1 < p.2}, Mᵢ ij.val.1 →ₗ[R] Mᵢ ij.val.2 →ₗ[R] N)) ≃ₗ[R]
      QuadraticMap R (⨁ i, Mᵢ i) N :=
  QuadraticMap.dfinsuppTriangle
