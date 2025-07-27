import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.DFinsupp
import QuadraticAndBilinear.ForMathlib.LinearAlgebra.BilinearMap

section


variable {ι R} {M N : ι → Type*} [Semiring R]
  [∀ i, AddCommMonoid (M i)][∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)][∀ i, Module R (N i)]

/-- `Pi.map` as a linear map. -/
@[simps]
def LinearMap.piMap (f : ∀ i, M i →ₗ[R] N i) :
    (Π i, M i) →ₗ[R] (Π i, N i) where
  toFun := Pi.map (f ·)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

end

variable {R : Type*} {ι κ : Type*} {Mᵢ : ι → Type*} {Mₖ : κ → Type*} {N : Type*}
variable [CommSemiring R] [DecidableEq ι] [DecidableEq κ]
variable [(i : ι) → AddCommMonoid (Mᵢ i)] [(i : ι) → Module R (Mᵢ i)]
variable [(i : κ) → AddCommMonoid (Mₖ i)] [(i : κ) → Module R (Mₖ i)]
variable [AddCommMonoid N] [Module R N]

namespace LinearMap

open LinearMap (BilinMap)

/-- The bilinear version of `DFinsupp.lsum`. -/
def dfinsupp₂ : (Π i j, Mᵢ i →ₗ[R] Mₖ j →ₗ[R] N) →ₗ[R] (Π₀ i, Mᵢ i) →ₗ[R] (Π₀ i, Mₖ i) →ₗ[R] N :=
  (DFinsupp.lsum R).toLinearMap ∘ₗ LinearMap.piMap fun _ =>
    LinearMap.lflip ∘ₗ (DFinsupp.lsum R).toLinearMap ∘ₗ LinearMap.piMap fun _ =>
      LinearMap.lflip

@[simp]
theorem dfinsupp₂_piSingle_piSingle (i : ι) (j : κ) (B : Mᵢ i →ₗ[R] Mₖ j →ₗ[R] N) :
    dfinsupp₂ (Pi.single i (Pi.single j B)) = B.compl₁₂ (DFinsupp.lapply i) (DFinsupp.lapply j) := by
  ext i' mj j' mk
  dsimp [dfinsupp₂]
  simp
  obtain rfl | hij := eq_or_ne i i' <;> obtain rfl | hij := eq_or_ne j j'
  all_goals simp_all [Ne.symm]

@[simp]
theorem dfinsupp₂_single_single (B : Π i j, Mᵢ i →ₗ[R] Mₖ j →ₗ[R] N) (i : ι) (j : κ) (x y) :
    dfinsupp₂ B (.single i x) (.single j y) = B i j x y := by
  simp [dfinsupp₂]

/-- The diagonal version of `LinearMap.dfinsupp₂`.

This is essential a bilinear map built from a block diagonal matrix. -/
def BilinMap.dfinsupp :
    (Π i, BilinMap R (Mᵢ i) N) →ₗ[R] BilinMap R (Π₀ i, Mᵢ i) N :=
  (DFinsupp.lsum R).toLinearMap ∘ₗ LinearMap.piMap fun i =>
    lcompl₁₂ R (LinearMap.id) <| DFinsupp.lapply i

@[simp]
theorem BilinMap.dfinsupp_piSingle (i : ι) (B : BilinMap R (Mᵢ i) N) :
    BilinMap.dfinsupp (Pi.single i B) = B.compl₁₂ (DFinsupp.lapply i) (DFinsupp.lapply i) := by
  ext j mj k mk
  dsimp [dfinsupp]
  obtain rfl | hij := eq_or_ne i j <;> obtain rfl | hij := eq_or_ne k i
  all_goals simp_all [Ne.symm]

@[simp]
theorem BilinMap.dfinsupp_single_single_same (B : Π i, BilinMap R (Mᵢ i) N) (i : ι) (x y) :
    BilinMap.dfinsupp B (.single i x) (.single i y) = B i x y := by
  simp [dfinsupp]

@[simp]
theorem BilinMap.dfinsupp_single_single_of_ne (B : Π i, BilinMap R (Mᵢ i) N) (i j : ι) (hij : i ≠ j)
    (x y) :
    BilinMap.dfinsupp B (.single i x) (.single j y) = 0 := by
  simp [dfinsupp, hij.symm]
