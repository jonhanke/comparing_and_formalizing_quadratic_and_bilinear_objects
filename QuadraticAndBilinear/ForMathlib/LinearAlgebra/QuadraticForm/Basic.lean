import Mathlib.LinearAlgebra.QuadraticForm.Basic

variable {R M N P : Type*}

section Semiring
variable [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- `QuadraticMap.comp` as a linear map. -/
@[simps]
def QuadraticMap.compL
    (f : M →ₗ[R] N) :
    QuadraticMap R N P →ₗ[R] QuadraticMap R M P where
  toFun Q := Q.comp f
  map_add' _ _ := ext fun _ => rfl
  map_smul' _ _ := ext fun _ => rfl

end Semiring

section Ring
variable [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- `QuadraticMap.polarBilin` is linear in the form `Q`. -/
@[simps]
def QuadraticMap.polarBilinHom : QuadraticMap R M N →ₗ[R] LinearMap.BilinMap R M N where
  toFun := polarBilin
  map_add' _ _ := by ext; simp [polar_add]
  map_smul' _ _ := by ext; simp [polar_smul]
