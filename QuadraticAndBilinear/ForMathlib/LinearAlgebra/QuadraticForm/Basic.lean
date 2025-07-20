import Mathlib.LinearAlgebra.QuadraticForm.Basic

variable {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

@[simp]
theorem QuadraticMap.coe_mk (f : M → N) (h1 h2) :
    ⇑(QuadraticMap.mk f h1 h2 : QuadraticMap R M N) = f := rfl

/-- `QuadraticMap.comp` as a linear map. -/
@[simps]
def QuadraticMap.compL
    (f : M →ₗ[R] N) :
    QuadraticMap R N P →ₗ[R] QuadraticMap R M P where
  toFun Q := Q.comp f
  map_add' _ _ := ext fun _ => rfl
  map_smul' _ _ := ext fun _ => rfl
