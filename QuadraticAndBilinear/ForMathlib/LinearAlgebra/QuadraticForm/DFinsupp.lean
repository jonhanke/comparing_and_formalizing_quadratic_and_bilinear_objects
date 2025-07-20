import QuadraticAndBilinear.ForMathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.DFinsupp
import QuadraticAndBilinear.ForMathlib.Data.DFinsupp.BigOperators

variable {R : Type*} {ι : Type*} {Mᵢ : ι → Type*} {N : Type*}
variable [CommSemiring R] [DecidableEq ι]
variable [(i : ι) → AddCommMonoid (Mᵢ i)] [(i : ι) → Module R (Mᵢ i)]
variable [AddCommMonoid N] [Module R N]


-- defn:direct_sums_of_quadratic_maps
def QuadraticMap.dfinsupp [DecidableEq ι] :
    (Π i, QuadraticMap R (Mᵢ i) N) →ₗ[R] QuadraticMap R (Π₀ i, Mᵢ i) N where
  toFun Q :=
    { toFun := DFinsupp.sumZeroHom fun i => Q i
      toFun_smul a x := by
        classical
        simp [DFinsupp.sumZeroHom_apply]
        sorry
      exists_companion' := sorry}
  map_add' Q₁ Q₂ := by
    ext x
    classical
    simp [DFinsupp.sumZeroHom_apply]
  map_smul' _ _ := by
    ext x
    classical
    simp [DFinsupp.sumZeroHom_apply, DFinsupp.smul_sum]

@[simp]
theorem QuadraticMap.dfinsupp_piSingle (i : ι) (Q : QuadraticMap R (Mᵢ i) N) :
    QuadraticMap.dfinsupp (Pi.single i Q) = Q.comp (DFinsupp.lapply i) :=
  sorry

@[simp]
theorem QuadraticMap.dfinsupp_apply_single
      (Q : Π₀ i, QuadraticMap R (Mᵢ i) N) (i : ι) (m : Mᵢ i) :
    QuadraticMap.dfinsupp Q (DFinsupp.single i m) = Q i m := by
  simp [QuadraticMap.dfinsupp]
