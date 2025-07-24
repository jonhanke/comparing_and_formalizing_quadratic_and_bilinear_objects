import QuadraticAndBilinear.ForMathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.DFinsupp
import QuadraticAndBilinear.ForMathlib.Data.DFinsupp.BigOperators

namespace DFinsupp

universe u u₁ u₂ v v₁ v₂ v₃ w x y l
variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] : SMulZeroClass γ (Π₀ i, β i) where
  smul c v := v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _
  smul_zero _ := mapRange_zero _ _

end DFinsupp

variable {R : Type*} {ι : Type*} {Mᵢ : ι → Type*} {N : Type*}
variable [CommSemiring R] [DecidableEq ι]
variable [(i : ι) → AddCommMonoid (Mᵢ i)] [(i : ι) → Module R (Mᵢ i)]
variable [AddCommMonoid N] [Module R N]

theorem DFinsupp.sum_smul_index {α R : Type*} {M : α → Type*}
    [DecidableEq α] [∀ i, Zero (M i)] [∀ i (x : M i), Decidable (x ≠ 0)]
    [∀ i, SMulZeroClass R (M i)] [AddCommMonoid N] {g : Π₀ a, M a}
    {b : R} {h : ∀ a, M a → N} (h0 : ∀ (i : α), h i 0 = 0) :
    (b • g).sum h = g.sum fun i c ↦ h i (b • c) :=
  DFinsupp.sum_mapRange_index h0

-- defn:direct_sums_of_quadratic_maps
def QuadraticMap.dfinsupp [DecidableEq ι] :
    (Π i, QuadraticMap R (Mᵢ i) N) →ₗ[R] QuadraticMap R (Π₀ i, Mᵢ i) N where
  toFun Q :=
    { toFun := DFinsupp.sumZeroHom fun i => Q i
      toFun_smul a x := by
        classical
        simp [DFinsupp.sumZeroHom_apply, DFinsupp.sum_smul_index, QuadraticMap.map_smul,
          DFinsupp.smul_sum]
      exists_companion' := by
        choose B hB using fun i => (Q i).exists_companion
        classical
        use DFinsupp.lsum ℕ fun i => LinearMap.flip <| DFinsupp.lsum ℕ fun j =>
          if h : i = j then h ▸ B i else 0
        intro x y
        simp [DFinsupp.sumZeroHom_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
          hB, Finset.sum_add_distrib]


        sorry}
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
