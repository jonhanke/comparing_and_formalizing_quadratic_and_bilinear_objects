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
          Pi.single (M := fun j => Mᵢ j →ₗ[R] Mᵢ i →ₗ[R] N) i (B i).flip j
        rintro ⟨x, sx, hx⟩ ⟨y, sy, hy⟩
        dsimp [DFinsupp.sumAddHom, DFinsupp.sumZeroHom]
        change ∑ xyi ∈ (sx + sy).toFinset, _ =
          ∑ xi ∈ sx.toFinset, _ + ∑ y ∈ sy.toFinset, _ +
            (∑ xi ∈ sx.toFinset, _ : _ →ₗ[_] _) _
        rw [LinearMap.sum_apply]
        simp [hB, Finset.sum_add_distrib]
        congrm ?_ + ?_ + ?_
        · refine Finset.sum_subset Finset.subset_union_left (fun i _ hi => ?_) |>.symm
          rw [hx i |>.resolve_left (by simpa using hi), map_zero]
        · refine Finset.sum_subset Finset.subset_union_right (fun i _ hi => ?_) |>.symm
          rw [hy i |>.resolve_left (by simpa using hi), map_zero]
        · change _ = ∑ xi ∈ sx.toFinset, (∑ yi ∈ sy.toFinset, _ : _ →ₗ[_] _) _
          dsimp
          simp_rw [LinearMap.sum_apply]
          conv_rhs =>
            enter [2, xi, 2, yi]
            rw [
              Pi.apply_single
                (f' := fun i (f : Mᵢ i →ₗ[R] Mᵢ xi →ₗ[R] N) => DFunLike.coe f (y i))
                (fun i => rfl) xi (B xi).flip yi,
              Pi.apply_single (M := fun i ↦ Mᵢ xi →ₗ[R] N)
                (f' := fun i (f : Mᵢ xi →ₗ[R] N) => DFunLike.coe f (x xi))
                (fun i => rfl) xi ((B xi).flip (y xi)) yi,
              LinearMap.flip_apply]
          simp only [Finset.sum_pi_single']
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
          rw [← Finset.sum_subset Finset.inter_subset_union]
          intros i _ hi
          simp only [Finset.mem_inter, Multiset.mem_toFinset, not_and_or] at hi
          obtain h | h := hi.imp (hx i |>.resolve_left) (hy i |>.resolve_left) <;> simp [h] }
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
