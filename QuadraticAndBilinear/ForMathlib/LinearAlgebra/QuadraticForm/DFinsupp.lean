import QuadraticAndBilinear.ForMathlib.LinearAlgebra.QuadraticForm.Basic
import QuadraticAndBilinear.ForMathlib.LinearAlgebra.BilinearMap.DFinsupp
import Mathlib.LinearAlgebra.DFinsupp
import QuadraticAndBilinear.ForMathlib.Data.DFinsupp.BigOperators

variable {R : Type*} {ι : Type*} {Mᵢ : ι → Type*} {N : Type*}
variable [CommSemiring R] [DecidableEq ι]
variable [(i : ι) → AddCommMonoid (Mᵢ i)] [(i : ι) → Module R (Mᵢ i)]
variable [AddCommMonoid N] [Module R N]


/-- The diagonal quadratic map on finitely supported functions. -/
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
        use LinearMap.BilinMap.dfinsupp B
        rintro ⟨x, sx, hx⟩ ⟨y, sy, hy⟩
        dsimp [DFinsupp.sumAddHom, DFinsupp.sumZeroHom]
        change ∑ xyi ∈ (sx + sy).toFinset, _ =
          ∑ xi ∈ sx.toFinset, _ + ∑ y ∈ sy.toFinset, _ + (∑ xi ∈ sx.toFinset, _ : _ →ₗ[_] _) _
        rw [LinearMap.sum_apply]
        simp_rw [hB, Finset.sum_add_distrib, Multiset.toFinset_add]
        congrm ?_ + ?_ + ?_
        · refine Finset.sum_subset Finset.subset_union_left (fun i _ hi => ?_) |>.symm
          rw [hx i |>.resolve_left (by simpa using hi), map_zero]
        · refine Finset.sum_subset Finset.subset_union_right (fun i _ hi => ?_) |>.symm
          rw [hy i |>.resolve_left (by simpa using hi), map_zero]
        · refine Finset.sum_subset Finset.subset_union_left (fun i _ hi => ?_) |>.symm
          rw [hx i |>.resolve_left (by simpa using hi), LinearMap.map_zero₂] }
  map_add' Q₁ Q₂ := by
    ext x
    classical
    simp [DFinsupp.sumZeroHom_apply]
    eta_expand
    simp
  map_smul' _ _ := by
    ext x
    classical
    simp [DFinsupp.sumZeroHom_apply, DFinsupp.smul_sum]
    eta_expand
    simp

theorem QuadraticMap.dfinsupp_mk (Q : Π i, QuadraticMap R (Mᵢ i) N)
    (v : Π i, Mᵢ i) (s : Multiset ι) (hs) :
    QuadraticMap.dfinsupp Q ⟨v, Trunc.mk ⟨s, hs⟩⟩ = ∑ i ∈ s.toFinset, Q i (v i) :=
  rfl

@[simp]
theorem QuadraticMap.dfinsupp_piSingle (i : ι) (Q : QuadraticMap R (Mᵢ i) N) :
    QuadraticMap.dfinsupp (Pi.single i Q) = Q.comp (DFinsupp.lapply i) := by
  ext ⟨x, xs, hx⟩
  erw [QuadraticMap.dfinsupp_mk]
  rw [Finset.sum_eq_single i] <;> simp +contextual [hx _ |>.resolve_left]

@[simp]
theorem QuadraticMap.dfinsupp_apply_single
      (Q : Π i, QuadraticMap R (Mᵢ i) N) (i : ι) (m : Mᵢ i) :
    QuadraticMap.dfinsupp Q (DFinsupp.single i m) = Q i m := by
  simp [QuadraticMap.dfinsupp]
