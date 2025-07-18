import Mathlib

-- Some basics

variable {R M N : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

-- defn:linear_maps
example (L : M →ₗ[R] N) (a : R) (m : M) : L (a • m) = a • L m := map_smul L a m

-- defn:alternating_bilinear_maps
example (B : M →ₗ[R] M →ₗ[R] N) : B.IsAlt ↔ ∀ m, B m m = 0 := Iff.rfl

-- defn:quadratic_maps
example (Q : QuadraticMap R M N) (a : R) (m : M) : Q (a • m) = (a * a) • Q m := Q.map_smul a m

/-- `QuadraticMap.comp` as a linear map. -/
@[simps]
def QuadraticMap.compL {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] N) :
    QuadraticMap R N P →ₗ[R] QuadraticMap R M P where
  toFun Q := Q.comp f
  map_add' _ _ := ext fun _ => rfl
  map_smul' _ _ := ext fun _ => rfl

open scoped DirectSum

variable {ι : Type*} {Mᵢ : ι → Type*}
variable [DecidableEq ι]  [(i : ι) → AddCommGroup (Mᵢ i)] [(i : ι) → Module R (Mᵢ i)]

-- defn:direct_sums_of_quadratic_maps
def QuadraticMap.directSum [DecidableEq ι] :
    (⨁ i, QuadraticMap R (Mᵢ i) N) →ₗ[R] QuadraticMap R (⨁ i, Mᵢ i) N :=
  DirectSum.toModule _ _ _ fun i => QuadraticMap.compL (DirectSum.component _ _ _ i)

@[simp]
theorem QuadraticMap.directSum_single (i : ι) (Q : QuadraticMap R (Mᵢ i) N) :
    QuadraticMap.directSum (DirectSum.of _ i Q) = Q.comp (DirectSum.component _ _ _ i) :=
  DirectSum.toModule_lof _ _ _


@[simp]
theorem QuadraticMap.directSum_apply_single
      (Q : ⨁ i, QuadraticMap R (Mᵢ i) N) (i : ι) (m : Mᵢ i) :
    QuadraticMap.directSum Q (DirectSum.of _ i m) = Q i m := by
  -- this one is annoying because the API is bad, the actual content is boring.
  sorry

/-- Two quadratic maps from a direct sum agree if they agree:
1. On the diagonal
2. Off the diagonal

We could require `i < j` in `offDiag`, but as `polarBilin` is symmetric it's not very useful.
-/
noncomputable def QuadraticMap.directSum_ext'
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
noncomputable def QuadraticMap.directSum_ext [LinearOrder ι]
    {Q₁ Q₂ : QuadraticMap R (⨁ i, Mᵢ i) N}
    (diag : ∀ i, Q₁.comp (DirectSum.lof R _ Mᵢ i) = Q₂.comp (DirectSum.lof R _ Mᵢ i))
    (upperTri : ∀ i j, i ≠ j →
      Q₁.polarBilin.compl₁₂ (DirectSum.lof R ι Mᵢ i) (DirectSum.lof R ι Mᵢ j) =
      Q₂.polarBilin.compl₁₂ (DirectSum.lof R ι Mᵢ i) (DirectSum.lof R ι Mᵢ j)) :
    Q₁ = Q₂ :=
  QuadraticMap.directSum_ext'
    (fun i => DFunLike.congr_fun <| diag i)
    (fun i j hij m n => DFunLike.congr_fun (DFunLike.congr_fun (upperTri i j hij) m) n)

noncomputable def QuadraticMap.directSumTriangle [LinearOrder ι] :
    ((⨁ i, QuadraticMap R (Mᵢ i) N) ×
      (⨁ ij : {p : ι × ι // p.1 < p.2}, Mᵢ ij.val.1 →ₗ[R] Mᵢ ij.val.2 →ₗ[R] N)) ≃ₗ[R]
      QuadraticMap R (⨁ i, Mᵢ i) N :=
  .ofLinear
    -- the forward map
    (LinearMap.coprod
      QuadraticMap.directSum
      (LinearMap.BilinMap.toQuadraticMapLinearMap R R (⨁ i, Mᵢ i) ∘ₗ
        -- this one will be `BilinMap.directSum`
        sorry))
    -- the reverse map
    (LinearMap.prod
      sorry
      sorry)
    -- proof they are inverses
    (by
      ext Q i j hij : 2 <;> dsimp
      · ext mi
        dsimp
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
