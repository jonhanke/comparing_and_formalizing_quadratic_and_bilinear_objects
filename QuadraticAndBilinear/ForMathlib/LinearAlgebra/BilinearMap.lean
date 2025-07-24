import Mathlib.LinearAlgebra.BilinearMap

variable  {S R₁ R₂ N Mₗ Pₗ Qₗ Qₗ' : Type*}

variable (S) in
/-- `LinearMap.lcompl₁₂` is linear in the bilinear map. -/
@[simps]
def LinearMap.lcompl₁₂ [Semiring S] [Semiring R₁] [Semiring R₂]
    [AddCommMonoid N]
    [AddCommMonoid Mₗ] [AddCommMonoid Pₗ] [AddCommMonoid Qₗ] [AddCommMonoid Qₗ'] [Module R₁ Mₗ] [Module R₂ N]
    [Module R₁ Pₗ] [Module R₁ Qₗ] [Module R₂ Pₗ] [Module S Pₗ] [Module R₂ Qₗ']
    [SMulCommClass R₂ R₁ Pₗ]
    [SMulCommClass R₁ S Pₗ]
    [SMulCommClass R₂ S Pₗ]
    (g : Qₗ →ₗ[R₁] Mₗ) (g' : Qₗ' →ₗ[R₂] N) : (Mₗ →ₗ[R₁] N →ₗ[R₂] Pₗ) →ₗ[S] (Qₗ →ₗ[R₁] Qₗ' →ₗ[R₂] Pₗ) where
  toFun f := f.compl₁₂ g g'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
