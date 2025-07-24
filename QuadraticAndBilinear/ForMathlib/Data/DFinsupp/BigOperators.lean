import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Module

-- https://github.com/leanprover-community/mathlib4/pull/27272

variable {α} {β : α → Type*} {γ : Type*}

namespace DFinsupp

variable [DecidableEq α]

/--
When summing over an `ZeroHom`, the decidability assumption is not needed, and the result is
also an `ZeroHom`.
-/
def sumZeroHom [∀ i, Zero (β i)] [AddCommMonoid γ] (φ : ∀ i, ZeroHom (β i) γ) :
    ZeroHom (Π₀ i, β i) γ where
  toFun f :=
    (f.support'.lift fun s => ∑ i ∈ Multiset.toFinset s.1, φ i (f i)) <| by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset ∩ sy.toFinset ⊆ sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset ∩ sy.toFinset ⊆ sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl

@[simp]
theorem sumZeroHom_single [∀ i, Zero (β i)] [AddCommMonoid γ] (φ : ∀ i, ZeroHom (β i) γ) (i)
    (x : β i) : sumZeroHom φ (single i x) = φ i x := by
  dsimp [sumZeroHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton, Finset.sum_singleton, Pi.single_eq_same]



/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sumZeroHom_apply [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] (φ : ∀ i, ZeroHom (β i) γ) (f : Π₀ i, β i) :
    sumZeroHom φ f = f.sum fun x m => φ x m := by
  rcases f with ⟨f, s, hf⟩
  change (∑ i ∈ _, _) = ∑ i ∈ _ with _, _
  rw [Finset.sum_filter, Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, map_zero]

theorem sum_smul_index {α R : Type*} {M : α → Type*} {N}
    [DecidableEq α] [∀ i, Zero (M i)] [∀ i (x : M i), Decidable (x ≠ 0)]
    [∀ i, SMulZeroClass R (M i)] [AddCommMonoid N] {g : Π₀ a, M a}
    {b : R} {h : ∀ a, M a → N} (h0 : ∀ (i : α), h i 0 = 0) :
    (b • g).sum h = g.sum fun i c ↦ h i (b • c) :=
  DFinsupp.sum_mapRange_index h0

end DFinsupp
