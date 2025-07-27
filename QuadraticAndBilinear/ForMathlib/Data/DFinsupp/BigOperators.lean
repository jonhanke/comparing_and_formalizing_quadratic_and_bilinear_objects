import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Module

variable {α} {β : α → Type*} {γ : Type*}

namespace DFinsupp

theorem sum_smul_index {α R : Type*} {M : α → Type*} {N}
    [DecidableEq α] [∀ i, Zero (M i)] [∀ i (x : M i), Decidable (x ≠ 0)]
    [∀ i, SMulZeroClass R (M i)] [AddCommMonoid N] {g : Π₀ a, M a}
    {b : R} {h : ∀ a, M a → N} (h0 : ∀ (i : α), h i 0 = 0) :
    (b • g).sum h = g.sum fun i c ↦ h i (b • c) :=
  DFinsupp.sum_mapRange_index h0

end DFinsupp
