/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.Data.Set.Countable
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Disjointed

/-!
# σ-complete Boolean algebras

This file introduces **`σ`-complete Boolean algebras**.
-/

universe u

/-- A **`σ`-complete Boolean algebra** is a Boolean algebra in which every countable subset has a
least upper bound. -/
class SigmaCompleteBooleanAlgebra (B : Type u) extends BooleanAlgebra B, SupSet B where
  isLUB_sSup_of_countable (s : Set B) (hs : s.Countable) : IsLUB s (sSup s)

namespace SigmaCompleteBooleanAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- Every member of a countable set is below its supremum. -/
theorem le_sSup_of_countable {s : Set B} (hs : s.Countable)
    {a : B} (ha : a ∈ s) : a ≤ sSup s := by
  exact (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable s hs).1 ha

/-- The supremum of a countable set is below each of its upper bounds. -/
theorem sSup_le_of_countable {s : Set B} (hs : s.Countable)
    {a : B} (ha : ∀ b ∈ s, b ≤ a) : sSup s ≤ a := by
  exact (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable s hs).2 ha

/-- Every member of a sequence is below its supremum. -/
theorem le_iSup_nat (a : ℕ → B) (n : ℕ) : a n ≤ ⨆ i, a i := by
  exact le_sSup_of_countable (Set.countable_range a) ⟨n, rfl⟩

/-- The supremum of a sequence is below each of its upper bounds. -/
theorem iSup_nat_le (a : ℕ → B) {b : B} (h : ∀ n, a n ≤ b) : (⨆ n, a n) ≤ b := by
  exact sSup_le_of_countable (Set.countable_range a) (by rintro _ ⟨n, rfl⟩; exact h n)

/-- A sequence and its sequence of partial suprema have the same supremum. -/
theorem iSup_partialSups_nat (a : ℕ → B) :
    (⨆ n, partialSups a n) = ⨆ n, a n := by
  apply le_antisymm
  · exact iSup_nat_le _ fun n ↦ partialSups_le a n _ fun j _ ↦ le_iSup_nat a j
  · exact iSup_nat_le _ fun n ↦ (le_partialSups a n).trans (le_iSup_nat (partialSups a) n)

/-- Disjointing a sequence preserves its supremum. -/
theorem iSup_disjointed_nat (a : ℕ → B) :
    (⨆ n, disjointed a n) = ⨆ n, a n := by
  rw [← iSup_partialSups_nat (disjointed a), partialSups_disjointed,
    iSup_partialSups_nat]

end SigmaCompleteBooleanAlgebra
