/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.Order.Atoms
import Mathlib.Order.Cover

/-!
# Atomless Boolean algebras

This file defines **atomless Boolean algebras** and characterizes them as densely
ordered Boolean algebras.
-/

universe u

namespace BooleanAlgebra

/-- A Boolean algebra is atomless if it has no order-theoretic atoms. -/
def IsAtomless (B : Type u) [BooleanAlgebra B] : Prop :=
  ∀ a : B, ¬ IsAtom a

variable {B : Type u} [BooleanAlgebra B]

private theorem isAtom_sdiff_of_covBy {a b : B} (h : CovBy a b) :
    IsAtom (b \ a) := by
  refine ⟨?_, ?_⟩
  · rw [Ne, sdiff_eq_bot_iff]
    exact not_le_of_gt h.lt
  · intro x hx
    have hxb : x ≤ b := hx.le.trans sdiff_le
    have hdisj : Disjoint a x :=
      disjoint_sdiff_self_right.mono_right hx.le
    rcases h.eq_or_eq le_sup_left (sup_le h.le hxb) with hsup | hsup
    · apply le_bot_iff.mp
      calc
        x = a ⊓ x := (inf_eq_right.mpr (sup_eq_left.mp hsup)).symm
        _ ≤ ⊥ := hdisj.le_bot
    · exact False.elim (not_le_of_gt hx (sdiff_le_iff.2 hsup.ge))

/-- A Boolean algebra is atomless if and only if its order dense. -/
theorem isAtomless_iff_denselyOrdered :
    IsAtomless B ↔ DenselyOrdered B := by
  constructor
  · intro hB
    rw [denselyOrdered_iff_forall_not_covBy]
    intro a b hab
    exact hB _ (isAtom_sdiff_of_covBy hab)
  · intro hB a ha
    letI : DenselyOrdered B := hB
    obtain ⟨x, hbotx, hxa⟩ := exists_between ha.bot_lt
    rw [ha.2 x hxa] at hbotx
    exact (lt_irrefl ⊥ hbotx).elim

end BooleanAlgebra
