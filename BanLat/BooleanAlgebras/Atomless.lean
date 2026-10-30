/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Adjoin
import BanLat.BooleanAlgebras.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Cover

/-!
# Atomless and relatively atomless Boolean algebras

This file introduces **atomless Boolean algebras**, and shows that:
* non-trivial atomless Boolean algebras are infinite,
* every principal interval of an atomless Boolean algebra is atomless,
* a Boolean algebra is atomless iff it is order-dense.

It also defines when a Boolean algebra `B` is **relatively atomless** with respect
to some subalgebra `A`, and shows that:
* relative atomlessness over the trivial subalgebra `{⊥, ⊤}` is ordinary atomlessness.
* If `B` is relatively atomless with respect to `A`, then it is relatively atomless with respect
to every subalgebra of `A`.
* Every atomless subalgebra is relatively atomless with respect to a finite subalgebra.
-/

universe u

namespace BooleanAlgebra

/-- A Boolean algebra is atomless if it has no order-theoretic atoms. -/
def IsAtomless (B : Type u) [BooleanAlgebra B] : Prop :=
  ∀ a : B, ¬ IsAtom a

variable {B : Type u} [BooleanAlgebra B]

/-- A nontrivial atomless Boolean algebra is infinite. -/
theorem infinite_of_isAtomless [Nontrivial B] (hB : IsAtomless B) : Infinite B := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  let : Finite B := hfinite
  obtain ⟨a, ha⟩ := IsAtomic.exists_atom (α := B)
  exact hB a ha

/-- Every principal interval in an atomless Boolean algebra is atomless. -/
theorem IsAtomless.iic (hB : IsAtomless B) {a : B} : IsAtomless (Set.Iic a) := by
  intro b hb
  exact hB (b : B) hb.of_isAtom_coe_Iic

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
    let : DenselyOrdered B := hB
    obtain ⟨x, hbotx, hxa⟩ := exists_between ha.bot_lt
    rw [ha.2 x hxa] at hbotx
    exact (lt_irrefl ⊥ hbotx).elim

/-- Every nonzero element of an atomless Boolean algebra contains a strictly
smaller nonzero element. -/
theorem IsAtomless.exists_nonzero_lt (hB : IsAtomless B) {b : B} (hb : b ≠ ⊥) :
    ∃ a : B, a < b ∧ a ≠ ⊥ := by
  let : DenselyOrdered B := isAtomless_iff_denselyOrdered.mp hB
  obtain ⟨a, ha_bot, ha_b⟩ := exists_between (bot_lt_iff_ne_bot.mpr hb)
  exact ⟨a, ha_b, ne_of_gt ha_bot⟩

end BooleanAlgebra

namespace BooleanSubalgebra

variable {B : Type u} [BooleanAlgebra B]

/-- An ambient Boolean `B` algebra is relatively atomless over one of its subalgebras `A`
if every nonzero element `b` contains an element `c` which is not of the form `b ⊓ a`. -/
def IsRelativelyAtomless (A : BooleanSubalgebra B) : Prop :=
  ∀ ⦃b : B⦄, b ≠ ⊥ → ∃ c ≤ b, ∀ a : A, c ≠ b ⊓ (a : B)

/-- Relative atomlessness over the `{⊥, ⊤}` is ordinary atomlessness. -/
theorem isRelativelyAtomless_bot_iff_isAtomless :
    (⊥ : BooleanSubalgebra B).IsRelativelyAtomless ↔
      BooleanAlgebra.IsAtomless B := by
  constructor
  · intro h b hb
    obtain ⟨c, hcb, hc⟩ := h hb.1
    rcases hb.le_iff.mp hcb with rfl | rfl
    · exact hc ⊥ (by simp)
    · exact hc ⊤ (by simp)
  · intro hB b hb
    obtain ⟨c, hc, hc_ne⟩ := hB.exists_nonzero_lt hb
    refine ⟨c, hc.le, ?_⟩
    intro a
    rcases BooleanSubalgebra.mem_bot.mp a.property with ha | ha
    · simpa [ha] using hc_ne
    · simpa [ha] using ne_of_lt hc

/-- If `B` is relatively atomless over `D`, then it is relatively atomless over every
Boolean subalgebra of `D`. -/
theorem IsRelativelyAtomless.mono {A D : BooleanSubalgebra B}
    (hD : D.IsRelativelyAtomless) (hAD : A ≤ D) :
    A.IsRelativelyAtomless := by
  intro b hb
  obtain ⟨c, hcb, hc⟩ := hD hb
  refine ⟨c, hcb, ?_⟩
  intro a
  exact hc ⟨a, hAD a.property⟩

/-- Let `A ⊆ B` be a finite Boolean subalgebra. If `b ∈ B` and `a ∈ A` satisfy
`b ⊓ a ≠ ⊥`, then there is an atom `p ∈ A` such that `p ≤ a` and `b ⊓ p ≠ ⊥`. -/
private lemma exists_atom_inf_ne_bot_of_finite
    {A : BooleanSubalgebra B} (hA : (A : Set B).Finite)
    (b : B) (a : A) (hba : b ⊓ (a : B) ≠ ⊥) :
    ∃ p : A, IsAtom p ∧ p ≤ a ∧ b ⊓ (p : B) ≠ ⊥ := by
  classical
  let := hA.fintype
  let : CompleteAtomicBooleanAlgebra A :=
    Fintype.toCompleteAtomicBooleanAlgebra A
  let atoms : Finset A := Finset.univ.filter fun p ↦ IsAtom p ∧ p ≤ a
  have hatoms : atoms.sup id = a := by
    rw [Finset.sup_id_eq_sSup]
    simp [atoms]
  by_contra h
  push Not at h
  apply hba
  have hcoe : ((atoms.sup id : A) : B) = atoms.sup fun p ↦ (p : B) := by
    change A.subtype (atoms.sup id) = atoms.sup (A.subtype ∘ id)
    exact map_finset_sup A.subtype atoms id
  calc
    b ⊓ (a : B) = b ⊓ ((atoms.sup id : A) : B) := by rw [hatoms]
    _ = b ⊓ atoms.sup fun p ↦ (p : B) := congrArg (b ⊓ ·) hcoe
    _ = atoms.sup fun p ↦ b ⊓ (p : B) := Finset.sup_inf_distrib_left ..
    _ = ⊥ := (Finset.sup_eq_bot_iff _ _).2 fun p hp ↦ by
      exact h p (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2

/-- An atomless Boolean algebra is relatively atomless over every finite
Boolean subalgebra. -/
theorem isRelativelyAtomless_of_isAtomless_of_finite
    (A : BooleanSubalgebra B) (hB : BooleanAlgebra.IsAtomless B)
    (hA : (A : Set B).Finite) :
    A.IsRelativelyAtomless := by
  intro b hb
  obtain ⟨p, hp, -, hbp⟩ :=
    exists_atom_inf_ne_bot_of_finite hA b ⊤ (by simpa using hb)
  obtain ⟨c, hc, hc_ne⟩ := hB.exists_nonzero_lt hbp
  refine ⟨c, hc.le.trans inf_le_left, ?_⟩
  intro a hca
  have hc_p : c ≤ (p : B) := hc.le.trans inf_le_right
  have hc_a : c ≤ (a : B) := hca.le.trans inf_le_right
  have hpinf_ne : (p ⊓ a : A) ≠ ⊥ := by
    intro hpinf
    apply not_le_of_gt (bot_lt_iff_ne_bot.mpr hc_ne)
    calc
      c ≤ (p : B) ⊓ (a : B) := le_inf hc_p hc_a
      _ = ((p ⊓ a : A) : B) := rfl
      _ = ⊥ := congrArg Subtype.val hpinf
  have hpa : p ≤ a := by
    rw [← inf_eq_left]
    exact (hp.le_iff_eq hpinf_ne).mp inf_le_left
  apply not_le_of_gt hc
  rw [hca]
  exact inf_le_inf_left b hpa

end BooleanSubalgebra
