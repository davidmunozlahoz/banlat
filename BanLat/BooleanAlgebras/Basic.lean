/-
Authors: Jesús Illescas-Fiorito
-/

import Mathlib.Order.ModularLattice
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.SymmDiff
import Mathlib.Tactic.Order

/-!
# Boolean algebras

This file add some basic constructions for Boolean algebras that are missing in mathlib:
* principal intervals `Set.Iic a = {b ∈ B, b ≤ a}`, `a ∈ B`, become Boolean algebras with
the induced structure.
* the increasing union over a (non-empty) linearly ordered set `{A i, i ∈ ι}` of Boolean
subalgebras becomes as well a Boolean subalgebra.
* a compatible family of order isomorphisms `εᵢ : A i ≃o C i` between two increasing
families of Boolean subalgebras extends to an order isomorphism `ε : (⋃ i, A i) ≃o (⋃ i, C i)`.
-/

universe u v

open scoped symmDiff

variable {B : Type u} [BooleanAlgebra B]

/-- Let `a, x, y ∈ B`. If `a ⊓ x = a ⊓ y` and `aᶜ ⊓ x = aᶜ ⊓ y`, then `x=y`. -/
theorem eq_of_inf_eq_inf_compl {a x y : B}
    (ha : a ⊓ x = a ⊓ y) (hac : aᶜ ⊓ x = aᶜ ⊓ y) : x = y := by
  calc
    x = (a ⊔ aᶜ) ⊓ x := by simp
    _ = (a ⊓ x) ⊔ (aᶜ ⊓ x) := inf_sup_right ..
    _ = (a ⊓ y) ⊔ (aᶜ ⊓ y) := by rw [ha, hac]
    _ = (a ⊔ aᶜ) ⊓ y := (inf_sup_right ..).symm
    _ = y := by simp

/-- Let `a, b, c ∈ B`. Then `a ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = a ⊓ b`. -/
theorem inf_conditional (a b c : B) :
    a ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = a ⊓ b := by
  rw [inf_sup_left]
  have h : a ⊓ (aᶜ ⊓ c) = ⊥ := eq_bot_iff.2 <| calc
    a ⊓ (aᶜ ⊓ c) ≤ a ⊓ aᶜ := inf_le_inf_left a inf_le_left
    _ = ⊥ := inf_compl_eq_bot
  rw [h]
  simp

/-- Let `a, b, c ∈ B`. Then `aᶜ ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = aᶜ ⊓ c`. -/
theorem compl_inf_conditional (a b c : B) :
    aᶜ ⊓ ((a ⊓ b) ⊔ (aᶜ ⊓ c)) = aᶜ ⊓ c := by
  rw [inf_sup_left]
  have h : aᶜ ⊓ (a ⊓ b) = ⊥ := eq_bot_iff.2 <| calc
    aᶜ ⊓ (a ⊓ b) ≤ aᶜ ⊓ a := inf_le_inf_left aᶜ inf_le_left
    _ = ⊥ := compl_inf_eq_bot
  rw [h]
  simp

/-- Let `a, b, c ∈ B`. Then `(a ⊓ bᶜ) ⊔ (aᶜ ⊓ cᶜ) = ((a ⊓ b) ⊔ (aᶜ ⊓ c))ᶜ`. -/
theorem conditional_compl (a b c : B) :
    (a ⊓ bᶜ) ⊔ (aᶜ ⊓ cᶜ) = ((a ⊓ b) ⊔ (aᶜ ⊓ c))ᶜ := by
  apply eq_of_inf_eq_inf_compl (a := a)
  · rw [inf_conditional, compl_sup, compl_inf, compl_inf, compl_compl]
    symm
    calc
      a ⊓ ((aᶜ ⊔ bᶜ) ⊓ (a ⊔ cᶜ)) =
          (a ⊓ (aᶜ ⊔ bᶜ)) ⊓ (a ⊔ cᶜ) := (inf_assoc ..).symm
      _ = ((a ⊓ aᶜ) ⊔ (a ⊓ bᶜ)) ⊓ (a ⊔ cᶜ) :=
        congrArg (fun x ↦ x ⊓ (a ⊔ cᶜ)) (inf_sup_left ..)
      _ = (a ⊓ bᶜ) ⊓ (a ⊔ cᶜ) := by simp
      _ = a ⊓ bᶜ := inf_eq_left.2 (le_trans inf_le_left le_sup_left)
  · rw [compl_inf_conditional, compl_sup, compl_inf, compl_inf, compl_compl]
    symm
    calc
      aᶜ ⊓ ((aᶜ ⊔ bᶜ) ⊓ (a ⊔ cᶜ)) =
          (aᶜ ⊓ (aᶜ ⊔ bᶜ)) ⊓ (a ⊔ cᶜ) := (inf_assoc ..).symm
      _ = aᶜ ⊓ (a ⊔ cᶜ) := congrArg (fun x ↦ x ⊓ (a ⊔ cᶜ))
        (inf_eq_left.2 le_sup_left)
      _ = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ cᶜ) := inf_sup_left ..
      _ = aᶜ ⊓ cᶜ := by simp

/-- Taking suprema is Lipschitz with respect to the order-valued symmetric difference. -/
theorem symmDiff_sup_le_sup (a b c d : B) :
    (a ⊔ b) ∆ (c ⊔ d) ≤ (a ∆ c) ⊔ (b ∆ d) := by
  apply symmDiff_le
  · have ha := le_symmDiff_sup_right a c
    have hb := le_symmDiff_sup_right b d
    order
  · have hc := le_symmDiff_sup_right c a
    have hd := le_symmDiff_sup_right d b
    rw [symmDiff_comm c a] at hc
    rw [symmDiff_comm d b] at hd
    order

namespace Set.Iic

noncomputable instance instDistribLattice {a : B} : DistribLattice (Set.Iic a) :=
  Subtype.distribLattice
    (fun _ _ hx hy ↦ sup_le hx hy)
    (fun _ _ hx _ ↦ inf_le_left.trans hx)

noncomputable instance instBooleanAlgebra {a : B} : BooleanAlgebra (Set.Iic a) :=
  DistribLattice.booleanAlgebraOfComplemented (Set.Iic a)

/-- In the principal interval below `a`, the complement of `b` is `a \ b`. -/
@[simp]
theorem coe_compl {a : B} (b : Set.Iic a) :
    ((bᶜ : Set.Iic a) : B) = a \ (b : B) := by
  have hb := Set.Iic.isCompl_iff.mp (isCompl_compl (x := b))
  exact (hb.1.sdiff_eq_of_sup_eq hb.2).symm

/-- Boolean difference in a principal interval agrees with Boolean difference
in the ambient algebra. -/
@[simp]
theorem coe_sdiff {a : B} (b c : Set.Iic a) :
    ((b \ c : Set.Iic a) : B) = (b : B) \ (c : B) := by
  rw [show b \ c = b ⊓ cᶜ from _root_.sdiff_eq]
  change (b : B) ⊓ ((cᶜ : Set.Iic a) : B) = (b : B) \ (c : B)
  rw [coe_compl, ← inf_sdiff_assoc, inf_eq_left.mpr b.property]

/-- Symmetric difference in a principal interval agrees with symmetric
difference in the ambient algebra. -/
@[simp]
theorem coe_symmDiff {a : B} (b c : Set.Iic a) :
    ((symmDiff b c : Set.Iic a) : B) = symmDiff (b : B) (c : B) := by
  simp [symmDiff_def]

end Set.Iic

namespace BooleanSubalgebra

/-- Let `(A i)_{i ∈ ι}` be an increasing family of Boolean subalgebras of `B`, indexed
by a nonempty linear order `ι`. Then `increasingUnion A hA` is the Boolean subalgebra
of `B` whose underlying set is `⋃ i, A i`. -/
noncomputable def increasingUnion {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (A : ι → BooleanSubalgebra B) (hA : Monotone A) : BooleanSubalgebra B where
  carrier := ⋃ i, (A i : Set B)
  bot_mem' := Set.mem_iUnion.2
    ⟨Classical.choice inferInstance, (A _).bot_mem⟩
  compl_mem' := by
    rintro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨i, (A i).compl_mem hi⟩
  supClosed' := by
    rintro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact Set.mem_iUnion.2 ⟨max i j, (A (max i j)).sup_mem
      (hA (le_max_left i j) hi) (hA (le_max_right i j) hj)⟩
  infClosed' := by
    rintro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact Set.mem_iUnion.2 ⟨max i j, (A (max i j)).inf_mem
      (hA (le_max_left i j) hi) (hA (le_max_right i j) hj)⟩

/-- Membership in an increasing union of Boolean subalgebras. -/
@[simp]
theorem mem_increasingUnion {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (A : ι → BooleanSubalgebra B) (hA : Monotone A) (x : B) :
    x ∈ increasingUnion A hA ↔ ∃ i, x ∈ A i := by
  change x ∈ ⋃ i, (A i : Set B) ↔ ∃ i, x ∈ A i
  exact Set.mem_iUnion

section IncreasingUnionOrderIso

variable {D : Type v} [BooleanAlgebra D]
variable {ι : Type*} [LinearOrder ι] [Nonempty ι]
variable (A : ι → BooleanSubalgebra B) (C : ι → BooleanSubalgebra D)
variable (hA : Monotone A) (hC : Monotone C)
variable (e : ∀ i, A i ≃o C i)

private noncomputable def increasingUnionStage
    (a : increasingUnion A hA) : ι :=
  Classical.choose ((mem_increasingUnion A hA a).1 a.property)

private theorem increasingUnionStage_mem
    (a : increasingUnion A hA) :
    (a : B) ∈ A (increasingUnionStage A hA a) :=
  Classical.choose_spec ((mem_increasingUnion A hA a).1 a.property)

private noncomputable def increasingUnionMap
    (a : increasingUnion A hA) : increasingUnion C hC :=
  ⟨e (increasingUnionStage A hA a)
      ⟨a, increasingUnionStage_mem A hA a⟩,
    (mem_increasingUnion C hC _).2
      ⟨increasingUnionStage A hA a,
        (e (increasingUnionStage A hA a)
          ⟨a, increasingUnionStage_mem A hA a⟩).property⟩⟩

private theorem increasingUnionMap_apply
    (he : ∀ i j (hij : i ≤ j) (a : A i),
      ((e j ⟨a, hA hij a.property⟩ : C j) : D) = (e i a : D))
    (i) (a : A i) :
    ((increasingUnionMap A C hA hC e
      ⟨a, (mem_increasingUnion A hA a).2 ⟨i, a.property⟩⟩ :
        increasingUnion C hC) : D) = (e i a : D) := by
  let a' : increasingUnion A hA :=
    ⟨a, (mem_increasingUnion A hA a).2 ⟨i, a.property⟩⟩
  let j := increasingUnionStage A hA a'
  have hj : (a : B) ∈ A j := increasingUnionStage_mem A hA a'
  change (e j ⟨a, hj⟩ : D) = (e i a : D)
  exact (he j (max j i) (le_max_left _ _) _).symm.trans
    (he i (max j i) (le_max_right _ _) a)

private theorem increasingUnionMap_le_iff
    (he : ∀ i j (hij : i ≤ j) (a : A i),
      ((e j ⟨a, hA hij a.property⟩ : C j) : D) = (e i a : D))
    (a a' : increasingUnion A hA) :
    increasingUnionMap A C hA hC e a ≤ increasingUnionMap A C hA hC e a' ↔
      a ≤ a' := by
  let i := max (increasingUnionStage A hA a) (increasingUnionStage A hA a')
  have ha : (a : B) ∈ A i :=
    hA (le_max_left _ _) (increasingUnionStage_mem A hA a)
  have ha' : (a' : B) ∈ A i :=
    hA (le_max_right _ _) (increasingUnionStage_mem A hA a')
  change (increasingUnionMap A C hA hC e a : D) ≤
    (increasingUnionMap A C hA hC e a' : D) ↔ (a : B) ≤ (a' : B)
  rw [show (increasingUnionMap A C hA hC e a : D) = (e i ⟨a, ha⟩ : D) by
      simpa using increasingUnionMap_apply A C hA hC e he i ⟨a, ha⟩,
    show (increasingUnionMap A C hA hC e a' : D) = (e i ⟨a', ha'⟩ : D) by
      simpa using increasingUnionMap_apply A C hA hC e he i ⟨a', ha'⟩]
  exact (e i).le_iff_le

private theorem increasingUnionMap_surjective
    (he : ∀ i j (hij : i ≤ j) (a : A i),
      ((e j ⟨a, hA hij a.property⟩ : C j) : D) = (e i a : D)) :
    Function.Surjective (increasingUnionMap A C hA hC e) := by
  intro d
  obtain ⟨i, hi⟩ := (mem_increasingUnion C hC d).1 d.property
  let ai := (e i).symm ⟨d, hi⟩
  let a : increasingUnion A hA :=
    ⟨ai, (mem_increasingUnion A hA ai).2 ⟨i, ai.property⟩⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  rw [show (increasingUnionMap A C hA hC e a : D) = (e i ai : D) by
      simpa [a] using increasingUnionMap_apply A C hA hC e he i ai]
  simp [ai]

private noncomputable def increasingUnionOrderEmbedding
    (he : ∀ i j (hij : i ≤ j) (a : A i),
      ((e j ⟨a, hA hij a.property⟩ : C j) : D) = (e i a : D)) :
    increasingUnion A hA ↪o increasingUnion C hC :=
  OrderEmbedding.ofMapLEIff (increasingUnionMap A C hA hC e)
    (increasingUnionMap_le_iff A C hA hC e he)

/-- Compatible order isomorphisms between increasing families of Boolean subalgebras
induce an order isomorphism between their increasing unions. -/
noncomputable def increasingUnionOrderIso
    (he : ∀ i j (hij : i ≤ j) (a : A i),
      ((e j ⟨a, hA hij a.property⟩ : C j) : D) = (e i a : D)) :
    increasingUnion A hA ≃o increasingUnion C hC :=
  OrderIso.ofSurjective (increasingUnionOrderEmbedding A C hA hC e he)
    (increasingUnionMap_surjective A C hA hC e he)

/-- The order isomorphism between increasing unions agrees with each order isomorphism
in the compatible family. -/
theorem increasingUnionOrderIso_apply
    (he : ∀ i j (hij : i ≤ j) (a : A i),
      ((e j ⟨a, hA hij a.property⟩ : C j) : D) = (e i a : D))
    (i) (a : A i) :
    ((increasingUnionOrderIso A C hA hC e he
      ⟨a, (mem_increasingUnion A hA a).2 ⟨i, a.property⟩⟩ :
        increasingUnion C hC) : D) = (e i a : D) :=
  increasingUnionMap_apply A C hA hC e he i a

end IncreasingUnionOrderIso

end BooleanSubalgebra
