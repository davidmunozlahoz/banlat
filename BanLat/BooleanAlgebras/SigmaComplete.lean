/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.CountableSupClosed
import Mathlib.Order.Disjointed

/-!
# σ-complete Boolean algebras

This file introduces **`σ`-complete Boolean algebras**.

We prove:
* An order isomorphism between `σ`-complete Boolean algebras preserves countable suprema.
* That principal intervals in `σ`-complete Boolean algebras are `σ`-complete Boolean algebras.

We also define when some Boolean subalgebra is `σ`-complete, and prove that:
* A Boolean subalgebra is `σ`-complete iff it contains the supremum of every sequence of elements.
* An arbitrary intersection of `σ`-complete Boolean subalgebras is `σ`-complete.

Lastly, for some Boolean subalgebra `A`, `sigmaCompleteClosure A` is defined as the interseccion of
all `σ`-complete Boolean subalgebras that contain `A`. Some of its usual properties are derived.
-/

universe u v

/-- A **`σ`-complete Boolean algebra** is a Boolean algebra in which every countable subset has a
least upper bound. -/
class SigmaCompleteBooleanAlgebra (B : Type u) extends BooleanAlgebra B, SupSet B where
  isLUB_sSup_of_countable (s : Set B) (hs : s.Countable) : IsLUB s (sSup s)

namespace SigmaCompleteBooleanAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- In a `σ`-complete Boolean algebra, every member of a countable set is below its supremum. -/
theorem le_sSup_of_countable {s : Set B} (hs : s.Countable)
    {a : B} (ha : a ∈ s) : a ≤ sSup s := by
  exact (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable s hs).1 ha

/-- In a `σ`-complete Boolean algebra, the supremum of a countable set is below each
of its upper bounds. -/
theorem sSup_le_of_countable {s : Set B} (hs : s.Countable)
    {a : B} (ha : ∀ b ∈ s, b ≤ a) : sSup s ≤ a := by
  exact (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable s hs).2 ha

/-- In a `σ`-complete Boolean algebra, every member of a sequence is below its supremum. -/
theorem le_iSup_nat (a : ℕ → B) (n : ℕ) : a n ≤ ⨆ i, a i := by
  exact le_sSup_of_countable (Set.countable_range a) ⟨n, rfl⟩

/-- In a `σ`-complete Boolean algebra, the supremum of a sequence is below each
of its upper bounds. -/
theorem iSup_nat_le (a : ℕ → B) {b : B} (h : ∀ n, a n ≤ b) : (⨆ n, a n) ≤ b := by
  exact sSup_le_of_countable (Set.countable_range a) (by rintro _ ⟨n, rfl⟩; exact h n)

/-- In a `σ`-complete Boolean algebra, intersection distributes over the supremum of a sequence. -/
theorem inf_iSup_nat (a : B) (b : ℕ → B) :
    a ⊓ (⨆ n, b n) = ⨆ n, a ⊓ b n := by
  apply le_antisymm
  · have hb : (⨆ n, b n) ≤ aᶜ ⊔ (⨆ n, a ⊓ b n) := by
      apply iSup_nat_le
      intro n
      calc
        b n = (aᶜ ⊔ a) ⊓ b n := by simp
        _ = (aᶜ ⊓ b n) ⊔ (a ⊓ b n) := inf_sup_right ..
        _ ≤ aᶜ ⊔ (⨆ n, a ⊓ b n) :=
          sup_le_sup inf_le_left (le_iSup_nat (fun n ↦ a ⊓ b n) n)
    calc
      a ⊓ (⨆ n, b n) ≤ a ⊓ (aᶜ ⊔ (⨆ n, a ⊓ b n)) := inf_le_inf_left a hb
      _ = a ⊓ (⨆ n, a ⊓ b n) := by rw [inf_sup_left]; simp
      _ ≤ ⨆ n, a ⊓ b n := inf_le_right
  · apply iSup_nat_le
    intro n
    exact inf_le_inf_left a (le_iSup_nat b n)

/-- The supremum of a sequence distributes over intersection in a
`σ`-complete Boolean algebra. -/
theorem iSup_inf_nat (a : ℕ → B) (b : B) :
    (⨆ n, a n) ⊓ b = ⨆ n, a n ⊓ b := by
  simpa only [inf_comm] using inf_iSup_nat b a

/-- The infimum of a sequence in a `σ`-complete Boolean algebra, obtained by
De Morgan duality from its supremum. -/
noncomputable def iInfNat (a : ℕ → B) : B :=
  (⨆ n, (a n)ᶜ)ᶜ

/-- De Morgan's identity for the infimum of a sequence in a `σ`-complete Boolean algebra. -/
@[simp]
theorem compl_iInfNat (a : ℕ → B) :
    (iInfNat a)ᶜ = ⨆ n, (a n)ᶜ := by
  simp [iInfNat]

/-- In a `σ`-complete Boolean algebra, the infimum of a sequence is below each member of the
sequence. -/
theorem iInfNat_le (a : ℕ → B) (n : ℕ) : iInfNat a ≤ a n := by
  rw [iInfNat, ← compl_compl (a n), compl_le_compl_iff_le]
  exact le_iSup_nat (fun n ↦ (a n)ᶜ) n

/-- In a `σ`-complete Boolean algebra, every lower bound of a sequence is below its infimum. -/
theorem le_iInfNat (a : ℕ → B) {b : B} (h : ∀ n, b ≤ a n) :
    b ≤ iInfNat a := by
  rw [iInfNat, ← compl_compl b, compl_le_compl_iff_le]
  exact iSup_nat_le _ fun n ↦ compl_le_compl (h n)

/-- In a `σ`-complete Boolean algebra, a sequence and its sequence of partial suprema have the
same supremum. -/
theorem iSup_partialSups_nat (a : ℕ → B) :
    (⨆ n, partialSups a n) = ⨆ n, a n := by
  apply le_antisymm
  · exact iSup_nat_le _ fun n ↦ partialSups_le a n _ fun j _ ↦ le_iSup_nat a j
  · exact iSup_nat_le _ fun n ↦ (le_partialSups a n).trans (le_iSup_nat (partialSups a) n)

/-- In a `σ`-complete Boolean algebra, disjointing a sequence preserves its supremum. -/
theorem iSup_disjointed_nat (a : ℕ → B) :
    (⨆ n, disjointed a n) = ⨆ n, a n := by
  rw [← iSup_partialSups_nat (disjointed a), partialSups_disjointed,
    iSup_partialSups_nat]

end SigmaCompleteBooleanAlgebra

namespace OrderIso

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]

/-- An order isomorphism between `σ`-complete Boolean algebras preserves
countable suprema. -/
theorem map_iSup_nat (e : B ≃o C) (a : ℕ → B) :
    e (⨆ n, a n) = ⨆ n, e (a n) := by
  apply le_antisymm
  · apply e.le_symm_apply.mp
    apply SigmaCompleteBooleanAlgebra.iSup_nat_le
    intro n
    apply e.le_symm_apply.mpr
    exact SigmaCompleteBooleanAlgebra.le_iSup_nat (fun n ↦ e (a n)) n
  · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
    intro n
    exact e.monotone (SigmaCompleteBooleanAlgebra.le_iSup_nat a n)

end OrderIso

namespace Set.Iic

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- If `B` is a `σ`-complete Boolean algebra, then the principal interval
`Set.Iic a = {b ∈ B | b ≤ a}` is a `σ`-complete Boolean algebra. -/
noncomputable instance {a : B} : SigmaCompleteBooleanAlgebra (Set.Iic a) where
  sSup s := ⟨a ⊓ sSup ((↑) '' s), inf_le_left⟩
  isLUB_sSup_of_countable s hs := by
    have hs' : ((fun x : Set.Iic a ↦ (x : B)) '' s).Countable := hs.image _
    constructor
    · intro x hx
      change (x : B) ≤ a ⊓ sSup ((↑) '' s)
      exact le_inf x.property
        (SigmaCompleteBooleanAlgebra.le_sSup_of_countable hs' ⟨x, hx, rfl⟩)
    · intro z hz
      change a ⊓ sSup ((↑) '' s) ≤ (z : B)
      apply inf_le_of_right_le
      apply SigmaCompleteBooleanAlgebra.sSup_le_of_countable hs'
      rintro _ ⟨x, hx, rfl⟩
      exact hz hx

/-- Countable suprema in the principal interval below `a` are computed as
countable suprema in `B`. -/
@[simp]
theorem coe_iSup_nat (a : B) (f : ℕ → Set.Iic a) :
    ((↑(⨆ n, f n) : B)) = ⨆ n, (f n : B) := by
  apply le_antisymm
  · have hle : (⨆ n, f n) ≤
        (⟨⨆ n, (f n : B), SigmaCompleteBooleanAlgebra.iSup_nat_le _ fun n ↦ (f n).property⟩ :
          Set.Iic a) :=
      SigmaCompleteBooleanAlgebra.iSup_nat_le _ fun n ↦
        show (f n : B) ≤ ⨆ n, (f n : B) from
          SigmaCompleteBooleanAlgebra.le_iSup_nat (fun n ↦ (f n : B)) n
    exact hle
  · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
    intro n
    exact SigmaCompleteBooleanAlgebra.le_iSup_nat f n

end Set.Iic

open Set

namespace BooleanSubalgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- A Boolean subalgebra is `σ`-complete if it is closed under countable
suprema computed in the ambient Boolean algebra. -/
def IsSigmaComplete (A : BooleanSubalgebra B) : Prop :=
  CountableSupClosed (A : Set B)

/-- A `σ`-complete Boolean subalgebra contains the supremum of every countable
subset of its carrier. -/
theorem IsSigmaComplete.sSup_mem {A : BooleanSubalgebra B}
    (hA : A.IsSigmaComplete) {s : Set B} (hs : s.Countable)
    (hsub : s ⊆ A) :
    sSup s ∈ A := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · have hsSup : sSup (∅ : Set B) = ⊥ := by
      exact (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable
        (∅ : Set B) Set.countable_empty).unique isLUB_empty
    simp [hsSup]
  · exact hA.isLUB_mem s hsub hsne hs _
      (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable s hs)

/-- A `σ`-complete Boolean subalgebra contains the supremum of every sequence
of its elements. -/
theorem IsSigmaComplete.iSup_mem {A : BooleanSubalgebra B}
    (hA : A.IsSigmaComplete) (a : ℕ → B)
    (ha : ∀ n, a n ∈ A) :
    ⨆ n, a n ∈ A := by
  rw [iSup]
  apply hA.sSup_mem (Set.countable_range a)
  rintro _ ⟨n, rfl⟩
  exact ha n

/-- A Boolean subalgebra is `σ`-complete exactly when it contains the supremum
of every sequence of its elements. -/
theorem isSigmaComplete_iff_iSup_mem {A : BooleanSubalgebra B} :
    A.IsSigmaComplete ↔
      ∀ (a : ℕ → B), (∀ n, a n ∈ A) → ⨆ n, a n ∈ A := by
  constructor
  · exact fun hA a ha ↦ hA.iSup_mem a ha
  · intro h
    unfold IsSigmaComplete
    refine ⟨?_⟩
    intro t hsub hne hcount x hx
    obtain ⟨a, rfl⟩ := hcount.exists_eq_range hne
    have hx_eq : x = ⨆ n, a n := hx.unique
      (SigmaCompleteBooleanAlgebra.isLUB_sSup_of_countable
        (Set.range a) (Set.countable_range a))
    rw [hx_eq]
    apply h
    intro n
    exact hsub (Set.mem_range_self n)

/-- A `σ`-complete Boolean subalgebra becomes a `σ`-complete Boolean algebra. -/
@[implicit_reducible]
noncomputable def IsSigmaComplete.toSigmaCompleteBooleanAlgebra
    {A : BooleanSubalgebra B} (hA : A.IsSigmaComplete) :
    SigmaCompleteBooleanAlgebra A := by
  classical
  let sup : Set A → A := fun s ↦
    if hs : s.Countable then
      ⟨sSup ((↑) '' s), hA.sSup_mem (hs.image Subtype.val)
        (fun _ ⟨a, _, ha⟩ ↦ ha ▸ a.property)⟩
    else ⊥
  refine
    { (inferInstance : BooleanAlgebra A) with
      sSup := sup
      isLUB_sSup_of_countable := by
        intro s hs
        dsimp only [sup]
        rw [dite_eq_left hs]
        constructor
        · intro a ha
          change (a : B) ≤ sSup ((↑) '' s)
          exact SigmaCompleteBooleanAlgebra.le_sSup_of_countable
            (hs.image Subtype.val) ⟨a, ha, rfl⟩
        · intro b hb
          change sSup ((↑) '' s) ≤ (b : B)
          apply SigmaCompleteBooleanAlgebra.sSup_le_of_countable (hs.image Subtype.val)
          intro x hx
          obtain ⟨x, hx, rfl⟩ := hx
          exact hb hx }

/-- Countable suprema in a `σ`-complete Boolean subalgebra are computed in the ambient
Boolean algebra. -/
theorem IsSigmaComplete.coe_sSup {A : BooleanSubalgebra B}
    (hA : A.IsSigmaComplete) (s : Set A) (hs : s.Countable) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ((sSup s : A) : B) = sSup ((↑) '' s) := by
  classical
  change ((if h : s.Countable then
      (⟨sSup ((↑) '' s), hA.sSup_mem (h.image Subtype.val)
        (fun _ ⟨a, _, ha⟩ ↦ ha ▸ a.property)⟩ : A)
    else ⊥ : A) : B) = sSup ((↑) '' s)
  rw [dite_eq_left hs]

/-- Suprema of sequences in a `σ`-complete Boolean subalgebra are computed in
the ambient Boolean algebra. -/
theorem IsSigmaComplete.coe_iSup {A : BooleanSubalgebra B}
    (hA : A.IsSigmaComplete) (a : ℕ → A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    ((⨆ n, a n : A) : B) = ⨆ n, (a n : B) := by
  classical
  simpa only [iSup, ← Set.range_comp'] using
    hA.coe_sSup (Set.range a) (Set.countable_range a)

/-- The full Boolean subalgebra is `σ`-complete. -/
theorem isSigmaComplete_top :
    (⊤ : BooleanSubalgebra B).IsSigmaComplete := by
  exact CountableSupClosed.univ

/-- The trivial Boolean subalgebra `{⊥, ⊤}` is `σ`-complete. -/
theorem isSigmaComplete_bot :
    (⊥ : BooleanSubalgebra B).IsSigmaComplete := by
  rw [isSigmaComplete_iff_iSup_mem]
  intro a ha
  by_cases htop : ∃ n, a n = ⊤
  · obtain ⟨n, hn⟩ := htop
    have hiSup_top : (⨆ n, a n) = ⊤ := by
      apply le_antisymm
      · exact le_top
      · rw [← hn]
        exact SigmaCompleteBooleanAlgebra.le_iSup_nat a n
    rw [hiSup_top]
    exact BooleanSubalgebra.top_mem
  · have ha_bot : ∀ n, a n = ⊥ := fun n ↦
      (BooleanSubalgebra.mem_bot.mp (ha n)).resolve_right
        (fun hn ↦ htop ⟨n, hn⟩)
    have hiSup_bot : (⨆ n, a n) = ⊥ := by
      apply le_antisymm
      · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
        intro n
        rw [ha_bot n]
      · exact bot_le
    rw [hiSup_bot]
    exact BooleanSubalgebra.bot_mem

/-- The intersection of two `σ`-complete Boolean subalgebras is again `σ`-complete. -/
theorem IsSigmaComplete.inf {A D : BooleanSubalgebra B}
    (hA : A.IsSigmaComplete) (hD : D.IsSigmaComplete) :
    (A ⊓ D).IsSigmaComplete := by
  exact hA.inter hD

/-- An arbitrary intersection of `σ`-complete Boolean subalgebras is
`σ`-complete. -/
theorem isSigmaComplete_sInf {S : Set (BooleanSubalgebra B)}
    (hS : ∀ A ∈ S, A.IsSigmaComplete) :
    (sInf S).IsSigmaComplete := by
  change CountableSupClosed (⋂ A ∈ S, (A : Set B))
  apply CountableSupClosed.iInter
  intro A
  apply CountableSupClosed.iInter
  intro hAS
  exact hS A hAS

/-- The smallest `σ`-complete Boolean subalgebra containing a set. -/
def sigmaCompleteClosure (s : Set B) : BooleanSubalgebra B :=
  sInf {A | s ⊆ A ∧ A.IsSigmaComplete}

/-- A set is contained in the `σ`-complete Boolean subalgebra it generates. -/
theorem subset_sigmaCompleteClosure (s : Set B) :
    s ⊆ sigmaCompleteClosure s := by
  intro x hx
  unfold sigmaCompleteClosure
  apply BooleanSubalgebra.mem_sInf.mpr
  intro A hA
  exact hA.1 hx

/-- The `σ`-complete Boolean subalgebra generated by a set is `σ`-complete. -/
theorem isSigmaComplete_sigmaCompleteClosure (s : Set B) :
    (sigmaCompleteClosure s).IsSigmaComplete := by
  unfold sigmaCompleteClosure
  apply isSigmaComplete_sInf
  intro A hA
  exact hA.2

/-- The `σ`-complete Boolean subalgebra generated by `s` is contained in every
`σ`-complete Boolean subalgebra containing `s`. -/
theorem sigmaCompleteClosure_le {s : Set B} {A : BooleanSubalgebra B}
    (hA : A.IsSigmaComplete) :
    sigmaCompleteClosure s ≤ A ↔ s ⊆ A := by
  constructor
  · exact fun h ↦ (subset_sigmaCompleteClosure s).trans h
  · intro hs
    unfold sigmaCompleteClosure
    exact sInf_le ⟨hs, hA⟩

/-- The operation of taking the generated `σ`-complete Boolean subalgebra is
monotone. -/
theorem sigmaCompleteClosure_mono {s t : Set B} (hst : s ⊆ t) :
    sigmaCompleteClosure s ≤ sigmaCompleteClosure t := by
  apply (sigmaCompleteClosure_le (isSigmaComplete_sigmaCompleteClosure t)).2
  exact hst.trans (subset_sigmaCompleteClosure t)

/-- A Boolean subalgebra generates itself as a `σ`-complete Boolean subalgebra
exactly when it is already `σ`-complete. -/
theorem sigmaCompleteClosure_eq_self {A : BooleanSubalgebra B} :
    sigmaCompleteClosure (A : Set B) = A ↔ A.IsSigmaComplete := by
  constructor
  · intro h
    rw [← h]
    exact isSigmaComplete_sigmaCompleteClosure (A : Set B)
  · intro hA
    apply le_antisymm
    · exact (sigmaCompleteClosure_le hA).2 Set.Subset.rfl
    · exact subset_sigmaCompleteClosure (A : Set B)

end BooleanSubalgebra
