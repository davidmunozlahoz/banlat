/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.SigmaComplete
import Mathlib.Order.BooleanSubalgebra
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Adjoining elements to Boolean subalgebras

Given a Boolean subalgebra `A` of a Boolean algebra `B` and some `b ∈ B`,
this file develops the Boolean subalgebra `A.adjoin b` obtained by adjoining
`b` to `A`.

We show that:
* `A` and `b` are always contained in `A.adjoin b`.
* if `A` is finite, `A.adjoin b` is finite.
* if `A` is `σ`-order complete, `A.adjoin b` is `σ`-order complete.

We also include the following extension result for order-isomorphism:

Let `A ⊆ B` and `C ⊆ D` are Boolean subalgebras, `b ∈ B, d ∈ D`. Let
`e : A → C` be an order-isomorphism such that: `∀ (a₁, a₂), (c₁, c₂) ∈ A × A`,
`(b ⊓ a₁) ⊔ (bᶜ ⊓ a₂) ≤ (b ⊓ c₁) ⊔ (bᶜ ⊓ c₂)` if and only if
`(d ⊓ e(a₁)) ⊔ (dᶜ ⊓ e(a₂)) ≤ (d ⊓ e(c₁)) ⊔ (dᶜ ⊓ e(c₂))`.
Then `e` can be extended to an order-isomorphism between `A.adjoin b` and
`C.adjoing d`, with `b ↦ d`.
-/

universe u v

namespace BooleanSubalgebra

variable {B : Type u} [BooleanAlgebra B]

/-- For a Boolean subalgebra `A`, an element `b ∈ B`, and `p = (a₁, a₂) ∈ A × A`,
`adjoinValue A b p` is the element `(b ⊓ a₁) ⊔ (bᶜ ⊓ a₂)` of `B`. -/
def adjoinValue (A : BooleanSubalgebra B) (b : B) (p : A × A) : B :=
  (b ⊓ (p.1 : B)) ⊔ (bᶜ ⊓ (p.2 : B))

/-- `b ⊓ adjoinValue A b (a₁, a₂) = b ⊓ a₁`. -/
private lemma inf_adjoinValue (A : BooleanSubalgebra B) (b : B) (p : A × A) :
    b ⊓ adjoinValue A b p = b ⊓ (p.1 : B) := by
  rw [adjoinValue, inf_sup_left]
  have h₁ : b ⊓ (b ⊓ (p.1 : B)) = b ⊓ (p.1 : B) := by
    rw [← inf_assoc, inf_idem]
  have h₂ : b ⊓ (bᶜ ⊓ (p.2 : B)) = ⊥ := by
    rw [← inf_assoc, inf_compl_eq_bot]
    simp
  simp only [h₁, h₂, sup_bot_eq]

/-- `bᶜ ⊓ adjoinValue A b (a₁, a₂) = bᶜ ⊓ a₂`. -/
private lemma compl_inf_adjoinValue (A : BooleanSubalgebra B) (b : B)
    (p : A × A) :
    bᶜ ⊓ adjoinValue A b p = bᶜ ⊓ (p.2 : B) := by
  rw [adjoinValue, inf_sup_left]
  have h₁ : bᶜ ⊓ (b ⊓ (p.1 : B)) = ⊥ := by
    rw [← inf_assoc, compl_inf_eq_bot]
    simp
  have h₂ : bᶜ ⊓ (bᶜ ⊓ (p.2 : B)) = bᶜ ⊓ (p.2 : B) := by
    rw [← inf_assoc, inf_idem]
  simp only [h₁, h₂, bot_sup_eq]

/-- Let `p = (a₁, a₂)` and `q = (c₁, c₂)`. Then
`adjoinValue A b p ≤ adjoinValue A b q` iff `b ⊓ a₁ ≤ b ⊓ c₁` and
`bᶜ ⊓ a₂ ≤ bᶜ ⊓ c₂`. -/
theorem adjoinValue_le_iff (A : BooleanSubalgebra B) (b : B) (p q : A × A) :
    adjoinValue A b p ≤ adjoinValue A b q ↔
      b ⊓ (p.1 : B) ≤ b ⊓ (q.1 : B) ∧
        bᶜ ⊓ (p.2 : B) ≤ bᶜ ⊓ (q.2 : B) := by
  constructor
  · intro h
    exact ⟨by simpa only [inf_adjoinValue] using inf_le_inf_left b h,
      by simpa only [compl_inf_adjoinValue] using inf_le_inf_left bᶜ h⟩
  · rintro ⟨h₁, h₂⟩
    exact sup_le_sup h₁ h₂

/-- The Boolean subalgebra obtained by adjoining `b` to some Boolean subalgebra `A`.
Its elements are exactly those of the form `(b ⊓ a₁) ⊔ (bᶜ ⊓ a₂)` with `a₁, a₂ ∈ A`. -/
def adjoin (A : BooleanSubalgebra B) (b : B) : BooleanSubalgebra B where
  carrier := Set.range (adjoinValue A b)
  bot_mem' := ⟨(⊥, ⊥), by simp [adjoinValue]⟩
  compl_mem' := by
    rintro _ ⟨⟨a₁, a₂⟩, rfl⟩
    exact ⟨⟨⟨a₁ᶜ, A.compl_mem a₁.property⟩, ⟨a₂ᶜ, A.compl_mem a₂.property⟩⟩,
      conditional_compl b a₁ a₂⟩
  supClosed' := by
    rintro _ ⟨⟨a₁, a₂⟩, rfl⟩ _ ⟨⟨c₁, c₂⟩, rfl⟩
    refine ⟨⟨⟨a₁ ⊔ c₁, A.sup_mem a₁.property c₁.property⟩,
      ⟨a₂ ⊔ c₂, A.sup_mem a₂.property c₂.property⟩⟩, ?_⟩
    apply eq_of_inf_eq_inf_compl (a := b)
    · calc
        b ⊓ ((b ⊓ (a₁ ⊔ c₁)) ⊔ (bᶜ ⊓ (a₂ ⊔ c₂))) = b ⊓ (a₁ ⊔ c₁) :=
          inf_conditional ..
        _ = (b ⊓ a₁) ⊔ (b ⊓ c₁) := inf_sup_left ..
        _ = (b ⊓ ((b ⊓ a₁) ⊔ (bᶜ ⊓ a₂))) ⊔
            (b ⊓ ((b ⊓ c₁) ⊔ (bᶜ ⊓ c₂))) := by
              rw [inf_conditional, inf_conditional]
        _ = b ⊓ (((b ⊓ a₁) ⊔ (bᶜ ⊓ a₂)) ⊔
            ((b ⊓ c₁) ⊔ (bᶜ ⊓ c₂))) := (inf_sup_left ..).symm
    · calc
        bᶜ ⊓ ((b ⊓ (a₁ ⊔ c₁)) ⊔ (bᶜ ⊓ (a₂ ⊔ c₂))) = bᶜ ⊓ (a₂ ⊔ c₂) :=
          compl_inf_conditional ..
        _ = (bᶜ ⊓ a₂) ⊔ (bᶜ ⊓ c₂) := inf_sup_left ..
        _ = (bᶜ ⊓ ((b ⊓ a₁) ⊔ (bᶜ ⊓ a₂))) ⊔
            (bᶜ ⊓ ((b ⊓ c₁) ⊔ (bᶜ ⊓ c₂))) := by
              rw [compl_inf_conditional, compl_inf_conditional]
        _ = bᶜ ⊓ (((b ⊓ a₁) ⊔ (bᶜ ⊓ a₂)) ⊔
            ((b ⊓ c₁) ⊔ (bᶜ ⊓ c₂))) := (inf_sup_left ..).symm
  infClosed' := by
    rintro _ ⟨⟨a₁, a₂⟩, rfl⟩ _ ⟨⟨c₁, c₂⟩, rfl⟩
    refine ⟨⟨⟨a₁ ⊓ c₁, A.inf_mem a₁.property c₁.property⟩,
      ⟨a₂ ⊓ c₂, A.inf_mem a₂.property c₂.property⟩⟩, ?_⟩
    apply eq_of_inf_eq_inf_compl (a := b)
    · calc
        b ⊓ ((b ⊓ ((a₁ : B) ⊓ c₁)) ⊔ (bᶜ ⊓ ((a₂ : B) ⊓ c₂))) =
            b ⊓ ((a₁ : B) ⊓ c₁) := inf_conditional ..
        _ = (b ⊓ ((b ⊓ (a₁ : B)) ⊔ (bᶜ ⊓ a₂))) ⊓
            ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂)) := by
              rw [inf_conditional]
              calc
                b ⊓ ((a₁ : B) ⊓ c₁) = (a₁ : B) ⊓ (b ⊓ c₁) := by ac_rfl
                _ = (a₁ : B) ⊓ (b ⊓ ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂))) := by
                  rw [inf_conditional]
                _ = (b ⊓ (a₁ : B)) ⊓ ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂)) := by ac_rfl
        _ = b ⊓ (((b ⊓ (a₁ : B)) ⊔ (bᶜ ⊓ a₂)) ⊓
            ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂))) := inf_assoc ..
    · calc
        bᶜ ⊓ ((b ⊓ ((a₁ : B) ⊓ c₁)) ⊔ (bᶜ ⊓ ((a₂ : B) ⊓ c₂))) =
            bᶜ ⊓ ((a₂ : B) ⊓ c₂) := compl_inf_conditional ..
        _ = (bᶜ ⊓ ((b ⊓ (a₁ : B)) ⊔ (bᶜ ⊓ a₂))) ⊓
            ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂)) := by
              rw [compl_inf_conditional]
              calc
                bᶜ ⊓ ((a₂ : B) ⊓ c₂) = (a₂ : B) ⊓ (bᶜ ⊓ c₂) := by ac_rfl
                _ = (a₂ : B) ⊓ (bᶜ ⊓ ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂))) := by
                  rw [compl_inf_conditional]
                _ = (bᶜ ⊓ (a₂ : B)) ⊓ ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂)) := by
                  ac_rfl
        _ = bᶜ ⊓ (((b ⊓ (a₁ : B)) ⊔ (bᶜ ⊓ a₂)) ⊓
            ((b ⊓ (c₁ : B)) ⊔ (bᶜ ⊓ c₂))) := inf_assoc ..

/-- A Boolean subalgebra is contained in the result of adjoining to it any element. -/
theorem le_adjoin (A : BooleanSubalgebra B) (a : B) : A ≤ A.adjoin a := by
  intro b hb
  refine ⟨⟨⟨b, hb⟩, ⟨b, hb⟩⟩, ?_⟩
  calc
    (a ⊓ b) ⊔ (aᶜ ⊓ b) = (a ⊔ aᶜ) ⊓ b := (inf_sup_right ..).symm
    _ = b := by simp

/-- The adjoined element belongs to the enlarged Boolean subalgebra. -/
theorem mem_adjoin (A : BooleanSubalgebra B) (a : B) : a ∈ A.adjoin a := by
  refine ⟨⟨⟨⊤, A.top_mem⟩, ⟨⊥, A.bot_mem⟩⟩, ?_⟩
  simp [adjoinValue]

/-- The Boolean subalgebra obtaining by adjoining one element to a finite Boolean
subalgebra is again finite. -/
theorem finite_adjoin {A : BooleanSubalgebra B} (hA : (A : Set B).Finite)
    (a : B) : (A.adjoin a : Set B).Finite := by
  let := hA.fintype
  exact Set.finite_range _

/-- The Boolean subalgebra obtained by adjoining one element to a `σ`-complete Boolean
subalgebra is again `σ`-complete. -/
theorem IsSigmaComplete.adjoin {C : Type v} [SigmaCompleteBooleanAlgebra C]
    {A : BooleanSubalgebra C} (hA : A.IsSigmaComplete) (b : C) :
    (A.adjoin b).IsSigmaComplete := by
  rw [isSigmaComplete_iff_iSup_mem]
  intro x hx
  have hp (n : ℕ) : ∃ p : A × A,
      x n = (b ⊓ (p.1 : C)) ⊔ (bᶜ ⊓ (p.2 : C)) := by
    rcases hx n with ⟨p, hp⟩
    exact ⟨p, hp.symm⟩
  choose p hp using hp
  let l : C := ⨆ n, ((p n).1 : C)
  let r : C := ⨆ n, ((p n).2 : C)
  have hl : l ∈ A := by
    apply hA.iSup_mem
    exact fun n ↦ (p n).1.property
  have hr : r ∈ A := hA.iSup_mem _ fun n ↦ (p n).2.property
  refine ⟨⟨⟨l, hl⟩, ⟨r, hr⟩⟩, ?_⟩
  change (b ⊓ l) ⊔ (bᶜ ⊓ r) = ⨆ n, x n
  calc
    (b ⊓ l) ⊔ (bᶜ ⊓ r) =
        (⨆ n, b ⊓ ((p n).1 : C)) ⊔ (⨆ n, bᶜ ⊓ ((p n).2 : C)) := by
      simp only [l, r, SigmaCompleteBooleanAlgebra.inf_iSup_nat,
        SigmaCompleteBooleanAlgebra.inf_iSup_nat]
    _ = ⨆ n, x n := by
      apply le_antisymm
      · apply sup_le
        · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
          intro n
          exact (le_sup_left.trans_eq (hp n).symm).trans
            (SigmaCompleteBooleanAlgebra.le_iSup_nat x n)
        · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
          intro n
          exact (le_sup_right.trans_eq (hp n).symm).trans
            (SigmaCompleteBooleanAlgebra.le_iSup_nat x n)
      · apply SigmaCompleteBooleanAlgebra.iSup_nat_le
        intro n
        rw [hp n]
        apply sup_le
        · exact le_sup_of_le_left <|
            SigmaCompleteBooleanAlgebra.le_iSup_nat
              (fun n ↦ b ⊓ ((p n).1 : C)) n
        · exact le_sup_of_le_right <|
            SigmaCompleteBooleanAlgebra.le_iSup_nat
              (fun n ↦ bᶜ ⊓ ((p n).2 : C)) n

/-- The Boolean subalgebra generated by a finite set is again finite. -/
theorem finite_closure {s : Set B} (hs : s.Finite) :
    (BooleanSubalgebra.closure s : Set B).Finite := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      apply (show ((⊥ : BooleanSubalgebra B) : Set B).Finite by simp).subset
      exact BooleanSubalgebra.closure_le.2
        (Set.empty_subset ((⊥ : BooleanSubalgebra B) : Set B))
  | @insert a s _ _ ih =>
      apply (finite_adjoin ih a).subset
      apply BooleanSubalgebra.closure_le.2
      rintro x (rfl | hx)
      · exact mem_adjoin _ _
      · exact le_adjoin _ _ (BooleanSubalgebra.subset_closure hx)

/-- Every element of the Boolean subalgebra generated by `s` already belongs
to the Boolean subalgebra generated by some finite subset of `s`. -/
private theorem exists_finset_closure_of_mem_closure
    {s : Set B} {b : B} (hb : b ∈ closure s) :
    ∃ t : Finset s, b ∈ closure (Subtype.val '' (t : Set s)) := by
  classical
  induction hb using closure_bot_sup_induction with
  | mem b hb =>
      refine ⟨{⟨b, hb⟩}, subset_closure ?_⟩
      simp
  | bot =>
      exact ⟨∅, BooleanSubalgebra.bot_mem⟩
  | sup x hx y hy hx' hy' =>
      obtain ⟨t, ht⟩ := hx'
      obtain ⟨r, hr⟩ := hy'
      refine ⟨t ∪ r, BooleanSubalgebra.sup_mem ?_ ?_⟩
      · apply closure_mono _ ht
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a, Finset.mem_union_left r ha, rfl⟩
      · apply closure_mono _ hr
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a, Finset.mem_union_right t ha, rfl⟩
  | compl x hx hx' =>
      obtain ⟨t, ht⟩ := hx'
      exact ⟨t, BooleanSubalgebra.compl_mem ht⟩

/-- The Boolean subalgebra generated by `s` has cardinality at most
`max #s ℵ₀`. -/
theorem cardinalMk_closure_le_max (s : Set B) :
    Cardinal.mk (closure s) ≤ max (Cardinal.mk s) Cardinal.aleph0 := by
  classical
  let codes := Σ t : Finset s, closure (Subtype.val '' (t : Set s))
  let evaluate : codes → closure s := fun x ↦
    ⟨x.2, closure_mono (by
      rintro _ ⟨a, -, rfl⟩
      exact a.property) x.2.property⟩
  have hevaluate : Function.Surjective evaluate := by
    intro b
    obtain ⟨t, ht⟩ := exists_finset_closure_of_mem_closure b.property
    exact ⟨⟨t, ⟨b, ht⟩⟩, Subtype.ext rfl⟩
  have hfinset : Cardinal.mk (Finset s) ≤
      max (Cardinal.mk s) Cardinal.aleph0 := by
    calc
      Cardinal.mk (Finset s) ≤ Cardinal.mk (List s) :=
        Cardinal.mk_le_of_surjective List.toFinset_surjective
      _ ≤ max Cardinal.aleph0 (Cardinal.mk s) := Cardinal.mk_list_le_max s
      _ = max (Cardinal.mk s) Cardinal.aleph0 := max_comm _ _
  calc
    Cardinal.mk (closure s) ≤ Cardinal.mk codes :=
      Cardinal.mk_le_of_surjective hevaluate
    _ = Cardinal.sum (fun t : Finset s ↦
        Cardinal.mk (closure (Subtype.val '' (t : Set s)))) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : Finset s ↦ Cardinal.aleph0) := by
      apply Cardinal.sum_le_sum
      intro t
      let := (finite_closure (t.finite_toSet.image Subtype.val)).fintype
      exact (Cardinal.lt_aleph0_of_finite _).le
    _ = Cardinal.mk (Finset s) * Cardinal.aleph0 := Cardinal.sum_const' _ _
    _ ≤ max (Cardinal.mk s) Cardinal.aleph0 := by
      exact Cardinal.mul_le_of_le (le_max_right _ _) hfinset (le_max_right _ _)

/-- For fixed `A` and `b`, every `x ∈ A.adjoin b` has a chosen representation
`p = (a₁, a₂) ∈ A × A` such that `x = (b ⊓ a₁) ⊔ (bᶜ ⊓ a₂)`. -/
noncomputable def adjoinRepresentation (A : BooleanSubalgebra B) (b : B)
    (x : A.adjoin b) : A × A :=
  Classical.choose x.property

/-- The pair `adjoinRepresentation A b x` represents `x` through
`adjoinValue A b`. -/
theorem adjoinRepresentation_spec (A : BooleanSubalgebra B) (b : B)
    (x : A.adjoin b) :
    adjoinValue A b (adjoinRepresentation A b x) = (x : B) :=
  Classical.choose_spec x.property

/-- Given Boolean subalgebras `A ⊆ B` and `C ⊆ D`, a map `f : A → C`, and elements
`b ∈ B` and `d ∈ D`, `adjoinMap f b d` is the map from `A.adjoin b` to `C.adjoin d`
that sends `x` to `(d ⊓ f(a₁)) ⊔ (dᶜ ⊓ f(a₂))`, where `(a₁, a₂)` is the
particular representation of `x` selected by `adjoinRepresentation A b`. -/
private noncomputable def adjoinMap {D : Type v} [BooleanAlgebra D]
    {A : BooleanSubalgebra B} {C : BooleanSubalgebra D}
    (f : A → C) (b : B) (d : D) : A.adjoin b → C.adjoin d := fun x ↦
  ⟨adjoinValue C d (Prod.map f f (adjoinRepresentation A b x)),
    ⟨Prod.map f f (adjoinRepresentation A b x), rfl⟩⟩

private lemma adjoinMap_eq_of_eq {D : Type v} [BooleanAlgebra D]
    {A : BooleanSubalgebra B} {C : BooleanSubalgebra D}
    (e : A ≃o C) (b : B) (d : D)
    (horder : ∀ p q : A × A,
      adjoinValue A b p ≤ adjoinValue A b q ↔
        adjoinValue C d (Prod.map e e p) ≤ adjoinValue C d (Prod.map e e q))
    (x : A.adjoin b) (p : A × A) (hp : adjoinValue A b p = (x : B)) :
    (adjoinMap e b d x : D) = adjoinValue C d (Prod.map e e p) := by
  apply le_antisymm
  · apply (horder _ p).mp
    rw [adjoinRepresentation_spec, hp]
  · apply (horder p _).mp
    rw [adjoinRepresentation_spec, hp]

/-- Given Boolean subalgebras `A ⊆ B` and `C ⊆ D`, an order isomorphism `e : A ≃o C`, and
elements `b ∈ B` and `d ∈ D`, `adjoinOrderIso e b d horder` is an order isomorphism from
`A.adjoin b` to `C.adjoin d` that extends `e` and maps `b` to `d`. This can be done if, for all
`(a₁, a₂), (c₁, c₂) ∈ A × A`,
`(b ⊓ a₁) ⊔ (bᶜ ⊓ a₂) ≤ (b ⊓ c₁) ⊔ (bᶜ ⊓ c₂)` if and only if
`(d ⊓ e(a₁)) ⊔ (dᶜ ⊓ e(a₂)) ≤ (d ⊓ e(c₁)) ⊔ (dᶜ ⊓ e(c₂))`. -/
noncomputable def adjoinOrderIso {D : Type v} [BooleanAlgebra D]
    {A : BooleanSubalgebra B} {C : BooleanSubalgebra D}
    (e : A ≃o C) (b : B) (d : D)
    (horder : ∀ p q : A × A,
      adjoinValue A b p ≤ adjoinValue A b q ↔
        adjoinValue C d (Prod.map e e p) ≤ adjoinValue C d (Prod.map e e q)) :
    A.adjoin b ≃o C.adjoin d := by
  let f : A.adjoin b ↪o C.adjoin d :=
    OrderEmbedding.ofMapLEIff (adjoinMap e b d) fun x y ↦ by
      change adjoinValue C d (Prod.map e e (adjoinRepresentation A b x)) ≤
          adjoinValue C d (Prod.map e e (adjoinRepresentation A b y)) ↔ x ≤ y
      rw [← horder, adjoinRepresentation_spec, adjoinRepresentation_spec]
      rfl
  apply OrderIso.ofSurjective f
  intro y
  let q := adjoinRepresentation C d y
  let p : A × A := (e.symm q.1, e.symm q.2)
  let x : A.adjoin b := ⟨adjoinValue A b p, ⟨p, rfl⟩⟩
  refine ⟨x, Subtype.ext ?_⟩
  change (adjoinMap e b d x : D) = (y : D)
  calc
    (adjoinMap e b d x : D) = adjoinValue C d (Prod.map e e p) :=
      adjoinMap_eq_of_eq e b d horder x p rfl
    _ = adjoinValue C d q := by
      simp only [p, Prod.map, OrderIso.apply_symm_apply]
    _ = (y : D) := adjoinRepresentation_spec C d y

/-- Under the hypotheses defining `adjoinOrderIso e b d horder`, if `p = (a₁, a₂)` and
`adjoinValue A b p = x`, then the extended order isomorphism sends `x` to
`adjoinValue C d (e(a₁), e(a₂))`. -/
theorem adjoinOrderIso_apply_eq_of_eq {D : Type v} [BooleanAlgebra D]
    {A : BooleanSubalgebra B} {C : BooleanSubalgebra D}
    (e : A ≃o C) (b : B) (d : D)
    (horder : ∀ p q : A × A,
      adjoinValue A b p ≤ adjoinValue A b q ↔
        adjoinValue C d (Prod.map e e p) ≤ adjoinValue C d (Prod.map e e q))
    (x : A.adjoin b) (p : A × A) (hp : adjoinValue A b p = (x : B)) :
    ((adjoinOrderIso e b d horder x : C.adjoin d) : D) =
      adjoinValue C d (Prod.map e e p) := by
  exact adjoinMap_eq_of_eq e b d horder x p hp

end BooleanSubalgebra
