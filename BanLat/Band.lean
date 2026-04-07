import BanLat.Ideal
import BanLat.OrderComplete
import BanLat.Operators.Hom

/-!
# Bands and projection bands

A **band** in a vector lattice is an order ideal that is **order closed**: if
an upward-directed set of positive elements lies in the band and its supremum
exists, then the supremum belongs to the band. The **disjoint complement**
`Aᵈ` of a set `A` consists of all elements disjoint from every member of `A`;
it is always a band. In the Archimedean case, a subset is a band iff it equals
its double disjoint complement.

A band `B` is a **projection band** when every element of `X` decomposes
uniquely as a sum of an element of `B` and an element of `Bᵈ`. This file
defines bands, disjoint complements, and projection bands, and states the main
structural results.
-/

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### Disjointness -/

/-- Two elements of a lattice-ordered group are **disjoint** when
`|x| ⊓ |y| = 0`. -/
def IsVLDisjoint (x y : X) : Prop := |x| ⊓ |y| = 0

omit [IsOrderedAddMonoid X] [VectorLattice X] in
@[simp]
theorem isVLDisjoint_comm {x y : X} :
    IsVLDisjoint x y ↔ IsVLDisjoint y x := by
  unfold IsVLDisjoint; rw [inf_comm]

omit [VectorLattice X] in
/-- Zero is disjoint from every element. -/
theorem isVLDisjoint_zero_left (x : X) : IsVLDisjoint 0 x := by
  unfold IsVLDisjoint; simp [abs_zero]

omit [VectorLattice X] in
/-- Disjoint positive elements satisfy `x ⊓ y = 0`. -/
theorem inf_eq_zero_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsVLDisjoint x y) : x ⊓ y = 0 := by
  unfold IsVLDisjoint at h; rwa [abs_of_nonneg hx, abs_of_nonneg hy] at h

omit [VectorLattice X] in
/-- If `x ⊓ y = 0` then `x` and `y` are disjoint. -/
theorem isVLDisjoint_of_inf_eq_zero {x y : X}
    (h : x ⊓ y = 0) : IsVLDisjoint x y := by
  have hx : 0 ≤ x := h ▸ inf_le_left
  have hy : 0 ≤ y := h ▸ inf_le_right
  unfold IsVLDisjoint; rwa [abs_of_nonneg hx, abs_of_nonneg hy]

omit [VectorLattice X] in
/-- Disjoint decomposition is unique: if `x = u₁ - v₁ = u₂ - v₂` with
`u₁ ⊥ v₁` and `u₂ ⊥ v₂` (all non-negative), then `u₁ = u₂` and
`v₁ = v₂`. -/
theorem isVLDisjoint_decomposition_unique {u₁ v₁ u₂ v₂ : X}
    (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hd₁ : IsVLDisjoint u₁ v₁) (hd₂ : IsVLDisjoint u₂ v₂)
    (h : u₁ - v₁ = u₂ - v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have h1 := inf_eq_zero_of_isVLDisjoint hu₁ hv₁ hd₁
  have h2 := inf_eq_zero_of_isVLDisjoint hu₂ hv₂ hd₂
  have eq1 : u₁ = (u₁ - v₁)⁺ :=
    uniqueness_posPart (u₁ - v₁) rfl h1
  have eq2 : u₂ = (u₂ - v₂)⁺ :=
    uniqueness_posPart (u₂ - v₂) rfl h2
  have hu : u₁ = u₂ := by rw [eq1, h, ← eq2]
  refine ⟨hu, ?_⟩
  have := h; rw [hu, sub_eq_add_neg, sub_eq_add_neg] at this
  exact neg_injective (add_left_cancel this)

omit [IsOrderedAddMonoid X] [VectorLattice X] in
private theorem inf_eq_zero_of_le_disjoint {a b c d : X}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d)
    (hcd : c ⊓ d = 0) : a ⊓ b = 0 :=
  le_antisymm (hcd ▸ inf_le_inf hac hbd) (le_inf ha hb)

omit [VectorLattice X] in
/-- If `x ⊥ y` then `|x + y| = |x| + |y|` (Birkhoff identity). -/
theorem abs_add_of_isVLDisjoint {x y : X} (h : IsVLDisjoint x y) :
    |x + y| = |x| + |y| := by
  -- Extract pairwise disjointness of parts
  have hd : |x| ⊓ |y| = 0 := h
  have hxp_yp : x⁺ ⊓ y⁺ = 0 := inf_eq_zero_of_le_disjoint
    (posPart_nonneg x) (posPart_nonneg y)
    (sup_le (le_abs_self x) (abs_nonneg x))
    (sup_le (le_abs_self y) (abs_nonneg y)) hd
  have hxp_yn : x⁺ ⊓ y⁻ = 0 := inf_eq_zero_of_le_disjoint
    (posPart_nonneg x) (negPart_nonneg y)
    (sup_le (le_abs_self x) (abs_nonneg x))
    (sup_le (neg_le_abs y) (abs_nonneg y)) hd
  have hxn_yp : x⁻ ⊓ y⁺ = 0 := inf_eq_zero_of_le_disjoint
    (negPart_nonneg x) (posPart_nonneg y)
    (sup_le (neg_le_abs x) (abs_nonneg x))
    (sup_le (le_abs_self y) (abs_nonneg y)) hd
  have hxn_yn : x⁻ ⊓ y⁻ = 0 := inf_eq_zero_of_le_disjoint
    (negPart_nonneg x) (negPart_nonneg y)
    (sup_le (neg_le_abs x) (abs_nonneg x))
    (sup_le (neg_le_abs y) (abs_nonneg y)) hd
  -- Show (x⁺ + y⁺) ⊓ (x⁻ + y⁻) = 0
  have hxn_xp : x⁻ ⊓ x⁺ = 0 := by
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero x
  have hyn_yp : y⁻ ⊓ y⁺ = 0 := by
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero y
  have term1 : (x⁺ + y⁺) ⊓ x⁻ = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (negPart_nonneg x))
    rw [inf_comm]
    calc x⁻ ⊓ (x⁺ + y⁺)
        ≤ x⁻ ⊓ x⁺ + x⁻ ⊓ y⁺ := inf_le_inf_add_inf_of_nonneg x⁻ x⁺ y⁺
            (negPart_nonneg x) (posPart_nonneg x) (posPart_nonneg y)
      _ = 0 := by rw [hxn_xp, hxn_yp, add_zero]
  have term2 : (x⁺ + y⁺) ⊓ y⁻ = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (negPart_nonneg y))
    rw [inf_comm]
    calc y⁻ ⊓ (x⁺ + y⁺)
        ≤ y⁻ ⊓ x⁺ + y⁻ ⊓ y⁺ := inf_le_inf_add_inf_of_nonneg y⁻ x⁺ y⁺
            (negPart_nonneg y) (posPart_nonneg x) (posPart_nonneg y)
      _ = 0 := by rw [inf_comm y⁻ x⁺, hxp_yn, hyn_yp, add_zero]
  have sum_disj : (x⁺ + y⁺) ⊓ (x⁻ + y⁻) = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (add_nonneg (negPart_nonneg x) (negPart_nonneg y)))
    calc (x⁺ + y⁺) ⊓ (x⁻ + y⁻)
        ≤ (x⁺ + y⁺) ⊓ x⁻ + (x⁺ + y⁺) ⊓ y⁻ :=
          inf_le_inf_add_inf_of_nonneg (x⁺ + y⁺) x⁻ y⁻
            (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
            (negPart_nonneg x) (negPart_nonneg y)
      _ = 0 := by rw [term1, term2, add_zero]
  -- By uniqueness_posPart, (x + y)⁺ = x⁺ + y⁺
  have hdec : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
    calc x + y = (x⁺ - x⁻) + (y⁺ - y⁻) := by
          rw [posPart_sub_negPart, posPart_sub_negPart]
      _ = (x⁺ + y⁺) - (x⁻ + y⁻) := by abel
  have hup := uniqueness_posPart (x + y) hdec sum_disj
  have hun : (x + y)⁻ = x⁻ + y⁻ := by
    have h3 := posPart_sub_negPart (x + y)
    rw [← hup] at h3
    -- h3 : (x⁺ + y⁺) - (x + y)⁻ = x + y
    have h4 : x⁺ + y⁺ - (x + y)⁻ = x⁺ + y⁺ - (x⁻ + y⁻) := by
      rw [h3, hdec]
    exact sub_right_injective h4
  calc |x + y| = (x + y)⁺ + (x + y)⁻ := (posPart_add_negPart (x + y)).symm
    _ = (x⁺ + y⁺) + (x⁻ + y⁻) := by rw [← hup, hun]
    _ = (x⁺ + x⁻) + (y⁺ + y⁻) := by abel
    _ = |x| + |y| := by rw [posPart_add_negPart, posPart_add_negPart]

omit [VectorLattice X] in
/-- If `x ⊥ y` then `|x ⊔ y| = |x| ⊔ |y|`. -/
theorem abs_sup_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_ : IsVLDisjoint x y) : |x ⊔ y| = |x| ⊔ |y| := by
  rw [abs_of_nonneg (le_sup_of_le_left hx), abs_of_nonneg hx, abs_of_nonneg hy]

/-! ### Disjoint complement -/

/-- The **disjoint complement** of a set `A ⊆ X` is the set of all elements
disjoint from every member of `A`. -/
def disjointComplement (A : Set X) : Set X :=
  {x : X | ∀ a ∈ A, IsVLDisjoint x a}

postfix:max "ᵈ" => disjointComplement

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Anti-monotonicity: if `A ⊆ B` then `Bᵈ ⊆ Aᵈ`. -/
theorem disjointComplement_anti {A B : Set X} (h : A ⊆ B) :
    Bᵈ ⊆ Aᵈ := by
  intro x hx a ha; exact hx a (h ha)

omit [VectorLattice X] in
/-- The intersection of a set with its disjoint complement is `{0}`. -/
theorem disjointComplement_inter_eq_zero (A : Set X) :
    A ∩ Aᵈ ⊆ {0} := by
  intro x ⟨hxA, hxAd⟩
  simp only [Set.mem_singleton_iff]
  have h := hxAd x hxA
  unfold IsVLDisjoint at h
  rw [inf_idem] at h
  exact (abs_eq_zero_iff_zero x).mp h

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Every set is contained in its double disjoint complement. -/
theorem subset_disjointComplement_disjointComplement (A : Set X) :
    A ⊆ (Aᵈ)ᵈ := by
  intro a ha x hx; exact isVLDisjoint_comm.mpr (hx a ha)

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- The triple disjoint complement equals the single disjoint complement. -/
theorem disjointComplement_disjointComplement_disjointComplement
    (A : Set X) : ((Aᵈ)ᵈ)ᵈ = Aᵈ := by
  apply Set.Subset.antisymm
  · exact disjointComplement_anti (subset_disjointComplement_disjointComplement A)
  · exact subset_disjointComplement_disjointComplement Aᵈ

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- The disjoint complement of a union is the intersection of the disjoint
complements. -/
theorem disjointComplement_union (A B : Set X) :
    (A ∪ B)ᵈ = Aᵈ ∩ Bᵈ := by
  ext x
  simp only [disjointComplement, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨ha, hb⟩ c (hc | hc)
    · exact ha c hc
    · exact hb c hc

/-! ### Bands -/

/-- A **band** in a vector lattice is an order ideal that is **order closed**:
whenever a directed set of positive elements in the band has a supremum in `X`,
that supremum also lies in the band. -/
structure Band (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends OrderIdeal X where
  directed_sSup_mem' :
    ∀ (S : Set X), S ⊆ carrier → (∀ x ∈ S, 0 ≤ x)
      → DirectedOn (· ≤ ·) S → S.Nonempty
      → ∀ x, IsLUB S x → x ∈ carrier

namespace Band

instance : SetLike (Band X) X where
  coe B := B.carrier
  coe_injective' p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

variable (B : Band X)

/-- Every band is an order ideal. -/
def toOrderIdeal' : OrderIdeal X :=
  B.toOrderIdeal

/-- An order ideal that is closed under directed suprema is a band. -/
theorem directed_sSup_mem {S : Set X} (hS : S ⊆ (B : Set X))
    (hpos : ∀ x ∈ S, 0 ≤ x) (hdir : DirectedOn (· ≤ ·) S)
    (hne : S.Nonempty) {x : X} (hx : IsLUB S x) : x ∈ B :=
  B.directed_sSup_mem' S hS hpos hdir hne x hx

/-- A band is closed under `⊔`. -/
theorem sup_mem {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊔ y ∈ B :=
  B.toOrderIdeal.sup_mem hx hy

/-- A band is closed under `⊓`. -/
theorem inf_mem {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊓ y ∈ B :=
  B.toOrderIdeal.inf_mem hx hy

/-- A band is solid. -/
theorem solid {x y : X} (hx : x ∈ B) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    y ∈ B :=
  B.toOrderIdeal.solid hx hy0 hyx

/-- A band is closed under absolute value. -/
theorem abs_mem {x : X} (hx : x ∈ B) : |x| ∈ B :=
  B.toOrderIdeal.abs_mem hx

/-- Membership in a band is equivalent to membership of the absolute value. -/
theorem mem_of_abs_mem {x : X} (h : |x| ∈ B) : x ∈ B :=
  B.toOrderIdeal.mem_of_abs_mem h

/-- Solidity in terms of absolute value. -/
theorem mem_of_abs_le_abs {x y : X} (hx : x ∈ B) (h : |y| ≤ |x|) :
    y ∈ B :=
  B.toOrderIdeal.mem_of_abs_le_abs hx h

/-! ### Vector lattice structure on the underlying subtype

A band `B` is a submodule of `X`, and its underlying subtype inherits a
pointwise vector lattice structure. -/

/-- The lattice structure on the underlying subtype of a band. -/
noncomputable instance instLatticeSubtype : Lattice ↥B.toSubmodule :=
  Subtype.lattice (P := fun x => x ∈ B.toSubmodule)
    (fun _ _ hx hy => B.sup_mem hx hy) (fun _ _ hx hy => B.inf_mem hx hy)

/-- The subtype of a band is an ordered additive monoid. -/
instance instIsOrderedAddMonoidSubtype : IsOrderedAddMonoid ↥B.toSubmodule where
  add_le_add_left := by intro a b (h : a.1 ≤ b.1) c; exact add_le_add_left h c.1
  add_le_add_right := by intro a b (h : a.1 ≤ b.1) c; exact add_le_add_right h c.1

/-- Scalar multiplication by non-negative reals is monotone on the subtype of
a band. -/
instance instPosSMulMonoSubtype : PosSMulMono ℝ ↥B.toSubmodule where
  smul_le_smul_of_nonneg_left := by
    intro a ha b₁ b₂ h
    change (a • b₁).1 ≤ (a • b₂).1
    exact smul_le_smul_of_nonneg_left h ha

/-- The subtype of a band is itself a vector lattice. -/
instance instVectorLatticeSubtype : VectorLattice ↥B.toSubmodule := ⟨⟩

/-- A finite nonempty subset of a band has its supremum (computed in the
ambient space) inside the band. -/
private lemma finset_sup'_mem {F : Finset X} (hne : F.Nonempty)
    (hsub : (↑F : Set X) ⊆ (↑B : Set X)) : F.sup' hne id ∈ B := by
  classical
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a =>
    rw [Finset.sup'_singleton]
    exact hsub (by simp)
  | cons a s ha hsne ih =>
    rw [Finset.sup'_cons hsne]
    refine B.sup_mem (hsub (by simp)) (ih ?_)
    intro x hx
    exact hsub (by simp [Finset.mem_coe.mp hx])

/-- A band in an order complete vector lattice is itself order complete. -/
instance instIsOrderCompleteSubtype [IsOrderComplete X] :
    IsOrderComplete ↥B.toSubmodule := by
  classical
  rw [isOrderComplete_iff_pos_bddAbove_isLUB]
  intro S hSpos hbdd hne
  obtain ⟨u, hu⟩ := hbdd
  obtain ⟨s₀, hs₀⟩ := hne
  -- Lift `S` to a subset of `X`.
  let SX : Set X := Subtype.val '' S
  have hSX_sub : SX ⊆ (↑B : Set X) := by rintro _ ⟨a, _, rfl⟩; exact a.2
  have hSX_le : ∀ y ∈ SX, y ≤ u.val := by
    rintro _ ⟨a, ha, rfl⟩; exact (hu ha : a.val ≤ u.val)
  have hSX_nn : ∀ y ∈ SX, (0 : X) ≤ y := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hSpos ha : (0 : ↥B.toSubmodule).val ≤ a.val)
  -- Build the directed closure under finite suprema in `X`.
  let D : Set X := {y : X | ∃ (F : Finset X) (hne : F.Nonempty),
      (↑F : Set X) ⊆ SX ∧ y = F.sup' hne id}
  have hD_sub_B : D ⊆ (↑B : Set X) := by
    rintro _ ⟨F, hne, hF, rfl⟩
    exact finset_sup'_mem _ hne (hF.trans hSX_sub)
  have hD_ne : D.Nonempty :=
    ⟨s₀.val, {s₀.val}, Finset.singleton_nonempty _,
      by intro x hx; rw [Finset.coe_singleton] at hx;
         exact hx ▸ ⟨s₀, hs₀, rfl⟩,
      (Finset.sup'_singleton (id : X → X)).symm⟩
  have hD_bdd : BddAbove D := by
    refine ⟨u.val, ?_⟩
    rintro _ ⟨F, hne, hF, rfl⟩
    exact Finset.sup'_le _ _
      fun x hx => hSX_le x (hF (Finset.mem_coe.mpr hx))
  have hD_dir : DirectedOn (· ≤ ·) D := by
    rintro _ ⟨F₁, hne₁, hF₁, rfl⟩ _ ⟨F₂, hne₂, hF₂, rfl⟩
    refine ⟨(F₁ ∪ F₂).sup' (hne₁.mono Finset.subset_union_left) id,
      ⟨F₁ ∪ F₂, hne₁.mono Finset.subset_union_left,
        ?_, rfl⟩, ?_, ?_⟩
    · intro x hx; rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
      · exact hF₁ (Finset.mem_coe.mpr h)
      · exact hF₂ (Finset.mem_coe.mpr h)
    · exact Finset.sup'_le _ _ fun x hx =>
        Finset.le_sup' (f := id) (Finset.mem_union_left _ hx)
    · exact Finset.sup'_le _ _ fun x hx =>
        Finset.le_sup' (f := id) (Finset.mem_union_right _ hx)
  have hD_pos : ∀ y ∈ D, (0 : X) ≤ y := by
    rintro _ ⟨F, hne, hF, rfl⟩
    obtain ⟨a, ha⟩ := hne
    refine le_trans (hSX_nn a (hF (Finset.mem_coe.mpr ha))) ?_
    exact Finset.le_sup' (f := id) ha
  -- LUB of `D` in `X`.
  obtain ⟨t, ht⟩ := IsOrderComplete.isLUB_of_bddAbove hD_bdd hD_ne
  have htB : t ∈ B := B.directed_sSup_mem hD_sub_B hD_pos hD_dir hD_ne ht
  refine ⟨⟨t, htB⟩, ?_, ?_⟩
  · -- upper bound
    intro a ha
    change a.val ≤ t
    have : a.val ∈ D := ⟨{a.val}, Finset.singleton_nonempty _,
      by intro x hx; rw [Finset.coe_singleton] at hx; exact hx ▸ ⟨a, ha, rfl⟩,
      (Finset.sup'_singleton (id : X → X)).symm⟩
    exact ht.1 this
  · -- least upper bound
    intro v hv
    change t ≤ v.val
    refine ht.2 ?_
    rintro _ ⟨F, hne, hF, rfl⟩
    refine Finset.sup'_le _ _ fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := hF (Finset.mem_coe.mpr hx)
    exact (hv ha : a.val ≤ v.val)

/-! ### The disjoint complement is a band -/

/-- The disjoint complement of any set is an order ideal. -/
def disjointComplementOrderIdeal (A : Set X) : OrderIdeal X where
  toSubmodule :=
    { carrier := Aᵈ
      add_mem' := fun {x y} hx hy a ha => by
        unfold IsVLDisjoint
        apply le_antisymm _ (le_inf (abs_nonneg _) (abs_nonneg _))
        calc |x + y| ⊓ |a|
            ≤ (|x| + |y|) ⊓ |a| := inf_le_inf_right _ (abs_add_le x y)
          _ = |a| ⊓ (|x| + |y|) := inf_comm _ _
          _ ≤ |a| ⊓ |x| + |a| ⊓ |y| := inf_le_inf_add_inf_of_nonneg
              |a| |x| |y| (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
          _ = 0 := by
              rw [inf_comm (a := |a|) (b := |x|), hx a ha,
                  inf_comm (a := |a|) (b := |y|), hy a ha, add_zero]
      zero_mem' := fun a _ => by unfold IsVLDisjoint; simp [abs_zero]
      smul_mem' := fun r x hx a ha => by
        unfold IsVLDisjoint
        rw [abs_smul' x r]
        exact disjoint_smul |x| |a| |r| (abs_nonneg r) (hx a ha) }
  sup_mem' := fun {x y} hx hy a ha => by
    unfold IsVLDisjoint
    apply le_antisymm _ (le_inf (abs_nonneg _) (abs_nonneg _))
    calc |x ⊔ y| ⊓ |a|
        ≤ (|x| + |y|) ⊓ |a| := by
          apply inf_le_inf_right
          exact sup_le
            (sup_le (le_trans (le_abs_self x) (le_add_of_nonneg_right (abs_nonneg y)))
              (le_trans (le_abs_self y) (le_add_of_nonneg_left (abs_nonneg x))))
            (le_trans (by rw [neg_sup]; exact inf_le_left)
              (le_trans (neg_le_abs x) (le_add_of_nonneg_right (abs_nonneg y))))
      _ = |a| ⊓ (|x| + |y|) := inf_comm _ _
      _ ≤ |a| ⊓ |x| + |a| ⊓ |y| := inf_le_inf_add_inf_of_nonneg
          |a| |x| |y| (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      _ = 0 := by
          rw [inf_comm (a := |a|) (b := |x|), hx a ha,
              inf_comm (a := |a|) (b := |y|), hy a ha, add_zero]
  solid' := fun {x y} hx hy0 hyx a ha => by
    unfold IsVLDisjoint
    apply le_antisymm _ (le_inf (abs_nonneg _) (abs_nonneg _))
    calc |y| ⊓ |a| ≤ |x| ⊓ |a| := inf_le_inf_right _
          (by rw [abs_of_nonneg hy0, abs_of_nonneg (le_trans hy0 hyx)]; exact hyx)
      _ = 0 := hx a ha

/-- The disjoint complement of any set is a band. -/
def disjointComplementBand (A : Set X) : Band X where
  toOrderIdeal := disjointComplementOrderIdeal A
  directed_sSup_mem' := fun S hS hpos _ hne x hx a ha => by
    obtain ⟨s₀, hs₀⟩ := hne
    have hx_nn : 0 ≤ x := le_trans (hpos s₀ hs₀) (hx.1 hs₀)
    have hsd : ∀ s ∈ S, s ⊓ |a| = 0 := fun s hs => by
      have := hS hs a ha; unfold IsVLDisjoint at this
      rwa [abs_of_nonneg (hpos s hs)] at this
    have hub : ∀ s ∈ S, s ≤ (x - |a|)⁺ := fun s hs => by
      calc s = (s - |a|)⁺ := by
              rw [← sub_inf_eq_posPart s |a|, hsd s hs, sub_zero]
        _ ≤ (x - |a|)⁺ := sup_le_sup_right (sub_le_sub_right (hx.1 hs) _) 0
    have hle : x ≤ (x - |a|)⁺ := hx.2 hub
    have hinf_le : x ⊓ |a| ≤ 0 := by
      have h1 : x ≤ x - x ⊓ |a| := by
        rw [sub_inf_eq_posPart]; exact hle
      have h2 := sub_le_sub_right h1 x
      rw [sub_self] at h2
      have h3 : (x - x ⊓ |a|) - x = -(x ⊓ |a|) := by abel
      rw [h3] at h2; exact neg_nonneg.mp h2
    unfold IsVLDisjoint; rw [abs_of_nonneg hx_nn]
    exact le_antisymm hinf_le (le_inf hx_nn (abs_nonneg a))

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Characterisation: `x ∈ Aᵈ` iff `|x| ⊓ |a| = 0` for all `a ∈ A`. -/
theorem mem_disjointComplement_iff {A : Set X} {x : X} :
    x ∈ Aᵈ ↔ ∀ a ∈ A, IsVLDisjoint x a := Iff.rfl

/-! ### Band generated by a set -/

/-- The **band generated** by a set `A` is the smallest band containing `A`. -/
private theorem mem_bandGen_aux {A : Set X} {x : X}
    (hx : x ∈ ⋂₀ {B : Set X | ∃ b : Band X, ↑b = B ∧ A ⊆ B})
    (b : Band X) (hAb : A ⊆ ↑b) : x ∈ b :=
  Set.mem_sInter.mp hx (↑b) ⟨b, rfl, hAb⟩

def bandGenerated (A : Set X) : Band X where
  toOrderIdeal :=
    { toSubmodule :=
        { carrier := ⋂₀ {B : Set X | ∃ b : Band X, ↑b = B ∧ A ⊆ B}
          add_mem' := fun {x y} hx hy => Set.mem_sInter.mpr fun _ ⟨b, hbB, hAB⟩ => by
            subst hbB
            exact b.toSubmodule.add_mem (mem_bandGen_aux hx b hAB)
              (mem_bandGen_aux hy b hAB)
          zero_mem' := Set.mem_sInter.mpr fun _ ⟨b, hbB, _⟩ => by
            subst hbB; exact b.toSubmodule.zero_mem
          smul_mem' := fun r x hx => Set.mem_sInter.mpr fun _ ⟨b, hbB, hAB⟩ => by
            subst hbB
            exact b.toSubmodule.smul_mem r (mem_bandGen_aux hx b hAB) }
      sup_mem' := fun {x y} hx hy => Set.mem_sInter.mpr fun _ ⟨b, hbB, hAB⟩ => by
        subst hbB
        exact b.sup_mem (mem_bandGen_aux hx b hAB) (mem_bandGen_aux hy b hAB)
      solid' := fun {x y} hx hy0 hyx => Set.mem_sInter.mpr fun _ ⟨b, hbB, hAB⟩ => by
        subst hbB; exact b.solid (mem_bandGen_aux hx b hAB) hy0 hyx }
  directed_sSup_mem' := fun S hS hpos hdir hne x hx =>
    Set.mem_sInter.mpr fun _ ⟨b, hbB, hAB⟩ => by
      subst hbB
      exact b.directed_sSup_mem (fun s hs => mem_bandGen_aux (hS hs) b hAB)
        hpos hdir hne hx

/-- `A` is contained in the band it generates. -/
theorem subset_bandGenerated (A : Set X) :
    A ⊆ (bandGenerated A : Set X) := by
  intro x hx
  exact Set.mem_sInter.mpr fun B ⟨_, hbB, hAB⟩ => hbB ▸ hAB hx

/-- The band generated by `A` is the smallest band containing `A`. -/
theorem bandGenerated_le {A : Set X} {B : Band X} (h : A ⊆ ↑B) :
    (bandGenerated A : Set X) ⊆ ↑B := by
  intro x hx
  exact Set.mem_sInter.mp hx (↑B) ⟨B, rfl, h⟩

/-- A band is order dense in its double disjoint complement: if `0 < d` and
`d ∈ Bᵈᵈ`, there exists `w ∈ B` with `0 < w ≤ d`. -/
private theorem order_dense_in_bicompl (B : Band X) {d : X}
    (hd_pos : 0 < d) (hd_mem : d ∈ (↑B : Set X)ᵈᵈ) :
    ∃ w : X, w ∈ B ∧ 0 < w ∧ w ≤ d := by
  by_contra h
  push_neg at h
  have hd_nn : 0 ≤ d := le_of_lt hd_pos
  -- d ∈ Bᵈ: for every b ∈ B, |d| ⊓ |b| = 0
  have hd_Bd : d ∈ (↑B : Set X)ᵈ := by
    intro b hb; unfold IsVLDisjoint; rw [abs_of_nonneg hd_nn]
    have hab : |b| ∈ B := B.abs_mem hb
    have h1 : d ⊓ |b| ∈ B := B.solid hab (le_inf hd_nn (abs_nonneg b)) inf_le_right
    have h2 : 0 ≤ d ⊓ |b| := le_inf hd_nn (abs_nonneg b)
    have h3 : d ⊓ |b| ≤ d := inf_le_left
    rcases eq_or_lt_of_le h2 with heq | hlt
    · exact heq.symm
    · exact absurd h3 (h _ h1 hlt)
  -- d ∈ Bᵈ ∩ Bᵈᵈ ⊆ {0}
  have := disjointComplement_inter_eq_zero (↑B : Set X)ᵈ ⟨hd_Bd, hd_mem⟩
  simp only [Set.mem_singleton_iff] at this; exact absurd this (ne_of_gt hd_pos)

/-- In an Archimedean vector lattice, `Bᵈᵈ ⊆ B` for every band `B`. -/
private theorem bicompl_subset_band [IsVLArchimedean X] (B : Band X) :
    ((↑B : Set X)ᵈ)ᵈ ⊆ (↑B : Set X) := by
  intro x hx
  -- Suffices to show |x| ∈ B
  apply B.mem_of_abs_mem
  -- Set up: |x| ∈ Bᵈᵈ, |x| ≥ 0
  have habs_mem : |x| ∈ ((↑B : Set X)ᵈ)ᵈ :=
    (disjointComplementBand (↑B : Set X)ᵈ).abs_mem hx
  set u := |x| with hu_def
  have hu_nn : 0 ≤ u := abs_nonneg x
  -- S = {y ∈ B : 0 ≤ y ≤ u} is directed, nonempty, positive, and has LUB u
  set S := {y : X | y ∈ B ∧ 0 ≤ y ∧ y ≤ u}
  -- S is nonempty
  have hS_ne : S.Nonempty := ⟨0, B.toSubmodule.zero_mem, le_refl 0, hu_nn⟩
  -- S ⊆ B
  have hS_sub : S ⊆ (↑B : Set X) := fun y hy => hy.1
  -- S consists of nonneg elements
  have hS_pos : ∀ y ∈ S, 0 ≤ y := fun y hy => hy.2.1
  -- S is directed
  have hS_dir : DirectedOn (· ≤ ·) S := by
    intro a ha b hb
    refine ⟨a ⊔ b, ⟨B.sup_mem ha.1 hb.1, le_sup_of_le_left ha.2.1,
      sup_le ha.2.2 hb.2.2⟩, le_sup_left, le_sup_right⟩
  -- u is IsLUB of S
  have hS_lub : IsLUB S u := by
    refine ⟨fun y hy => hy.2.2, ?_⟩
    intro z hz
    -- Replace z by u ⊓ z (still an upper bound of S, and ≤ u)
    suffices u ≤ u ⊓ z from le_trans this inf_le_right
    set z' := u ⊓ z with hz'_def
    have hz'_ub : ∀ y ∈ S, y ≤ z' := fun y hy => le_inf hy.2.2 (hz hy)
    have hz_nn : 0 ≤ z := hz ⟨B.toSubmodule.zero_mem, le_refl 0, hu_nn⟩
    have hz'_nn : 0 ≤ z' := le_inf hu_nn hz_nn
    have hz'_le_u : z' ≤ u := inf_le_left
    -- d = u - z' ≥ 0 with d ≤ u
    set d := u - z' with hd_def
    have hd_nn : 0 ≤ d := sub_nonneg.mpr hz'_le_u
    have hd_le_u : d ≤ u := sub_le_iff_le_add'.mpr (le_add_of_nonneg_left hz'_nn)
    -- If d = 0, done
    by_contra h_not_le
    have hd_pos : 0 < d := by
      rcases eq_or_lt_of_le hd_nn with heq | hlt
      · exfalso; apply h_not_le
        have : u - z' = 0 := heq.symm
        rw [sub_eq_zero] at this; rw [this]
      · exact hlt
    -- d ∈ Bᵈᵈ by solidity (d ≤ u = |x| and |x| ∈ Bᵈᵈ)
    have hd_mem : d ∈ ((↑B : Set X)ᵈ)ᵈ :=
      (disjointComplementBand (↑B : Set X)ᵈ).solid habs_mem hd_nn hd_le_u
    -- By order density, find w ∈ B with 0 < w ≤ d
    obtain ⟨w, hw_mem, hw_pos, hw_le_d⟩ := order_dense_in_bicompl B hd_pos hd_mem
    -- n•w ≤ z' for all n, by induction
    -- Step: n•w ≤ z' → (n+1)•w = n•w + w ≤ z' + d = u → (n+1)•w ∈ S → (n+1)•w ≤ z'
    have hw_nn : 0 ≤ w := le_of_lt hw_pos
    have : ∀ n : ℕ, n • w ≤ z' := by
      intro n; induction n with
      | zero => simpa
      | succ n ih =>
        have hnw_le_u : n • w + w ≤ u := by
          calc n • w + w ≤ z' + d := add_le_add ih hw_le_d
            _ = u := by rw [hd_def]; abel
        rw [succ_nsmul]
        have hnw_mem : n • w ∈ B := by
          have : (n : ℝ) • w ∈ B := B.toSubmodule.smul_mem (n : ℝ) hw_mem
          convert this using 1; exact (Nat.cast_smul_eq_nsmul ℝ n w).symm
        exact hz'_ub _ ⟨B.toSubmodule.add_mem hnw_mem hw_mem,
          add_nonneg (nsmul_nonneg hw_nn n) hw_nn, hnw_le_u⟩
    -- By Archimedean, w = 0
    have hw_zero := IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le hw_nn
      (fun n => le_trans (this n) hz'_le_u)
    exact absurd hw_zero (ne_of_gt hw_pos)
  exact B.directed_sSup_mem hS_sub hS_pos hS_dir hS_ne hS_lub

/-- In an Archimedean vector lattice, the double disjoint complement `Aᵈᵈ` is
the band generated by `A`. -/
theorem disjointComplement_disjointComplement_eq_bandGenerated
    [IsVLArchimedean X] (A : Set X) :
    ((Aᵈ)ᵈ : Set X) = (bandGenerated A : Set X) := by
  apply Set.Subset.antisymm
  · -- Aᵈᵈ ⊆ bandGenerated A
    -- A ⊆ bandGenerated A, so (bandGenerated A)ᵈ ⊆ Aᵈ, so Aᵈᵈ ⊆ (bandGenerated A)ᵈᵈ
    calc ((Aᵈ)ᵈ : Set X)
        ⊆ (((bandGenerated A : Set X)ᵈ)ᵈ : Set X) :=
          disjointComplement_anti (disjointComplement_anti (subset_bandGenerated A))
      _ ⊆ (bandGenerated A : Set X) := bicompl_subset_band (bandGenerated A)
  · -- bandGenerated A ⊆ Aᵈᵈ: Aᵈᵈ is a band containing A
    have : A ⊆ ↑(disjointComplementBand Aᵈ) :=
      subset_disjointComplement_disjointComplement A
    exact bandGenerated_le this

/-! ### Characterisation of bands in the Archimedean case -/

/-- In an Archimedean vector lattice, a subset is a band iff it equals its
double disjoint complement. -/
theorem eq_disjointComplement_disjointComplement [IsVLArchimedean X]
    (B : Band X) : ((↑B : Set X)ᵈ)ᵈ = ↑B := by
  rw [disjointComplement_disjointComplement_eq_bandGenerated]
  exact Set.Subset.antisymm (bandGenerated_le (Set.Subset.refl _))
    (subset_bandGenerated _)

/-- In an Archimedean vector lattice, a subset is a band iff it is of the form
`Aᵈ` for some set `A`. -/
theorem exists_eq_disjointComplement [IsVLArchimedean X] (B : Band X) :
    ∃ A : Set X, Aᵈ = ↑B := by
  exact ⟨(↑B : Set X)ᵈ, eq_disjointComplement_disjointComplement B⟩

/-! ### Principal band -/

/-- The **principal band** generated by a single element `a`. -/
def principalBand (a : X) : Band X :=
  bandGenerated {a}

/-- In an Archimedean vector lattice, `x ∈ Bₐ` for positive `a, x` iff
`x = sup {x ⊓ n • a | n ∈ ℕ}`. -/
theorem mem_principalBand_iff_isLUB [IsVLArchimedean X] {a x : X}
    (ha : 0 ≤ a) (hx : 0 ≤ x) :
    x ∈ principalBand a ↔
      IsLUB (Set.range (fun n : ℕ => x ⊓ n • a)) x := by
  constructor
  · -- Forward: x ∈ principalBand a → IsLUB
    intro hxB
    constructor
    · rintro _ ⟨n, rfl⟩; exact inf_le_left
    · intro y hy
      suffices h : x ≤ x ⊓ y from le_trans h inf_le_right
      set y' := x ⊓ y
      have hy'_nn : 0 ≤ y' := by
        apply le_inf hx
        have : x ⊓ 0 • a ≤ y := hy ⟨0, rfl⟩
        rwa [zero_nsmul, inf_eq_right.mpr hx] at this
      set d := x - y' with hd_def
      have hd_nn : 0 ≤ d := sub_nonneg.mpr inf_le_left
      have hd_le : ∀ n : ℕ, d ≤ (x - n • a)⁺ := fun n => by
        have hle : x ⊓ n • a ≤ y' :=
          le_inf inf_le_left (hy ⟨n, rfl⟩)
        calc d = x - y' := rfl
          _ ≤ x - x ⊓ (n • a) := sub_le_sub_left hle x
          _ = (x - n • a)⁺ := sub_inf_eq_posPart x (n • a)
      -- n • (d ⊓ a) ≤ x ⊓ n • a for all n, by telescoping induction
      have hda_le : ∀ n : ℕ, n • (d ⊓ a) ≤ x ⊓ n • a := by
        intro n; induction n with
        | zero =>
          rw [zero_nsmul, zero_nsmul, inf_eq_right.mpr hx]
        | succ n ih =>
          rw [succ_nsmul, succ_nsmul]
          have hda_step : d ⊓ a ≤ (x - n • a)⁺ ⊓ a :=
            inf_le_inf_right a (hd_le n)
          have hle_x : x ⊓ n • a + (x - n • a)⁺ ⊓ a ≤ x :=
            calc x ⊓ n • a + (x - n • a)⁺ ⊓ a
                ≤ x ⊓ n • a + (x - n • a)⁺ := by
                  exact add_le_add le_rfl
                    (inf_le_left (a := (x - n • a)⁺))
              _ = x := by
                  rw [← sub_inf_eq_posPart x (n • a)]; abel
          have hle_na : x ⊓ n • a + (x - n • a)⁺ ⊓ a
              ≤ n • a + a :=
            add_le_add inf_le_right inf_le_right
          calc n • (d ⊓ a) + (d ⊓ a)
              ≤ x ⊓ n • a + ((x - n • a)⁺ ⊓ a) :=
                add_le_add ih hda_step
            _ ≤ x ⊓ (n • a + a) := le_inf hle_x hle_na
      -- By Archimedean, d ⊓ a = 0
      have hda_zero : d ⊓ a = 0 :=
        IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
          (le_inf hd_nn ha) fun n =>
            le_trans (hda_le n) inf_le_left
      -- d ∈ {a}ᵈ
      have hd_Bd : d ∈ ({a} : Set X)ᵈ := fun b hb => by
        rw [Set.mem_singleton_iff] at hb
        unfold IsVLDisjoint
        rw [abs_of_nonneg hd_nn, hb, abs_of_nonneg ha, hda_zero]
      -- x ∈ {a}ᵈᵈ (since principalBand a = bandGenerated {a} = {a}ᵈᵈ)
      have hx_Bdd : x ∈ (({a} : Set X)ᵈ)ᵈ := by
        rw [disjointComplement_disjointComplement_eq_bandGenerated]
        exact hxB
      -- x ⊓ d = 0
      have hxd : x ⊓ d = 0 := by
        have h := hx_Bdd d hd_Bd
        unfold IsVLDisjoint at h
        rwa [abs_of_nonneg hx, abs_of_nonneg hd_nn] at h
      -- d ≤ x, so d = 0
      have hd_le_x : d ≤ x := sub_le_self x hy'_nn
      have hd_zero : d = 0 :=
        le_antisymm (calc d ≤ x ⊓ d := le_inf hd_le_x le_rfl
          _ = 0 := hxd) hd_nn
      rw [hd_def, sub_eq_zero] at hd_zero
      exact le_of_eq hd_zero
  · -- Backward: IsLUB → x ∈ principalBand a
    intro hlub
    -- Each x ⊓ n • a is in principalBand a
    have hmem : ∀ n : ℕ, x ⊓ n • a ∈ principalBand a := fun n => by
      have ha_mem : a ∈ principalBand a := subset_bandGenerated {a}
        (Set.mem_singleton a)
      have hna_mem : n • a ∈ principalBand a := by
        have : (n : ℝ) • a ∈ principalBand a :=
          (principalBand a).toSubmodule.smul_mem (n : ℝ) ha_mem
        rwa [Nat.cast_smul_eq_nsmul ℝ n a] at this
      exact (principalBand a).solid hna_mem
        (le_inf hx (nsmul_nonneg ha n)) inf_le_right
    -- The set is directed
    set S := Set.range (fun n : ℕ => x ⊓ n • a)
    have hS_sub : S ⊆ (principalBand a : Set X) := by
      rintro _ ⟨n, rfl⟩; exact hmem n
    have hS_pos : ∀ y ∈ S, 0 ≤ y := by
      rintro _ ⟨n, rfl⟩; exact le_inf hx (nsmul_nonneg ha n)
    have hS_ne : S.Nonempty := ⟨x ⊓ 0 • a, ⟨0, rfl⟩⟩
    have hS_dir : DirectedOn (· ≤ ·) S := by
      rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      refine ⟨x ⊓ (m + n) • a, ⟨m + n, rfl⟩, ?_, ?_⟩
      · exact inf_le_inf_left x (nsmul_le_nsmul_left ha (Nat.le_add_right m n))
      · exact inf_le_inf_left x (nsmul_le_nsmul_left ha (Nat.le_add_left n m))
    exact (principalBand a).directed_sSup_mem hS_sub hS_pos hS_dir hS_ne hlub

/-- The principal ideal is contained in the principal band. -/
theorem principal_le_principalBand (a : X) :
    (OrderIdeal.principal a : Set X) ⊆ (principalBand a : Set X) := by
  intro x ⟨c, hc, hxc⟩
  apply Set.mem_sInter.mpr
  intro B ⟨b, hbB, hAB⟩
  subst hbB
  have ha : a ∈ b := hAB (Set.mem_singleton a)
  have hab : |a| ∈ b := b.abs_mem ha
  have hsmul : c • |a| ∈ b := b.toSubmodule.smul_mem c hab
  exact b.mem_of_abs_mem (b.solid hsmul (abs_nonneg x) hxc)

/-! ### Lattice structure of bands -/

/-- The whole space is a band. -/
instance : Top (Band X) where
  top := {
    toOrderIdeal := ⊤
    directed_sSup_mem' := fun _ _ _ _ _ _ _ => Submodule.mem_top
  }

/-- Every element belongs to `⊤`. -/
@[simp]
theorem mem_top {x : X} : x ∈ (⊤ : Band X) := Submodule.mem_top

/-- The intersection of two bands is a band. -/
def inf (B₁ B₂ : Band X) : Band X where
  toOrderIdeal := B₁.toOrderIdeal.inf B₂.toOrderIdeal
  directed_sSup_mem' := fun _S hS hpos hdir hne _x hx =>
    ⟨B₁.directed_sSup_mem (fun _s hs => (hS hs).1) hpos hdir hne hx,
     B₂.directed_sSup_mem (fun _s hs => (hS hs).2) hpos hdir hne hx⟩

/-- The intersection of an arbitrary family of bands is a band. -/
theorem iInter_isBand {ι : Type*} (B : ι → Band X) :
    ∃ C : Band X, (C : Set X) = ⋂ i, (B i : Set X) := by
  refine ⟨{
    toOrderIdeal :=
      { toSubmodule :=
          { carrier := ⋂ i, (B i : Set X)
            add_mem' := fun {x y} hx hy => Set.mem_iInter.mpr fun i =>
              (B i).toSubmodule.add_mem (Set.mem_iInter.mp hx i)
                (Set.mem_iInter.mp hy i)
            zero_mem' := Set.mem_iInter.mpr fun i =>
              (B i).toSubmodule.zero_mem
            smul_mem' := fun r x hx => Set.mem_iInter.mpr fun i =>
              (B i).toSubmodule.smul_mem r (Set.mem_iInter.mp hx i) }
        sup_mem' := fun {x y} hx hy => Set.mem_iInter.mpr fun i =>
          (B i).sup_mem (Set.mem_iInter.mp hx i) (Set.mem_iInter.mp hy i)
        solid' := fun {x y} hx hy0 hyx => Set.mem_iInter.mpr fun i =>
          (B i).solid (Set.mem_iInter.mp hx i) hy0 hyx }
    directed_sSup_mem' := fun S hS hpos hdir hne x hx =>
      Set.mem_iInter.mpr fun i =>
        (B i).directed_sSup_mem
          (fun s hs => Set.mem_iInter.mp (hS hs) i)
          hpos hdir hne hx }, rfl⟩

end Band

/-! ## Projection bands -/

/-- A band `B` in a vector lattice is a **projection band** if every element
of `X` decomposes (uniquely) as a sum of an element of `B` and an element of
`Bᵈ`. Equivalently, `X = B ⊕ Bᵈ` as a direct sum. -/
structure ProjectionBand (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends Band X where
  decomposition' : ∀ x : X, ∃ y z : X, y ∈ carrier
    ∧ z ∈ disjointComplement carrier ∧ x = y + z

namespace ProjectionBand

instance : SetLike (ProjectionBand X) X where
  coe P := P.carrier
  coe_injective' p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

variable (P : ProjectionBand X)

/-- Every element of `X` decomposes as `y + z` with `y ∈ B` and `z ∈ Bᵈ`. -/
theorem decomposition (x : X) :
    ∃ y z : X, y ∈ P ∧ z ∈ disjointComplement (P : Set X) ∧ x = y + z :=
  P.decomposition' x

/-- The decomposition in a projection band is unique. -/
theorem decomposition_unique {x y₁ z₁ y₂ z₂ : X}
    (hy₁ : y₁ ∈ P) (hz₁ : z₁ ∈ disjointComplement (P : Set X))
    (hy₂ : y₂ ∈ P) (hz₂ : z₂ ∈ disjointComplement (P : Set X))
    (h₁ : x = y₁ + z₁) (h₂ : x = y₂ + z₂) :
    y₁ = y₂ ∧ z₁ = z₂ := by
  -- y₁ - y₂ = z₂ - z₁, and this element lies in P ∩ Pᵈ ⊆ {0}
  have heq : y₁ - y₂ = z₂ - z₁ := by
    have h := h₁.symm.trans h₂
    calc y₁ - y₂ = (y₁ + z₁) - z₁ - y₂ := by abel
      _ = (y₂ + z₂) - z₁ - y₂ := by rw [h]
      _ = z₂ - z₁ := by abel
  have hmem_P : y₁ - y₂ ∈ P :=
    P.toBand.toOrderIdeal.toSubmodule.sub_mem hy₁ hy₂
  have hmem_Pd : y₁ - y₂ ∈ disjointComplement (P : Set X) := by
    rw [heq]
    exact (Band.disjointComplementOrderIdeal
      (P : Set X)).toSubmodule.sub_mem (show z₂ ∈ (Band.disjointComplementOrderIdeal
        (P : Set X)).toSubmodule from hz₂) hz₁
  have hmem_both : y₁ - y₂ ∈ (↑P) ∩ (↑P)ᵈ := ⟨hmem_P, hmem_Pd⟩
  have hzero : y₁ - y₂ = 0 :=
    Set.mem_singleton_iff.mp (disjointComplement_inter_eq_zero (↑P) hmem_both)
  refine ⟨sub_eq_zero.mp hzero, ?_⟩
  have : z₂ - z₁ = 0 := heq ▸ hzero
  exact eq_of_sub_eq_zero this |>.symm

/-- The **band projection** onto a projection band: the linear map sending
`x` to its component in `B`. -/
noncomputable def bandProjection : X →ₗ[ℝ] X where
  toFun x := (P.decomposition x).choose
  map_add' := fun x y => by
    set yx := (P.decomposition x).choose
    set zx := (P.decomposition x).choose_spec.choose
    set yy := (P.decomposition y).choose
    set zy := (P.decomposition y).choose_spec.choose
    set yxy := (P.decomposition (x + y)).choose
    set zxy := (P.decomposition (x + y)).choose_spec.choose
    have hyx : yx ∈ P := (P.decomposition x).choose_spec.choose_spec.1
    have hzx : zx ∈ (↑P)ᵈ := (P.decomposition x).choose_spec.choose_spec.2.1
    have hx_eq : x = yx + zx := (P.decomposition x).choose_spec.choose_spec.2.2
    have hyy : yy ∈ P := (P.decomposition y).choose_spec.choose_spec.1
    have hzy : zy ∈ (↑P)ᵈ := (P.decomposition y).choose_spec.choose_spec.2.1
    have hy_eq : y = yy + zy := (P.decomposition y).choose_spec.choose_spec.2.2
    have hyxy : yxy ∈ P := (P.decomposition (x + y)).choose_spec.choose_spec.1
    have hzxy : zxy ∈ (↑P)ᵈ :=
      (P.decomposition (x + y)).choose_spec.choose_spec.2.1
    have hxy_eq : x + y = yxy + zxy :=
      (P.decomposition (x + y)).choose_spec.choose_spec.2.2
    have hsum_P : yx + yy ∈ P := P.toBand.toOrderIdeal.toSubmodule.add_mem hyx hyy
    have hsum_Pd : zx + zy ∈ (↑P)ᵈ :=
      (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule.add_mem
        (show zx ∈ (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule from hzx)
        hzy
    have hsum_eq : x + y = (yx + yy) + (zx + zy) := by rw [hx_eq, hy_eq]; abel
    exact (P.decomposition_unique hyxy hzxy hsum_P hsum_Pd hxy_eq hsum_eq).1
  map_smul' := fun r x => by
    set yx := (P.decomposition x).choose
    set zx := (P.decomposition x).choose_spec.choose
    set yr := (P.decomposition (r • x)).choose
    set zr := (P.decomposition (r • x)).choose_spec.choose
    have hyx : yx ∈ P := (P.decomposition x).choose_spec.choose_spec.1
    have hzx : zx ∈ (↑P)ᵈ := (P.decomposition x).choose_spec.choose_spec.2.1
    have hx_eq : x = yx + zx := (P.decomposition x).choose_spec.choose_spec.2.2
    have hyr : yr ∈ P := (P.decomposition (r • x)).choose_spec.choose_spec.1
    have hzr : zr ∈ (↑P)ᵈ :=
      (P.decomposition (r • x)).choose_spec.choose_spec.2.1
    have hr_eq : r • x = yr + zr :=
      (P.decomposition (r • x)).choose_spec.choose_spec.2.2
    have hscal_P : r • yx ∈ P := P.toBand.toOrderIdeal.toSubmodule.smul_mem r hyx
    have hscal_Pd : r • zx ∈ (↑P)ᵈ :=
      (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule.smul_mem r
        (show zx ∈ (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule from hzx)
    have hscal_eq : r • x = r • yx + r • zx := by rw [hx_eq, smul_add]
    simp only [RingHom.id_apply]
    exact (P.decomposition_unique hyr hzr hscal_P hscal_Pd hr_eq hscal_eq).1

/-- The band projection is idempotent. -/
theorem bandProjection_sq :
    P.bandProjection ∘ₗ P.bandProjection = P.bandProjection := by
  ext x
  simp only [LinearMap.comp_apply]
  -- Px ∈ P, and Px = Px + 0 with 0 ∈ Pᵈ
  have hPx_mem : P.bandProjection x ∈ P :=
    (P.decomposition x).choose_spec.choose_spec.1
  have hPPx_mem : P.bandProjection (P.bandProjection x) ∈ P :=
    (P.decomposition (P.bandProjection x)).choose_spec.choose_spec.1
  set z' := (P.decomposition (P.bandProjection x)).choose_spec.choose
  have hz' : z' ∈ disjointComplement (P : Set X) :=
    (P.decomposition (P.bandProjection x)).choose_spec.choose_spec.2.1
  have hPx_dec : P.bandProjection x =
      P.bandProjection (P.bandProjection x) + z' :=
    (P.decomposition (P.bandProjection x)).choose_spec.choose_spec.2.2
  have h0_mem : (0 : X) ∈ disjointComplement (P : Set X) :=
    (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule.zero_mem
  have hPx_eq : P.bandProjection x = P.bandProjection x + 0 := (add_zero _).symm
  exact (P.decomposition_unique hPPx_mem hz' hPx_mem h0_mem hPx_dec hPx_eq).1

/-- The band projection is positive: `0 ≤ x → 0 ≤ Px`. -/
private theorem id_sub_bandProjection_mem' (x : X) :
    x - P.bandProjection x ∈ disjointComplement (P : Set X) := by
  have spec := (P.decomposition x).choose_spec.choose_spec
  have heq : x = P.bandProjection x + (P.decomposition x).choose_spec.choose :=
    spec.2.2
  have : x - P.bandProjection x = (P.decomposition x).choose_spec.choose :=
    (eq_sub_of_add_eq' heq.symm).symm
  rw [this]; exact spec.2.1

theorem bandProjection_nonneg {x : X} (hx : 0 ≤ x) :
    0 ≤ P.bandProjection x := by
  set Px := P.bandProjection x
  set Qx := x - Px with hQx_def
  have hPx_mem : Px ∈ P := (P.decomposition x).choose_spec.choose_spec.1
  have hQx_mem : Qx ∈ disjointComplement (P : Set X) := id_sub_bandProjection_mem' P x
  have hPxneg_mem_P : Px⁻ ∈ P :=
    P.toBand.toOrderIdeal.solid (P.toBand.abs_mem hPx_mem)
      (negPart_nonneg Px) (sup_le (neg_le_abs Px) (abs_nonneg Px))
  have hle_neg_Px : -Px ≤ Qx := by
    rw [neg_le_sub_iff_le_add]; exact le_add_of_nonneg_left hx
  have hle : Px⁻ ≤ |Qx| :=
    le_trans (sup_le_sup_right hle_neg_Px 0)
      (sup_le (le_abs_self Qx) (abs_nonneg Qx))
  have hQx_abs_mem : |Qx| ∈ disjointComplement (P : Set X) :=
    (Band.disjointComplementOrderIdeal (P : Set X)).abs_mem hQx_mem
  have hPxneg_mem_Pd : Px⁻ ∈ disjointComplement (P : Set X) :=
    (Band.disjointComplementOrderIdeal (P : Set X)).solid
      hQx_abs_mem (negPart_nonneg Px) hle
  have hzero : Px⁻ = 0 :=
    Set.mem_singleton_iff.mp (disjointComplement_inter_eq_zero (↑P)
      ⟨hPxneg_mem_P, hPxneg_mem_Pd⟩)
  exact negPart_eq_zero.mp hzero

/-- The band projection is dominated by the identity: `0 ≤ x → Px ≤ x`. -/
theorem bandProjection_le {x : X} (hx : 0 ≤ x) :
    P.bandProjection x ≤ x := by
  rw [← sub_nonneg]
  set Px := P.bandProjection x
  set Qx := x - Px
  have hPx_mem : Px ∈ P := (P.decomposition x).choose_spec.choose_spec.1
  have hQx_mem : Qx ∈ disjointComplement (P : Set X) :=
    id_sub_bandProjection_mem' P x
  have hQxneg_mem_Pd : Qx⁻ ∈ disjointComplement (P : Set X) :=
    (Band.disjointComplementOrderIdeal (P : Set X)).solid
      ((Band.disjointComplementOrderIdeal (P : Set X)).abs_mem hQx_mem)
      (negPart_nonneg Qx) (sup_le (neg_le_abs Qx) (abs_nonneg Qx))
  have hle_neg_Qx : -Qx ≤ Px := by
    change -(x - Px) ≤ Px; rw [neg_sub]; exact sub_le_self Px (by exact hx)
  have hle : Qx⁻ ≤ |Px| :=
    le_trans (sup_le_sup_right hle_neg_Qx 0)
      (sup_le (le_abs_self Px) (abs_nonneg Px))
  have hQxneg_mem_P : Qx⁻ ∈ P :=
    P.toBand.toOrderIdeal.solid (P.toBand.abs_mem hPx_mem) (negPart_nonneg Qx) hle
  have hzero : Qx⁻ = 0 :=
    Set.mem_singleton_iff.mp (disjointComplement_inter_eq_zero (↑P)
      ⟨hQxneg_mem_P, hQxneg_mem_Pd⟩)
  exact negPart_eq_zero.mp hzero

/-- The band projection maps into the band. -/
theorem bandProjection_mem (x : X) :
    P.bandProjection x ∈ P := by
  exact (P.decomposition x).choose_spec.choose_spec.1

/-- The complement `I - P` maps into the disjoint complement. -/
theorem id_sub_bandProjection_mem (x : X) :
    x - P.bandProjection x ∈ disjointComplement (P : Set X) := by
  set y := (P.decomposition x).choose
  set z := (P.decomposition x).choose_spec.choose
  have hz : z ∈ disjointComplement (P : Set X) :=
    (P.decomposition x).choose_spec.choose_spec.2.1
  have hxyz : x = y + z :=
    (P.decomposition x).choose_spec.choose_spec.2.2
  have : x - P.bandProjection x = z := by
    change x - y = z; rw [hxyz, add_sub_cancel_left]
  rw [this]; exact hz

private theorem bandProjection_of_mem {x : X} (hx : x ∈ P) :
    P.bandProjection x = x := by
  have h0_mem : (0 : X) ∈ disjointComplement (P : Set X) :=
    (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule.zero_mem
  have hQx_mem : x - P.bandProjection x ∈ disjointComplement (P : Set X) :=
    id_sub_bandProjection_mem' P x
  have hx_dec : x = P.bandProjection x + (x - P.bandProjection x) := by abel
  exact (P.decomposition_unique (P.bandProjection_mem x) hQx_mem
    hx h0_mem hx_dec (add_zero x).symm).1

/-- The range of the band projection is the band itself. -/
theorem range_bandProjection :
    Set.range P.bandProjection = (P : Set X) := by
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact P.bandProjection_mem y
  · intro hx; exact ⟨x, bandProjection_of_mem P hx⟩

/-- The disjoint complement of a projection band is a projection band. -/
def disjointComplementProjectionBand : ProjectionBand X where
  toBand := Band.disjointComplementBand (P : Set X)
  decomposition' := fun x => ⟨x - P.bandProjection x, P.bandProjection x,
    (show x - P.bandProjection x ∈ ((P : Set X))ᵈ from P.id_sub_bandProjection_mem x),
    (show P.bandProjection x ∈ ((P : Set X))ᵈᵈ from
      subset_disjointComplement_disjointComplement (P : Set X) (P.bandProjection_mem x)),
    by abel⟩

/-- An ideal `J` is a projection band iff `J + Jᵈ = X`. -/
theorem projectionBand_iff_add_disjointComplement
    (J : OrderIdeal X) :
    (∃ P : ProjectionBand X, (P : Set X) = (J : Set X)) ↔
      ∀ x : X, ∃ y z : X, y ∈ (J : Set X)
        ∧ z ∈ disjointComplement (J : Set X) ∧ x = y + z := by
  constructor
  · rintro ⟨P, hPJ⟩ x
    obtain ⟨y, z, hy, hz, hxyz⟩ := P.decomposition x
    exact ⟨y, z, hPJ ▸ hy, hPJ ▸ hz, hxyz⟩
  · intro hdecomp
    have heq : ((J : Set X)ᵈ)ᵈ = (J : Set X) := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨y, z, hy, hz, hxyz⟩ := hdecomp x
        have hy_dd : y ∈ ((J : Set X)ᵈ)ᵈ :=
          subset_disjointComplement_disjointComplement (J : Set X) hy
        have hxmy_dd : x - y ∈ ((J : Set X)ᵈ)ᵈ :=
          (Band.disjointComplementOrderIdeal ((J : Set X)ᵈ)).toSubmodule.sub_mem
            hx hy_dd
        have hxmy_both : x - y ∈ (J : Set X)ᵈ ∩ ((J : Set X)ᵈ)ᵈ :=
          ⟨(hxyz ▸ add_sub_cancel_left y z : x - y = z) ▸ hz, hxmy_dd⟩
        rwa [sub_eq_zero.mp (Set.mem_singleton_iff.mp
          (disjointComplement_inter_eq_zero ((J : Set X)ᵈ) hxmy_both))]
      · exact subset_disjointComplement_disjointComplement (J : Set X)
    exact ⟨{
      toBand := {
        toOrderIdeal := J
        directed_sSup_mem' := fun S hS hpos hdir hne x hx => by
          have hS_dd : S ⊆ ((J : Set X)ᵈ)ᵈ := fun s hs =>
            subset_disjointComplement_disjointComplement (J : Set X) (hS hs)
          have hx_dd := (Band.disjointComplementBand ((J : Set X)ᵈ)).directed_sSup_mem
            hS_dd hpos hdir hne hx
          change x ∈ ((J : Set X)ᵈ)ᵈ at hx_dd
          rw [heq] at hx_dd; exact hx_dd }
      decomposition' := hdecomp }, rfl⟩

/-- If `X = J₁ ⊕ J₂` where `J₁` and `J₂` are ideals with `J₁ ⊥ J₂`, then
both are projection bands and `J₂ = J₁ᵈ`. -/
theorem of_direct_sum_of_disjoint (J₁ J₂ : OrderIdeal X)
    (hperp : ∀ x ∈ (J₁ : Set X), ∀ y ∈ (J₂ : Set X), IsVLDisjoint x y)
    (hdecomp : ∀ x : X, ∃ y ∈ (J₁ : Set X), ∃ z ∈ (J₂ : Set X),
      x = y + z) :
    disjointComplement (J₁ : Set X) = (J₂ : Set X)
      ∧ ∃ P : ProjectionBand X, (P : Set X) = (J₁ : Set X) := by
  have hJ₂_sub : (J₂ : Set X) ⊆ ((J₁ : Set X))ᵈ := fun z hz a ha =>
    isVLDisjoint_comm.mpr (hperp a ha z hz)
  have hJ₁d_sub : ((J₁ : Set X))ᵈ ⊆ (J₂ : Set X) := by
    intro z hz
    obtain ⟨y, hy, w, hw, hzyw⟩ := hdecomp z
    have hw_d : w ∈ ((J₁ : Set X))ᵈ := hJ₂_sub hw
    have hy_d : y ∈ ((J₁ : Set X))ᵈ := by
      have : y = z - w := by rw [hzyw]; abel
      rw [this]
      exact (Band.disjointComplementOrderIdeal (J₁ : Set X)).toSubmodule.sub_mem
        (show z ∈ (Band.disjointComplementOrderIdeal (J₁ : Set X)).toSubmodule
          from hz) hw_d
    have hy_zero : y = 0 := Set.mem_singleton_iff.mp
      (disjointComplement_inter_eq_zero (J₁ : Set X) ⟨hy, hy_d⟩)
    rw [hy_zero, zero_add] at hzyw; rwa [hzyw]
  refine ⟨Set.Subset.antisymm hJ₁d_sub hJ₂_sub, ?_⟩
  have hdecomp' : ∀ x : X, ∃ y z : X, y ∈ (J₁ : Set X)
      ∧ z ∈ disjointComplement (J₁ : Set X) ∧ x = y + z := fun x => by
    obtain ⟨y, hy, z, hz, hxyz⟩ := hdecomp x
    exact ⟨y, z, hy, hJ₂_sub hz, hxyz⟩
  exact (projectionBand_iff_add_disjointComplement J₁).mpr hdecomp'

/-! ### Characterisation of band projections -/

private theorem bpi_monotone {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x) {x y : X} (hxy : x ≤ y) :
    T x ≤ T y := by
  have : 0 ≤ T (y - x) := hpos _ (sub_nonneg.mpr hxy)
  rwa [map_sub, sub_nonneg] at this

/-- Range and kernel have disjoint positive cones. -/
private theorem bpi_pos_cone_disjoint {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {y z : X} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hTy : T y = y) (hTz : T z = 0) :
    y ⊓ z = 0 := by
  have hyz_nn : 0 ≤ y ⊓ z := le_inf hy hz
  have hT_yz_le_z : T (y ⊓ z) ≤ T z := bpi_monotone hpos inf_le_right
  rw [hTz] at hT_yz_le_z
  have hT_yz_zero : T (y ⊓ z) = 0 := le_antisymm hT_yz_le_z (hpos _ hyz_nn)
  -- y ⊓ z ≤ y = T y ≤ T z = 0 ... no, need I-T argument
  -- Since T(y ⊓ z) = 0: y ⊓ z = (y ⊓ z) - T(y ⊓ z)
  -- Need to show (I-T) is monotone on nonneg elements? No, just direct:
  -- y ⊓ z ≤ y and y ⊓ z ≤ z, plus T(y ⊓ z) = 0 and Ty = y.
  -- (I-T)(y) = 0, (I-T)(y ⊓ z) = y ⊓ z
  -- But (I-T) is also positive (0 ≤ x → (I-T)x = x - Tx ≥ 0)
  -- and (I-T) ≤ I. So (I-T) is monotone on nonneg elements.
  -- (I-T)(y ⊓ z) ≤ (I-T)(y) since y ⊓ z ≤ y, both nonneg.
  -- Monotonicity of I-T: if a ≤ b with 0 ≤ a then (I-T)a ≤ (I-T)b
  -- follows from 0 ≤ (I-T)(b-a) = (b-a) - T(b-a) ≥ 0.
  have hIT_mono : ∀ {a b : X}, a ≤ b → a - T a ≤ b - T b := fun {a b} hab => by
    have h1 : 0 ≤ (b - a) - T (b - a) := sub_nonneg.mpr
      (hle (b - a) (sub_nonneg.mpr hab))
    rw [map_sub] at h1
    -- h1 : 0 ≤ (b - a) - (T b - T a) = (b - T b) - (a - T a)
    rwa [show (b - a) - (T b - T a) = (b - T b) - (a - T a) by abel,
         sub_nonneg] at h1
  have : y ⊓ z ≤ 0 := by
    calc y ⊓ z = (y ⊓ z) - T (y ⊓ z) := by rw [hT_yz_zero, sub_zero]
      _ ≤ y - T y := hIT_mono inf_le_left
      _ = 0 := by rw [hTy, sub_self]
  exact le_antisymm this hyz_nn

/-- If `T w = w` then `T(w⁺) = w⁺` and `T(w⁻) = w⁻`. -/
private theorem bpi_preserves_parts {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {w : X} (hTw : T w = w) :
    T w⁺ = w⁺ ∧ T w⁻ = w⁻ := by
  have hTwp_le : T w⁺ ≤ w⁺ := hle w⁺ (posPart_nonneg w)
  have hTwn_le : T w⁻ ≤ w⁻ := hle w⁻ (negPart_nonneg w)
  have hdiff : T w⁺ - T w⁻ = w⁺ - w⁻ := by
    rw [← map_sub, posPart_sub_negPart, hTw]
  have hTdisj : T w⁺ ⊓ T w⁻ = 0 :=
    le_antisymm (le_trans (inf_le_inf hTwp_le hTwn_le)
      (le_of_eq (posPart_inf_negPart_eq_zero w)))
      (le_inf (hpos w⁺ (posPart_nonneg w)) (hpos w⁻ (negPart_nonneg w)))
  exact isVLDisjoint_decomposition_unique
    (hpos w⁺ (posPart_nonneg w)) (hpos w⁻ (negPart_nonneg w))
    (posPart_nonneg w) (negPart_nonneg w)
    (isVLDisjoint_of_inf_eq_zero hTdisj)
    (isVLDisjoint_of_inf_eq_zero (posPart_inf_negPart_eq_zero w))
    hdiff

/-- If `T w = w` then `T |w| = |w|`. -/
private theorem bpi_preserves_abs {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {w : X} (hTw : T w = w) : T |w| = |w| := by
  rw [show |w| = w⁺ + w⁻ from (posPart_add_negPart w).symm, map_add,
    (bpi_preserves_parts hpos hle hTw).1, (bpi_preserves_parts hpos hle hTw).2]

/-- Solidity of the range: if `T x = x`, `0 ≤ y ≤ x`, then `T y = y`. -/
private theorem bpi_range_solid {T : X →ₗ[ℝ] X}
    (hTT : T ∘ₗ T = T) (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    {x y : X} (hx_fixed : T x = x) (hy_nn : 0 ≤ y) (hyx : y ≤ x) :
    T y = y := by
  have hTy_le_y : T y ≤ y := hle y hy_nn
  have hd_nn : 0 ≤ y - T y := sub_nonneg.mpr hTy_le_y
  have hd_le_x : y - T y ≤ x := le_trans (sub_le_self y (hpos y hy_nn)) hyx
  have hx_nn : 0 ≤ x := le_trans hy_nn hyx
  have hres : T (y - T y) = 0 := by
    have : T (T y) = T y := LinearMap.congr_fun hTT y
    rw [map_sub, this, sub_self]
  have hdisjoint := bpi_pos_cone_disjoint hpos hle hx_nn hd_nn hx_fixed hres
  have hle_zero : y - T y ≤ 0 := by
    calc y - T y ≤ x ⊓ (y - T y) := le_inf hd_le_x le_rfl
      _ = 0 := hdisjoint
  exact eq_of_sub_eq_zero (le_antisymm hle_zero hd_nn) |>.symm

/-- The range `{x | T x = x}` is an `OrderIdeal`. -/
private noncomputable def bpi_rangeIdeal {T : X →ₗ[ℝ] X}
    (hTT : T ∘ₗ T = T) (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x) : OrderIdeal X :=
  OrderIdeal.ofSolid
    { carrier := {x | T x = x}
      add_mem' := fun {a b} (ha : T a = a) (hb : T b = b) =>
        show T (a + b) = a + b by rw [map_add, ha, hb]
      zero_mem' := map_zero T
      smul_mem' := fun r a (ha : T a = a) =>
        show T (r • a) = r • a by rw [map_smul, ha] }
    (fun a b (ha : T a = a) hab => by
      change T b = b
      have ha_abs : T |a| = |a| := bpi_preserves_abs hpos hle ha
      have hb_abs : T |b| = |b| :=
        bpi_range_solid hTT hpos hle ha_abs (abs_nonneg b) hab
      have hTyp : T b⁺ = b⁺ := bpi_range_solid hTT hpos hle hb_abs
        (posPart_nonneg b) (sup_le (le_abs_self b) (abs_nonneg b))
      have hTyn : T b⁻ = b⁻ := bpi_range_solid hTT hpos hle hb_abs
        (negPart_nonneg b) (sup_le (neg_le_abs b) (abs_nonneg b))
      calc T b = T (b⁺ - b⁻) := by rw [posPart_sub_negPart]
        _ = T b⁺ - T b⁻ := map_sub T b⁺ b⁻
        _ = b⁺ - b⁻ := by rw [hTyp, hTyn]
        _ = b := posPart_sub_negPart b)

/-- The kernel `{x | T x = 0}` is an `OrderIdeal`. -/
private noncomputable def bpi_kernelIdeal {T : X →ₗ[ℝ] X}
    (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x) : OrderIdeal X :=
  OrderIdeal.ofSolid
    { carrier := {x | T x = 0}
      add_mem' := fun {a b} (ha : T a = 0) (hb : T b = 0) =>
        show T (a + b) = 0 by rw [map_add, ha, hb, add_zero]
      zero_mem' := map_zero T
      smul_mem' := fun r a (ha : T a = 0) =>
        show T (r • a) = 0 by rw [map_smul, ha, smul_zero] }
    (fun a b (ha : T a = 0) hab => by
      change T b = 0
      -- From T a = 0 derive T|a| = 0 via T a⁺ = T a⁻ and disjointness
      have hTxp_le : T a⁺ ≤ a⁺ := hle a⁺ (posPart_nonneg a)
      have hTxn_le : T a⁻ ≤ a⁻ := hle a⁻ (negPart_nonneg a)
      have hTdiff : T a⁺ - T a⁻ = 0 := by
        rw [← map_sub, posPart_sub_negPart]; exact ha
      have heq : T a⁺ = T a⁻ := sub_eq_zero.mp hTdiff
      have hTxp_zero : T a⁺ = 0 := by
        apply le_antisymm _ (hpos a⁺ (posPart_nonneg a))
        calc T a⁺ ≤ a⁺ ⊓ T a⁺ := le_inf hTxp_le le_rfl
          _ ≤ a⁺ ⊓ a⁻ := inf_le_inf_left a⁺ (heq ▸ hTxn_le)
          _ = 0 := posPart_inf_negPart_eq_zero a
      have hTxn_zero : T a⁻ = 0 := heq ▸ hTxp_zero
      have hTabsa : T |a| = 0 := by
        rw [show |a| = a⁺ + a⁻ from (posPart_add_negPart a).symm,
            map_add, hTxp_zero, hTxn_zero, add_zero]
      -- T|b| ≤ T|a| = 0 by monotonicity
      have hTabsb : T |b| = 0 :=
        le_antisymm (le_trans (bpi_monotone hpos hab) (le_of_eq hTabsa))
          (hpos |b| (abs_nonneg b))
      -- T b⁺, T b⁻ ≤ T|b| = 0
      have hTyp : T b⁺ = 0 :=
        le_antisymm (le_trans (bpi_monotone hpos
          (sup_le (le_abs_self b) (abs_nonneg b))) (le_of_eq hTabsb))
          (hpos b⁺ (posPart_nonneg b))
      have hTyn : T b⁻ = 0 :=
        le_antisymm (le_trans (bpi_monotone hpos
          (sup_le (neg_le_abs b) (abs_nonneg b))) (le_of_eq hTabsb))
          (hpos b⁻ (negPart_nonneg b))
      calc T b = T (b⁺ - b⁻) := by rw [posPart_sub_negPart]
        _ = T b⁺ - T b⁻ := map_sub T b⁺ b⁻
        _ = 0 := by rw [hTyp, hTyn, sub_self])

/-- Range and kernel are VL-disjoint. -/
private theorem bpi_range_kernel_disjoint {T : X →ₗ[ℝ] X}
    (hTT : T ∘ₗ T = T) (hpos : ∀ x : X, 0 ≤ x → 0 ≤ T x)
    (hle : ∀ x : X, 0 ≤ x → T x ≤ x)
    (u : X) (hu : u ∈ (bpi_rangeIdeal hTT hpos hle : Set X))
    (v : X) (hv : v ∈ (bpi_kernelIdeal hpos hle : Set X)) :
    IsVLDisjoint u v := by
  change T u = u at hu; change T v = 0 at hv
  have hu_abs : T |u| = |u| := bpi_preserves_abs hpos hle hu
  have hv_abs : T |v| = 0 :=
    show |v| ∈ (bpi_kernelIdeal hpos hle : Set X) from
      (bpi_kernelIdeal hpos hle).abs_mem hv
  change |u| ⊓ |v| = 0
  exact bpi_pos_cone_disjoint (y := |u|) (z := |v|) hpos hle
    (abs_nonneg u) (abs_nonneg v) hu_abs hv_abs

/-- A linear operator is a band projection iff `P² = P` and `0 ≤ P ≤ I`. -/
theorem bandProjection_iff (T : X →ₗ[ℝ] X) :
    (∃ P : ProjectionBand X, P.bandProjection = T) ↔
      T ∘ₗ T = T
        ∧ (∀ x : X, 0 ≤ x → 0 ≤ T x)
        ∧ (∀ x : X, 0 ≤ x → T x ≤ x) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.bandProjection_sq,
           fun x hx => P.bandProjection_nonneg hx,
           fun x hx => P.bandProjection_le hx⟩
  · -- The converse requires showing Range(T) is a projection band
    rintro ⟨hTT, hpos, hle⟩
    set R := bpi_rangeIdeal hTT hpos hle
    set K := bpi_kernelIdeal hpos hle
    -- R and K are disjoint and decompose X
    have hperp : ∀ u ∈ (R : Set X), ∀ v ∈ (K : Set X),
        IsVLDisjoint u v :=
      bpi_range_kernel_disjoint hTT hpos hle
    have hdecomp : ∀ x : X, ∃ y ∈ (R : Set X), ∃ z ∈ (K : Set X),
        x = y + z := fun x => by
      refine ⟨T x, ?_, x - T x, ?_, ?_⟩
      · change T (T x) = T x; exact LinearMap.congr_fun hTT x
      · change T (x - T x) = 0
        have : T (T x) = T x := LinearMap.congr_fun hTT x
        rw [map_sub, this, sub_self]
      · abel
    obtain ⟨hdc, P, hPset⟩ := of_direct_sum_of_disjoint R K hperp hdecomp
    refine ⟨P, ?_⟩
    ext x
    -- P.bandProjection x and T x are both the R-component of x
    have hTx_P : T x ∈ (P : Set X) := by
      rw [hPset]; change T (T x) = T x; exact LinearMap.congr_fun hTT x
    have hQx_Pd : x - T x ∈ disjointComplement (P : Set X) := by
      rw [hPset, hdc]
      change T (x - T x) = 0
      have : T (T x) = T x := LinearMap.congr_fun hTT x
      rw [map_sub, this, sub_self]
    have hPx_dec : x = P.bandProjection x + (x - P.bandProjection x) := by
      abel
    have hTx_dec : x = T x + (x - T x) := by abel
    exact (P.decomposition_unique (P.bandProjection_mem x)
      (P.id_sub_bandProjection_mem x) hTx_P hQx_Pd hPx_dec hTx_dec).1

/-- A band projection is a lattice homomorphism. -/
theorem bandProjection_isVecLatHom :
    IsVecLatHom P.bandProjection.toFun := by
  apply IsVecLatHom.of_disjoint
  · exact P.bandProjection.isLinear
  · intro x hx; exact P.bandProjection_nonneg hx
  · intro x y hxy
    have hx : 0 ≤ x := hxy ▸ inf_le_left
    have hy : 0 ≤ y := hxy ▸ inf_le_right
    apply le_antisymm
    · calc P.bandProjection x ⊓ P.bandProjection y
          ≤ x ⊓ y := inf_le_inf (P.bandProjection_le hx) (P.bandProjection_le hy)
        _ = 0 := hxy
    · exact le_inf (P.bandProjection_nonneg hx) (P.bandProjection_nonneg hy)

end ProjectionBand

/-! ## Infinite band decompositions

We introduce the **Projection Property** (PP) and **Principal Projection
Property** (PPP) of a vector lattice, the notion of a **maximal disjoint
family** of positive vectors, and **weak units**, and we state the main
results: every vector in a lattice with PPP is the supremum of its
principal-band projections along a maximal disjoint family; the resulting map
into a product of principal bands is a lattice homomorphic embedding with
order dense range; and every Archimedean vector lattice embeds as an order
dense sublattice into a product of order complete vector lattices with weak
units.
-/

/-! ### Projection properties -/

/-- A vector lattice has the **Projection Property** (PP) when every band in
`X` is a projection band. -/
class HasProjectionProperty (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  exists_projectionBand : ∀ B : Band X, ∃ P : ProjectionBand X,
    (P : Set X) = (B : Set X)

/-- A vector lattice has the **Principal Projection Property** (PPP) when every
principal band in `X` is a projection band. -/
class HasPrincipalProjectionProperty (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Prop where
  exists_projectionBand : ∀ a : X, ∃ P : ProjectionBand X,
    (P : Set X) = (Band.principalBand a : Set X)

/-- PP implies PPP. -/
instance (priority := 100) HasPrincipalProjectionProperty.of_hasProjectionProperty
    [HasProjectionProperty X] : HasPrincipalProjectionProperty X :=
  sorry

/-- A vector lattice with PPP is Archimedean. -/
theorem isVLArchimedean_of_hasPrincipalProjectionProperty
    [HasPrincipalProjectionProperty X] : IsVLArchimedean X :=
  sorry

/-! ### Maximal disjoint families and weak units -/

/-- A subset of `X` is **pairwise disjoint** when distinct members are
vector-lattice disjoint. -/
def IsDisjointSet (Λ : Set X) : Prop :=
  ∀ ⦃a⦄, a ∈ Λ → ∀ ⦃b⦄, b ∈ Λ → a ≠ b → IsVLDisjoint a b

/-- A **maximal disjoint family** in `X₊` is a pairwise disjoint set of strictly
positive elements that is not properly contained in any larger such set. The
order is by inclusion (not refinement). -/
def IsMaximalDisjoint (Λ : Set X) : Prop :=
  Maximal (fun S : Set X => (∀ x ∈ S, 0 < x) ∧ IsDisjointSet S) Λ

/-- A pairwise disjoint family of positive elements is maximal iff its disjoint
complement reduces to `{0}`. -/
theorem isMaximalDisjoint_iff_disjointComplement_eq_zero {Λ : Set X}
    (hpos : ∀ x ∈ Λ, 0 < x) (hdis : IsDisjointSet Λ) :
    IsMaximalDisjoint Λ ↔ Λᵈ = ({0} : Set X) :=
  sorry

/-- **Zorn's lemma.** Every vector lattice admits a maximal disjoint family of
positive vectors. -/
theorem exists_isMaximalDisjoint (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    ∃ Λ : Set X, IsMaximalDisjoint Λ :=
  sorry

/-- A positive element `e` is a **weak (order) unit** when the only element of
`X` disjoint from `e` is `0`. -/
def IsWeakOrderUnit (e : X) : Prop :=
  0 ≤ e ∧ ∀ x : X, IsVLDisjoint x e → x = 0

/-- For `a ∈ X₊`, `a` is a weak order unit of the principal band it generates. -/
theorem isWeakOrderUnit_principalBand_self [IsVLArchimedean X] {a : X}
    (ha : 0 ≤ a) :
    ∀ x ∈ Band.principalBand a, IsVLDisjoint x a → x = 0 :=
  sorry

/-! ### Principal band projections under PPP -/

namespace Band

/-- Under PPP, the principal band generated by `a` is a (chosen) projection
band. -/
noncomputable def principalProjectionBand [HasPrincipalProjectionProperty X]
    (a : X) : ProjectionBand X :=
  (HasPrincipalProjectionProperty.exists_projectionBand a).choose

/-- The chosen projection band has the same underlying set as `principalBand a`. -/
theorem principalProjectionBand_coe [HasPrincipalProjectionProperty X]
    (a : X) :
    ((principalProjectionBand a : ProjectionBand X) : Set X)
      = (principalBand a : Set X) :=
  (HasPrincipalProjectionProperty.exists_projectionBand a).choose_spec

/-- The band projection onto the principal band generated by `a`, available
under PPP. We write `Pₐ` informally for this map. -/
noncomputable def principalBandProjection [HasPrincipalProjectionProperty X]
    (a : X) : X →ₗ[ℝ] X :=
  (principalProjectionBand a).bandProjection

end Band

/-! ### Decomposition Lemma -/

open Band in
/-- Let `X` have PPP and let `Λ` be a maximal disjoint family in `X₊`. For
every `x ∈ X₊`, `x` is the supremum of the family `(Pₐ x)_{a ∈ Λ}`, where `Pₐ`
is the band projection onto the principal band generated by `a`. -/
theorem isLUB_principalBandProjection_of_isMaximalDisjoint
    [HasPrincipalProjectionProperty X] {Λ : Set X} (hΛ : IsMaximalDisjoint Λ)
    {x : X} (hx : 0 ≤ x) :
    IsLUB (Set.range fun a : Λ => principalBandProjection (a : X) x) x :=
  sorry

/-! The next two consequences of the Decomposition Lemma — that `T x a := Pₐ x`
is an order dense lattice embedding into the product `Λ → X`, and that every
Archimedean vector lattice embeds as an order dense sublattice into a product
of order complete vector lattices with weak units — live in `BanLat/Pi.lean`,
since they are statements about products. -/

/-! **Decomposition Lemma.** In an order continuous Banach lattice, fix a
maximal disjoint family `Λ` in `X₊`. For every `x ∈ X`, only countably many
of the principal-band projections `Pz x` are non-zero, and `x` is the sum of
those terms. The statement requires `IsOrderContinuousNorm`, which is
introduced downstream of `Band.lean`, so the formal version lives in
`BanLat/OrderContinuous.lean`. -/
