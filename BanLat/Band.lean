import BanLat.Ideal
import BanLat.Hom

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

@[simp]
theorem isVLDisjoint_comm {x y : X} :
    IsVLDisjoint x y ↔ IsVLDisjoint y x := by
  sorry

/-- Zero is disjoint from every element. -/
theorem isVLDisjoint_zero_left (x : X) : IsVLDisjoint 0 x := by
  sorry

/-- Disjoint positive elements satisfy `x ⊓ y = 0`. -/
theorem inf_eq_zero_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsVLDisjoint x y) : x ⊓ y = 0 := by
  sorry

/-- If `x ⊓ y = 0` then `x` and `y` are disjoint. -/
theorem isVLDisjoint_of_inf_eq_zero {x y : X}
    (h : x ⊓ y = 0) : IsVLDisjoint x y := by
  sorry

/-- Disjoint decomposition is unique: if `x = u₁ - v₁ = u₂ - v₂` with
`u₁ ⊥ v₁` and `u₂ ⊥ v₂` (all non-negative), then `u₁ = u₂` and
`v₁ = v₂`. -/
theorem isVLDisjoint_decomposition_unique {u₁ v₁ u₂ v₂ : X}
    (hu₁ : 0 ≤ u₁) (hv₁ : 0 ≤ v₁) (hu₂ : 0 ≤ u₂) (hv₂ : 0 ≤ v₂)
    (hd₁ : IsVLDisjoint u₁ v₁) (hd₂ : IsVLDisjoint u₂ v₂)
    (h : u₁ - v₁ = u₂ - v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  sorry

/-- If `x ⊥ y` then `|x + y| = |x| + |y|` (Birkhoff identity). -/
theorem abs_add_of_isVLDisjoint {x y : X} (h : IsVLDisjoint x y) :
    |x + y| = |x| + |y| := by
  sorry

/-- If `x ⊥ y` then `|x ⊔ y| = |x| ⊔ |y|`. -/
theorem abs_sup_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : IsVLDisjoint x y) : |x ⊔ y| = |x| ⊔ |y| := by
  sorry

/-! ### Disjoint complement -/

/-- The **disjoint complement** of a set `A ⊆ X` is the set of all elements
disjoint from every member of `A`. -/
def disjointComplement (A : Set X) : Set X :=
  {x : X | ∀ a ∈ A, IsVLDisjoint x a}

postfix:max "ᵈ" => disjointComplement

/-- Anti-monotonicity: if `A ⊆ B` then `Bᵈ ⊆ Aᵈ`. -/
theorem disjointComplement_anti {A B : Set X} (h : A ⊆ B) :
    Bᵈ ⊆ Aᵈ := by
  sorry

/-- The intersection of a set with its disjoint complement is `{0}`. -/
theorem disjointComplement_inter_eq_zero (A : Set X) :
    A ∩ Aᵈ ⊆ {0} := by
  sorry

/-- Every set is contained in its double disjoint complement. -/
theorem subset_disjointComplement_disjointComplement (A : Set X) :
    A ⊆ (Aᵈ)ᵈ := by
  sorry

/-- The triple disjoint complement equals the single disjoint complement. -/
theorem disjointComplement_disjointComplement_disjointComplement
    (A : Set X) : ((Aᵈ)ᵈ)ᵈ = Aᵈ := by
  sorry

/-- The disjoint complement of a union is the intersection of the disjoint
complements. -/
theorem disjointComplement_union (A B : Set X) :
    (A ∪ B)ᵈ = Aᵈ ∩ Bᵈ := by
  sorry

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

/-! ### The disjoint complement is a band -/

/-- The disjoint complement of any set is an order ideal. -/
def disjointComplementOrderIdeal (A : Set X) : OrderIdeal X where
  toSubmodule :=
    { carrier := Aᵈ
      add_mem' := sorry
      zero_mem' := sorry
      smul_mem' := sorry }
  sup_mem' := sorry
  solid' := sorry

/-- The disjoint complement of any set is a band. -/
def disjointComplementBand (A : Set X) : Band X where
  toOrderIdeal := disjointComplementOrderIdeal A
  directed_sSup_mem' := sorry

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Characterisation: `x ∈ Aᵈ` iff `|x| ⊓ |a| = 0` for all `a ∈ A`. -/
theorem mem_disjointComplement_iff {A : Set X} {x : X} :
    x ∈ Aᵈ ↔ ∀ a ∈ A, IsVLDisjoint x a := Iff.rfl

/-! ### Band generated by a set -/

/-- The **band generated** by a set `A` is the smallest band containing `A`. -/
def bandGenerated (A : Set X) : Band X where
  toOrderIdeal :=
    { toSubmodule :=
        { carrier := ⋂₀ {(B : Set X) | ∃ b : Band X, ↑b = B ∧ A ⊆ B}
          add_mem' := sorry
          zero_mem' := sorry
          smul_mem' := sorry }
      sup_mem' := sorry
      solid' := sorry }
  directed_sSup_mem' := sorry

/-- `A` is contained in the band it generates. -/
theorem subset_bandGenerated (A : Set X) :
    A ⊆ (bandGenerated A : Set X) := by
  sorry

/-- The band generated by `A` is the smallest band containing `A`. -/
theorem bandGenerated_le {A : Set X} {B : Band X} (h : A ⊆ ↑B) :
    (bandGenerated A : Set X) ⊆ ↑B := by
  sorry

/-- In an Archimedean vector lattice, the double disjoint complement `Aᵈᵈ` is
the band generated by `A`. -/
theorem disjointComplement_disjointComplement_eq_bandGenerated
    [IsVLArchimedean X] (A : Set X) :
    ((Aᵈ)ᵈ : Set X) = (bandGenerated A : Set X) := by
  sorry

/-! ### Characterisation of bands in the Archimedean case -/

/-- In an Archimedean vector lattice, a subset is a band iff it equals its
double disjoint complement. -/
theorem eq_disjointComplement_disjointComplement [IsVLArchimedean X]
    (B : Band X) : ((↑B : Set X)ᵈ)ᵈ = ↑B := by
  sorry

/-- In an Archimedean vector lattice, a subset is a band iff it is of the form
`Aᵈ` for some set `A`. -/
theorem exists_eq_disjointComplement [IsVLArchimedean X] (B : Band X) :
    ∃ A : Set X, Aᵈ = ↑B := by
  sorry

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
  sorry

/-- The principal ideal is contained in the principal band. -/
theorem principal_le_principalBand (a : X) :
    (OrderIdeal.principal a : Set X) ⊆ (principalBand a : Set X) := by
  sorry

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
  directed_sSup_mem' := sorry

/-- The intersection of an arbitrary family of bands is a band. -/
theorem iInter_isBand {ι : Type*} (B : ι → Band X) :
    ∃ C : Band X, (C : Set X) = ⋂ i, (B i : Set X) := by
  sorry

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
  sorry

/-- The **band projection** onto a projection band: the linear map sending
`x` to its component in `B`. -/
noncomputable def bandProjection : X →ₗ[ℝ] X where
  toFun x := (P.decomposition x).choose
  map_add' := sorry
  map_smul' := sorry

/-- The band projection is idempotent. -/
theorem bandProjection_sq :
    P.bandProjection ∘ₗ P.bandProjection = P.bandProjection := by
  sorry

/-- The band projection is positive: `0 ≤ x → 0 ≤ Px`. -/
theorem bandProjection_nonneg {x : X} (hx : 0 ≤ x) :
    0 ≤ P.bandProjection x := by
  sorry

/-- The band projection is dominated by the identity: `0 ≤ x → Px ≤ x`. -/
theorem bandProjection_le {x : X} (hx : 0 ≤ x) :
    P.bandProjection x ≤ x := by
  sorry

/-- The band projection maps into the band. -/
theorem bandProjection_mem (x : X) :
    P.bandProjection x ∈ P := by
  sorry

/-- The complement `I - P` maps into the disjoint complement. -/
theorem id_sub_bandProjection_mem (x : X) :
    x - P.bandProjection x ∈ disjointComplement (P : Set X) := by
  sorry

/-- The range of the band projection is the band itself. -/
theorem range_bandProjection :
    Set.range P.bandProjection = (P : Set X) := by
  sorry

/-- The disjoint complement of a projection band is a projection band. -/
def disjointComplementProjectionBand : ProjectionBand X where
  toBand := Band.disjointComplementBand (P : Set X)
  decomposition' := sorry

/-- An ideal `J` is a projection band iff `J + Jᵈ = X`. -/
theorem projectionBand_iff_add_disjointComplement
    (J : OrderIdeal X) :
    (∃ P : ProjectionBand X, (P : Set X) = (J : Set X)) ↔
      ∀ x : X, ∃ y z : X, y ∈ (J : Set X)
        ∧ z ∈ disjointComplement (J : Set X) ∧ x = y + z := by
  sorry

/-- If `X = J₁ ⊕ J₂` where `J₁` and `J₂` are ideals with `J₁ ⊥ J₂`, then
both are projection bands and `J₂ = J₁ᵈ`. -/
theorem of_direct_sum_of_disjoint (J₁ J₂ : OrderIdeal X)
    (hperp : ∀ x ∈ (J₁ : Set X), ∀ y ∈ (J₂ : Set X), IsVLDisjoint x y)
    (hdecomp : ∀ x : X, ∃ y ∈ (J₁ : Set X), ∃ z ∈ (J₂ : Set X),
      x = y + z) :
    disjointComplement (J₁ : Set X) = (J₂ : Set X)
      ∧ ∃ P : ProjectionBand X, (P : Set X) = (J₁ : Set X) := by
  sorry

/-! ### Characterisation of band projections -/

/-- A linear operator is a band projection iff `P² = P` and `0 ≤ P ≤ I`. -/
theorem bandProjection_iff (T : X →ₗ[ℝ] X) :
    (∃ P : ProjectionBand X, P.bandProjection = T) ↔
      T ∘ₗ T = T
        ∧ (∀ x : X, 0 ≤ x → 0 ≤ T x)
        ∧ (∀ x : X, 0 ≤ x → T x ≤ x) := by
  sorry

/-- A band projection is a lattice homomorphism. -/
theorem bandProjection_isVecLatHom :
    IsVecLatHom P.bandProjection.toFun := by
  sorry

end ProjectionBand
