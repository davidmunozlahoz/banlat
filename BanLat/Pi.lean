/-
Authors: David Muñoz-Lahoz, Pedro Tradacete
-/

import BanLat.Normed
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Products of vector, normed and Banach lattices

Pointwise products of vector lattices carry a vector lattice structure. For a finite index
set and `1 ≤ p ≤ ∞`, the product `PiLp p X` of normed (resp. Banach) lattices is again a normed
(resp. Banach) lattice. Binary products `WithLp 1 (A × B)` have the coordinatewise lattice
structure and the norm `‖(a, b)‖ = ‖a‖ + ‖b‖`, and are Banach lattices when both factors are.
-/

open scoped ENNReal

/-! ### Pointwise product -/

namespace Pi

variable {ι : Type*} {X : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Lattice (X i)] [∀ i, IsOrderedAddMonoid (X i)]
  [∀ i, VectorLattice (X i)]

/-- The pointwise product of a family of vector lattices is a vector lattice.
The lattice operations and absolute value are computed pointwise (see
`Pi.sup_apply`, `Pi.inf_apply`, `Pi.abs_apply` in Mathlib). -/
instance instVectorLattice : VectorLattice (∀ i, X i) := ⟨⟩

end Pi

/-! ### ℓ^p product

For a finite index set `ι` and `1 ≤ p ≤ ∞`, the ℓ^p product of normed vector
lattices is again a normed vector lattice, and Banachness is preserved. The
order structure is pointwise; only the norm depends on `p`.
-/

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : ι → Type*}

section Order

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

/-- Pointwise `≤` on `PiLp p X`. -/
instance instLE : LE (PiLp p X) where
  le x y := ∀ i, x i ≤ y i

/-- Pointwise `<` on `PiLp p X`. -/
instance instLT : LT (PiLp p X) where
  lt x y := WithLp.ofLp x < WithLp.ofLp y

/-- Pointwise `⊔` on `PiLp p X`. -/
instance instMax : Max (PiLp p X) where
  max x y := WithLp.toLp p (fun i => x i ⊔ y i)

/-- Pointwise `⊓` on `PiLp p X`. -/
instance instMin : Min (PiLp p X) where
  min x y := WithLp.toLp p (fun i => x i ⊓ y i)

/-- Pointwise lattice structure on `PiLp p X`. -/
instance instLattice : Lattice (PiLp p X) :=
  Function.Injective.lattice (β := ∀ i, X i) WithLp.ofLp (WithLp.ofLp_injective p)
    Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- The order on `PiLp p X` is compatible with addition. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (PiLp p X) :=
  Function.Injective.isOrderedAddMonoid (β := PiLp p X) (α := ∀ i, X i)
    WithLp.ofLp (fun _ _ => rfl) Iff.rfl

/-- The ℓ^p norm is solid: `|x| ≤ |y|` implies `‖x‖ ≤ ‖y‖`. -/
instance instHasSolidNorm [∀ i, HasSolidNorm (X i)] : HasSolidNorm (PiLp p X) where
  solid := fun x y h => by
    -- pointwise bound on norms via the solid norm of each factor
    have hpt : ∀ i, ‖x i‖ ≤ ‖y i‖ := fun i =>
      HasSolidNorm.solid (α := X i) (h i)
    rcases eq_or_ne p ∞ with hp | hp
    · subst hp
      simp only [PiLp.norm_eq_ciSup]
      exact ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) hpt
    · have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
      have hpos : 0 < p.toReal := by
        have := ENNReal.toReal_lt_toReal (by norm_num) hp |>.mpr
          (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) h1)
        simpa using this
      simp only [PiLp.norm_eq_sum hpos]
      gcongr with i
      exact hpt i

end Order

/-! #### Vector and Banach lattice structure -/

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

instance instPosSMulMono [∀ i, NormedVectorLattice (X i)] :
    PosSMulMono ℝ (PiLp p X) where
  smul_le_smul_of_nonneg_left := by
    intro a ha b₁ b₂ hb i
    exact smul_le_smul_of_nonneg_left (hb i) ha

/-- The ℓ^p product of normed vector lattices is a vector lattice. -/
instance instVectorLattice [∀ i, NormedVectorLattice (X i)] :
    VectorLattice (PiLp p X) := ⟨⟩

/-- The ℓ^p product of normed vector lattices is a normed vector lattice. -/
instance instNormedVectorLattice [∀ i, NormedVectorLattice (X i)] :
    NormedVectorLattice (PiLp p X) where

/-- The ℓ^p product of Banach lattices is a Banach lattice. -/
instance instBanachLattice [∀ i, BanachLattice (X i)] :
    BanachLattice (PiLp p X) where

end PiLp

/-! ### Binary products -/

namespace WithLp

variable {A B : Type*} {p : ℝ≥0∞}

/-- The lattice operations on a binary `WithLp` product are computed coordinatewise. -/
instance instProdLattice [Lattice A] [Lattice B] : Lattice (WithLp p (A × B)) :=
  (WithLp.equiv p (A × B)).lattice

section Algebra

variable [AddCommGroup A] [AddCommGroup B] [Lattice A] [Lattice B]
  [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]

/-- Addition respects the coordinatewise order on a binary `WithLp` product. -/
instance instProdIsOrderedAddMonoid : IsOrderedAddMonoid (WithLp p (A × B)) :=
  Function.Injective.isOrderedAddMonoid (α := A × B) (β := WithLp p (A × B))
    WithLp.ofLp (fun _ _ ↦ rfl) Iff.rfl

/-- A binary `WithLp` product of vector lattices is a vector lattice. -/
instance instProdVectorLattice [VectorLattice A] [VectorLattice B] :
    VectorLattice (WithLp p (A × B)) where
  smul_le_smul_of_nonneg_left _ hr _ _ h :=
    ⟨smul_le_smul_of_nonneg_left h.1 hr, smul_le_smul_of_nonneg_left h.2 hr⟩

end Algebra

section Norm

variable [NormedAddCommGroup A] [NormedAddCommGroup B] [Lattice A] [Lattice B]
  [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]

/-- The sum norm on a binary `ℓ¹` product is solid when both factor norms are solid. -/
instance instProdHasSolidNormL1 [HasSolidNorm A] [HasSolidNorm B] :
    HasSolidNorm (WithLp 1 (A × B)) where
  solid x y h := by
    change |x.fst| ≤ |y.fst| ∧ |x.snd| ≤ |y.snd| at h
    simpa only [prod_norm_eq_of_L1] using
      add_le_add (HasSolidNorm.solid (α := A) h.1) (HasSolidNorm.solid (α := B) h.2)

/-- The binary `ℓ¹` product of normed vector lattices is a normed vector lattice. -/
instance instProdNormedVectorLatticeL1 [NormedVectorLattice A] [NormedVectorLattice B] :
    NormedVectorLattice (WithLp 1 (A × B)) where

/-- The binary `ℓ¹` product of Banach lattices is a Banach lattice. -/
instance instProdBanachLatticeL1 [BanachLattice A] [BanachLattice B] :
    BanachLattice (WithLp 1 (A × B)) where

end Norm

end WithLp
