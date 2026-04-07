import BanLat.AMSpace
import BanLat.Examples.CofK
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Kakutani's representation theorem for AM-spaces with unit

(Bohnenblust–Kakutani–Krein) Every AM-space with unit `(X, e)` is lattice
isometrically isomorphic to `C(K, ℝ)` for the compact Hausdorff space `K` of
*lattice characters* of `X`: the real-valued vector lattice homomorphisms
`X → ℝ` normalised by `φ e = 1`. Under the isomorphism — the Gelfand transform
sending `x` to evaluation `φ ↦ φ x` — the unit `e` corresponds to the constant
function `1`.
-/

namespace AMSpaceWithUnit

variable (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [AMSpaceWithUnit X]

/-! ### Lattice characters -/

/-- A **lattice character** of an AM-space with unit `(X, e)` is a real-valued
vector lattice homomorphism `X → ℝ` that maps the unit `e` to `1`. -/
structure LatticeCharacter extends VecLatHom X ℝ where
  /-- A lattice character maps the unit to `1`. -/
  map_unit : toVecLatHom (e : X) = 1

namespace LatticeCharacter

variable {X}

/-- The canonical `FunLike` instance, making `LatticeCharacter X` a type of
functions `X → ℝ`. -/
instance instFunLike : FunLike (LatticeCharacter X) X ℝ where
  coe φ := fun x => φ.toVecLatHom x
  coe_injective' := by
    intro φ ψ h
    cases φ; cases ψ
    congr
    exact DFunLike.coe_injective h

@[simp] theorem coe_mk (f : VecLatHom X ℝ) (hf : f (e : X) = 1) (x : X) :
    (mk f hf : X → ℝ) x = f x := rfl

@[simp] theorem map_unit_apply (φ : LatticeCharacter X) :
    φ (e : X) = 1 := φ.map_unit

/-- A lattice character preserves `⊔`. -/
theorem map_sup (φ : LatticeCharacter X) (x y : X) :
    φ (x ⊔ y) = max (φ x) (φ y) :=
  φ.toVecLatHom.toLatticeHom.map_sup' x y

/-- A lattice character preserves `⊓`. -/
theorem map_inf (φ : LatticeCharacter X) (x y : X) :
    φ (x ⊓ y) = min (φ x) (φ y) :=
  φ.toVecLatHom.toLatticeHom.map_inf' x y

/-- A lattice character is monotone. -/
theorem monotone (φ : LatticeCharacter X) : Monotone (φ : X → ℝ) :=
  φ.toVecLatHom.monotone

/-- A lattice character sends positive elements to non-negative reals. -/
theorem nonneg_apply (φ : LatticeCharacter X) {x : X} (hx : 0 ≤ x) : 0 ≤ φ x :=
  φ.toVecLatHom.map_nonneg hx

/-- The fundamental norm bound for a lattice character: `|φ x| ≤ ‖x‖`. This
follows from `|x| ≤ ‖x‖ • e` and the fact that `φ` is a positive linear map
sending `e` to `1`. -/
theorem abs_apply_le_norm (φ : LatticeCharacter X) (x : X) : |φ x| ≤ ‖x‖ := by
  have h1 : |(φ x : ℝ)| = φ.toVecLatHom |x| := (φ.toVecLatHom.map_abs x).symm
  have h2 : φ.toVecLatHom (‖x‖ • e) = ‖x‖ := by
    rw [map_smul, φ.map_unit, smul_eq_mul, mul_one]
  rw [h1, ← h2]
  exact φ.toVecLatHom.monotone (abs_le_norm_smul_unit x)

/-- A lattice character is a continuous functional. -/
theorem continuous (φ : LatticeCharacter X) : Continuous (φ : X → ℝ) := by
  have h : Continuous (φ.toVecLatHom.toLinearMap : X → ℝ) :=
    AddMonoidHomClass.continuous_of_bound φ.toVecLatHom.toLinearMap 1 fun x => by
      rw [Real.norm_eq_abs, one_mul]; exact abs_apply_le_norm φ x
  exact h

variable (X)

/-- The character space is topologised as a subspace of `X → ℝ` with the
product topology. Equivalently, this is the weak* topology inherited from the
norm dual of `X`. -/
instance instTopologicalSpace : TopologicalSpace (LatticeCharacter X) :=
  TopologicalSpace.induced (fun φ : LatticeCharacter X => (φ : X → ℝ))
    Pi.topologicalSpace

/-- For each `x : X`, the evaluation `φ ↦ φ x` is continuous. -/
theorem continuous_eval (x : X) :
    Continuous (fun φ : LatticeCharacter X => φ x) :=
  (continuous_apply x).comp continuous_induced_dom

/-- The character space is Hausdorff. -/
instance instT2Space : T2Space (LatticeCharacter X) :=
  T2Space.of_injective_continuous (f := fun φ : LatticeCharacter X => (φ : X → ℝ))
    DFunLike.coe_injective continuous_induced_dom

/-- The character space is compact. By Banach–Alaoglu, the dual unit ball is
weak*-compact, and the lattice characters form a weak*-closed subset. -/
instance instCompactSpace : CompactSpace (LatticeCharacter X) := sorry

/-- The character space is non-empty. By Hahn–Banach extend the functional
`r • e ↦ r` from the line `ℝ • e` to a positive functional on `X`, then take
an extreme point of the convex compact set of positive functionals normalised
at `e`; that extreme point is a lattice character. -/
instance instNonempty : Nonempty (LatticeCharacter X) := sorry

end LatticeCharacter

/-! ### The Gelfand transform -/

variable {X}

/-- The **Gelfand transform** sends an element `x : X` to the continuous
function `φ ↦ φ x` on the character space. -/
noncomputable def gelfand (x : X) : C(LatticeCharacter X, ℝ) where
  toFun φ := φ x
  continuous_toFun := LatticeCharacter.continuous_eval X x

@[simp] theorem gelfand_apply (x : X) (φ : LatticeCharacter X) :
    gelfand x φ = φ x := rfl

@[simp] theorem gelfand_unit : gelfand (e : X) = 1 := by
  ext φ
  exact φ.map_unit

/-- The Gelfand transform separates points: for every nonzero `x : X` there is
a lattice character `φ` with `φ x ≠ 0`. -/
theorem exists_latticeCharacter_ne_zero {x : X} (hx : x ≠ 0) :
    ∃ φ : LatticeCharacter X, φ x ≠ 0 := sorry

/-- The Gelfand transform is a vector lattice homomorphism. -/
theorem gelfand_isVecLatHom :
    IsVecLatHom (gelfand : X → C(LatticeCharacter X, ℝ)) where
  map_add x y := by ext φ; exact map_add φ.toVecLatHom x y
  map_smul r x := by ext φ; exact map_smul φ.toVecLatHom r x
  map_sup' x y := by
    ext φ
    change φ (x ⊔ y) = max (φ x) (φ y)
    exact LatticeCharacter.map_sup φ x y
  map_inf' x y := by
    ext φ
    change φ (x ⊓ y) = min (φ x) (φ y)
    exact LatticeCharacter.map_inf φ x y

/-- The Gelfand transform is an isometry: `‖gelfand x‖ = ‖x‖` for every `x`. -/
theorem norm_gelfand (x : X) :
    ‖(gelfand x : C(LatticeCharacter X, ℝ))‖ = ‖x‖ := sorry

/-- The Gelfand transform is surjective. The image is a unital sublattice of
`C(K, ℝ)` that separates points, and the lattice version of the
Stone–Weierstrass theorem identifies the closed unital sublattice generated by
such a family with all of `C(K, ℝ)`. -/
theorem gelfand_surjective :
    Function.Surjective (gelfand : X → C(LatticeCharacter X, ℝ)) := sorry

/-! ### Kakutani's theorem -/

variable (X)

/-- **Kakutani's representation theorem** for AM-spaces with unit. Every
AM-space with unit `(X, e)` is Banach-lattice isomorphic to `C(K, ℝ)` for the
compact Hausdorff space `K = LatticeCharacter X` of its lattice characters,
via the Gelfand transform `x ↦ (φ ↦ φ x)`. -/
noncomputable def kakutaniEquiv :
    BanachLatEquiv X C(LatticeCharacter X, ℝ) := sorry

variable {X}

@[simp] theorem kakutaniEquiv_apply (x : X) (φ : LatticeCharacter X) :
    kakutaniEquiv X x φ = φ x := sorry

/-- Under the Kakutani isomorphism, the unit `e` corresponds to the constant
function `1`. -/
theorem kakutaniEquiv_unit :
    kakutaniEquiv X (e : X) = 1 := sorry

end AMSpaceWithUnit
