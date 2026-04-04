import BanLat.Basic
import Mathlib.Order.Sublattice

/-!
# Sublattices of vector lattices

A **vector sublattice** of a vector lattice is a linear subspace that is closed under the
lattice operations. Since all lattice operations are expressible in terms of each other, it
suffices that the subspace be closed under any one operation — for example, `⊔` or `|·|`.
The key characterisation proved here is that closure under absolute value is equivalent to
the sublattice property.
-/

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- A `VectorSublattice` of a vector lattice `X` is a linear subspace closed under
`⊔`. This is the bundled version: it extends `Submodule ℝ X` with lattice closure. -/
structure VectorSublattice (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] extends Submodule ℝ X where
  sup_mem' : ∀ {x y : X}, x ∈ carrier → y ∈ carrier → x ⊔ y ∈ carrier

namespace VectorSublattice

instance : SetLike (VectorSublattice X) X where
  coe Y := Y.carrier
  coe_injective' p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

variable (Y : VectorSublattice X)

/-- A vector sublattice is closed under `⊔`. -/
theorem sup_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x ⊔ y ∈ Y :=
  Y.sup_mem' hx hy

/-- A vector sublattice is closed under `⊓`. -/
theorem inf_mem {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    x ⊓ y ∈ Y := by
  rw [inf_eq_sub_posPart x y]
  exact Y.toSubmodule.sub_mem hx (Y.sup_mem' (Y.toSubmodule.sub_mem hx hy) (Y.toSubmodule.zero_mem))

/-- A vector sublattice is closed under the positive part. -/
theorem posPart_mem {x : X} (hx : x ∈ Y) : x⁺ ∈ Y :=
  Y.sup_mem' hx (Y.toSubmodule.zero_mem)

/-- A vector sublattice is closed under the negative part. -/
theorem negPart_mem {x : X} (hx : x ∈ Y) : x⁻ ∈ Y :=
  posPart_mem Y (Y.toSubmodule.neg_mem hx)

/-- A vector sublattice is closed under absolute value. -/
theorem abs_mem {x : X} (hx : x ∈ Y) : |x| ∈ Y :=
  sup_mem Y hx (Y.toSubmodule.neg_mem hx)

/-- The underlying set of a vector sublattice is an `IsSublattice`. -/
theorem isSublattice : IsSublattice (Y : Set X) where
  supClosed := by intro _ ha _ hb; exact sup_mem Y ha hb
  infClosed := by intro _ ha _ hb; exact inf_mem Y ha hb

/-! ### Construction from absolute-value closure -/

/-- The positive part lies in a submodule closed under absolute value. -/
private theorem posPart_mem_of_absClosed (M : Submodule ℝ X)
    (h : ∀ x : X, x ∈ M → |x| ∈ M) {x : X} (hx : x ∈ M) : x⁺ ∈ M := by
  have key : x + |x| = 2 • x⁺ := add_abs_eq_two_nsmul_posPart x
  have h2 : (2 : ℝ)⁻¹ • (x + |x|) = x⁺ := by
    rw [key, ← Nat.cast_smul_eq_nsmul ℝ 2]; norm_num [smul_smul]
  rw [← h2]
  exact M.smul_mem _ (M.add_mem hx (h x hx))

/-- Build a `VectorSublattice` from a submodule closed under `|·|`. -/
def ofAbsClosed (M : Submodule ℝ X)
    (h : ∀ x : X, x ∈ M → |x| ∈ M) : VectorSublattice X where
  toSubmodule := M
  sup_mem' := fun {x y} hx hy => by
    rw [sup_eq_add_posPart x y]
    exact M.add_mem hx (posPart_mem_of_absClosed M h (M.sub_mem hy hx))

/-- A submodule is a vector sublattice iff it is closed under absolute value. -/
theorem abs_mem_iff_sup_mem (M : Submodule ℝ X) :
    (∀ x : X, x ∈ M → |x| ∈ M) ↔
      ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by
  constructor
  · intro h x y hx hy
    exact (ofAbsClosed M h).sup_mem' hx hy
  · intro h x hx
    exact h x (-x) hx (M.neg_mem hx)

/-! ### The whole space -/

/-- The whole space is a vector sublattice. -/
instance : Top (VectorSublattice X) where
  top := {
    toSubmodule := ⊤
    sup_mem' := fun _ _ => Submodule.mem_top
  }

/-- Every element belongs to `⊤`. -/
@[simp]
theorem mem_top {x : X} : x ∈ (⊤ : VectorSublattice X) :=
  Submodule.mem_top

/-! ### Coercion to submodule -/

/-- The coercion to `Submodule ℝ X` is injective. -/
theorem toSubmodule_injective :
    Function.Injective
      (toSubmodule : VectorSublattice X → Submodule ℝ X) := by
  intro p q h
  cases p; cases q; congr

end VectorSublattice
