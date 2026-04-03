import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Tactic

/-!
# Lattice-ordered groups and vector lattices

This file develops the basic order-theoretic algebra of lattice-ordered groups and vector
lattices. The first part works in the general setting of an additive commutative group with a
compatible lattice order (`IsOrderedAddMonoid`): it establishes properties of `x⁺`, `x⁻`,
and `|x|`, a uniqueness result for the positive part, and the Riesz decomposition theorem.
The second part adds a real scalar multiplication (`VectorLattice`) and proves that positive
scalars distribute over `⊔` and `⊓`, culminating in `abs_smul'`. The Archimedean case is
treated at the end.
-/

class VectorLattice (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] extends
  Module ℝ X,
  PosSMulMono ℝ X

section LatticeOrderedGroup

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

variable (x : X)

/-- An element of a lattice-ordered group is zero iff its absolute value is zero.
Extends `Mathlib.Algebra.Order.Module.Basic.abs_eq_zero` to the non-total-order setting. -/
theorem abs_eq_zero_iff_zero : |x| = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← negPart_add_posPart, add_eq_zero_iff_eq_neg] at h
    have h1 : x⁺ = 0 := by
      apply le_antisymm
      · rw [← neg_zero]
        apply le_neg_of_le_neg
        rw [← h]
        exact negPart_nonneg x
      · exact posPart_nonneg x
    have h2 : x⁻ = 0 := by
      apply le_antisymm
      · rw [h]
        apply neg_le_of_neg_le
        rw [neg_zero]
        exact posPart_nonneg x
      · exact negPart_nonneg x
    rw [← posPart_sub_negPart x]
    rw [h1, h2]
    simp
  · intro h
    simp [h]

/-- If `x = u - v` with `u ⊓ v = 0`, then `u` is the positive part of `x`. -/
theorem uniqueness_posPart {u v : X} (hdif : x = u - v) (udisv : u ⊓ v = 0) :
    u = x⁺ := by
  symm
  calc
         x⁺ = x ⊔ 0 := by rfl
         _ = (u - v) ⊔ 0 := by rw [hdif]
         _ = u ⊔ v + (-v) := by rw [add_comm, add_sup]; simp [sub_eq_add_neg, add_comm]
         _ = u + v + (-v) := by rw [← inf_add_sup u v, udisv, zero_add]
         _ = u := by simp

/-- Riesz decomposition: if `0 ≤ x ≤ y + z` with `y, z ≥ 0`, then `x = x₁ + x₂`
with `0 ≤ x₁ ≤ y` and `0 ≤ x₂ ≤ z`. -/
theorem riesz_decomposition (y z : X) (xnonneg : 0 ≤ x) (ynonneg : 0 ≤ y)
  (znonneg : 0 ≤ z) (h : x ≤ y + z) : ∃ x1 x2 : X, (0 ≤ x1) ∧ (x1 ≤ y) ∧
  (0 ≤ x2) ∧ (x2 ≤ z) ∧ (x = x1 + x2) := by
    use (x ⊓ y); use (x - x ⊓ y)
    repeat (any_goals constructor)
    · exact le_inf xnonneg ynonneg
    · exact inf_le_right
    · simp
    · rw [sub_inf]
      have : x - y ≤ z := by
        calc
          x - y = x + (-y) := by rw [sub_eq_add_neg]
              _ ≤ (y + z) + (-y) := by apply add_le_add h (le_refl (-y))
              _ ≤ z := by simp
      rw [le_iff_posPart_negPart] at this
      rw [sub_self, sup_comm, ← posPart_def]
      rw [← posPart_of_nonneg znonneg]
      exact this.1
    · simp

/-- `x ⊔ y = x + (y - x)⁺`. -/
theorem sup_eq_add_posPart (y : X) : x ⊔ y = x + (y - x)⁺ := by
  rw [posPart_def, add_sup, add_sub_cancel, add_zero, sup_comm]

/-- `x ⊓ y = x - (x - y)⁺`. -/
theorem inf_eq_sub_posPart (y : X) : x ⊓ y = x - (x - y)⁺ := by
  rw [posPart_def, sub_eq_add_neg, neg_sup, neg_sub, neg_zero, add_inf, add_zero, inf_comm]
  congr 1; abel

/-- `x - x ⊓ y = (x - y)⁺`. -/
theorem sub_inf_eq_posPart (y : X) : x - x ⊓ y = (x - y)⁺ := by
  rw [inf_eq_sub_posPart, sub_sub_cancel]

/-- The positive part is subadditive: `(x + y)⁺ ≤ x⁺ + y⁺`. -/
theorem posPart_add_le (y : X) : (x + y)⁺ ≤ x⁺ + y⁺ :=
  sup_le (add_le_add (le_posPart x) (le_posPart y))
    (add_nonneg (posPart_nonneg x) (posPart_nonneg y))

/-- For non-negative `x`, `a`, `b`: `x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b`. -/
theorem inf_le_inf_add_inf_of_nonneg (a b : X) (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x ⊓ (a + b) ≤ x ⊓ a + x ⊓ b := by
  obtain ⟨c1, c2, hc1nn, hc1a, hc2nn, hc2b, hsum⟩ :=
    riesz_decomposition (x ⊓ (a + b)) a b (le_inf hx (add_nonneg ha hb)) ha hb inf_le_right
  have hc1x : c1 ≤ x := le_trans (le_add_of_nonneg_right hc2nn) (hsum ▸ inf_le_left)
  have hc2x : c2 ≤ x := le_trans (le_add_of_nonneg_left hc1nn) (hsum ▸ inf_le_left)
  calc x ⊓ (a + b) = c1 + c2 := hsum
    _ ≤ x ⊓ a + x ⊓ b := add_le_add (le_inf hc1x hc1a) (le_inf hc2x hc2b)

end LatticeOrderedGroup

section VectorLattice

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

variable (x y : X)

/-- A non-negative scalar distributes over `⊔`. -/
theorem nonneg_smul_sup (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊔ y) = (a • x) ⊔ (a • y) := by
  by_cases h : a = 0
  · subst h
    simp only [zero_smul]; exact Eq.symm Std.max_self
  · apply le_antisymm
    · have hx : a⁻¹ • a • x ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_left
         (by norm_num [nonneg])
      have hy : a⁻¹ • a • y ≤ a⁻¹ • (a • x ⊔ a • y) := by
        exact smul_le_smul_of_nonneg_left
         le_sup_right
         (by norm_num [nonneg])
      simp [h] at hx hy
      have hxy : x ⊔ y ≤ a⁻¹ • (a • x ⊔ a • y) :=
        sup_le hx hy
      calc
        a • (x ⊔ y) ≤ a • (a⁻¹ • (a • x ⊔ a • y)) := by
                      exact smul_le_smul_of_nonneg_left hxy nonneg
                  _ = a • x ⊔ a • y := by rw [smul_smul a a⁻¹ _]; norm_num [h];
    · have hx : a • x ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_left nonneg
      have hy : a • y ≤ a • (x ⊔ y) :=
        smul_le_smul_of_nonneg_left le_sup_right nonneg
      exact sup_le hx hy

/-- A non-negative scalar distributes over `⊓`. -/
theorem nonneg_smul_inf (a : ℝ) (nonneg : a ≥ 0) :
  a • (x ⊓ y) = (a • x) ⊓ (a • y) := by
    calc
      a • (x ⊓ y) = (-1) • a • (- (x ⊓ y)) := by simp
                _ = (-1) • a • ((-x) ⊔ (-y)) := by rw [neg_inf]
                _ = (-1) • ((a • -x) ⊔ (a • -y)) := by rw [nonneg_smul_sup (-x) (-y) a nonneg]
                _ = - ((-a • x) ⊔ (-a • y)) := by simp
                _ = (a • x) ⊓ (a • y) := by rw [neg_sup]; simp

/-- Scalar `sup` distributes over a non-negative element. -/
theorem sup_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊔ b) • x = (a • x) ⊔ (b • x) := by
  apply le_antisymm
  · cases max_choice a b with
      | inl h => rw [h]; exact le_sup_left
      | inr h => rw [h]; exact le_sup_right
  · apply sup_le
    · exact smul_le_smul_of_nonneg_right le_sup_left h
    · exact smul_le_smul_of_nonneg_right le_sup_right h

/-- Scalar `inf` distributes over a non-negative element. -/
theorem inf_smul_nonneg (a b : ℝ) (h : 0 ≤ x) :
    (a ⊓ b) • x = (a • x) ⊓ (b • x) := by
  apply le_antisymm
  · apply le_inf
    · exact smul_le_smul_of_nonneg_right inf_le_left h
    · exact smul_le_smul_of_nonneg_right inf_le_right h
  · cases min_choice a b with
      | inl h => rw [h]; exact inf_le_left
      | inr h => rw [h]; exact inf_le_right

/-- `|a • x| = |a| • |x|` in a vector lattice.
Extends the Mathlib result of the same name from total orders to lattice orders. -/
theorem abs_smul' (a : ℝ) : |a • x| = |a| • |x| := by
  by_cases ha : a ≥ 0
  · rw [abs_of_nonneg ha]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) a ha]
    simp
  · have hna : a < 0 := by linarith
    rw [abs_of_neg hna]
    rw [abs, abs]
    rw [nonneg_smul_sup x (-x) (-a) (by linarith)]
    simp [sup_comm]

/-- Scaling a disjoint pair preserves disjointness: if `x ⊓ y = 0` and `a ≥ 0`,
then `(a • x) ⊓ y = 0`. -/
theorem disjoint_smul (a : ℝ) (nonneg : 0 ≤ a) (h : x ⊓ y = 0) :
    (a • x) ⊓ y = 0 := by
  let aux (x y : X) (h : x ⊓ y = 0) (a : ℝ)
  (nonneg : 0 ≤ a) (hone : a ≤ 1) : (a • x) ⊓ y = 0 := by
    have xnonneg : 0 ≤ x := by rw [← h]; exact inf_le_left
    have ynonneg : 0 ≤ y := by rw [← h]; exact inf_le_right
    apply le_antisymm
    · calc
        a • x ⊓ y ≤ (1 : ℝ) • x ⊓ y := by
            apply inf_le_inf
            · exact smul_le_smul_of_nonneg_right hone xnonneg
            · exact le_refl y
          _ = 0 := by simp [h]
    · apply le_inf
      · exact smul_nonneg nonneg xnonneg
      · exact ynonneg
  have (hone : ¬ a ≤ 1) : (a • x) ⊓ y = 0 := by
    push_neg at hone
    suffices x ⊓ (a⁻¹ • y) = 0 from by
      symm
      calc
        0 = a • ( x ⊓ (a⁻¹ • y) ):= by rw [this, smul_zero]
        _ = (a • x ⊓ a • a⁻¹ • y) := by
            exact nonneg_smul_inf x (a⁻¹ • y) a nonneg
        _ = (a • x) ⊓ y := by rw [smul_smul]; field_simp [hone]; simp
    rw [inf_comm]
    rw [inf_comm] at h
    refine aux y x h a⁻¹ ?nonneg ?one
    · exact inv_nonneg.mpr nonneg
    · field_simp
      exact (le_of_lt hone)
  by_cases hone : a ≤ 1
  · exact aux x y h a nonneg hone
  · exact this hone

section Archimedean

/-- A lattice-ordered group is **Archimedean** (in the vector-lattice sense) when the only
non-negative element all of whose multiples are bounded is zero: `0 ≤ x` and `∀ n, n • x ≤ y`
imply `x = 0`. This is the standard Archimedean property for partially ordered groups; it is
weaker than Mathlib's `Archimedean` class, which is stated for linearly ordered monoids. -/

class IsVLArchimedean (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] : Prop where
  eq_zero_of_nonneg_of_forall_nsmul_le {x y : X} :
    0 ≤ x → (∀ n : ℕ, n • x ≤ y) → x = 0

variable [IsVLArchimedean X]

/-- An element whose absolute-value multiples are bounded must be zero. -/
theorem infinitesimal_eq_zero {x y : X}
    (h : ∀ n : ℕ, n • |x| ≤ y) : x = 0 := by
  have hab : |x| = 0 :=
    IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le (abs_nonneg x) h
  exact (abs_eq_zero_iff_zero x).mp hab

/-- In an Archimedean vector lattice, if `n • x ≤ y` for all `n : ℕ`, then `x ≤ 0`. -/
theorem le_zero_of_forall_nsmul_le {x y : X} (h : ∀ n : ℕ, n • x ≤ y) : x ≤ 0 := by
  apply (le_iff_posPart_negPart x 0).mpr
  constructor
  · have : ∀ n : ℕ, n • x⁺ ≤ y⁺ := by
      intro n
      calc
        n • x⁺ = n • (x ⊔ 0) := by rw [posPart_def]
             _ = (n:ℝ) • (x ⊔ 0) := by norm_cast
             _ = ((n:ℝ) • x) ⊔ ((n:ℝ) • 0) := by
               rw [nonneg_smul_sup x 0 (n:ℝ) (by norm_num)]
             _ = ((n:ℝ) • x) ⊔ 0 := by rw [smul_zero (n:ℝ)]
             _ = ((n:ℝ) • x)⁺ := by rw [posPart_def]
             _ ≤ y⁺ := by norm_cast; exact ((le_iff_posPart_negPart (n • x) y).mp (h n)).1
    have xpos_zero : x⁺ = 0 :=
      IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le (posPart_nonneg x) this
    rw [xpos_zero]; simp
  · simp; exact negPart_nonneg x

end Archimedean

end VectorLattice
