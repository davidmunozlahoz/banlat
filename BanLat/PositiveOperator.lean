import BanLat.Banach

/-!
# Positive operators

A linear map between vector lattices is **positive** if it sends non-negative elements to
non-negative elements. For linear maps, positivity is equivalent to monotonicity. A positive
operator satisfies `|f x| ≤ f |x|`, and every positive operator from a Banach lattice to a
normed vector lattice is automatically continuous.
-/

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A linear map is *positive* if it sends non-negative elements to non-negative elements. -/
def Positive (f : X →ₗ[ℝ] Y) : Prop :=
  ∀ x : X, 0 ≤ x → 0 ≤ f x

namespace Positive

/-- For a linear map between vector lattices, monotonicity and positivity are equivalent. -/
theorem monotone_iff {f : X →ₗ[ℝ] Y} : Monotone f ↔ Positive f := by
  constructor
  · intro hm x hx
    simpa [map_zero] using hm hx
  · intro hp a b hab
    have h : 0 ≤ f (b - a) := hp (b - a) (sub_nonneg.mpr hab)
    rwa [map_sub, sub_nonneg] at h

/-- A positive operator satisfies `|f x| ≤ f |x|`. -/
theorem abs_le_map_abs {f : X →ₗ[ℝ] Y} (hf : Positive f) (x : X) : |f x| ≤ f |x| := by
  rw [abs]
  apply sup_le
  · exact (monotone_iff.mpr hf) (by rw [abs]; exact le_sup_left)
  · have h : f (-x) ≤ f |x| := (monotone_iff.mpr hf) (by rw [abs]; exact le_sup_right)
    rwa [map_neg] at h

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]

/-- Every positive linear operator from a Banach lattice to a normed vector lattice
is continuous. -/
theorem continuous {f : X →ₗ[ℝ] Y} (hf : Positive f) : Continuous f := by
  sorry

end Positive
