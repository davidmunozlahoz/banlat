import BanLat.Banach

/-!
# Positive operators

A linear map between vector lattices is **positive** if it sends non-negative elements to
non-negative elements. For linear maps, positivity is equivalent to monotonicity. A positive
operator satisfies `|f x| ≤ f |x|`, and every positive operator from a Banach lattice to a
normed vector lattice is automatically continuous. As a corollary, every vector lattice
isomorphism between Banach lattices is a Banach space isomorphism.
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

private lemma norm_map_le_of_abs_le {f : X →ₗ[ℝ] Y} (hf : Positive f)
    {x y : X} (h : |x| ≤ y) : ‖f x‖ ≤ ‖f y‖ :=
  norm_le_norm_of_abs_le_abs <|
    (abs_le_map_abs hf x).trans <|
    ((monotone_iff.mpr hf) h).trans (le_abs_self _)

/-- Every positive linear operator from a Banach lattice to a normed vector lattice
is continuous. -/
theorem continuous {f : X →ₗ[ℝ] Y} (hf : Positive f) : Continuous f := by
  by_contra hcont
  have hunb : ∀ C : ℝ, ∃ x : X, C * ‖x‖ < ‖f x‖ := by
    by_contra h; push_neg at h; obtain ⟨C, hC⟩ := h
    exact hcont (continuous_of_linear_of_bound f.map_add f.map_smul hC)
  -- For each n, find xₙ with ‖xₙ‖ ≤ (1/2)ⁿ and n < ‖f xₙ‖
  have hseq : ∀ n : ℕ, ∃ x : X, ‖x‖ ≤ (1 / 2 : ℝ) ^ n ∧ (n : ℝ) < ‖f x‖ := by
    intro n
    obtain ⟨z, hz⟩ := hunb ((n : ℝ) * (2 : ℝ) ^ n)
    have hznz : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨((2 : ℝ) ^ n * ‖z‖)⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      simp [one_div, mul_comm]
    · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [lt_inv_mul_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      linarith [mul_comm ((n : ℝ) * (2 : ℝ) ^ n) ‖z‖]
  choose x hxn hxf using hseq
  have habs : Summable (fun n => |x n|) :=
    .of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (fun n => by rw [norm_abs_eq_norm]; exact hxn n)
  set y := ∑' n, |x n|
  have hle : ∀ n, |x n| ≤ y := fun n => habs.le_tsum n (fun j _ => abs_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt ‖f y‖
  exact absurd (lt_of_lt_of_le (hxf N) (norm_map_le_of_abs_le hf (hle N)))
    (not_lt.mpr hN.le)

end Positive

namespace VecLatEquiv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- A vector lattice isomorphism between Banach lattices extends to a continuous linear
equivalence. -/
noncomputable def toContinuousLinearEquiv (e : VecLatEquiv X Y) : X ≃L[ℝ] Y :=
  ContinuousLinearEquiv.mk e.toLinearEquiv
    (Positive.continuous (Positive.monotone_iff.mp e.toVecLatHom.monotone))
    (Positive.continuous (Positive.monotone_iff.mp e.symm.toVecLatHom.monotone))

end VecLatEquiv
