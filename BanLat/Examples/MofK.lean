import BanLat.Banach
import BanLat.Preliminaries.SignedMeasure

/-!
# The space `M(K)` of finite signed measures as a Banach lattice

For a measurable space `K`, the space `MeasureTheory.SignedMeasure K` of finite
signed measures carries a canonical Banach lattice structure. Order, lattice
operations, and norm all flow from the **Jordan decomposition**: every signed
measure `s` is uniquely a difference `s⁺ - s⁻` of two mutually singular finite
measures, and

* the order is the pointwise (set-wise) order coming from `VectorMeasure.LE`;
* the lattice operations are `s ⊔ t := t + (s - t).posPart` and
  `s ⊓ t := s - (s - t).posPart`, where `(s - t).posPart` is the Jordan
  positive part of `s - t`, viewed as a signed measure;
* the norm is the **total variation**, `‖s‖ := |s|(K)`, where
  `|s| = s⁺ + s⁻` is the total-variation measure;
* completeness in this norm follows from the Vitali–Hahn–Saks theorem.

This is the space classically denoted `M(K)`. The identification of `M(K)`
with the dual of `C(K, ℝ)` (the **Riesz–Markov–Kakutani representation
theorem** for signed functionals) is formalised separately in
`BanLat.Examples.CofK`.
-/

open MeasureTheory

namespace MeasureTheory
namespace SignedMeasure

variable {α : Type*} [MeasurableSpace α]

/-! ### Positive and negative parts as signed measures

Re-bundling the Jordan parts (which Mathlib stores as positive `Measure`s)
back as signed measures gives the algebraic identity `s = posPart - negPart`
inside `SignedMeasure α` and lets us state the lattice operations cleanly.
-/

/-- The Jordan positive part of `s`, viewed as a signed measure. -/
noncomputable def posPart (s : SignedMeasure α) : SignedMeasure α :=
  s.toJordanDecomposition.posPart.toSignedMeasure

/-- The Jordan negative part of `s`, viewed as a signed measure. -/
noncomputable def negPart (s : SignedMeasure α) : SignedMeasure α :=
  s.toJordanDecomposition.negPart.toSignedMeasure

/-- Reconstructing a signed measure from its Jordan parts:
`s = s.posPart - s.negPart`. Direct from
`JordanDecomposition.toSignedMeasure_toJordanDecomposition`. -/
theorem posPart_sub_negPart (s : SignedMeasure α) :
    s.posPart - s.negPart = s := by
  unfold posPart negPart
  exact s.toSignedMeasure_toJordanDecomposition

/-- The positive part is non-negative as a signed measure. Direct from
`Measure.toSignedMeasure_nonneg` for finite measures. -/
theorem zero_le_posPart (s : SignedMeasure α) : 0 ≤ s.posPart :=
  Measure.zero_le_toSignedMeasure _

/-- The negative part is non-negative as a signed measure. -/
theorem zero_le_negPart (s : SignedMeasure α) : 0 ≤ s.negPart :=
  Measure.zero_le_toSignedMeasure _

/-- Order characterisation: `0 ≤ s` iff the Jordan negative part vanishes.
This is the bridge between the pointwise order on `SignedMeasure α` and the
Jordan-decomposition machinery. -/
theorem nonneg_iff_negPart_eq_zero {s : SignedMeasure α} :
    0 ≤ s ↔ s.negPart = 0 := by
  refine ⟨fun hs => ?_, fun h => ?_⟩
  · have hs' : (0 : SignedMeasure α) ≤[Set.univ] s :=
      (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hs
    let j : JordanDecomposition α :=
      { posPart := s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs'
        negPart := 0
        mutuallySingular := Measure.MutuallySingular.zero_right }
    have hj : s.toJordanDecomposition = j := by
      refine toJordanDecomposition_eq ?_
      change s = (s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs').toSignedMeasure
                  - (0 : Measure α).toSignedMeasure
      rw [Measure.toSignedMeasure_zero, sub_zero, toMeasureOfZeroLE_toSignedMeasure s hs']
    change s.toJordanDecomposition.negPart.toSignedMeasure = 0
    rw [hj]
    exact Measure.toSignedMeasure_zero
  · have heq := posPart_sub_negPart s
    rw [h, sub_zero] at heq
    exact heq ▸ zero_le_posPart s

/-- The positive part dominates `s`: `s ≤ s.posPart`. -/
private theorem self_le_posPart (s : SignedMeasure α) : s ≤ s.posPart := by
  intro i hi
  have h := posPart_sub_negPart s
  have hi' : (s.posPart - s.negPart) i = s i := by rw [h]
  rw [VectorMeasure.sub_apply] at hi'
  have hn : (0 : SignedMeasure α) i ≤ s.negPart i := zero_le_negPart s i hi
  rw [VectorMeasure.zero_apply] at hn
  linarith

/-- Universal property of the positive part: `(s - t).posPart` is the smallest
non-negative signed measure `u` with `s - t ≤ u`. This is the key lemma behind
the lattice axioms for `⊔`. -/
theorem posPart_isLeast (s : SignedMeasure α) :
    IsLeast {u : SignedMeasure α | 0 ≤ u ∧ s ≤ u} s.posPart := by
  refine ⟨⟨zero_le_posPart s, self_le_posPart s⟩, ?_⟩
  rintro u ⟨hu0, hsu⟩
  obtain ⟨P, hP, hPpos, hPneg, hposEq, _⟩ := s.toJordanDecomposition_spec
  intro i hi
  have hpp : s.posPart i = s (P ∩ i) := by
    change (s.toJordanDecomposition.posPart).toSignedMeasure i = s (P ∩ i)
    rw [Measure.toSignedMeasure_apply_measurable hi, hposEq,
        toMeasureOfZeroLE_real_apply _ hPpos hP hi]
  rw [hpp]
  have h1 : s (P ∩ i) ≤ u (P ∩ i) := hsu _ (hP.inter hi)
  have hdisj : Disjoint (P ∩ i) (i \ P) :=
    Set.disjoint_sdiff_right.mono_left Set.inter_subset_left
  have huni : (P ∩ i) ∪ (i \ P) = i := by
    rw [Set.inter_comm]; exact Set.inter_union_diff i P
  have h2 : u (P ∩ i) + u (i \ P) = u i := by
    rw [← VectorMeasure.of_union hdisj (hP.inter hi) (hi.diff hP), huni]
  have h3 : (0 : SignedMeasure α) (i \ P) ≤ u (i \ P) := hu0 _ (hi.diff hP)
  rw [VectorMeasure.zero_apply] at h3
  linarith

/-! ### Lattice structure -/

/-- Maximum of two signed measures via the Jordan positive part of their
difference. -/
noncomputable instance instMax : Max (SignedMeasure α) where
  max s t := t + (s - t).posPart

/-- Minimum of two signed measures. -/
noncomputable instance instMin : Min (SignedMeasure α) where
  min s t := s - (s - t).posPart

theorem max_def (s t : SignedMeasure α) : s ⊔ t = t + (s - t).posPart := rfl

theorem min_def (s t : SignedMeasure α) : s ⊓ t = s - (s - t).posPart := rfl

/-- The lattice instance extends the existing `PartialOrder` on
`SignedMeasure α`. The lattice axioms reduce, via `posPart_isLeast`, to the
universal property of the Jordan positive part. -/
noncomputable instance instLattice : Lattice (SignedMeasure α) where
  __ := (inferInstance : PartialOrder (SignedMeasure α))
  sup := Max.max
  inf := Min.min
  le_sup_left s t := by
    intro i hi
    have h := self_le_posPart (s - t) i hi
    rw [VectorMeasure.sub_apply] at h
    change s i ≤ (t + (s - t).posPart) i
    rw [VectorMeasure.add_apply]
    linarith
  le_sup_right s t := by
    intro i hi
    have h := zero_le_posPart (s - t) i hi
    rw [VectorMeasure.zero_apply] at h
    change t i ≤ (t + (s - t).posPart) i
    rw [VectorMeasure.add_apply]
    linarith
  sup_le s t u hsu htu := by
    have h0 : (0 : SignedMeasure α) ≤ u - t := by
      intro i hi
      rw [VectorMeasure.zero_apply, VectorMeasure.sub_apply]
      linarith [htu i hi]
    have h1 : s - t ≤ u - t := by
      intro i hi
      rw [VectorMeasure.sub_apply, VectorMeasure.sub_apply]
      linarith [hsu i hi]
    have h2 : (s - t).posPart ≤ u - t :=
      (posPart_isLeast (s - t)).2 ⟨h0, h1⟩
    intro i hi
    change (t + (s - t).posPart) i ≤ u i
    have := h2 i hi
    rw [VectorMeasure.sub_apply] at this
    rw [VectorMeasure.add_apply]
    linarith
  inf_le_left s t := by
    intro i hi
    have h := zero_le_posPart (s - t) i hi
    rw [VectorMeasure.zero_apply] at h
    change (s - (s - t).posPart) i ≤ s i
    rw [VectorMeasure.sub_apply]
    linarith
  inf_le_right s t := by
    intro i hi
    have h := self_le_posPart (s - t) i hi
    rw [VectorMeasure.sub_apply] at h
    change (s - (s - t).posPart) i ≤ t i
    rw [VectorMeasure.sub_apply]
    linarith
  le_inf u s t hus hut := by
    have h0 : (0 : SignedMeasure α) ≤ s - u := by
      intro i hi
      rw [VectorMeasure.zero_apply, VectorMeasure.sub_apply]
      linarith [hus i hi]
    have h1 : s - t ≤ s - u := by
      intro i hi
      rw [VectorMeasure.sub_apply, VectorMeasure.sub_apply]
      linarith [hut i hi]
    have h2 : (s - t).posPart ≤ s - u :=
      (posPart_isLeast (s - t)).2 ⟨h0, h1⟩
    intro i hi
    change u i ≤ (s - (s - t).posPart) i
    have := h2 i hi
    rw [VectorMeasure.sub_apply] at this
    rw [VectorMeasure.sub_apply]
    linarith

/-- Translation invariance of the order: the addition on `SignedMeasure α` is
set-wise, hence preserves the set-wise order. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (SignedMeasure α) where
  add_le_add_left a b h c := by
    intro i hi
    rw [VectorMeasure.add_apply, VectorMeasure.add_apply]
    linarith [h i hi]

/-- Multiplication by a non-negative real preserves the order: `(c • s) i =
c • s i`, and `c • _` is monotone on `ℝ` for `0 ≤ c`. -/
instance instPosSMulMono : PosSMulMono ℝ (SignedMeasure α) where
  smul_le_smul_of_nonneg_left := fun _ hc _ _ h i hi => by
    rw [VectorMeasure.smul_apply, VectorMeasure.smul_apply]
    exact mul_le_mul_of_nonneg_left (h i hi) hc

/-- `SignedMeasure α` is a real vector lattice. The `VectorLattice` axioms
reduce to `instPosSMulMono` and the lattice structure already in place. -/
noncomputable instance instVectorLattice : VectorLattice (SignedMeasure α) where

/-! ### Modulus and total variation

The vector-lattice modulus `|s| = s.posPart + s.negPart` (a non-negative
signed measure) corresponds, via `Measure.toSignedMeasure`, to the
total-variation measure of Mathlib's `SignedMeasure.totalVariation`. -/

private theorem supZero_eq_posPart (s : SignedMeasure α) : s ⊔ 0 = s.posPart := by
  change 0 + (s - 0).posPart = s.posPart
  rw [zero_add, sub_zero]

private theorem negSupZero_eq_negPart (s : SignedMeasure α) : (-s) ⊔ 0 = s.negPart := by
  rw [supZero_eq_posPart]
  change (-s).toJordanDecomposition.posPart.toSignedMeasure =
    s.toJordanDecomposition.negPart.toSignedMeasure
  apply Measure.toSignedMeasure_congr
  rw [SignedMeasure.toJordanDecomposition_neg]
  rfl

/-- Modulus as the sum of Jordan parts. Direct from `posPart_sub_negPart`,
`zero_le_posPart`, `zero_le_negPart`, and the formula
`|x| = x⁺ + x⁻` valid in any vector lattice. -/
theorem abs_eq_posPart_add_negPart (s : SignedMeasure α) :
    |s| = s.posPart + s.negPart := by
  rw [← posPart_add_negPart s, posPart_def, negPart_def, supZero_eq_posPart,
    negSupZero_eq_negPart]

/-- Identification of the modulus with the total variation: applying `|s|` (a
non-negative signed measure) to a measurable set returns the total-variation
measure of `s` on that set. -/
theorem abs_apply_eq_totalVariation (s : SignedMeasure α) (i : Set α)
    (hi : MeasurableSet i) :
    (|s| : SignedMeasure α) i = (s.totalVariation i).toReal := by
  rw [abs_eq_posPart_add_negPart, VectorMeasure.add_apply]
  change s.toJordanDecomposition.posPart.toSignedMeasure i +
      s.toJordanDecomposition.negPart.toSignedMeasure i = _
  rw [Measure.toSignedMeasure_apply_measurable hi,
      Measure.toSignedMeasure_apply_measurable hi,
      SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply]

/-! ### Total-variation norm

We package `s ↦ (s.totalVariation univ).toReal` as an `AddGroupNorm`, then
upgrade to a `NormedAddCommGroup` via `AddGroupNorm.toNormedAddCommGroup`. -/

/-- The total variation, as an additive group norm on `SignedMeasure α`. The
four field obligations reduce, via `BanLat.Preliminaries.SignedMeasure`, to
`totalVariation_zero_eq`, `toReal_totalVariation_add_univ_le`,
`SignedMeasure.totalVariation_neg`, and
`eq_zero_of_totalVariation_univ_eq_zero`. -/
noncomputable def tvAddGroupNorm : AddGroupNorm (SignedMeasure α) where
  toFun s := (s.totalVariation Set.univ).toReal
  map_zero' := by rw [totalVariation_zero_eq]; simp
  add_le' s t := toReal_totalVariation_add_univ_le s t
  neg' s := by rw [SignedMeasure.totalVariation_neg]
  eq_zero_of_map_eq_zero' s h := by
    apply eq_zero_of_totalVariation_univ_eq_zero
    rcases (ENNReal.toReal_eq_zero_iff _).mp h with h₁ | h₁
    · exact h₁
    · exact absurd h₁ (totalVariation_univ_lt_top s).ne

/-- Total-variation norm structure on `SignedMeasure α`. -/
noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (SignedMeasure α) :=
  tvAddGroupNorm.toNormedAddCommGroup

/-- The norm of a signed measure is its total variation on the universe. -/
theorem norm_def (s : SignedMeasure α) :
    ‖s‖ = (s.totalVariation Set.univ).toReal := rfl

/-! ### Compatibility of the norm with scalar multiplication and the order

The two compatibility properties — solidness of the norm and homogeneity under
scalar multiplication — give the `NormedVectorLattice` instance, and
completeness then yields `BanachLattice`. -/

/-- The total-variation norm is solid: if `|s| ≤ |t|` (as signed measures) then
`‖s‖ ≤ ‖t‖`. Argument: applying both sides to `Set.univ` and using
`abs_apply_eq_totalVariation` reduces this to monotonicity of
`(·).toReal` on finite values of the total variation. -/
private theorem norm_le_of_abs_le_abs {s t : SignedMeasure α} (h : |s| ≤ |t|) :
    ‖s‖ ≤ ‖t‖ := by
  rw [norm_def, norm_def]
  have hst := h Set.univ MeasurableSet.univ
  rw [abs_apply_eq_totalVariation _ _ MeasurableSet.univ,
      abs_apply_eq_totalVariation _ _ MeasurableSet.univ] at hst
  exact hst

instance instHasSolidNorm : HasSolidNorm (SignedMeasure α) where
  solid := fun {_ _} h => norm_le_of_abs_le_abs h

/-- Homogeneity of the norm under real scalar multiplication. Argument:
`norm_def` reduces this to `totalVariation_smul_univ` from the preliminaries. -/
private theorem norm_smul_eq (c : ℝ) (s : SignedMeasure α) :
    ‖c • s‖ = ‖c‖ * ‖s‖ := by
  rw [norm_def, norm_def, totalVariation_smul_univ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg c), Real.norm_eq_abs]

instance instNormSMulClass : NormSMulClass ℝ (SignedMeasure α) where
  norm_smul := norm_smul_eq

/-- `SignedMeasure α` is a normed vector lattice. -/
noncomputable instance instNormedVectorLattice :
    NormedVectorLattice (SignedMeasure α) where

/-! ### Completeness and Banach lattice instance

Completeness of `(SignedMeasure α, ‖·‖_TV)` is the **Vitali–Hahn–Saks**
theorem in disguise: a TV-Cauchy sequence of finite signed measures has a
set-wise limit which is itself a finite signed measure, with TV convergence.

A clean proof proceeds by:
1. extracting set-wise limits `s univ_E := lim n, sₙ E` for each measurable
   `E`, using completeness of `ℝ`;
2. checking countable additivity of the resulting set function via
   Vitali–Hahn–Saks (uniform countable additivity passes to limits);
3. verifying TV convergence directly from the Cauchy hypothesis.
-/

/-- `SignedMeasure α` is complete in the total-variation norm. -/
instance instCompleteSpace : CompleteSpace (SignedMeasure α) :=
  sorry

/-- `SignedMeasure α` is a Banach lattice. -/
noncomputable instance instBanachLattice : BanachLattice (SignedMeasure α) where

/-! ### Total variation and the order: positivity criterion

A direct corollary of `totalVariation_univ_eq_of_nonneg`: for non-negative
signed measures the norm equals the value at `univ`. -/

/-- For a non-negative signed measure, the norm is just the (real-valued)
total mass `s univ`. -/
theorem norm_of_nonneg {s : SignedMeasure α} (hs : 0 ≤ s) :
    ‖s‖ = (s Set.univ : ℝ) := by
  rw [norm_def, totalVariation_univ_eq_of_nonneg hs]

end SignedMeasure
end MeasureTheory
