import BanLat.Atom
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

/-- `SignedMeasure α` is complete in the total-variation norm. The reduction
to `exists_tv_limit_of_cauchy` is a translation between `dist`/`Tendsto` in the
metric topology and the total-variation form of the Cauchy/limit conditions. -/
instance instCompleteSpace : CompleteSpace (SignedMeasure α) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  rw [Metric.cauchySeq_iff] at hu
  have hu' : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ((u m - u n).totalVariation Set.univ).toReal < ε := fun ε hε => by
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rwa [dist_eq_norm, norm_def] at h
  obtain ⟨t, ht⟩ := exists_tv_limit_of_cauchy u hu'
  refine ⟨t, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_def]
  exact hN n hn

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

/-! ### Atoms of `M(K)` and Dirac deltas

In a vector lattice, an **atom** (`IsVLAtom`) is a strictly positive element
whose order interval `[0, a]` is one-dimensional: every `0 ≤ x ≤ a` is a
scalar multiple of `a`. For the Banach lattice `M(K) = SignedMeasure α` with
measurable singletons, the atoms are precisely the strictly positive scalar
multiples of the Dirac measures `δ_x` at points `x ∈ K`. -/

section Atoms

variable [MeasurableSingletonClass α]

/-- The Dirac delta at a point, viewed as a finite signed measure. -/
noncomputable def dirac (x : α) : SignedMeasure α :=
  (Measure.dirac x).toSignedMeasure

omit [MeasurableSingletonClass α] in
/-- The Dirac delta evaluates to `1` on any measurable set containing the
point. -/
theorem dirac_apply_of_mem {x : α} {i : Set α} (hi : MeasurableSet i)
    (hx : x ∈ i) : dirac x i = 1 := by
  unfold dirac
  rw [Measure.toSignedMeasure_apply_measurable hi, measureReal_def,
      Measure.dirac_apply_of_mem hx, ENNReal.toReal_one]

omit [MeasurableSingletonClass α] in
/-- The Dirac delta evaluates to `0` on any measurable set not containing the
point. -/
theorem dirac_apply_of_notMem {x : α} {i : Set α} (hi : MeasurableSet i)
    (hx : x ∉ i) : dirac x i = 0 := by
  unfold dirac
  rw [Measure.toSignedMeasure_apply_measurable hi, measureReal_def,
      Measure.dirac_apply' x hi, Set.indicator_of_notMem hx, ENNReal.toReal_zero]

omit [MeasurableSingletonClass α] in
/-- The Dirac delta is non-negative as a signed measure. -/
theorem zero_le_dirac (x : α) : (0 : SignedMeasure α) ≤ dirac x :=
  Measure.zero_le_toSignedMeasure _

/-- The Dirac delta is non-zero. -/
theorem dirac_ne_zero (x : α) : dirac x ≠ 0 := by
  intro h
  have h₁ : dirac x {x} = 1 :=
    dirac_apply_of_mem (measurableSet_singleton x) (Set.mem_singleton x)
  rw [h, VectorMeasure.zero_apply] at h₁
  exact one_ne_zero h₁.symm

omit [MeasurableSingletonClass α] in
/-- The norm (total variation) of a Dirac delta is `1`. -/
theorem norm_dirac (x : α) : ‖dirac x‖ = 1 := by
  rw [norm_of_nonneg (zero_le_dirac x)]
  exact dirac_apply_of_mem MeasurableSet.univ (Set.mem_univ x)

/-- The Dirac measures at two distinct points are mutually singular. -/
private theorem mutuallySingular_dirac_dirac {x y : α} (h : x ≠ y) :
    Measure.dirac x ⟂ₘ Measure.dirac y := by
  refine ⟨{x}ᶜ, (measurableSet_singleton x).compl, ?_, ?_⟩
  · rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem (by simp) _
  · rw [compl_compl, Measure.dirac_apply]
    exact Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr h.symm) _

/-- The positive part of `dirac x - dirac y` is `dirac x` when `x ≠ y`. -/
private theorem posPart_dirac_sub_dirac {x y : α} (h : x ≠ y) :
    (dirac x - dirac y).posPart = dirac x := by
  let j : JordanDecomposition α :=
    { posPart := Measure.dirac x
      negPart := Measure.dirac y
      mutuallySingular := mutuallySingular_dirac_dirac h }
  have hjd : (dirac x - dirac y).toJordanDecomposition = j :=
    toJordanDecomposition_eq rfl
  change (dirac x - dirac y).toJordanDecomposition.posPart.toSignedMeasure =
       (Measure.dirac x).toSignedMeasure
  rw [hjd]

/-- Two Dirac deltas at distinct points are vector-lattice disjoint. -/
theorem isVLDisjoint_dirac_of_ne {x y : α} (h : x ≠ y) :
    IsVLDisjoint (dirac x) (dirac y) := by
  refine isVLDisjoint_of_inf_eq_zero ?_
  change dirac x - (dirac x - dirac y).posPart = 0
  rw [posPart_dirac_sub_dirac h, sub_self]

omit [MeasurableSingletonClass α] in
/-- A non-negative signed measure dominated by `dirac x` vanishes outside `x`. -/
private theorem apply_eq_zero_of_notMem_of_le_dirac {x : α} {y : SignedMeasure α}
    (hy0 : 0 ≤ y) (hyd : y ≤ dirac x) {i : Set α} (hi : MeasurableSet i)
    (hx : x ∉ i) : y i = 0 := by
  have h1 : (0 : SignedMeasure α) i ≤ y i := hy0 _ hi
  rw [VectorMeasure.zero_apply] at h1
  have h2 : y i ≤ dirac x i := hyd _ hi
  rw [dirac_apply_of_notMem hi hx] at h2
  linarith

/-- A non-negative signed measure dominated by `dirac x` is determined on sets
containing `x` by its value on the singleton `{x}`. -/
private theorem apply_eq_singleton_of_mem_of_le_dirac {x : α} {y : SignedMeasure α}
    (hy0 : 0 ≤ y) (hyd : y ≤ dirac x) {i : Set α} (hi : MeasurableSet i)
    (hx : x ∈ i) : y i = y {x} := by
  have hx_set : MeasurableSet ({x} : Set α) := measurableSet_singleton x
  have h_subset : ({x} : Set α) ⊆ i := Set.singleton_subset_iff.mpr hx
  have h_split : y ({x} : Set α) + y (i \ {x}) = y i :=
    VectorMeasure.of_add_of_diff hx_set hi h_subset
  have h_diff_zero : y (i \ {x}) = 0 :=
    apply_eq_zero_of_notMem_of_le_dirac hy0 hyd (hi.diff hx_set) (by simp)
  rw [h_diff_zero, add_zero] at h_split
  exact h_split.symm

/-- The Dirac delta is itself an atom of `M(K)`. -/
theorem isVLAtom_dirac (x : α) : IsVLAtom (dirac x) := by
  refine ⟨lt_of_le_of_ne (zero_le_dirac x) (Ne.symm (dirac_ne_zero x)), ?_⟩
  intro y hy0 hyd
  refine ⟨y {x}, ?_⟩
  ext i hi
  rw [VectorMeasure.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ i
  · rw [dirac_apply_of_mem hi hx, mul_one]
    exact apply_eq_singleton_of_mem_of_le_dirac hy0 hyd hi hx
  · rw [dirac_apply_of_notMem hi hx, mul_zero]
    exact apply_eq_zero_of_notMem_of_le_dirac hy0 hyd hi hx

/-- A strictly positive scalar multiple of a Dirac delta is an atom of
`M(K)`. -/
theorem isVLAtom_smul_dirac {c : ℝ} (hc : 0 < c) (x : α) :
    IsVLAtom (c • dirac x) :=
  IsVLAtom.smul (isVLAtom_dirac x) hc

omit [MeasurableSingletonClass α] in
/-- A non-negative signed measure is monotone with respect to set inclusion. -/
private lemma le_of_subset_of_nonneg {s : SignedMeasure α} (hs : 0 ≤ s)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
    s A ≤ s B := by
  have h1 := VectorMeasure.of_add_of_diff hA hB h (v := s)
  have h2 : (0 : SignedMeasure α) (B \ A) ≤ s (B \ A) := hs _ (hB.diff hA)
  rw [VectorMeasure.zero_apply] at h2
  linarith

omit [MeasurableSingletonClass α] in
/-- For a vector-lattice atom of `M(K)`, every measurable set takes value either
`0` or the full mass `s univ`. The proof uses the atom property applied to the
"restriction of `s` to `A`" as a signed measure. -/
private lemma atom_value_eq_zero_or_univ (s : SignedMeasure α) (hs : IsVLAtom s)
    {A : Set α} (hA : MeasurableSet A) :
    s A = 0 ∨ s A = s Set.univ := by
  have hs0 : 0 ≤ s := hs.1.le
  have hs0A : (0 : SignedMeasure α) ≤[A] s :=
    VectorMeasure.restrict_le_restrict_of_subset_le 0 s (fun j hj _ => hs0 j hj)
  let t : SignedMeasure α := (s.toMeasureOfZeroLE A hA hs0A).toSignedMeasure
  have ht_apply : ∀ {i : Set α}, MeasurableSet i → t i = s (A ∩ i) := by
    intro i hi
    change ((s.toMeasureOfZeroLE A hA hs0A).toSignedMeasure) i = _
    rw [Measure.toSignedMeasure_apply_measurable hi,
        toMeasureOfZeroLE_real_apply _ _ _ hi]
  have ht0 : 0 ≤ t := Measure.zero_le_toSignedMeasure _
  have hts : t ≤ s := fun i hi => by
    rw [ht_apply hi]
    exact le_of_subset_of_nonneg hs0 (hA.inter hi) hi Set.inter_subset_right
  obtain ⟨c, hc⟩ := hs.2 t ht0 hts
  have h1 : t Set.univ = s A := by rw [ht_apply MeasurableSet.univ, Set.inter_univ]
  have h2 : t Set.univ = c * s Set.univ := by
    rw [hc, VectorMeasure.smul_apply, smul_eq_mul]
  have h3 : t A = s A := by rw [ht_apply hA, Set.inter_self]
  have h4 : t A = c * s A := by
    rw [hc, VectorMeasure.smul_apply, smul_eq_mul]
  have h_univ : s A = c * s Set.univ := h1 ▸ h2
  have h_A : s A = c * s A := h3 ▸ h4
  rcases eq_or_ne (s A) 0 with hsA0 | hsA_ne
  · exact Or.inl hsA0
  · have hc1 : c = 1 := by
      have hh : s A * (1 - c) = 0 := by linarith
      rcases mul_eq_zero.mp hh with h | h
      · exact absurd h hsA_ne
      · linarith
    rw [hc1, one_mul] at h_univ
    exact Or.inr h_univ

/-- For a non-negative signed measure on a countable space with positive total
mass, some singleton has positive mass. This is the bridge from the
"two-valued" property of an atom to a concrete point of concentration. -/
private lemma exists_singleton_pos [Countable α] {s : SignedMeasure α}
    (hs0 : 0 ≤ s) (hs_univ : 0 < s Set.univ) : ∃ x, 0 < s {x} := by
  by_contra h
  push_neg at h
  have h_zero : ∀ x, s ({x} : Set α) = 0 := fun x => by
    have h1 := h x
    have h2 : (0 : SignedMeasure α) ({x} : Set α) ≤ s {x} :=
      hs0 _ (measurableSet_singleton x)
    rw [VectorMeasure.zero_apply] at h2
    linarith
  have h_disj : Pairwise (Function.onFun Disjoint (fun x : α => ({x} : Set α))) := by
    intro x y hxy
    exact Set.disjoint_singleton.mpr hxy
  have h_meas : ∀ x : α, MeasurableSet ({x} : Set α) := fun x => measurableSet_singleton x
  have h_sum : (s : VectorMeasure α ℝ) (⋃ x : α, ({x} : Set α)) =
      ∑' x : α, s ({x} : Set α) :=
    VectorMeasure.of_disjoint_iUnion h_meas h_disj
  rw [Set.iUnion_of_singleton α] at h_sum
  rw [h_sum] at hs_univ
  simp only [h_zero, tsum_zero] at hs_univ
  exact lt_irrefl _ hs_univ

/-- **Atoms of `M(K)` are exactly the positive multiples of Dirac deltas.**
A finite signed measure is a vector-lattice atom of `M(K)` iff it is a
strictly positive scalar multiple of some Dirac delta `δ_x`. This identifies
the atoms of the Banach lattice `M(K)` with the parametrised family
`{c • δ_x : 0 < c, x ∈ K}`.

The countability hypothesis on `α` is essential: without it, two-valued
atomless measures (e.g., on the countable-or-cocountable `σ`-algebra of an
uncountable set) provide vector-lattice atoms that are not Dirac deltas. -/
theorem isVLAtom_iff_exists_smul_dirac [Countable α] (s : SignedMeasure α) :
    IsVLAtom s ↔ ∃ (c : ℝ) (x : α), 0 < c ∧ s = c • dirac x := by
  refine ⟨fun hs => ?_, ?_⟩
  · have hs0 : 0 ≤ s := hs.1.le
    have hs_univ : 0 < s Set.univ := by
      have h_norm : 0 < ‖s‖ := norm_pos_iff.mpr hs.ne_zero
      rwa [norm_of_nonneg hs0] at h_norm
    obtain ⟨x, hx⟩ := exists_singleton_pos hs0 hs_univ
    have hsx : s {x} = s Set.univ := by
      rcases atom_value_eq_zero_or_univ s hs (measurableSet_singleton x) with h | h
      · linarith
      · exact h
    refine ⟨s Set.univ, x, hs_univ, ?_⟩
    ext i hi
    rw [VectorMeasure.smul_apply, smul_eq_mul]
    by_cases hxi : x ∈ i
    · rw [dirac_apply_of_mem hi hxi, mul_one]
      rcases atom_value_eq_zero_or_univ s hs hi with h_i_zero | h_i_univ
      · exfalso
        have h_le : s {x} ≤ s i := le_of_subset_of_nonneg hs0
          (measurableSet_singleton x) hi (Set.singleton_subset_iff.mpr hxi)
        linarith
      · exact h_i_univ
    · rw [dirac_apply_of_notMem hi hxi, mul_zero]
      rcases atom_value_eq_zero_or_univ s hs hi with h_i_zero | h_i_univ
      · exact h_i_zero
      · exfalso
        have hdisj : Disjoint ({x} : Set α) i := Set.disjoint_singleton_left.mpr hxi
        have h_add : s ({x} ∪ i) = s {x} + s i :=
          VectorMeasure.of_union hdisj (measurableSet_singleton x) hi
        have h_le : s ({x} ∪ i) ≤ s Set.univ := le_of_subset_of_nonneg hs0
          ((measurableSet_singleton x).union hi) MeasurableSet.univ (Set.subset_univ _)
        rw [h_add, hsx, h_i_univ] at h_le
        linarith
  · rintro ⟨c, x, hc, rfl⟩
    exact isVLAtom_smul_dirac hc x

/-! ### Discrete–continuous decomposition

A finite signed measure `s` is **discrete** (or *purely atomic*) if it is a
countable signed combination of Dirac deltas — equivalently, an element of
the band generated by atoms in the sense of `BanLat.Atom`. It is
**continuous** (or *atomless*) if its total variation `|s|` has no atoms in
the sense of `MeasureTheory.NoAtoms`, equivalently `|s|({x}) = 0` for every
`x ∈ K`.

> **Note (Mathlib coverage).** `MeasureTheory.NoAtoms` is the Mathlib
> typeclass for atomless (= continuous) measures. There is, however, no
> Mathlib notion of a *discrete* measure on a general measurable space, nor
> the discrete–continuous decomposition stated below. The countable-space
> version `MeasureTheory.Measure.sum_smul_dirac` covers only the case where
> `α` itself is countable.
-/

omit [MeasurableSingletonClass α] in
/-- The value of a signed measure on any set is bounded in absolute value by the
total-variation norm. -/
private lemma abs_apply_le_norm (s : SignedMeasure α) (E : Set α) :
    |s E| ≤ ‖s‖ := by
  by_cases hE : MeasurableSet E
  · have h_tv : (|s| : SignedMeasure α) E ≤ ‖s‖ := by
      rw [abs_apply_eq_totalVariation s E hE, norm_def]
      exact ENNReal.toReal_mono (totalVariation_univ_lt_top s).ne
        (measure_mono (Set.subset_univ E))
    have h_pos : s E ≤ (|s| : SignedMeasure α) E := le_abs_self s E hE
    have h_neg : -s E ≤ (|s| : SignedMeasure α) E := by
      have h := (neg_le_abs s) E hE
      rwa [VectorMeasure.neg_apply] at h
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [VectorMeasure.not_measurable s hE, abs_zero]
    exact norm_nonneg s

omit [MeasurableSingletonClass α] in
/-- Evaluation of a signed measure at a fixed set, packaged as a continuous linear
map `M(K) →L[ℝ] ℝ`. Used to commute infinite sums with pointwise evaluation. -/
private noncomputable def applyCLM (E : Set α) : SignedMeasure α →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun s => s E
      map_add' := fun s t => VectorMeasure.add_apply s t E
      map_smul' := fun c s => by rw [VectorMeasure.smul_apply]; rfl }
    1
    (fun s => by rw [Real.norm_eq_abs, one_mul]; exact abs_apply_le_norm s E)

/-- The total variation of a signed measure on a singleton equals the absolute
value of the signed measure on that singleton, a consequence of mutual
singularity of the Jordan parts. -/
private lemma totalVariation_singleton_toReal (s : SignedMeasure α) (x : α) :
    (s.totalVariation ({x} : Set α)).toReal = |s ({x} : Set α)| := by
  obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
  have hxm : MeasurableSet ({x} : Set α) := measurableSet_singleton x
  rw [SignedMeasure.totalVariation, Measure.add_apply, hpos, hneg]
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [← measureReal_def, ← measureReal_def,
      toMeasureOfZeroLE_real_apply _ hi₂ hi₁ hxm,
      toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl hxm]
  by_cases hx : x ∈ i
  · have h1 : i ∩ ({x} : Set α) = ({x} : Set α) :=
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hx)
    have h2 : iᶜ ∩ ({x} : Set α) = ∅ :=
      Set.inter_singleton_of_notMem (fun h => h hx)
    rw [h1, h2, VectorMeasure.empty, neg_zero, add_zero]
    have h_nn : 0 ≤ s ({x} : Set α) := by
      have h := (VectorMeasure.restrict_le_restrict_iff _ _ hi₁).mp hi₂ hxm
        (Set.singleton_subset_iff.mpr hx)
      rwa [VectorMeasure.zero_apply] at h
    exact (abs_of_nonneg h_nn).symm
  · have h1 : i ∩ ({x} : Set α) = ∅ :=
      Set.inter_singleton_of_notMem hx
    have h2 : iᶜ ∩ ({x} : Set α) = ({x} : Set α) :=
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hx)
    rw [h1, h2, VectorMeasure.empty, zero_add]
    have h_np : s ({x} : Set α) ≤ 0 := by
      have h := (VectorMeasure.restrict_le_restrict_iff _ _ hi₁.compl).mp hi₃ hxm
        (Set.singleton_subset_iff.mpr hx)
      rwa [VectorMeasure.zero_apply] at h
    exact (abs_of_nonpos h_np).symm

/-- The absolute values of a signed measure on singletons form a summable family
when the index type is countable. -/
private lemma summable_abs_singleton [Countable α] (s : SignedMeasure α) :
    Summable (fun x : α => |s ({x} : Set α)|) := by
  have h_disj : Pairwise (Function.onFun Disjoint (fun x : α => ({x} : Set α))) :=
    fun _ _ hxy => Set.disjoint_singleton.mpr hxy
  have h_meas : ∀ x : α, MeasurableSet ({x} : Set α) := fun x => measurableSet_singleton x
  have h_tsum_eq : s.totalVariation (⋃ x : α, ({x} : Set α)) =
      ∑' x : α, s.totalVariation {x} := measure_iUnion h_disj h_meas
  rw [Set.iUnion_of_singleton α] at h_tsum_eq
  have h_finite : (∑' x : α, s.totalVariation ({x} : Set α)) ≠ ⊤ :=
    h_tsum_eq ▸ (totalVariation_univ_lt_top s).ne
  have h_sum_tv : Summable (fun x : α => (s.totalVariation ({x} : Set α)).toReal) :=
    ENNReal.summable_toReal h_finite
  exact h_sum_tv.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun x => (totalVariation_singleton_toReal s x).symm.le)

/-- For a countable measurable space, every signed measure is the sum over
singletons of its pointwise values weighted by Dirac deltas. -/
private lemma tsum_singleton_smul_dirac_eq [Countable α] (s : SignedMeasure α) :
    (∑' x : α, s ({x} : Set α) • dirac x) = s := by
  have hsum_smul : Summable (fun x : α => s ({x} : Set α) • dirac x) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, Real.norm_eq_abs, norm_dirac, mul_one]
      using summable_abs_singleton s
  refine VectorMeasure.ext (fun E hE => ?_)
  have h_apply : ∀ t : SignedMeasure α, applyCLM E t = t E := fun _ => rfl
  rw [← h_apply, ContinuousLinearMap.map_tsum (applyCLM E) hsum_smul]
  simp_rw [h_apply]
  have h_term : ∀ x : α, (s ({x} : Set α) • dirac x) E = s (({x} : Set α) ∩ E) := by
    intro x
    rw [VectorMeasure.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ E
    · rw [dirac_apply_of_mem hE hx, mul_one]
      congr 1
      exact (Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hx)).symm
    · rw [dirac_apply_of_notMem hE hx, mul_zero,
          Set.singleton_inter_of_notMem hx, VectorMeasure.empty]
  simp_rw [h_term]
  rw [← VectorMeasure.of_disjoint_iUnion (v := s)
    (fun x => (measurableSet_singleton x).inter hE)
    (fun _ _ hxy => (Set.disjoint_singleton.mpr hxy).inter_left _ |>.inter_right _)]
  congr 1
  ext y
  simp

/-- **Discrete–continuous decomposition of `M(K)`** (countable case). Every finite
signed measure on a countable measurable space decomposes as the sum of a
*discrete* part — an absolutely-summable signed combination of Dirac deltas,
indexed by a countable set of atoms — and a *continuous* (atomless) part, where
the latter has total variation in `MeasureTheory.NoAtoms`. The general case
requires infrastructure for decomposing measures into atomic and continuous
parts that is not yet available in Mathlib. -/
theorem exists_discrete_continuous_decomposition [Countable α] (s : SignedMeasure α) :
    ∃ (D : Set α) (c : α → ℝ) (sc : SignedMeasure α),
      D.Countable ∧
      Summable (fun x : D => |c x.val|) ∧
      MeasureTheory.NoAtoms sc.totalVariation ∧
      s = (∑' x : D, c x.val • dirac x.val) + sc := by
  refine ⟨Set.univ, fun x => s ({x} : Set α), 0, Set.countable_univ, ?_, ?_, ?_⟩
  · exact ((Equiv.Set.univ α).summable_iff).mpr (summable_abs_singleton s)
  · rw [SignedMeasure.totalVariation_zero]
    exact ⟨fun _ => rfl⟩
  · rw [add_zero]
    symm
    rw [show (∑' x : ↑(Set.univ : Set α), s ({x.val} : Set α) • dirac x.val) =
          ∑' x : α, s ({x} : Set α) • dirac x from
          (Equiv.Set.univ α).tsum_eq (fun x : α => s ({x} : Set α) • dirac x)]
    exact tsum_singleton_smul_dirac_eq s

end Atoms

end SignedMeasure
end MeasureTheory
