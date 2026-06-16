import BanLat.Normed
import BanLat.Preliminaries.SignedMeasure

/-!
# Finite signed measures as a Banach lattice

For a measurable space `α`, the space `MeasureTheory.SignedMeasure α` of finite
signed measures carries a canonical Banach lattice structure. Order, lattice
operations, and norm are described through the Jordan decomposition and the
total-variation measure. Completeness is obtained for the total-variation norm,
giving the Banach lattice of finite signed measures.
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

/-- A signed measure is the difference of its Jordan positive and negative
parts. -/
theorem posPart_sub_negPart (s : SignedMeasure α) :
    s.posPart - s.negPart = s := by
  unfold posPart negPart
  exact s.toSignedMeasure_toJordanDecomposition

/-- The positive part is non-negative as a signed measure. -/
theorem zero_le_posPart (s : SignedMeasure α) : 0 ≤ s.posPart :=
  Measure.zero_le_toSignedMeasure _

/-- The negative part is non-negative as a signed measure. -/
theorem zero_le_negPart (s : SignedMeasure α) : 0 ≤ s.negPart :=
  Measure.zero_le_toSignedMeasure _

/-- A signed measure is non-negative iff its Jordan negative part vanishes. -/
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

/-- Universal property of the positive part: `s.posPart` is the least
non-negative signed measure dominating `s`. -/
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
    rw [Set.inter_comm]
    exact Set.inter_union_diff i P
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

/-- The lattice supremum is represented by the Jordan positive part of the difference. -/
theorem max_def (s t : SignedMeasure α) : s ⊔ t = t + (s - t).posPart := rfl

/-- The lattice infimum is represented by subtracting the Jordan positive part
of the difference. -/
theorem min_def (s t : SignedMeasure α) : s ⊓ t = s - (s - t).posPart := rfl

/-- The lattice structure on signed measures, with suprema and infima computed
from the Jordan positive part of differences. -/
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

/-- Finite signed measures form a real vector lattice. -/
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

/-- The modulus of a signed measure is the sum of its Jordan positive and
negative parts. -/
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

/-! ### Absolute continuity and positive signed measures -/

/-- A non-negative signed measure equals the signed measure associated to its
positive Jordan part. -/
theorem eq_posPart_toSignedMeasure_of_nonneg {s : SignedMeasure α} (hs : 0 ≤ s) :
    s = s.toJordanDecomposition.posPart.toSignedMeasure := by
  have hneg : s.toJordanDecomposition.negPart.toSignedMeasure = 0 :=
    nonneg_iff_negPart_eq_zero.mp hs
  have h := posPart_sub_negPart s
  change s.toJordanDecomposition.posPart.toSignedMeasure -
      s.toJordanDecomposition.negPart.toSignedMeasure = s at h
  rw [hneg, sub_zero] at h
  exact h.symm

/-- For a non-negative signed measure, evaluating its positive Jordan part on
a measurable set agrees with evaluating the signed measure. -/
theorem real_apply_posPart_of_nonneg {s : SignedMeasure α} (hs : 0 ≤ s)
    {E : Set α} (hE : MeasurableSet E) :
    (s.toJordanDecomposition.posPart E).toReal = s E := by
  conv_rhs => rw [eq_posPart_toSignedMeasure_of_nonneg hs]
  rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def]

/-- For a non-negative signed measure, absolute continuity with respect to it
is equivalent to absolute continuity with respect to its positive Jordan part. -/
theorem absolutelyContinuous_iff_posPart_of_nonneg {s : SignedMeasure α}
    (hs : 0 ≤ s) {ν : SignedMeasure α} :
    ν ≪ᵥ s ↔ ν ≪ᵥ s.toJordanDecomposition.posPart.toENNRealVectorMeasure := by
  constructor
  · intro h
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hposE => ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at hposE
    have hsE : s E = 0 := by
      rw [← real_apply_posPart_of_nonneg hs hE, hposE, ENNReal.toReal_zero]
    exact h hsE
  · intro h
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE hsE => ?_
    have hfin : s.toJordanDecomposition.posPart E ≠ ⊤ := measure_ne_top _ _
    have hposzero : s.toJordanDecomposition.posPart E = 0 := by
      have : (s.toJordanDecomposition.posPart E).toReal = 0 := by
        rw [real_apply_posPart_of_nonneg hs hE]
        exact hsE
      rcases (ENNReal.toReal_eq_zero_iff _).mp this with hzero | htop
      · exact hzero
      · exact absurd htop hfin
    have hE' : s.toJordanDecomposition.posPart.toENNRealVectorMeasure E = 0 := by
      rw [Measure.toENNRealVectorMeasure_apply_measurable hE]
      exact hposzero
    exact h hE'

/-- For a non-negative signed measure, absolute continuity with respect to it
is equivalent to absolute continuity of total variations with respect to its
positive Jordan part. -/
theorem totalVariation_absolutelyContinuous_iff_of_nonneg {s : SignedMeasure α}
    (hs : 0 ≤ s) {ν : SignedMeasure α} :
    ν ≪ᵥ s ↔ ν.totalVariation ≪ s.toJordanDecomposition.posPart := by
  rw [absolutelyContinuous_iff_posPart_of_nonneg hs]
  rw [absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]

/-- If `ν₂` is dominated in modulus by `ν₁`, and `ν₁` is absolutely continuous
with respect to a non-negative signed measure `s`, then `ν₂` is also
absolutely continuous with respect to `s`. -/
theorem abs_le_of_absolutelyContinuous {s : SignedMeasure α} (hs : 0 ≤ s)
    {ν₁ ν₂ : SignedMeasure α} (h : ν₁ ≪ᵥ s) (hle : |ν₂| ≤ |ν₁|) :
    ν₂ ≪ᵥ s := by
  rw [totalVariation_absolutelyContinuous_iff_of_nonneg hs] at h ⊢
  refine Measure.AbsolutelyContinuous.mk fun E hE hposE => ?_
  have hν₁ : ν₁.totalVariation E = 0 := h hposE
  have h1 : (ν₁.totalVariation E).toReal = (|ν₁| : SignedMeasure α) E :=
    (abs_apply_eq_totalVariation ν₁ E hE).symm
  have h2 : (ν₂.totalVariation E).toReal = (|ν₂| : SignedMeasure α) E :=
    (abs_apply_eq_totalVariation ν₂ E hE).symm
  have h3 : (|ν₂| : SignedMeasure α) E ≤
      (|ν₁| : SignedMeasure α) E := hle E hE
  have h4 : (ν₂.totalVariation E).toReal ≤ (ν₁.totalVariation E).toReal := by
    rw [h2, h1]
    exact h3
  have hν₁zero : (ν₁.totalVariation E).toReal = 0 := by rw [hν₁]; simp
  rw [hν₁zero] at h4
  have hν₂nn : 0 ≤ (ν₂.totalVariation E).toReal := ENNReal.toReal_nonneg
  have hν₂real : (ν₂.totalVariation E).toReal = 0 := le_antisymm h4 hν₂nn
  have hfin : ν₂.totalVariation E ≠ ⊤ := measure_ne_top _ _
  rcases (ENNReal.toReal_eq_zero_iff _).mp hν₂real with hzero | htop
  · exact hzero
  · exact absurd htop hfin

/-! ### Total-variation norm

We package `s ↦ (s.totalVariation univ).toReal` as an `AddGroupNorm`, then
upgrade to a `NormedAddCommGroup` via `AddGroupNorm.toNormedAddCommGroup`. -/

/-- The additive group norm on finite signed measures given by total variation
on the universe. -/
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

/-- The value of a signed measure on a measurable set is bounded by its
total-variation norm. -/
theorem abs_apply_le_norm (s : SignedMeasure α) {E : Set α} (hE : MeasurableSet E) :
    |s E| ≤ ‖s‖ := by
  rw [norm_def]
  exact abs_apply_le_totalVariation_univ s hE

/-- Evaluation of a signed measure on a fixed measurable set is continuous for
the total-variation norm. -/
theorem continuous_apply {E : Set α} (hE : MeasurableSet E) :
    Continuous (fun ν : SignedMeasure α => ν E) := by
  refine Metric.continuous_iff.mpr fun ν ε hε => ⟨ε, hε, fun ν' hν' => ?_⟩
  rw [Real.dist_eq]
  have hsub : ν' E - ν E = (ν' - ν) E := by
    rw [VectorMeasure.sub_apply]
  rw [hsub]
  calc
    |(ν' - ν) E| ≤ ‖ν' - ν‖ := abs_apply_le_norm _ hE
    _ = dist ν' ν := (dist_eq_norm _ _).symm
    _ < ε := hν'

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

end SignedMeasure
end MeasureTheory
