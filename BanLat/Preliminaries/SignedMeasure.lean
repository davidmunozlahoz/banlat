import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-!
# Auxiliary measure-theoretic facts about signed measures

This file collects measure-theoretic facts about
`MeasureTheory.SignedMeasure.totalVariation` and the Jordan decomposition that
are used to put a Banach lattice structure on the space of finite signed
measures (see `BanLat.Examples.MofK`).

The statements here belong to measure theory, not to vector or Banach lattice
theory: nothing in this file mentions `Lattice`, `VectorLattice`, norms, or
the order on signed measures beyond what is already in Mathlib.
-/

namespace MeasureTheory
namespace SignedMeasure

variable {α : Type*} [MeasurableSpace α]

/-! ### Finiteness of the total variation -/

/-- The total variation of any signed measure is a finite (positive) measure. -/
instance instIsFiniteMeasure_totalVariation (s : SignedMeasure α) :
    IsFiniteMeasure s.totalVariation := by
  rw [SignedMeasure.totalVariation]; infer_instance

/-- The total variation on the universe is `< ⊤`. -/
theorem totalVariation_univ_lt_top (s : SignedMeasure α) :
    s.totalVariation Set.univ < ⊤ :=
  measure_lt_top _ _

/-! ### Vanishing -/

/-- The total variation of the zero signed measure is the zero measure. -/
theorem totalVariation_zero_eq :
    totalVariation (0 : SignedMeasure α) = 0 :=
  totalVariation_zero

/-- A signed measure with vanishing total variation on the universe is itself zero. -/
theorem eq_zero_of_totalVariation_univ_eq_zero {s : SignedMeasure α}
    (h : s.totalVariation Set.univ = 0) : s = 0 := by
  ext i hi
  change s i = 0
  exact null_of_totalVariation_zero s
    (le_antisymm (h ▸ measure_mono (Set.subset_univ i)) (zero_le _))

/-! ### Sub-additivity -/

/-- A signed measure equals the difference of the (real values of the) Jordan parts. -/
private lemma apply_eq_real_sub (s : SignedMeasure α) {A : Set α} (hA : MeasurableSet A) :
    s A = s.toJordanDecomposition.posPart.real A -
          s.toJordanDecomposition.negPart.real A := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.coe_sub, Pi.sub_apply,
    Measure.toSignedMeasure_apply_measurable hA,
    Measure.toSignedMeasure_apply_measurable hA]

/-- For any measurable set `P`, `s P - s Pᶜ ≤ |s|(univ)`. -/
private lemma diff_le_totalVariation_real (s : SignedMeasure α) {P : Set α}
    (hP : MeasurableSet P) :
    s P - s Pᶜ ≤ (s.totalVariation Set.univ).toReal := by
  rw [SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply,
    apply_eq_real_sub s hP, apply_eq_real_sub s hP.compl]
  have h1 : s.toJordanDecomposition.posPart.real P ≤
      s.toJordanDecomposition.posPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h2 : s.toJordanDecomposition.negPart.real Pᶜ ≤
      s.toJordanDecomposition.negPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h3 : 0 ≤ s.toJordanDecomposition.posPart.real Pᶜ := measureReal_nonneg
  have h4 : 0 ≤ s.toJordanDecomposition.negPart.real P := measureReal_nonneg
  linarith

/-- The total variation is sub-additive on the universe (real-valued form). -/
private lemma toReal_totalVariation_add_univ_le_aux (s t : SignedMeasure α) :
    ((s + t).totalVariation Set.univ).toReal ≤
      (s.totalVariation Set.univ).toReal +
        (t.totalVariation Set.univ).toReal := by
  obtain ⟨P, hP, hP₂, hP₃, hpos, hneg⟩ := (s + t).toJordanDecomposition_spec
  rw [SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply, hpos, hneg,
    toMeasureOfZeroLE_real_apply _ hP₂ hP MeasurableSet.univ,
    toMeasureOfLEZero_real_apply _ hP₃ hP.compl MeasurableSet.univ,
    Set.inter_univ, Set.inter_univ]
  have hs := diff_le_totalVariation_real s hP
  have ht := diff_le_totalVariation_real t hP
  have hadd_P : (s + t) P = s P + t P := by simp
  have hadd_Pc : (s + t) Pᶜ = s Pᶜ + t Pᶜ := by simp
  rw [hadd_P, hadd_Pc]
  linarith

/-- The total variation is sub-additive on the universe:
`|s + t|(univ) ≤ |s|(univ) + |t|(univ)`. -/
theorem totalVariation_add_univ_le (s t : SignedMeasure α) :
    (s + t).totalVariation Set.univ ≤
      s.totalVariation Set.univ + t.totalVariation Set.univ := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact toReal_totalVariation_add_univ_le_aux s t

/-! ### Scalar multiplication -/

/-- Total variation is positively homogeneous in the scalar:
`|c • s|(univ) = ENNReal.ofReal |c| * |s|(univ)`. -/
theorem totalVariation_smul_univ (c : ℝ) (s : SignedMeasure α) :
    (c • s).totalVariation Set.univ =
      ENNReal.ofReal |c| * s.totalVariation Set.univ := by
  rw [SignedMeasure.totalVariation, SignedMeasure.totalVariation,
    toJordanDecomposition_smul_real]
  by_cases hc : 0 ≤ c
  · rw [JordanDecomposition.real_smul_nonneg _ _ hc, JordanDecomposition.smul_posPart,
      JordanDecomposition.smul_negPart, Measure.add_apply, Measure.add_apply,
      Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, ← mul_add,
      abs_of_nonneg hc, ← ENNReal.ofNNReal_toNNReal]
  · push_neg at hc
    rw [JordanDecomposition.real_smul_neg _ _ hc, JordanDecomposition.neg_posPart,
      JordanDecomposition.neg_negPart, JordanDecomposition.smul_posPart,
      JordanDecomposition.smul_negPart, Measure.add_apply, Measure.add_apply,
      Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply, ← mul_add,
      add_comm (s.toJordanDecomposition.negPart Set.univ) _,
      abs_of_neg hc, ← ENNReal.ofNNReal_toNNReal]

/-! ### Comparison and modulus -/

/-- For a non-negative signed measure, the total variation on the universe agrees with the
value of the measure. -/
theorem totalVariation_univ_eq_of_nonneg {s : SignedMeasure α} (hs : 0 ≤ s) :
    (s.totalVariation Set.univ).toReal = (s Set.univ : ℝ) := by
  have hs' : (0 : SignedMeasure α) ≤[Set.univ] s :=
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
  rw [SignedMeasure.totalVariation, hj]
  change ((s.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs' + (0 : Measure α))
    Set.univ).toReal = s Set.univ
  rw [add_zero, toMeasureOfZeroLE_apply _ _ _ MeasurableSet.univ]
  simp

/-- Sub-additivity rewritten with `.toReal`. -/
theorem toReal_totalVariation_add_univ_le (s t : SignedMeasure α) :
    ((s + t).totalVariation Set.univ).toReal ≤
      (s.totalVariation Set.univ).toReal +
        (t.totalVariation Set.univ).toReal :=
  toReal_totalVariation_add_univ_le_aux s t

/-- The value of a signed measure on a measurable set is bounded in absolute
value by the total variation on the universe: `|s A| ≤ |s|(univ)`. Obtained by
splitting `A = (A ∩ P) ∪ (A ∩ Pᶜ)` along a Hahn decomposition `(P, Pᶜ)` of `s`
and bounding each piece by the corresponding Jordan part. -/
theorem abs_apply_le_totalVariation_univ (s : SignedMeasure α) {A : Set α}
    (hA : MeasurableSet A) :
    |(s A : ℝ)| ≤ (s.totalVariation Set.univ).toReal := by
  rw [SignedMeasure.totalVariation, ← measureReal_def, measureReal_add_apply,
    apply_eq_real_sub s hA]
  have h1 : s.toJordanDecomposition.posPart.real A ≤
      s.toJordanDecomposition.posPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h2 : s.toJordanDecomposition.negPart.real A ≤
      s.toJordanDecomposition.negPart.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  have h3 : 0 ≤ s.toJordanDecomposition.posPart.real A := measureReal_nonneg
  have h4 : 0 ≤ s.toJordanDecomposition.negPart.real A := measureReal_nonneg
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

/-! ### Completeness in total variation (Vitali–Hahn–Saks)

A sequence of signed measures that is Cauchy in the total-variation distance
admits a signed-measure limit, with convergence in total variation. This is
the measure-theoretic content underlying the `CompleteSpace` instance on the
Banach lattice `M(K)` of finite signed measures (see `BanLat.Examples.MofK`).

The result is the **Vitali–Hahn–Saks** (a.k.a. Nikodym convergence) theorem
in disguise: the set-wise limit of a TV-Cauchy sequence is automatically
countably additive, hence a signed measure.
-/

/-! ### Proof outline for `exists_tv_limit_of_cauchy`

Given a TV-Cauchy sequence of signed measures, we produce a signed-measure
limit in five steps.

1. *Set-wise Cauchy.* For any measurable set `A`, the bound
   `|(sₘ - sₙ) A| ≤ ((sₘ - sₙ).totalVariation Set.univ).toReal`
   (a routine consequence of `diff_le_totalVariation_real` applied to a Hahn
   decomposition of `sₘ - sₙ` and the splitting `A = (A ∩ P) ∪ (A ∩ Pᶜ)`)
   shows that `(sₙ A)ₙ` is Cauchy in `ℝ`, hence converges to some
   `t₀ A : ℝ`.

2. *Finite additivity of `t₀`.* For disjoint measurable `A`, `B`, finite
   additivity of each `sₙ` and continuity of addition give
   `t₀ (A ∪ B) = lim (sₙ (A ∪ B)) = lim (sₙ A + sₙ B) = t₀ A + t₀ B`,
   and `t₀ ∅ = 0` is immediate.

3. *Countable additivity (Nikodym / Vitali–Hahn–Saks).* For a pairwise
   disjoint measurable family `(Aₖ)`, the convergence of the partial sums
   `Σ_{k < K} sₙ Aₖ → sₙ (⋃ₖ Aₖ)` is **uniform in `n`**. Concretely, the
   tail bound
   `|Σ_{k ≥ K} sₙ Aₖ| ≤ (sₙ.totalVariation) (⋃_{k ≥ K} Aₖ)`,
   together with uniform absolute continuity of the family `{sₙ.totalVariation}`
   with respect to the finite control measure
   `μ := |s₀|.totalVariation +
        Σₙ 2 ^ (-n) • |sₙ₊₁ - sₙ|.totalVariation /
            (1 + ((sₙ₊₁ - sₙ).totalVariation Set.univ).toReal)`,
   lets us exchange the sum and the limit. Hence
   `t₀ (⋃ₖ Aₖ) = Σₖ t₀ Aₖ`.

4. *Bundle as a `SignedMeasure`.* Wrap `t₀` as a `VectorMeasure ℝ` using the
   countable additivity from step 3; finiteness of `t₀ Set.univ` is automatic
   from the TV-Cauchy bound applied to a fixed reference index.

5. *TV convergence.* Given `ε > 0`, pick `N` with
   `((sₘ - sₙ).totalVariation Set.univ).toReal < ε` for all `m, n ≥ N`. For
   `n ≥ N`, take a Hahn decomposition `(P, Pᶜ)` of `t - sₙ` and use
   `totalVariationReal_eq_sub_of_isHahnDecomposition` to rewrite
   `((t - sₙ).totalVariation Set.univ).toReal = (t - sₙ) P - (t - sₙ) Pᶜ`,
   then pass to the limit `m → ∞` inside the parentheses.

The intermediate lemmas below isolate the four nontrivial steps; only Step 3
(`exists_tail_lt_of_tvCauchy`) genuinely uses the Vitali–Hahn–Saks heart.
-/

/-- *Step 1.* A TV-Cauchy sequence of signed measures is set-wise Cauchy on
every measurable set; in particular it admits a real-valued set-wise limit.
Direct from `abs_apply_le_totalVariation_univ` applied to differences. -/
private theorem exists_tendsto_apply_of_tvCauchy
    (s : ℕ → SignedMeasure α)
    (hs : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ((s m - s n).totalVariation Set.univ).toReal < ε)
    {A : Set α} (hA : MeasurableSet A) :
    ∃ ℓ : ℝ, ∀ ε > 0, ∃ N, ∀ n ≥ N, |((s n) A : ℝ) - ℓ| < ε := by
  have hCauchy : CauchySeq (fun n => ((s n) A : ℝ)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    have hbound := abs_apply_le_totalVariation_univ (s m - s n) hA
    have heq : ((s m - s n) A : ℝ) = (s m A : ℝ) - (s n A : ℝ) := by
      simp [VectorMeasure.sub_apply]
    rw [heq] at hbound
    exact lt_of_le_of_lt hbound (hN m hm n hn)
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨ℓ, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hℓ ε hε
  exact ⟨N, fun n hn => by rw [← Real.dist_eq]; exact hN n hn⟩

/-- *Step 3 (Vitali–Hahn–Saks core).* If `(sₙ)` is Cauchy in total variation
and `(Aₖ)` is a pairwise disjoint sequence of measurable sets, then for any
`ε > 0` there exists `K` such that the value of every `sₙ` on the tail union
`⋃_{k ≥ K} Aₖ` is less than `ε` in absolute value, **uniformly in `n`**.

This is the heart of the Vitali–Hahn–Saks theorem and the only step that
genuinely uses the TV-Cauchy hypothesis (beyond producing the pointwise limit
in Step 1). The standard proof builds a finite control measure
`μ := |s₀|.totalVariation +
      Σₙ 2 ^ (-n) • |sₙ₊₁ - sₙ|.totalVariation /
          (1 + ((sₙ₊₁ - sₙ).totalVariation Set.univ).toReal)`
and observes that the family `{|sₙ|.totalVariation}` is uniformly absolutely
continuous with respect to `μ`. -/
private theorem exists_tail_lt_of_tvCauchy
    (s : ℕ → SignedMeasure α)
    (hs : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ((s m - s n).totalVariation Set.univ).toReal < ε)
    {A : ℕ → Set α} (hA : ∀ k, MeasurableSet (A k))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ n, |((s n) (⋃ k, ⋃ (_ : K ≤ k), A k) : ℝ)| < ε :=
  sorry

/-- *Step 5 (Hahn-decomposition formula).* Given a Hahn decomposition
`(P, Pᶜ)` of `s` — i.e., `s` is non-negative on `P` and non-positive on `Pᶜ` —
the real-valued total variation on the universe is the difference
`s P - s Pᶜ`. Used in the final step of `exists_tv_limit_of_cauchy` to extract
TV convergence from set-wise convergence. -/
private theorem totalVariationReal_eq_sub_of_isHahnDecomposition
    (s : SignedMeasure α) {P : Set α} (hP : MeasurableSet P)
    (hPpos : (0 : SignedMeasure α) ≤[P] s) (hPneg : s ≤[Pᶜ] 0) :
    (s.totalVariation Set.univ).toReal = (s P : ℝ) - s Pᶜ := by
  let j : JordanDecomposition α :=
    { posPart := s.toMeasureOfZeroLE P hP hPpos
      negPart := s.toMeasureOfLEZero Pᶜ hP.compl hPneg
      mutuallySingular := by
        refine ⟨Pᶜ, hP.compl, ?_, ?_⟩
        · rw [toMeasureOfZeroLE_apply _ _ hP hP.compl]; simp
        · rw [toMeasureOfLEZero_apply _ _ hP.compl hP.compl.compl]; simp }
  have hj : s.toJordanDecomposition = j := by
    refine toJordanDecomposition_eq ?_
    ext k hk
    have hdisj : Disjoint (P ∩ k) (Pᶜ ∩ k) := by
      exact Set.disjoint_left.mpr fun x ⟨hxP, _⟩ ⟨hxPc, _⟩ => hxPc hxP
    have hsplit : (s : SignedMeasure α) k = s (P ∩ k) + s (Pᶜ ∩ k) := by
      rw [← VectorMeasure.of_union (v := s) hdisj (hP.inter hk) (hP.compl.inter hk),
        ← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hk,
      toMeasureOfZeroLE_real_apply _ hPpos hP hk,
      toMeasureOfLEZero_real_apply _ hPneg hP.compl hk, sub_neg_eq_add, hsplit]
  rw [SignedMeasure.totalVariation, hj, ← measureReal_def, measureReal_add_apply,
    toMeasureOfZeroLE_real_apply _ hPpos hP MeasurableSet.univ,
    toMeasureOfLEZero_real_apply _ hPneg hP.compl MeasurableSet.univ,
    Set.inter_univ, Set.inter_univ]
  ring

/-- **Vitali–Hahn–Saks completeness for signed measures.** -/
theorem exists_tv_limit_of_cauchy
    (s : ℕ → SignedMeasure α)
    (hs : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ((s m - s n).totalVariation Set.univ).toReal < ε) :
    ∃ t : SignedMeasure α, ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ((s n - t).totalVariation Set.univ).toReal < ε :=
  sorry

end SignedMeasure
end MeasureTheory
