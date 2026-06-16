import BanLat.Examples.MofK.Atom
import BanLat.Examples.MofK.ALspace
import BanLat.Substructures.Band.PPP

/-!
# Atomic decompositions in `M(K)`

This file develops the atomic and continuous parts of `M(K)` and the
countable decomposition of atomic regular signed measures into Dirac masses.
-/

open MeasureTheory Set

namespace MofK

universe u

variable {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-! ### Atomic and continuous parts -/

namespace MeasureTheory.SignedMeasure

/-- A signed measure has no atoms when its total variation has no atoms. -/
abbrev NoAtoms (s : SignedMeasure K) : Prop :=
  MeasureTheory.NoAtoms s.totalVariation

end MeasureTheory.SignedMeasure

private theorem isVLDisjoint_dirac_iff_singleton_zero (μ : MofK K) (x : K) :
    IsVLDisjoint μ (dirac x) ↔ (|(μ : SignedMeasure K)|) ({x} : Set K) = 0 := by
  have habs_dx :
      |((dirac x : MofK K) : SignedMeasure K)| = ((dirac x : MofK K) : SignedMeasure K) :=
    abs_of_nonneg (zero_le_dirac x)
  refine Iff.trans ?_ (signedMeasure_inf_dirac_eq_zero_iff (abs_nonneg _) x)
  constructor
  · intro h
    have hh : ((|μ| ⊓ |dirac x| : MofK K) : SignedMeasure K) = 0 := congrArg Subtype.val h
    change (|(μ : SignedMeasure K)| ⊓ |((dirac x : MofK K) : SignedMeasure K)| :
      SignedMeasure K) = 0 at hh
    rwa [habs_dx] at hh
  · intro h
    apply Subtype.ext
    change (|(μ : SignedMeasure K)| ⊓ |((dirac x : MofK K) : SignedMeasure K)| :
      SignedMeasure K) = 0
    rwa [habs_dx]

/-- A measure belongs to the continuous part of `M(K)` exactly when it has no
atoms as a signed measure. -/
theorem mem_continuousPart_iff (μ : MofK K) :
    μ ∈ continuousPart (MofK K) ↔ MeasureTheory.SignedMeasure.NoAtoms (μ : SignedMeasure K) := by
  refine ⟨fun hμ => ?_, fun hμ a ha => ?_⟩
  · refine ⟨fun x => ?_⟩
    have hdisj : IsVLDisjoint μ (dirac x) := hμ _ (isVLAtom_dirac x)
    have h0r :
        (((μ : SignedMeasure K).totalVariation ({x} : Set K)).toReal) = 0 := by
      simpa [MeasureTheory.SignedMeasure.NoAtoms,
        MeasureTheory.SignedMeasure.abs_apply_eq_totalVariation _ _ (measurableSet_singleton x)]
        using (isVLDisjoint_dirac_iff_singleton_zero μ x).mp hdisj
    rcases (ENNReal.toReal_eq_zero_iff ((μ : SignedMeasure K).totalVariation ({x} : Set K))).mp h0r
      with h0 | htop
    · exact h0
    · exact False.elim ((measure_ne_top _ _) htop)
  · obtain ⟨c, x, hc, ha_eq⟩ := (isVLAtom_iff_exists_smul_dirac a).mp ha
    have hdx : IsVLDisjoint μ (dirac x) :=
      (isVLDisjoint_dirac_iff_singleton_zero μ x).mpr <| by
        rw [MeasureTheory.SignedMeasure.abs_apply_eq_totalVariation _ _
          (measurableSet_singleton x), hμ.measure_singleton x, ENNReal.toReal_zero]
    have hcd_nn : (0 : MofK K) ≤ c • dirac x := smul_nonneg hc.le (zero_le_dirac x)
    have hdirac_abs : |dirac x| = dirac x := abs_of_nonneg (zero_le_dirac x)
    have hzero : |μ| ⊓ dirac x = 0 := by
      have : |μ| ⊓ |dirac x| = 0 := hdx
      rwa [hdirac_abs] at this
    have hcd_disj : (c • dirac x) ⊓ |μ| = 0 :=
      inf_eq_zero_of_isVLDisjoint hcd_nn (abs_nonneg _)
        ((isVLDisjoint_of_inf_eq_zero (by rw [inf_comm, hzero])).smul_left c)
    change |μ| ⊓ |a| = 0
    rw [ha_eq, abs_of_nonneg hcd_nn, inf_comm]
    exact hcd_disj

private noncomputable def indicatorSubtype (A : Set K) {s : Set K} (c : s → ℝ) : s → ℝ := by
  classical
  exact fun x => if x.1 ∈ A then c x else 0

private noncomputable def evalCLM (A : Set K) (hA : MeasurableSet A) : MofK K →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun μ => (μ : SignedMeasure K) A
      map_add' := by intro μ ν; simp
      map_smul' := by intro c μ; simp [VectorMeasure.smul_apply, smul_eq_mul] }
    1
    (by
      intro μ
      calc
        |(μ : SignedMeasure K) A|
          ≤ ((μ : SignedMeasure K).totalVariation Set.univ).toReal :=
            MeasureTheory.SignedMeasure.abs_apply_le_totalVariation_univ _ hA
        _ = ‖(μ : SignedMeasure K)‖ := (MeasureTheory.SignedMeasure.norm_def _).symm
        _ ≤ 1 * ‖μ‖ := by simp)

private theorem evalCLM_apply (A : Set K) (hA : MeasurableSet A) (μ : MofK K) :
    evalCLM A hA μ = (μ : SignedMeasure K) A := rfl

omit [CompactSpace K] in
private theorem countable_pos_singletons (m : Measure K) [SFinite m] :
    Set.Countable {x : K | 0 < m ({x} : Set K)} := by
  simpa only [Set.mem_setOf_eq] using
    (Measure.countable_meas_pos_of_disjoint_iUnion (μ := m)
      (As_mble := fun x => measurableSet_singleton x)
      (As_disj := fun x y hxy => by
        simpa [Set.disjoint_singleton] using hxy))

private theorem finite_sum_smul_dirac_mem_atomicPart {s : Set K} (c : s → ℝ) :
    ∀ t : Finset s, (t.sum fun x => c x • dirac x.1 : MofK K) ∈ atomicPart (MofK K) := by
  intro t
  classical
  refine Finset.induction_on t ?_ ?_
  · exact (atomicPart (MofK K)).toOrderIdeal.toSubmodule.zero_mem
  · intro a t ha ht
    have ha_mem : c a • dirac a.1 ∈ atomicPart (MofK K) := by
      exact (atomicPart (MofK K)).toOrderIdeal.toSubmodule.smul_mem _ <|
        isVLAtom.mem_atomicPart (X := MofK K) (isVLAtom_dirac a.1)
    simpa [Finset.sum_insert, ha] using
      (atomicPart (MofK K)).toOrderIdeal.toSubmodule.add_mem ha_mem ht

private theorem tsum_smul_dirac_mem_atomicPart {s : Set K} (c : s → ℝ)
    (hc_sum : Summable (fun x : s => c x • dirac x.1)) :
    (∑' x : s, c x • dirac x.1 : MofK K) ∈ atomicPart (MofK K) := by
  have hclosed : IsClosed ((atomicPart (MofK K) : Band (MofK K)) : Set (MofK K)) :=
    (atomicPart (MofK K)).isClosed_coe
  exact hclosed.mem_of_tendsto hc_sum.hasSum
    (Filter.Eventually.of_forall (finite_sum_smul_dirac_mem_atomicPart (K := K) c))

private theorem tsum_smul_dirac_apply {s : Set K} {c : s → ℝ}
    (hc_sum : Summable (fun x : s => c x • dirac x.1))
    (A : Set K) (hA : MeasurableSet A) :
    ((∑' x : s, c x • dirac x.1 : MofK K) : SignedMeasure K) A =
      ∑' x : s, indicatorSubtype A c x := by
  classical
  rw [show ((∑' x : s, c x • dirac x.1 : MofK K) : SignedMeasure K) A =
      evalCLM A hA (∑' x : s, c x • dirac x.1) by rfl,
    (evalCLM A hA).map_tsum hc_sum]
  congr with x
  dsimp [evalCLM_apply, indicatorSubtype]
  by_cases hxA : x.1 ∈ A
  · rw [if_pos hxA, dirac_apply_of_mem hA hxA, mul_one]
  · rw [if_neg hxA, dirac_apply_of_notMem hA hxA, mul_zero]

omit [CompactSpace K] in
private theorem tsum_indicator_singletons_le_measure (m : Measure K) [SFinite m]
    (s : Set K) (A : Set K) (hA : MeasurableSet A) :
    ∑' x : s, A.indicator (fun y => m ({y} : Set K)) x.1 ≤ m A := by
  calc
    ∑' x : s, A.indicator (fun y => m ({y} : Set K)) x.1
        = ∑' x : s, m (A ∩ ({x.1} : Set K)) := by
          congr with x
          by_cases hxA : x.1 ∈ A
          · have hAx : A ∩ ({x.1} : Set K) = ({x.1} : Set K) := by
              ext y
              simp [hxA]
            simp [Set.indicator_of_mem, hxA, hAx]
          · have hAx : A ∩ ({x.1} : Set K) = ∅ := by
              ext y
              simp [hxA]
            simp [Set.indicator_of_notMem, hxA, hAx]
    _ ≤ m (⋃ x : s, A ∩ ({x.1} : Set K)) :=
      MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint m
        (As_mble := fun x : s => hA.inter (measurableSet_singleton x.1))
        (As_disj := fun x y hxy => by
          refine Set.disjoint_left.mpr ?_
          intro z hz1 hz2
          have hzx : z = x.1 := by simpa using hz1.2
          have hzy : z = y.1 := by simpa using hz2.2
          exact hxy (Subtype.ext (hzx.symm.trans hzy)))
    _ ≤ m A := by
      refine measure_mono ?_
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
      exact hx.1

omit [CompactSpace K] in
private theorem tsum_toReal_indicator_singletons_le_measure (m : Measure K)
    [IsFiniteMeasure m] [SFinite m] (s : Set K) (A : Set K) (hA : MeasurableSet A) :
    ∑' x : s, A.indicator (fun y => (m ({y} : Set K)).toReal) x.1 ≤ (m A).toReal := by
  have h_indicator :
      (fun x : s => A.indicator (fun y => (m ({y} : Set K)).toReal) x.1) =
        fun x : s => (A.indicator (fun y => m ({y} : Set K)) x.1).toReal := by
    funext x
    by_cases hxA : x.1 ∈ A
    · simp [Set.indicator_of_mem, hxA]
    · simp [Set.indicator_of_notMem, hxA]
  have hfin : ∀ x : s, A.indicator (fun y => m ({y} : Set K)) x.1 ≠ ⊤ := by
    intro x
    by_cases hxA : x.1 ∈ A
    · simp [Set.indicator_of_mem, hxA, measure_ne_top]
    · simp [Set.indicator_of_notMem, hxA]
  rw [h_indicator, ← ENNReal.tsum_toReal_eq hfin]
  exact ENNReal.toReal_mono (measure_ne_top _ _) <|
    tsum_indicator_singletons_le_measure m s A hA

private theorem tsum_smul_dirac_nonneg_of_nonneg {s : Set K} {c : s → ℝ}
    (hc_sum : Summable (fun x : s => c x • dirac x.1))
    (hc_nn : ∀ x, 0 ≤ c x) :
    (0 : MofK K) ≤ ∑' x : s, c x • dirac x.1 := by
  classical
  intro A hA
  change (0 : ℝ) ≤ (((∑' x : s, c x • dirac x.1 : MofK K) : SignedMeasure K) A)
  rw [tsum_smul_dirac_apply hc_sum A hA]
  exact tsum_nonneg fun x => by
    dsimp [indicatorSubtype]
    by_cases hxA : x.1 ∈ A
    · simp [hxA, hc_nn x]
    · simp [hxA]

private theorem tsum_pos_singleton_dirac_apply (m : Measure K) [IsFiniteMeasure m] [SFinite m]
    (s : Set K) (hs : s = {x : K | 0 < m ({x} : Set K)})
    (hc_sum : Summable (fun y : s => (m ({y.1} : Set K)).toReal • dirac y.1))
    (x : K) :
    (((∑' y : s, (m ({y.1} : Set K)).toReal • dirac y.1 : MofK K) : SignedMeasure K)
      ({x} : Set K)) = (m ({x} : Set K)).toReal := by
  classical
  rw [tsum_smul_dirac_apply hc_sum ({x} : Set K) (measurableSet_singleton x)]
  by_cases hx : x ∈ s
  · let y : s := ⟨x, hx⟩
    rw [tsum_eq_single y]
    · simp [indicatorSubtype, y]
    · intro z hz
      by_cases hzx : z.1 = x
      · exact False.elim (hz (Subtype.ext hzx))
      · simp [indicatorSubtype, hzx]
  · have hzero : ∀ y : s,
        indicatorSubtype ({x} : Set K) (fun y : s => (m ({y.1} : Set K)).toReal) y = 0 := by
      intro y
      dsimp [indicatorSubtype]
      by_cases hyx : y.1 = x
      · exfalso
        exact hx (hyx ▸ y.2)
      · simp [hyx]
    have hfun_zero :
        indicatorSubtype ({x} : Set K) (fun y : s => (m ({y.1} : Set K)).toReal) = 0 := by
      funext y
      exact hzero y
    have hx0 : ¬ 0 < m ({x} : Set K) := by simpa [hs] using hx
    have hm_zero : m ({x} : Set K) = 0 := le_antisymm (not_lt.mp hx0) bot_le
    rw [hfun_zero, hm_zero, ENNReal.toReal_zero]
    exact tsum_zero

private theorem noAtoms_of_nonneg_of_singleton_zero (ν : MofK K)
    (hν_nonneg : 0 ≤ ν)
    (hν_singleton : ∀ x : K, (ν : SignedMeasure K) ({x} : Set K) = 0) :
    MeasureTheory.SignedMeasure.NoAtoms (ν : SignedMeasure K) := by
  refine ⟨fun x => ?_⟩
  have h0r :
      (((ν : SignedMeasure K).totalVariation ({x} : Set K)).toReal) = 0 := by
    rw [← MeasureTheory.SignedMeasure.abs_apply_eq_totalVariation _ _ (measurableSet_singleton x),
      show |(ν : SignedMeasure K)| = (ν : SignedMeasure K) from abs_of_nonneg hν_nonneg]
    exact hν_singleton x
  rcases (ENNReal.toReal_eq_zero_iff ((ν : SignedMeasure K).totalVariation ({x} : Set K))).mp h0r
    with h0 | htop
  · exact h0
  · exact False.elim ((measure_ne_top _ _) htop)

/-- A non-negative measure in the atomic part of `M(K)` is a countable sum of
Dirac deltas with non-negative coefficients. -/
theorem exists_nonneg_sum_dirac_of_mem_atomicPart {μ : MofK K}
    (hμ0 : 0 ≤ μ) (hμa : μ ∈ atomicPart (MofK K)) :
    ∃ (ι : Type u) (_ : Countable ι) (c : ι → ℝ) (x : ι → K),
      (∀ i, 0 ≤ c i) ∧
      Summable (fun i : ι => c i • dirac (x i)) ∧
      μ = ∑' i : ι, c i • dirac (x i) := by
  let m : Measure K := (μ : SignedMeasure K).toMeasureOfZeroLE
    Set.univ MeasurableSet.univ ((VectorMeasure.le_restrict_univ_iff_le _ _).mpr hμ0)
  haveI : IsFiniteMeasure m := by
    dsimp [m]
    infer_instance
  letI : SFinite m := by infer_instance
  have hm_signed : m.toSignedMeasure = (μ : SignedMeasure K) := by
    exact MeasureTheory.SignedMeasure.toMeasureOfZeroLE_toSignedMeasure _ _
  let s : Set K := {x | 0 < m ({x} : Set K)}
  have hs_count : s.Countable := countable_pos_singletons m
  let f : s → MofK K := fun x => (m ({x.1} : Set K)).toReal • dirac x.1
  have hsum_ennreal : (∑' x : s, m ({x.1} : Set K)) ≠ ⊤ := by
    refine (lt_of_le_of_lt ?_ (measure_lt_top m Set.univ)).ne
    calc
      ∑' x : s, m ({x.1} : Set K) ≤ m (⋃ x : s, ({x.1} : Set K)) :=
        MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint m
          (As_mble := fun x : s => measurableSet_singleton x.1)
          (As_disj := fun x y hxy => by simpa [Subtype.val_inj] using hxy)
      _ ≤ m Set.univ := measure_mono (Set.subset_univ _)
  have hcoeff_sum : Summable (fun x : s => (m ({x.1} : Set K)).toReal) :=
    ENNReal.summable_toReal hsum_ennreal
  have hf_sum : Summable f := by
    refine Summable.of_norm_bounded hcoeff_sum ?_
    intro x
    calc
      ‖f x‖ = ‖(m ({x.1} : Set K)).toReal‖ * ‖dirac x.1‖ := norm_smul _ _
      _ ≤ (m ({x.1} : Set K)).toReal := by
        rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, norm_dirac, mul_one]
  have htsum_mem : (∑' x : s, f x) ∈ atomicPart (MofK K) := by
    simpa [f] using tsum_smul_dirac_mem_atomicPart (K := K)
      (fun x : s => (m ({x.1} : Set K)).toReal) hf_sum
  have hσ_le_μ : (∑' x : s, f x : MofK K) ≤ μ := by
    classical
    intro A hA
    have h_indicator :
        indicatorSubtype A (fun x : s => (m ({x.1} : Set K)).toReal) =
          fun x : s => A.indicator (fun y => (m ({y} : Set K)).toReal) x.1 := by
      funext x
      dsimp [indicatorSubtype]
      by_cases hxA : x.1 ∈ A
      · simp [hxA]
      · simp [hxA]
    rw [tsum_smul_dirac_apply hf_sum A hA, h_indicator, ← hm_signed,
      Measure.toSignedMeasure_apply_measurable hA, measureReal_def]
    exact tsum_toReal_indicator_singletons_le_measure m s A hA
  have hσ_nonneg : (0 : MofK K) ≤ ∑' x : s, f x := by
    simpa [f] using tsum_smul_dirac_nonneg_of_nonneg (K := K) hf_sum
      (fun x : s => ENNReal.toReal_nonneg)
  have hσ_singleton : ∀ x : K,
      (((∑' y : s, f y : MofK K) : SignedMeasure K) ({x} : Set K)) = (m ({x} : Set K)).toReal := by
    intro x
    simpa [f] using tsum_pos_singleton_dirac_apply m s rfl hf_sum x
  set ν : MofK K := μ - ∑' x : s, f x
  have hν_nonneg : (0 : MofK K) ≤ ν := sub_nonneg.mpr hσ_le_μ
  have hν_atomic : ν ∈ atomicPart (MofK K) :=
    (atomicPart (MofK K)).toOrderIdeal.toSubmodule.sub_mem hμa htsum_mem
  have hν_singleton : ∀ x : K, (ν : SignedMeasure K) ({x} : Set K) = 0 := by
    intro x
    rw [show (ν : SignedMeasure K) = (μ : SignedMeasure K) - (((∑' x : s, f x : MofK K) :
      MofK K) : SignedMeasure K) by rfl, VectorMeasure.sub_apply, hσ_singleton x,
      ← hm_signed, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton x),
      measureReal_def, sub_self]
  have hν_cont : MeasureTheory.SignedMeasure.NoAtoms (ν : SignedMeasure K) :=
    noAtoms_of_nonneg_of_singleton_zero ν hν_nonneg hν_singleton
  have hν_zero : ν = 0 :=
    atomicPart_inter_continuousPart_eq_zero hν_atomic <|
      (mem_continuousPart_iff ν).mpr hν_cont
  have hμ_eq : μ = ∑' x : s, f x := by
    simpa [ν] using (sub_eq_zero.mp hν_zero)
  refine ⟨↥s, hs_count.to_subtype, fun x => (m ({x.1} : Set K)).toReal, Subtype.val, ?_, hf_sum, ?_⟩
  · intro x
    exact ENNReal.toReal_nonneg
  · simpa [f] using hμ_eq

/-- A measure in the atomic part of `M(K)` is a countable sum of Dirac deltas. -/
theorem exists_sum_dirac_of_mem_atomicPart {μ : MofK K}
    (hμa : μ ∈ atomicPart (MofK K)) :
    ∃ (ι : Type u) (_ : Countable ι) (c : ι → ℝ) (x : ι → K),
      Summable (fun i : ι => c i • dirac (x i)) ∧
      μ = ∑' i : ι, c i • dirac (x i) := by
  have hμabs : |μ| ∈ atomicPart (MofK K) := (atomicPart (MofK K)).abs_mem hμa
  have hμpos : μ⁺ ∈ atomicPart (MofK K) :=
    (atomicPart (MofK K)).toOrderIdeal.solid hμabs (posPart_nonneg μ) (posPart_le_abs μ)
  have hμneg : μ⁻ ∈ atomicPart (MofK K) :=
    (atomicPart (MofK K)).toOrderIdeal.solid hμabs (negPart_nonneg μ) (negPart_le_abs μ)
  obtain ⟨ιp, hιp, cp, xp, _, hsp, hμp⟩ :=
    exists_nonneg_sum_dirac_of_mem_atomicPart (posPart_nonneg μ) hμpos
  obtain ⟨ιn, hιn, cn, xn, _, hsn, hμn⟩ :=
    exists_nonneg_sum_dirac_of_mem_atomicPart (negPart_nonneg μ) hμneg
  have hsn' : Summable (fun i : ιn => (-cn i) • dirac (xn i)) := by
    simpa [neg_smul] using hsn.neg
  have hsum :
      Summable (fun i : ιp ⊕ ιn =>
        (Sum.elim cp (fun i => -cn i) i) • dirac ((Sum.elim xp xn) i)) := by
    refine Summable.sum _ ?_ ?_
    · simpa using hsp
    · change Summable (fun i : ιn => (-cn i) • dirac (xn i))
      exact hsn'
  have hsum_eq :
      HasSum (fun i : ιp ⊕ ιn =>
        (Sum.elim cp (fun i => -cn i) i) • dirac ((Sum.elim xp xn) i))
        ((∑' i : ιp, cp i • dirac (xp i)) + ∑' i : ιn, (-cn i) • dirac (xn i)) := by
    refine HasSum.sum ?_ ?_
    · simpa using hsp.hasSum
    · change HasSum (fun i : ιn => (-cn i) • dirac (xn i)) _
      exact hsn'.hasSum
  refine ⟨ιp ⊕ ιn, inferInstance, Sum.elim cp (fun i => -cn i), Sum.elim xp xn, hsum, ?_⟩
  calc
    μ = μ⁺ - μ⁻ := (posPart_sub_negPart μ).symm
    _ = (∑' i : ιp, cp i • dirac (xp i)) - (∑' i : ιn, cn i • dirac (xn i)) := by
      rw [hμp, hμn]
    _ = (∑' i : ιp, cp i • dirac (xp i)) + -∑' i : ιn, cn i • dirac (xn i) := by
      rw [sub_eq_add_neg]
    _ = (∑' i : ιp, cp i • dirac (xp i)) + (∑' i : ιn, (-cn i) • dirac (xn i)) := by
      congr 1
      symm
      simpa [neg_smul] using (tsum_neg (f := fun i : ιn => cn i • dirac (xn i)))
    _ = ∑' i : ιp ⊕ ιn, (Sum.elim cp (fun i => -cn i) i) • dirac ((Sum.elim xp xn) i) := by
      symm
      exact hsum_eq.tsum_eq

/-- Every element of `M(K)` splits as a countable sum of Dirac deltas plus a
signed measure with no atoms. -/
theorem exists_sum_dirac_add_noAtoms (μ : MofK K) :
    ∃ (ι : Type u) (_ : Countable ι) (c : ι → ℝ) (x : ι → K) (ν : MofK K),
      Summable (fun i : ι => c i • dirac (x i)) ∧
      MeasureTheory.SignedMeasure.NoAtoms (ν : SignedMeasure K) ∧
      μ = (∑' i : ι, c i • dirac (x i)) + ν := by
  let addGroup : AddCommGroup (MofK K) := inferInstance
  let latticeOrig : Lattice (MofK K) := inferInstance
  let orderedAddOrig : @IsOrderedAddMonoid (MofK K) addGroup.toAddCommMonoid
      latticeOrig.toPartialOrder.toPreorder :=
    inferInstance
  let vectorOrig : @VectorLattice (MofK K) addGroup latticeOrig orderedAddOrig :=
    inferInstance
  letI ccl : ConditionallyCompleteLattice (MofK K) :=
    BanachLattice.conditionallyCompleteLatticeOf_isOrderContinuousNorm
  letI orderedAdd : @IsOrderedAddMonoid (MofK K) addGroup.toAddCommMonoid
      ccl.toLattice.toPartialOrder.toPreorder :=
    orderedAddOrig
  letI vector : @VectorLattice (MofK K) addGroup ccl.toLattice orderedAdd :=
    vectorOrig
  haveI hp : @HasProjectionProperty (MofK K) addGroup ccl.toLattice orderedAdd vector :=
    @HasProjectionProperty.of_isOrderComplete (MofK K) addGroup ccl orderedAdd vector
  obtain ⟨P, hP⟩ :=
    @HasProjectionProperty.exists_projectionBand (MofK K) addGroup ccl.toLattice
      orderedAdd vector hp (atomicPart (MofK K))
  obtain ⟨a, ν, haP, hνP, hμ⟩ := P.decomposition μ
  have ha : a ∈ atomicPart (MofK K) := by
    have : a ∈ (P : Set (MofK K)) := haP
    rwa [hP] at this
  have hν : ν ∈ continuousPart (MofK K) := by
    intro b hb
    have hbP : b ∈ (P : Set (MofK K)) := by
      rw [hP]
      exact isVLAtom.mem_atomicPart hb
    exact hνP b hbP
  obtain ⟨ι, hι, c, x, hsum, ha_sum⟩ := exists_sum_dirac_of_mem_atomicPart ha
  refine ⟨ι, hι, c, x, ν, hsum, (mem_continuousPart_iff ν).mp hν, ?_⟩
  rw [hμ, ha_sum]

end MofK
