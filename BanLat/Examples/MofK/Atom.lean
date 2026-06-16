import BanLat.Atom
import BanLat.Examples.MofK.Basic

/-!
# Atoms in `M(K)`

For a compact Hausdorff space `K` with its Borel σ-algebra, the atoms of
`M(K)` are exactly the strictly positive scalar multiples of Dirac deltas.
-/

open MeasureTheory Set

namespace MofK

universe u

variable {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

private noncomputable def signedDirac [MeasurableSingletonClass K] (x : K) :
    SignedMeasure K :=
  (Measure.dirac x).toSignedMeasure

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem signedDirac_apply_of_mem [MeasurableSingletonClass K] {x : K} {A : Set K}
    (hA : MeasurableSet A) (hx : x ∈ A) :
    signedDirac x A = 1 := by
  unfold signedDirac
  rw [Measure.toSignedMeasure_apply_measurable hA, measureReal_def,
    Measure.dirac_apply_of_mem hx, ENNReal.toReal_one]

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem signedDirac_apply_of_notMem [MeasurableSingletonClass K] {x : K} {A : Set K}
    (hA : MeasurableSet A) (hx : x ∉ A) :
    signedDirac x A = 0 := by
  unfold signedDirac
  rw [Measure.toSignedMeasure_apply_measurable hA, measureReal_def,
    Measure.dirac_apply' x hA, Set.indicator_of_notMem hx, ENNReal.toReal_zero]

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem zero_le_signedDirac [MeasurableSingletonClass K] (x : K) :
    (0 : SignedMeasure K) ≤ signedDirac x :=
  Measure.zero_le_toSignedMeasure _

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem signedDirac_ne_zero [MeasurableSingletonClass K] (x : K) :
    signedDirac x ≠ 0 := by
  intro h
  have h₁ : signedDirac x ({x} : Set K) = 1 :=
    signedDirac_apply_of_mem (measurableSet_singleton x) (Set.mem_singleton x)
  rw [h, VectorMeasure.zero_apply] at h₁
  exact one_ne_zero h₁.symm

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem apply_eq_zero_of_notMem_of_le_signedDirac [MeasurableSingletonClass K] {x : K}
    {y : SignedMeasure K} (hy0 : 0 ≤ y) (hyd : y ≤ signedDirac x) {A : Set K}
    (hA : MeasurableSet A) (hx : x ∉ A) :
    y A = 0 := by
  have h1 : (0 : SignedMeasure K) A ≤ y A := hy0 _ hA
  rw [VectorMeasure.zero_apply] at h1
  have h2 : y A ≤ signedDirac x A := hyd _ hA
  rw [signedDirac_apply_of_notMem hA hx] at h2
  linarith

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem apply_eq_singleton_of_mem_of_le_signedDirac [MeasurableSingletonClass K] {x : K}
    {y : SignedMeasure K} (hy0 : 0 ≤ y) (hyd : y ≤ signedDirac x) {A : Set K}
    (hA : MeasurableSet A) (hx : x ∈ A) :
    y A = y {x} := by
  have hx_set : MeasurableSet ({x} : Set K) := measurableSet_singleton x
  have h_subset : ({x} : Set K) ⊆ A := Set.singleton_subset_iff.mpr hx
  have h_split : y ({x} : Set K) + y (A \ {x}) = y A :=
    VectorMeasure.of_add_of_diff hx_set hA h_subset
  have h_diff_zero : y (A \ {x}) = 0 :=
    apply_eq_zero_of_notMem_of_le_signedDirac hy0 hyd (hA.diff hx_set) (by simp)
  rw [h_diff_zero, add_zero] at h_split
  exact h_split.symm

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
private theorem isVLAtom_signedDirac [MeasurableSingletonClass K] (x : K) :
    IsVLAtom (signedDirac x) := by
  refine ⟨lt_of_le_of_ne (zero_le_signedDirac x) (Ne.symm (signedDirac_ne_zero x)), ?_⟩
  intro y hy0 hyd
  refine ⟨y ({x} : Set K), ?_⟩
  ext A hA
  rw [VectorMeasure.smul_apply, smul_eq_mul]
  by_cases hx : x ∈ A
  · rw [signedDirac_apply_of_mem hA hx, mul_one]
    exact apply_eq_singleton_of_mem_of_le_signedDirac hy0 hyd hA hx
  · rw [signedDirac_apply_of_notMem hA hx, mul_zero]
    exact apply_eq_zero_of_notMem_of_le_signedDirac hy0 hyd hA hx

omit [CompactSpace K] in
private theorem regular_dirac (x : K) : (Measure.dirac x).Regular := by
  refine
    { toIsFiniteMeasureOnCompacts := inferInstance
      toOuterRegular := by
        refine ⟨?_⟩
        intro A hA r hr
        by_cases hx : x ∈ A
        · exact ⟨Set.univ, subset_univ A, isOpen_univ, by
            simpa [Measure.dirac_apply_of_mem hx] using hr⟩
        · exact ⟨({x} : Set K)ᶜ, Set.subset_compl_singleton_iff.mpr hx,
            isOpen_compl_iff.mpr isClosed_singleton, by
              simpa [Measure.dirac_apply' x hA, Set.indicator_of_notMem hx] using hr⟩
      innerRegular := by
        intro U hU r hr
        by_cases hx : x ∈ U
        · refine ⟨{x}, Set.singleton_subset_iff.mpr hx, isCompact_singleton, ?_⟩
          simpa [Measure.dirac_apply, hx] using hr
        · exfalso
          rw [Measure.dirac_apply, Set.indicator_of_notMem hx] at hr
          exact (not_lt_of_ge bot_le) hr }

private theorem isVLAtom_subtype_of_isVLAtom {a : SignedMeasure K}
    (ha : a.IsRegular) (hatom : IsVLAtom a) :
    IsVLAtom
      ((⟨a,
          (MeasureTheory.SignedMeasure.mem_regularSignedMeasureSublattice_iff).2
            ha⟩ : MofK K)) := by
  refine ⟨hatom.pos, ?_⟩
  intro y hy0 hya
  obtain ⟨c, hc⟩ := hatom.2 y.1 hy0 hya
  exact ⟨c, Subtype.ext hc⟩

/-- The Dirac delta at `x`, viewed as an element of `M(K)`. -/
noncomputable def dirac (x : K) : MofK K :=
  ⟨signedDirac x,
    (MeasureTheory.SignedMeasure.mem_regularSignedMeasureSublattice_iff).2
      (SignedMeasure.measure_toSignedMeasure_isRegular (regular_dirac x))⟩

/-- The Dirac delta is non-negative in `M(K)`. -/
theorem zero_le_dirac (x : K) : 0 ≤ dirac x := by
  exact zero_le_signedDirac x

/-- The Dirac delta evaluates to `1` on measurable sets containing its point. -/
theorem dirac_apply_of_mem {x : K} {A : Set K} (hA : MeasurableSet A) (hx : x ∈ A) :
    (((dirac x : MofK K) : SignedMeasure K) A) = 1 := by
  change (Measure.dirac x).toSignedMeasure A = 1
  rw [Measure.toSignedMeasure_apply_measurable hA, measureReal_def,
    Measure.dirac_apply_of_mem hx, ENNReal.toReal_one]

/-- The Dirac delta evaluates to `0` on measurable sets not containing its point. -/
theorem dirac_apply_of_notMem {x : K} {A : Set K} (hA : MeasurableSet A)
    (hx : x ∉ A) :
    (((dirac x : MofK K) : SignedMeasure K) A) = 0 := by
  change (Measure.dirac x).toSignedMeasure A = 0
  rw [Measure.toSignedMeasure_apply_measurable hA, measureReal_def,
    Measure.dirac_apply' x hA, Set.indicator_of_notMem hx, ENNReal.toReal_zero]

/-- The Dirac delta is non-zero in `M(K)`. -/
theorem dirac_ne_zero (x : K) : dirac x ≠ 0 := by
  intro h
  exact signedDirac_ne_zero x (congrArg Subtype.val h)

/-- The Dirac delta has norm `1` in `M(K)`. -/
theorem norm_dirac (x : K) : ‖dirac x‖ = 1 := by
  change ‖(Measure.dirac x).toSignedMeasure‖ = 1
  rw [MeasureTheory.SignedMeasure.norm_def, MeasureTheory.SignedMeasure.totalVariation,
    SignedMeasure.jordan_of_toSignedMeasure (Measure.dirac x)]
  simp

/-- The Dirac delta is an atom of `M(K)`. -/
theorem isVLAtom_dirac (x : K) : IsVLAtom (dirac x) :=
  isVLAtom_subtype_of_isVLAtom
    (SignedMeasure.measure_toSignedMeasure_isRegular (regular_dirac x))
    (isVLAtom_signedDirac x)

/-- A non-negative signed measure has zero infimum with a Dirac mass iff it vanishes on the
singleton. -/
theorem signedMeasure_inf_dirac_eq_zero_iff
    {s : SignedMeasure K} (hs : 0 ≤ s) (x : K) :
    s ⊓ ((dirac x : MofK K) : SignedMeasure K) = 0 ↔ s ({x} : Set K) = 0 := by
  have hxset : MeasurableSet ({x} : Set K) := measurableSet_singleton x
  have hsx_nn : 0 ≤ s ({x} : Set K) := by
    have := hs _ hxset
    rwa [VectorMeasure.zero_apply] at this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · set c : ℝ := min (s ({x} : Set K)) 1 with hc_def
    have hc_nn : 0 ≤ c := le_min hsx_nn (by norm_num)
    have hcd_le_s : c • ((dirac x : MofK K) : SignedMeasure K) ≤ s := by
      intro B hB
      rw [VectorMeasure.smul_apply, smul_eq_mul]
      by_cases hxB : x ∈ B
      · rw [dirac_apply_of_mem hB hxB, mul_one]
        calc
          c ≤ s ({x} : Set K) := min_le_left _ _
          _ ≤ s B := SignedMeasure.apply_le_apply_of_subset hs hxset hB
              (Set.singleton_subset_iff.mpr hxB)
      · rw [dirac_apply_of_notMem hB hxB, mul_zero]
        have := hs _ hB
        rwa [VectorMeasure.zero_apply] at this
    have hcd_le_d : c • ((dirac x : MofK K) : SignedMeasure K) ≤
        ((dirac x : MofK K) : SignedMeasure K) := by
      intro B hB
      rw [VectorMeasure.smul_apply, smul_eq_mul]
      by_cases hxB : x ∈ B
      · rw [dirac_apply_of_mem hB hxB, mul_one]
        exact min_le_right _ _
      · rw [dirac_apply_of_notMem hB hxB, mul_zero]
    have hcd_le_inf : c • ((dirac x : MofK K) : SignedMeasure K) ≤
        s ⊓ ((dirac x : MofK K) : SignedMeasure K) := le_inf hcd_le_s hcd_le_d
    rw [h] at hcd_le_inf
    have h_at_x := hcd_le_inf {x} hxset
    rw [VectorMeasure.smul_apply, smul_eq_mul,
      dirac_apply_of_mem hxset (Set.mem_singleton x), mul_one,
      VectorMeasure.zero_apply] at h_at_x
    have hc_zero : c = 0 := le_antisymm h_at_x hc_nn
    rw [hc_def] at hc_zero
    rcases min_eq_iff.mp hc_zero with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exfalso
      linarith
  · refine VectorMeasure.ext fun B hB => ?_
    rw [VectorMeasure.zero_apply]
    have hdirac_nonneg : (0 : SignedMeasure K) ≤ ((dirac x : MofK K) : SignedMeasure K) :=
      zero_le_dirac x
    have hinf_nn : (0 : SignedMeasure K) ≤ s ⊓ ((dirac x : MofK K) : SignedMeasure K) :=
      le_inf hs hdirac_nonneg
    have hinf_le_d : s ⊓ ((dirac x : MofK K) : SignedMeasure K) ≤
        ((dirac x : MofK K) : SignedMeasure K) := inf_le_right
    have hinf_le_s : s ⊓ ((dirac x : MofK K) : SignedMeasure K) ≤ s := inf_le_left
    have hBdiff : MeasurableSet (B \ {x}) := hB.diff hxset
    have hBint : MeasurableSet (B ∩ {x}) := hB.inter hxset
    have h_disj : Disjoint (B ∩ {x}) (B \ {x}) := by
      apply Set.disjoint_left.mpr
      rintro a ⟨_, ha⟩ ⟨_, ha'⟩
      exact ha' ha
    have h_cup : (B ∩ {x}) ∪ (B \ {x}) = B := Set.inter_union_diff B {x}
    have h_split : (s ⊓ ((dirac x : MofK K) : SignedMeasure K)) (B ∩ {x}) +
        (s ⊓ ((dirac x : MofK K) : SignedMeasure K)) (B \ {x}) =
          (s ⊓ ((dirac x : MofK K) : SignedMeasure K)) B := by
      rw [← VectorMeasure.of_union h_disj hBint hBdiff, h_cup]
    have h_diff_zero : (s ⊓ ((dirac x : MofK K) : SignedMeasure K)) (B \ {x}) = 0 := by
      have h_ub := hinf_le_d _ hBdiff
      have hxnotMem : x ∉ B \ {x} := by simp
      rw [dirac_apply_of_notMem hBdiff hxnotMem] at h_ub
      have h_lb := hinf_nn _ hBdiff
      rw [VectorMeasure.zero_apply] at h_lb
      linarith
    have h_int_zero : (s ⊓ ((dirac x : MofK K) : SignedMeasure K)) (B ∩ {x}) = 0 := by
      by_cases hxB : x ∈ B
      · have h_eq : B ∩ {x} = {x} := by
          ext y
          refine ⟨fun ⟨_, hy⟩ => hy, fun hy => ?_⟩
          rw [Set.mem_singleton_iff] at hy
          exact ⟨hy ▸ hxB, by simp [hy]⟩
        rw [h_eq]
        have h_ub := hinf_le_s _ hxset
        rw [h] at h_ub
        have h_lb := hinf_nn _ hxset
        rw [VectorMeasure.zero_apply] at h_lb
        linarith
      · have h_eq : B ∩ {x} = ∅ := by
          ext y
          refine ⟨fun ⟨hy1, hy2⟩ => ?_, fun h' => h'.elim⟩
          rw [Set.mem_singleton_iff] at hy2
          exact hxB (hy2 ▸ hy1)
        rw [h_eq]
        exact (s ⊓ ((dirac x : MofK K) : SignedMeasure K)).empty
    rw [← h_split, h_diff_zero, h_int_zero, add_zero]

/-- A strictly positive scalar multiple of a Dirac delta is an atom of `M(K)`. -/
theorem isVLAtom_smul_dirac {c : ℝ} (hc : 0 < c) (x : K) :
    IsVLAtom (c • dirac x) :=
  (isVLAtom_dirac x).smul hc

private theorem exists_singleton_of_isVLAtom (s : MofK K) (hs : IsVLAtom s) :
    ∃ x : K, ∃ c : ℝ, 0 < c ∧ s = c • dirac x := by
  have hs0 : (0 : MofK K) ≤ s := hs.pos.le
  have hs0' : (0 : SignedMeasure K) ≤[Set.univ] s.1 :=
    (VectorMeasure.le_restrict_univ_iff_le _ _).mpr hs0
  let μ : Measure K :=
    s.1.toMeasureOfZeroLE Set.univ MeasurableSet.univ hs0'
  have hμ_signed : μ.toSignedMeasure = s.1 :=
    MeasureTheory.SignedMeasure.toMeasureOfZeroLE_toSignedMeasure s.1 hs0'
  have hμ_reg : μ.Regular := by
    have hsreg : s.1.IsRegular :=
      (MeasureTheory.SignedMeasure.mem_regularSignedMeasureSublattice_iff).mp s.2
    apply SignedMeasure.regular_of_toSignedMeasure_isRegular
    simpa [hμ_signed] using hsreg
  have hμ_ne_zero : μ ≠ 0 := by
    intro hμ0
    have hs_zero : s = 0 := by
      apply Subtype.ext
      have : μ.toSignedMeasure = (0 : SignedMeasure K) := by simp [hμ0]
      exact hμ_signed.symm.trans this
    exact hs.ne_zero hs_zero
  have hμ_univ_ne_zero : μ Set.univ ≠ 0 := by
    exact Measure.measure_univ_ne_zero.mpr hμ_ne_zero
  have hzero_or_full : ∀ A : Set K, MeasurableSet A → μ A = 0 ∨ μ Aᶜ = 0 := by
    intro A hA
    let t : MofK K :=
      ⟨(μ.restrict A).toSignedMeasure,
        (MeasureTheory.SignedMeasure.mem_regularSignedMeasureSublattice_iff).2
          (SignedMeasure.measure_toSignedMeasure_isRegular
            (Measure.Regular.restrict_of_measure_ne_top (measure_ne_top _ _)))⟩
    have ht0 : (0 : MofK K) ≤ t := by
      exact Measure.zero_le_toSignedMeasure _
    have htle : t ≤ s := by
      change (t : SignedMeasure K) ≤ (s : SignedMeasure K)
      intro B hB
      rw [← hμ_signed, Measure.toSignedMeasure_apply_measurable hB,
        Measure.toSignedMeasure_apply_measurable hB, measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
    obtain ⟨d, hd⟩ := hs.2 t ht0 htle
    by_cases hd0 : d = 0
    · left
      have h_eval : (μ A).toReal = 0 := by
        have h_eval' := congrArg (fun u : MofK K => (u : SignedMeasure K) A) hd
        have h_left : (fun u : MofK K => (u : SignedMeasure K) A) t = (μ A).toReal := by
          change (μ.restrict A).toSignedMeasure A = (μ A).toReal
          rw [Measure.toSignedMeasure_apply_measurable hA, measureReal_def,
            Measure.restrict_apply hA, Set.inter_self]
        have h_right : (fun u : MofK K => (u : SignedMeasure K) A) (d • s) = d * s.1 A := by
          change ((d • s.1 : SignedMeasure K) A) = d * s.1 A
          rw [VectorMeasure.smul_apply, smul_eq_mul]
        rw [h_left, h_right, hd0, zero_mul] at h_eval'
        exact h_eval'
      rcases (ENNReal.toReal_eq_zero_iff (μ A)).mp h_eval with hA0 | hA0
      · exact hA0
      · exact False.elim ((measure_ne_top _ _) hA0)
    · right
      have hAcompl : MeasurableSet Aᶜ := hA.compl
      have h_eval : 0 = d * s.1 Aᶜ := by
        have h_eval' := congrArg (fun u : MofK K => (u : SignedMeasure K) Aᶜ) hd
        have h_left : (fun u : MofK K => (u : SignedMeasure K) Aᶜ) t = 0 := by
          change (μ.restrict A).toSignedMeasure Aᶜ = 0
          rw [Measure.toSignedMeasure_apply_measurable hAcompl, measureReal_def,
            Measure.restrict_apply hAcompl, Set.compl_inter_self, measure_empty,
            ENNReal.toReal_zero]
        have h_right : (fun u : MofK K => (u : SignedMeasure K) Aᶜ) (d • s) = d * s.1 Aᶜ := by
          change ((d • s.1 : SignedMeasure K) Aᶜ) = d * s.1 Aᶜ
          rw [VectorMeasure.smul_apply, smul_eq_mul]
        rw [h_left, h_right] at h_eval'
        exact h_eval'
      have hsAcompl_zero : s.1 Aᶜ = 0 := by
        have hm : d = 0 ∨ s.1 Aᶜ = 0 := mul_eq_zero.mp h_eval.symm
        exact hm.resolve_left hd0
      have h_toReal_zero : (μ Aᶜ).toReal = 0 := by
        have hsAcompl_eval : s.1 Aᶜ = (μ Aᶜ).toReal := by
          rw [← hμ_signed, Measure.toSignedMeasure_apply_measurable hAcompl, measureReal_def]
        rw [← hsAcompl_eval]
        exact hsAcompl_zero
      rcases (ENNReal.toReal_eq_zero_iff (μ Aᶜ)).mp h_toReal_zero with hA0 | hA0
      · exact hA0
      · exact False.elim ((measure_ne_top _ _) hA0)
  have hx_full : ∃ x : K, μ ({x} : Set K) = μ Set.univ := by
    by_contra h
    have hlt : ∀ x : K, μ ({x} : Set K) < μ Set.univ := by
      intro x
      refine lt_of_le_of_ne (measure_mono (Set.singleton_subset_iff.mpr (Set.mem_univ x))) ?_
      exact fun hx => h ⟨x, hx⟩
    choose U hUx hU_open hU_lt using
      fun x : K => Set.exists_isOpen_lt_of_lt ({x} : Set K) (μ Set.univ) (hlt x)
    have hU_zero : ∀ x : K, μ (U x) = 0 := by
      intro x
      rcases hzero_or_full (U x) (hU_open x).measurableSet with h0 | h0
      · exact h0
      · exfalso
        have hfull : μ (U x) = μ Set.univ := by
          have hadd := measure_add_measure_compl (μ := μ) (hU_open x).measurableSet
          rw [h0, add_zero] at hadd
          exact hadd
        exact (ne_of_lt (hU_lt x)) hfull
    have hcover : Set.univ ⊆ ⋃ x : K, U x := by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hUx x (Set.mem_singleton x)⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU_open hcover
    have hUnion_zero : μ (⋃ x ∈ t, U x) = 0 := by
      classical
      refine Finset.induction_on t ?_ ?_
      · simp
      · intro a t ha ih
        refine le_antisymm ?_ bot_le
        calc
          μ (⋃ x ∈ insert a t, U x)
            ≤ μ (U a) + μ (⋃ x ∈ t, U x) := by
                rw [Finset.set_biUnion_insert]
                exact measure_union_le _ _
          _ = 0 := by rw [hU_zero a, ih, zero_add]
    exact hμ_univ_ne_zero <| le_antisymm
      ((measure_mono ht).trans hUnion_zero.le) bot_le
  obtain ⟨x, hx⟩ := hx_full
  have hxc : μ (({x} : Set K)ᶜ) = 0 := by
    rw [measure_compl (measurableSet_singleton x) (measure_ne_top _ _), hx,
      tsub_self]
  refine ⟨x, (μ Set.univ).toReal, ENNReal.toReal_pos hμ_univ_ne_zero (measure_ne_top _ _), ?_⟩
  apply Subtype.ext
  ext A hA
  have hs_eval : s.1 A = (μ A).toReal := by
    rw [← hμ_signed, Measure.toSignedMeasure_apply_measurable hA, measureReal_def]
  rw [hs_eval]
  change (μ A).toReal =
    (((μ Set.univ).toReal • ((dirac x : MofK K) : SignedMeasure K)) A)
  rw [VectorMeasure.smul_apply, smul_eq_mul]
  by_cases hxA : x ∈ A
  · have hA_full : μ A = μ Set.univ := by
      refine le_antisymm (measure_mono (Set.subset_univ A)) ?_
      simpa [hx] using (hx.symm ▸ measure_mono (Set.singleton_subset_iff.mpr hxA))
    have hdirac : (((dirac x : MofK K) : SignedMeasure K) A) = signedDirac x A := rfl
    rw [hA_full, hdirac, signedDirac_apply_of_mem hA hxA, mul_one]
  · have hA_zero : μ A = 0 := by
      refine le_antisymm ?_ bot_le
      calc
        μ A ≤ μ ({x} : Set K)ᶜ := measure_mono <| by
          intro y hy
          have hy_ne : y ≠ x := by
            intro hyx
            exact hxA (hyx ▸ hy)
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hy_ne
        _ = 0 := hxc
    have hdirac : (((dirac x : MofK K) : SignedMeasure K) A) = signedDirac x A := rfl
    rw [hA_zero, ENNReal.toReal_zero, hdirac, signedDirac_apply_of_notMem hA hxA, mul_zero]

/-- The atoms of `M(K)` are exactly the strictly positive scalar multiples of
Dirac deltas. -/
theorem isVLAtom_iff_exists_smul_dirac (s : MofK K) :
    IsVLAtom s ↔ ∃ (c : ℝ) (x : K), 0 < c ∧ s = c • dirac x := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨x, c, hc, hsc⟩ := exists_singleton_of_isVLAtom s hs
    exact ⟨c, x, hc, hsc⟩
  · rcases hs with ⟨c, x, hc, rfl⟩
    exact isVLAtom_smul_dirac hc x

end MofK
