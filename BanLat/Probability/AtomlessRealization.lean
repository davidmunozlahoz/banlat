/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Preliminaries.HasNoAtoms
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Representation

/-!
# Realization of probability laws on atomless spaces

Let `P` be an atomless probability measure on a measurable space `Ω`.
We prove that:
* There exists a measurable map from `Ω → [0, 1]` whose pushforward of `P`
  is the Lebesgue measure on `[0, 1]`.
* Given any probability measure `ν` on a standard Borel space `E`,
  there exists a measurable map from `Ω` to `E` whose pushforward of `P` is `ν`.
* The space supports a sequence of independent random variables with any
  prescribed sequence of probability laws on a standard Borel space.
Conversely, a probability space supporting such a sequence with a non-Dirac
common law is atomless.
-/

open Set

open scoped ENNReal

namespace MeasureTheory.Measure.HasNoAtoms

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Split one dyadic fiber into two measurable sets of equal measure. -/
private lemma exists_dyadic_half_fiber (hP : P.HasNoAtoms)
    (n : ℕ) (f : Ω → Fin (2 ^ n)) (hf : Measurable f)
    (hmass : ∀ k, P {ω | f ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n) (k : Fin (2 ^ n)) :
    ∃ s : Set Ω, MeasurableSet s ∧ s ⊆ {ω | f ω = k} ∧
      P s = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) ∧
      P ({ω | f ω = k} \ s) = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  obtain ⟨s, hs, hsub, hms⟩ := hP.exists_measurable_subset_measure_eq_of_le
    (show MeasurableSet {ω | f ω = k} from measurableSet_eq_fun hf measurable_const)
    (ENNReal.half_le_self (a := P {ω | f ω = k}))
  have hhalf : P {ω | f ω = k} / 2 = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
    rw [hmass, pow_succ, div_eq_mul_inv]
  refine ⟨s, hs, hsub, hms.trans hhalf, ?_⟩
  rw [measure_sdiff hsub hs.nullMeasurableSet (measure_ne_top P _), hms,
    ENNReal.sub_half (measure_ne_top P _), hhalf]

omit [MeasurableSpace Ω] in
/-- A binary digit splits each fiber into its chosen subset and its complement. -/
private lemma binary_refinement_fibers {ι κ : Type*}
    (f : Ω → ι) (s : ι → Set Ω) (hsub : ∀ k, s k ⊆ {ω | f ω = k})
    (b : Ω → Fin 2) (hb : ∀ ω, b ω = 0 ↔ ω ∈ ⋃ k, s k) (e : ι × Fin 2 ≃ κ) :
    (∀ k, {ω | e (f ω, b ω) = e (k, 0)} = s k) ∧
      ∀ k, {ω | e (f ω, b ω) = e (k, 1)} = {ω | f ω = k} \ s k := by
  have hzero k : {ω | e (f ω, b ω) = e (k, 0)} = s k := by
    ext ω
    simp only [mem_ofPred_eq, e.injective.eq_iff, Prod.mk.injEq, hb]
    exact ⟨fun ⟨hk, hω⟩ ↦ (mem_iUnion.mp hω).elim fun j hj ↦
      ((hsub j hj).symm.trans hk) ▸ hj,
      fun hω ↦ ⟨hsub k hω, mem_iUnion.mpr ⟨k, hω⟩⟩⟩
  refine ⟨hzero, fun k ↦ ?_⟩
  rw [← hzero]
  ext ω
  simp only [mem_ofPred_eq, mem_sdiff, e.injective.eq_iff, Prod.mk.injEq]
  generalize b ω = j
  fin_cases j <;> simp

/-- Refine equal-mass dyadic labels by bisecting each fiber. -/
private lemma exists_dyadic_refinement (hP : P.HasNoAtoms)
    (n : ℕ) (f : Ω → Fin (2 ^ n)) (hf : Measurable f)
    (hmass : ∀ k, P {ω | f ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n) :
    ∃ g : Ω → Fin (2 ^ (n + 1)), Measurable g ∧
      (∀ ω, (g ω).val / 2 = (f ω).val) ∧
      ∀ k, P {ω | g ω = k} = (2 : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  classical
  choose s hs hsub hsmass hcmass using exists_dyadic_half_fiber hP n f hf hmass
  let S := ⋃ k, s k
  let e : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
    finProdFinEquiv.trans (finCongr (pow_succ 2 n).symm)
  let g : Ω → Fin (2 ^ (n + 1)) := fun ω ↦ e (f ω, if ω ∈ S then 0 else 1)
  obtain ⟨hzero, hone⟩ := binary_refinement_fibers f s hsub
    (fun ω ↦ if ω ∈ S then 0 else 1) (fun ω ↦ by simp [S]) e
  refine ⟨g, ?_, ?_, ?_⟩
  · exact (measurable_of_finite e).comp
      (hf.prodMk (Measurable.ite (MeasurableSet.iUnion hs) measurable_const measurable_const))
  · intro ω
    change ((if ω ∈ S then (0 : Fin 2) else 1).val + 2 * (f ω).val) / 2 = (f ω).val
    split_ifs <;> simp [Nat.add_mul_div_left]
  · intro j
    obtain ⟨⟨k, b⟩, rfl⟩ := e.surjective j
    fin_cases b
    · exact (congrArg P (hzero k)).trans (hsmass k)
    · exact (congrArg P (hone k)).trans (hcmass k)

/-- Construct compatible dyadic labels whose fibers all have equal measure. -/
private lemma exists_dyadic_labels (hP : P.HasNoAtoms) :
    ∃ f : (n : ℕ) → Ω → Fin (2 ^ n),
      (∀ n, Measurable (f n)) ∧
      (∀ n ω, (f (n + 1) ω).val / 2 = (f n ω).val) ∧
      (∀ n (k : Fin (2 ^ n)),
        P {ω | f n ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n) := by
  let L (n : ℕ) := {f : Ω → Fin (2 ^ n) //
    Measurable f ∧ ∀ k, P {ω | f ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n}
  have hstep n (p : L n) : ∃ q : L (n + 1),
      ∀ ω, (q.val ω).val / 2 = (p.val ω).val := by
    obtain ⟨g, hg, hcompat, hmass⟩ := exists_dyadic_refinement hP n p.val p.property.1 p.property.2
    exact ⟨⟨g, hg, hmass⟩, hcompat⟩
  choose step hstep_spec using hstep
  let z : L 0 := ⟨fun _ ↦ 0, measurable_const, by simp⟩
  let F : (n : ℕ) → L n := Nat.rec z step
  exact ⟨fun n ↦ (F n).val, fun n ↦ (F n).property.1,
    fun n ↦ hstep_spec n (F n), fun n ↦ (F n).property.2⟩

/-- Refining a dyadic label increases its lower endpoint and decreases its upper endpoint. -/
private lemma dyadic_step_bounds {a b : ℕ} (h : b / 2 = a) (n : ℕ) :
    (a : ℝ) / (2 : ℝ) ^ n ≤ (b : ℝ) / (2 : ℝ) ^ (n + 1) ∧
      ((b : ℝ) + 1) / (2 : ℝ) ^ (n + 1) ≤ ((a : ℝ) + 1) / (2 : ℝ) ^ n := by
  have hb : 2 * a ≤ b ∧ b ≤ 2 * a + 1 := by omega
  have hb' : 2 * (a : ℝ) ≤ b ∧ (b : ℝ) ≤ 2 * a + 1 := by exact_mod_cast hb
  constructor <;> simp only [pow_succ', div_mul_eq_div_div] <;>
    (apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).2) <;>
    linarith [hb'.1, hb'.2]

omit [MeasurableSpace Ω] in
/-- Every lower dyadic endpoint lies below every upper endpoint. -/
private lemma dyadic_endpoints_order (f : ℕ → ℕ)
    (hf : ∀ n, f (n + 1) / 2 = f n) (n m : ℕ) :
    (f n : ℝ) / (2 : ℝ) ^ n ≤ ((f m : ℝ) + 1) / (2 : ℝ) ^ m := by
  have hmono : Monotone (fun n ↦ (f n : ℝ) / (2 : ℝ) ^ n) :=
    monotone_nat_of_le_succ fun n ↦ (dyadic_step_bounds (hf n) n).1
  have hanti : Antitone (fun n ↦ ((f n : ℝ) + 1) / (2 : ℝ) ^ n) :=
    antitone_nat_of_succ_le fun n ↦ (dyadic_step_bounds (hf n) n).2
  exact (hmono (Nat.le_max_left n m)).trans
    ((div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)).trans
      (hanti (Nat.le_max_right n m)))

/-- Construct a measurable interval-valued map approximated by the dyadic labels. -/
private lemma exists_unitInterval_dyadic_approximation
    (f : (n : ℕ) → Ω → Fin (2 ^ n))
    (hf : ∀ n, Measurable (f n))
    (hcompat : ∀ n ω, (f (n + 1) ω).val / 2 = (f n ω).val) :
    ∃ U : Ω → unitInterval, Measurable U ∧
      ∀ n ω,
        ((f n ω).val : ℝ) / (2 : ℝ) ^ n ≤ (U ω : ℝ) ∧
        (U ω : ℝ) ≤ ((f n ω).val + 1 : ℝ) / (2 : ℝ) ^ n := by
  let a : ℕ → Ω → ℝ := fun n ω ↦ ((f n ω).val : ℝ) / (2 : ℝ) ^ n
  let b : ℕ → Ω → ℝ := fun n ω ↦ ((f n ω).val + 1 : ℝ) / (2 : ℝ) ^ n
  have hcross n m ω : a n ω ≤ b m ω :=
    dyadic_endpoints_order (fun n ↦ (f n ω).val) (fun n ↦ hcompat n ω) n m
  let u : Ω → ℝ := fun ω ↦ ⨆ n, a n ω
  have hbdd ω : BddAbove (range (fun n ↦ a n ω)) :=
    ⟨b 0 ω, fun _ ⟨n, hn⟩ ↦ hn ▸ hcross n 0 ω⟩
  have hbound n ω : a n ω ≤ u ω ∧ u ω ≤ b n ω :=
    ⟨le_ciSup (hbdd ω) n, ciSup_le (fun m ↦ hcross m n ω)⟩
  have huI ω : u ω ∈ unitInterval := by
    simpa [a, b, Fin.fin_one_eq_zero] using hbound 0 ω
  refine ⟨fun ω ↦ ⟨u ω, huI ω⟩, ?_, hbound⟩
  exact (Measurable.iSup (fun n ↦ (measurable_of_finite
    (fun k : Fin (2 ^ n) ↦ (k.val : ℝ) / (2 : ℝ) ^ n)).comp (hf n))).subtype_mk

/-- Count the probabilities of strict and weak initial segments of the dyadic labels. -/
private lemma measureReal_dyadic_initial_segments (n : ℕ) (f : Ω → Fin (2 ^ n))
    (hf : Measurable f)
    (hmass : ∀ k, P {ω | f ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n)
    (k : Fin (2 ^ n)) :
    P.real {ω | f ω < k} = (k.val : ℝ) / (2 : ℝ) ^ n ∧
      P.real {ω | f ω ≤ k} = (k.val + 1 : ℝ) / (2 : ℝ) ^ n := by
  have hfiber i : P.real {ω | f ω = i} = (2 : ℝ)⁻¹ ^ n := by
    simpa [measureReal_def, ENNReal.toReal_pow, Set.preimage, eq_comm] using
      congrArg ENNReal.toReal (hmass i)
  constructor
  · simpa [hfiber, Fin.card_Iio, div_eq_mul_inv, inv_pow, Set.preimage] using
      (sum_measureReal_preimage_singleton (μ := P) (Finset.Iio k)
        (fun i _ ↦ hf (measurableSet_singleton i))).symm
  · simpa [hfiber, Fin.card_Iic, div_eq_mul_inv, inv_pow, Set.preimage] using
      (sum_measureReal_preimage_singleton (μ := P) (Finset.Iic k)
        (fun i _ ↦ hf (measurableSet_singleton i))).symm

/-- Dyadic approximation sandwiches a sublevel event between two label events. -/
private lemma dyadic_cdf_sandwich (n : ℕ) (f : Ω → Fin (2 ^ n))
    {U : Ω → unitInterval}
    (happrox : ∀ ω,
      ((f ω).val : ℝ) / (2 : ℝ) ^ n ≤ (U ω : ℝ) ∧
      (U ω : ℝ) ≤ ((f ω).val + 1 : ℝ) / (2 : ℝ) ^ n)
    (t : unitInterval) (k : Fin (2 ^ n))
    (hklo : (k.val : ℝ) ≤ (t : ℝ) * 2 ^ n)
    (hkhi : (t : ℝ) * 2 ^ n < (k.val : ℝ) + 1) :
    P.real {ω | f ω < k} ≤ P.real {ω | U ω ≤ t} ∧
      P.real {ω | U ω ≤ t} ≤ P.real {ω | f ω ≤ k} := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · refine measureReal_mono ?_
    intro ω hω
    have hcast : ((f ω).val : ℝ) + 1 ≤ (k.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (show (f ω).val < k.val from hω)
    exact (happrox ω).2.trans ((div_le_iff₀ hpow).2 (hcast.trans hklo))
  · refine measureReal_mono ?_
    intro ω hω
    have hval : ((f ω).val : ℝ) < (k.val : ℝ) + 1 :=
      ((div_le_iff₀ hpow).1 ((happrox ω).1.trans hω)).trans_lt hkhi
    exact Nat.le_of_lt_succ (by exact_mod_cast hval)

/-- Dyadic approximation bounds the distribution function within the mesh size. -/
private lemma dyadic_cdf_bounds (n : ℕ) (f : Ω → Fin (2 ^ n))
    (hf : Measurable f)
    (hmass : ∀ k, P {ω | f ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n)
    {U : Ω → unitInterval}
    (happrox : ∀ ω,
      ((f ω).val : ℝ) / (2 : ℝ) ^ n ≤ (U ω : ℝ) ∧
      (U ω : ℝ) ≤ ((f ω).val + 1 : ℝ) / (2 : ℝ) ^ n)
    (t : unitInterval) :
    (t : ℝ) - (2 : ℝ)⁻¹ ^ n ≤ P.real {ω | U ω ≤ t} ∧
      P.real {ω | U ω ≤ t} ≤ (t : ℝ) + (2 : ℝ)⁻¹ ^ n := by
  by_cases ht : t = 1
  · have htop : {ω | U ω ≤ t} = univ :=
      eq_univ_of_forall fun ω ↦ ht.symm ▸ (U ω).property.2
    rw [htop]
    simp [ht]
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun h ↦ ht (Subtype.ext h))
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    let k : Fin (2 ^ n) := ⟨⌊(t : ℝ) * 2 ^ n⌋₊,
      (Nat.floor_lt (mul_nonneg t.property.1 hpow.le)).2
        (by simpa using mul_lt_of_lt_one_left hpow htlt)⟩
    have hklo : (k.val : ℝ) ≤ (t : ℝ) * 2 ^ n :=
      Nat.floor_le (mul_nonneg t.property.1 hpow.le)
    have hkhi : (t : ℝ) * 2 ^ n < (k.val : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    obtain ⟨hlower, hupper⟩ := dyadic_cdf_sandwich (P := P) n f happrox t k hklo hkhi
    obtain ⟨hlo, hhi⟩ := measureReal_dyadic_initial_segments n f hf hmass k
    have hklo' : (k.val : ℝ) / 2 ^ n ≤ (t : ℝ) := (div_le_iff₀ hpow).2 hklo
    have hkhi' : (t : ℝ) < ((k.val : ℝ) + 1) / 2 ^ n :=
      (lt_div_iff₀ hpow).2 hkhi
    simp only [add_div, one_div, ← inv_pow] at hhi hkhi'
    constructor <;> linarith

/-- Equal fiber measures and dyadic approximation imply the uniform law. -/
private lemma map_eq_volume_of_dyadic_approximation
    (f : (n : ℕ) → Ω → Fin (2 ^ n))
    (hf : ∀ n, Measurable (f n))
    (hmass : ∀ n (k : Fin (2 ^ n)),
      P {ω | f n ω = k} = (2 : ℝ≥0∞)⁻¹ ^ n)
    {U : Ω → unitInterval} (hU : Measurable U)
    (happrox : ∀ n ω,
      ((f n ω).val : ℝ) / (2 : ℝ) ^ n ≤ (U ω : ℝ) ∧
      (U ω : ℝ) ≤ ((f n ω).val + 1 : ℝ) / (2 : ℝ) ^ n) :
    P.map U = volume := by
  apply Measure.ext_of_Iic
  intro t
  have hlim : Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb n := dyadic_cdf_bounds n (f n) (hf n) (hmass n) (happrox n) t
  have heq : P.real {ω | U ω ≤ t} = (t : ℝ) := le_antisymm
    (ge_of_tendsto' (by simpa using tendsto_const_nhds.add hlim) fun n ↦ (hb n).2)
    (le_of_tendsto' (by simpa using tendsto_const_nhds.sub hlim) fun n ↦ (hb n).1)
  rw [Measure.map_apply hU measurableSet_Iic, unitInterval.volume_Iic,
    ← heq, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
  rfl

/-- An atomless probability space supports a measurable map with the uniform
law on the unit interval. -/
theorem exists_measurable_map_eq_unitInterval (hP : P.HasNoAtoms) :
    ∃ U : Ω → unitInterval, Measurable U ∧ P.map U = volume := by
  obtain ⟨f, hf, hcompat, hmass⟩ := exists_dyadic_labels hP
  obtain ⟨U, hU, happrox⟩ := exists_unitInterval_dyadic_approximation f hf hcompat
  exact ⟨U, hU, map_eq_volume_of_dyadic_approximation f hf hmass hU happrox⟩

/-- An atomless probability space realizes every probability measure on a
standard Borel space as a measurable pushforward. -/
theorem exists_measurable_map_eq
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (hP : P.HasNoAtoms)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    ∃ Y : Ω → E, Measurable Y ∧ P.map Y = ν := by
  have : Nonempty E := nonempty_of_isProbabilityMeasure ν
  obtain ⟨U, hU, hUP⟩ := hP.exists_measurable_map_eq_unitInterval
  obtain ⟨g, hg, hgν⟩ := MeasureTheory.Measure.exists_measurable_map_eq ν
  exact ⟨g ∘ U, hg.comp hU, by rw [← Measure.map_map hg hU, hUP, hgν]⟩

end MeasureTheory.Measure.HasNoAtoms

namespace MeasureTheory.Measure

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- A probability space supports a measurable map with the uniform law on the
unit interval exactly when it is atomless. -/
theorem exists_measurable_map_eq_unitInterval_iff_hasNoAtoms :
    (∃ U : Ω → unitInterval, Measurable U ∧ P.map U = volume) ↔ P.HasNoAtoms :=
  ⟨fun ⟨_, hU, hmap⟩ ↦ hasNoAtoms_of_map_eq hU hmap,
    HasNoAtoms.exists_measurable_map_eq_unitInterval⟩

end MeasureTheory.Measure

namespace ProbabilityTheory

open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- An atomless probability space supports an independent sequence with
prescribed probability laws on a standard Borel space. -/
theorem exists_indep_hasLaw_of_hasNoAtoms
    [StandardBorelSpace E]
    (hP : P.HasNoAtoms)
    (ν : ℕ → Measure E) [∀ n, IsProbabilityMeasure (ν n)] :
    ∃ X : ℕ → Ω → E,
      (∀ n, Measurable (X n)) ∧
      (∀ n, HasLaw (X n) (ν n) P) ∧
      iIndepFun X P := by
  obtain ⟨Y, hY, hmap⟩ := hP.exists_measurable_map_eq (Measure.infinitePi ν)
  have hLaw n : HasLaw (fun ω ↦ Y ω n) (ν n) P :=
    (measurePreserving_eval_infinitePi ν n).fun_comp_hasLaw
      ⟨hY.aemeasurable, hmap⟩
  refine ⟨fun n ω ↦ Y ω n, fun n ↦ (measurable_pi_apply n).comp hY, hLaw, ?_⟩
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (X := fun n ω ↦ Y ω n) (fun n ↦ (measurable_pi_apply n).comp hY)).2
  simpa only [fun n ↦ (hLaw n).map_eq] using hmap

/-- An atomless probability space supports an independent sequence with any
prescribed common probability law on a standard Borel space. -/
theorem exists_iid_hasLaw_of_hasNoAtoms
    [StandardBorelSpace E]
    (hP : P.HasNoAtoms)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    ∃ X : ℕ → Ω → E,
      (∀ n, Measurable (X n)) ∧
      (∀ n, HasLaw (X n) ν P) ∧
      iIndepFun X P :=
  exists_indep_hasLaw_of_hasNoAtoms hP (fun _ ↦ ν)

/-- A non-Dirac standard Borel probability law has an event of probability
strictly between zero and one. -/
private lemma exists_measurableSet_measure_pos_lt_one
    [StandardBorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : ∀ x : E, ν ≠ Measure.dirac x) :
    ∃ A : Set E, MeasurableSet A ∧ 0 < ν A ∧ ν A < 1 := by
  by_contra! h
  have : IsZeroOneMeasure ν := ⟨fun {A} hA ↦ or_iff_not_imp_left.mpr fun hzero ↦
    le_antisymm prob_le_one (h A hA (pos_iff_ne_zero.mpr hzero))⟩
  obtain ⟨x, hx⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := ν)
  exact hν x hx

/-- An atom lies almost entirely in an event or in its complement. -/
private lemma exists_atom_full_preimage_side
    {s : Set Ω} (hs : P.IsAtom s) {f : Ω → E} (hf : Measurable f)
    {A : Set E} (hA : MeasurableSet A) :
    ∃ B : Set E, (B = A ∨ B = Aᶜ) ∧ s ≤ᵐ[P] f ⁻¹' B := by
  rcases hs.2.2 (hs.1.inter (hf hA)) inter_subset_left with hzero | hfull
  · refine ⟨Aᶜ, Or.inr rfl, ae_le_set.mpr ?_⟩
    simpa only [preimage_compl, sdiff_compl] using hzero
  · refine ⟨A, Or.inl rfl, ?_⟩
    have heq := ae_eq_of_subset_of_measure_ge (μ := P) inter_subset_left hfull.ge
      (hs.1.inter (hf hA)).nullMeasurableSet (measure_ne_top P s)
    exact heq.symm.le.trans inter_subset_right.eventuallyLE

/-- Independence bounds the mass of a source atom by the probability of
a finite pattern of events or their complements. -/
private lemma measure_atom_le_pow_of_iid
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E}
    (hXm : ∀ n, Measurable (X n))
    (hX : ∀ n, HasLaw (X n) ν P)
    (hIndep : iIndepFun X P)
    {A : Set E} (hA : MeasurableSet A)
    {s : Set Ω} (hs : P.IsAtom s) (n : ℕ) :
    P s ≤ (max (ν A) (ν Aᶜ)) ^ n := by
  choose B hB hfull using fun i ↦ exists_atom_full_preimage_side hs (hXm i) hA
  have hBm i : MeasurableSet (B i) := (hB i).elim (fun h ↦ h ▸ hA) (fun h ↦ h ▸ hA.compl)
  have hprob i : P (X i ⁻¹' B i) = ν (B i) := by
    rw [← (hX i).map_eq, Measure.map_apply (hXm i) (hBm i)]
  have hbound i : ν (B i) ≤ max (ν A) (ν Aᶜ) :=
    (hB i).elim (fun h ↦ h ▸ le_max_left _ _) (fun h ↦ h ▸ le_max_right _ _)
  have hsub : s ≤ᵐ[P] ⋂ i ∈ Finset.range n, X i ⁻¹' B i := by
    refine (ae_all_iff.mpr hfull).mono ?_
    exact fun ω hω hsω ↦ mem_iInter.mpr fun i ↦ mem_iInter.mpr fun _ ↦ hω i hsω
  refine (measure_mono_ae hsub).trans ?_
  rw [hIndep.measure_inter_preimage_eq_mul (Finset.range n) (fun i _ ↦ hBm i)]
  simpa only [Finset.prod_const, Finset.card_range] using
    Finset.prod_le_prod (s := Finset.range n) (fun i _ ↦ (hprob i).trans_le (hbound i))

/-- An independent sequence with a common law having a nontrivial measurable
event forces the source probability measure to be atomless. -/
private lemma hasNoAtoms_of_iid_of_nontrivial_event
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E}
    (hXm : ∀ n, Measurable (X n))
    (hX : ∀ n, HasLaw (X n) ν P)
    (hIndep : iIndepFun X P)
    {A : Set E} (hA : MeasurableSet A)
    (hApos : 0 < ν A) (hAlt : ν A < 1) :
    P.HasNoAtoms := by
  have hc : max (ν A) (ν Aᶜ) < 1 := max_lt hAlt
    (by simpa using prob_compl_lt_one_sub_of_lt_prob hApos hA)
  intro s _ _ hs
  have hzero : P s ≤ 0 := ge_of_tendsto'
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc)
    (fun n ↦ measure_atom_le_pow_of_iid hXm hX hIndep hA hs n)
  exact hs.2.1.not_ge hzero

/-- A probability space supports an independent sequence with a prescribed
non-Dirac standard Borel law exactly when it is atomless. -/
theorem exists_iid_hasLaw_iff_hasNoAtoms
    [StandardBorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : ∀ x : E, ν ≠ Measure.dirac x) :
    (∃ X : ℕ → Ω → E,
      (∀ n, HasLaw (X n) ν P) ∧
      iIndepFun X P) ↔ P.HasNoAtoms := by
  constructor
  · rintro ⟨X, hX, hIndep⟩
    obtain ⟨A, hA, hApos, hAlt⟩ := exists_measurableSet_measure_pos_lt_one ν hν
    let Y : ℕ → Ω → E := fun n ↦ (hX n).aemeasurable.mk (X n)
    have hY n : HasLaw (Y n) ν P := (hX n).congr (hX n).aemeasurable.ae_eq_mk.symm
    exact hasNoAtoms_of_iid_of_nontrivial_event
      (fun n ↦ (hX n).aemeasurable.measurable_mk) hY
      (hIndep.congr fun n ↦ (hX n).aemeasurable.ae_eq_mk) hA hApos hAlt
  · intro hP
    obtain ⟨X, _, hX, hIndep⟩ := exists_iid_hasLaw_of_hasNoAtoms hP ν
    exact ⟨X, hX, hIndep⟩

end ProbabilityTheory
