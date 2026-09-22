/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Atomless
import BanLat.BooleanAlgebras.MeasureAlgebras.Basic
import BanLat.Preliminaries.DensityCharacter
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.SymmDiff
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Metric structure on measure algebras

This file shows that the function `d(a, b) = μ (a ∆ b)` defines a metric
over every measure algebra `(B, μ)`.

The metric space `(B, d)` **is complete.**

It also defines **separable measure algebras** and their **density character.**
-/

open scoped ENNReal symmDiff

universe u v

/-! ## The measure metric -/

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-- The metric associated with a finite measure algebra. -/
@[implicit_reducible]
noncomputable def toMetricSpace : MetricSpace B where
  dist a b := (μ (a ∆ b)).toReal
  dist_self := by
    simp
  dist_comm := by
    intro a b
    rw [symmDiff_comm]
  dist_triangle := by
    intro a b c
    rw [← ENNReal.toReal_add (μ.measure_ne_top _) (μ.measure_ne_top _)]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨μ.measure_ne_top _, μ.measure_ne_top _⟩)
      ((μ.measure_mono (symmDiff_triangle a b c)).trans (μ.measure_sup_le _ _))
  eq_of_dist_eq_zero := by
    intro a b h
    apply symmDiff_eq_bot.mp
    apply (μ.measure_eq_zero_iff _).mp
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (μ.measure_ne_top _)

/-- The distance is the real value of the measure of the symmetric difference. -/
@[simp]
theorem dist_eq_measure_symmDiff (a b : B) :
    letI := μ.toMetricSpace
    dist a b = (μ (a ∆ b)).toReal := by
  rfl

/-- The distance from an element to the bottom element is its measure. -/
theorem dist_bot (a : B) :
    letI := μ.toMetricSpace
    dist a ⊥ = (μ a).toReal := by
  simp [dist_eq_measure_symmDiff]

end MeasureAlgebra

/-! ## Isometries and Lipschitz operations -/

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-- Taking complements is an isometry. -/
theorem isometry_compl :
    letI := μ.toMetricSpace
    Isometry (fun a : B ↦ aᶜ) := by
  letI := μ.toMetricSpace
  rw [isometry_iff_dist_eq]
  intro a b
  simp only [dist_eq_measure_symmDiff, compl_symmDiff_compl]

end MeasureAlgebra

namespace MeasureAlgebraEquiv

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

/-- A measure-algebra equivalence is an isometry for the corresponding
measure metrics. -/
theorem isometry (e : MeasureAlgebraEquiv μ ν) :
    letI := μ.toMetricSpace
    letI := ν.toMetricSpace
    Isometry e := by
  letI := μ.toMetricSpace
  letI := ν.toMetricSpace
  rw [isometry_iff_dist_eq]
  intro a b
  simp only [MeasureAlgebra.dist_eq_measure_symmDiff]
  change (ν (e.toRelIso a ∆ e.toRelIso b)).toReal = _
  rw [← map_symmDiff' e.toRelIso, e.map_measure]

end MeasureAlgebraEquiv

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]
variable (μ : MeasureAlgebra B)

/-- Supremum is Lipschitz as a binary operation. -/
theorem lipschitzWith_sup :
    letI := μ.toMetricSpace
    LipschitzWith 2 (fun p : B × B ↦ p.1 ⊔ p.2) := by
  letI := μ.toMetricSpace
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Prod.dist_eq]
  calc
    dist (p.1 ⊔ p.2) (q.1 ⊔ q.2) ≤
        (μ ((p.1 ∆ q.1) ⊔ (p.2 ∆ q.2))).toReal :=
      ENNReal.toReal_mono (μ.measure_ne_top _)
        (μ.measure_mono (symmDiff_sup_le_sup p.1 p.2 q.1 q.2))
    _ ≤ (μ (p.1 ∆ q.1) + μ (p.2 ∆ q.2)).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨μ.measure_ne_top _, μ.measure_ne_top _⟩)
        (μ.measure_sup_le _ _)
    _ = dist p.1 q.1 + dist p.2 q.2 := by
      rw [ENNReal.toReal_add (μ.measure_ne_top _) (μ.measure_ne_top _)]
      rfl
    _ ≤ 2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      linarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
        le_max_right (dist p.1 q.1) (dist p.2 q.2)]
    _ = ((2 : NNReal) : ℝ) * max (dist p.1 q.1) (dist p.2 q.2) := by norm_num

/-- The density character of a measure algebra for its measure metric. -/
noncomputable def densityCharacter (μ : MeasureAlgebra B) : Cardinal.{u} :=
  letI := μ.toMetricSpace
  TopologicalSpace.densityCharacter B

/-- A measure algebra is separable when its measure-metric topology is separable. -/
noncomputable def IsSeparable : Prop :=
  letI := μ.toMetricSpace
  TopologicalSpace.SeparableSpace B

/-- The density character of a nontrivial atomless measure algebra is infinite. -/
theorem aleph0_le_densityCharacter_of_isAtomless [Nontrivial B]
    (μ : MeasureAlgebra B) (hB : BooleanAlgebra.IsAtomless B) :
    Cardinal.aleph0 ≤ μ.densityCharacter := by
  letI := μ.toMetricSpace
  letI : Infinite B := BooleanAlgebra.infinite_of_isAtomless hB
  unfold densityCharacter
  exact TopologicalSpace.aleph0_le_densityCharacter B

/-- For any sequence `(a n)`, its finite partial suprema
`a 0`, `a 0 ⊔ a 1`, ..., `⨆ k ≤ n, a k` converge in the measure metric to the
countable supremum `⨆ n, a n`. -/
theorem tendsto_partialSups (a : ℕ → B) :
    letI := μ.toMetricSpace
    Filter.Tendsto (partialSups a) Filter.atTop (nhds (⨆ n, a n)) := by
  letI := μ.toMetricSpace
  rw [tendsto_iff_dist_tendsto_zero]
  have hle : ∀ n, partialSups a n ≤ ⨆ n, a n := fun n ↦
    partialSups_le a n _ fun j _ ↦ SigmaCompleteBooleanAlgebra.le_iSup_nat a j
  have hsymm : ∀ n, partialSups a n ∆ (⨆ n, a n) =
      (⨆ n, a n) \ partialSups a n := by
    intro n
    rw [symmDiff_def, sdiff_eq_bot_iff.2 (hle n), bot_sup_eq]
  have hmeasure : ∀ n, μ ((⨆ n, a n) \ partialSups a n) =
      μ (⨆ n, a n) - μ (partialSups a n) := by
    intro n
    have hsum := μ.measure_sdiff_add_inf (⨆ n, a n) (partialSups a n)
    rw [inf_eq_right.mpr (hle n)] at hsum
    exact ENNReal.eq_sub_of_add_eq' (μ.measure_ne_top _) hsum
  have hμ_mono : Monotone (fun n ↦ μ (partialSups a n)) := fun _ _ hnm ↦
    μ.measure_mono (partialSups_monotone a hnm)
  have hμ_iSup : (⨆ n, μ (partialSups a n)) = μ (⨆ n, a n) := by
    rw [← μ.measure_iSup_eq_iSup (partialSups_monotone a),
      SigmaCompleteBooleanAlgebra.iSup_partialSups_nat]
  have hμ_tend : Filter.Tendsto (fun n ↦ μ (partialSups a n)) Filter.atTop
      (nhds (μ (⨆ n, a n))) := by
    rw [← hμ_iSup]
    exact tendsto_atTop_iSup hμ_mono
  have hsub_tend : Filter.Tendsto
      (fun n ↦ μ (⨆ n, a n) - μ (partialSups a n)) Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ ↦ μ (⨆ n, a n)) Filter.atTop
        (nhds (μ (⨆ n, a n))) := tendsto_const_nhds
    have h := ENNReal.tendsto_sub (Or.inr (μ.measure_ne_top (⨆ n, a n))) |>.comp
      (Filter.Tendsto.prodMk_nhds hconst hμ_tend)
    change Filter.Tendsto (fun n ↦ μ (⨆ n, a n) - μ (partialSups a n))
      Filter.atTop (nhds (μ (⨆ n, a n) - μ (⨆ n, a n))) at h
    simpa only [tsub_self] using h
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsub_tend
  convert hreal using 1
  · funext n
    rw [dist_eq_measure_symmDiff, Function.comp_apply, hsymm n, hmeasure n]
  · simp

private def symmDiffTail (g : ℕ → B) (n : ℕ) : B :=
  ⨆ k, g (n + k) ∆ g (n + k + 1)

private def symmDiffLimit (g : ℕ → B) : B :=
  ⨆ n, g n \ symmDiffTail g n

private theorem symmDiff_add_le_tail (g : ℕ → B) (n k : ℕ) :
    g n ∆ g (n + k) ≤ symmDiffTail g n := by
  induction k with
  | zero => simp
  | succ k ih =>
      apply (symmDiff_triangle (g n) (g (n + k)) (g (n + (k + 1)))).trans
      apply sup_le
      · exact ih
      · simpa [symmDiffTail, Nat.add_assoc] using
          SigmaCompleteBooleanAlgebra.le_iSup_nat
            (fun j ↦ g (n + j) ∆ g (n + j + 1)) k

private theorem symmDiff_core_le_later (g : ℕ → B) {m n : ℕ} (hmn : m ≤ n) :
    g m \ symmDiffTail g m ≤ g n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  apply sdiff_le_iff.2
  calc
    g m ≤ (g m ∆ g (m + k)) ⊔ g (m + k) := le_symmDiff_sup_right _ _
    _ ≤ symmDiffTail g m ⊔ g (m + k) :=
      sup_le_sup_right (symmDiff_add_le_tail g m k) _

private theorem symmDiff_core_le_later_sup_tail
    (g : ℕ → B) {n m : ℕ} (hnm : n ≤ m) :
    g m \ symmDiffTail g m ≤ g n ⊔ symmDiffTail g n := by
  apply sdiff_le.trans
  calc
    g m ≤ (g m ∆ g n) ⊔ g n := le_symmDiff_sup_right _ _
    _ ≤ symmDiffTail g n ⊔ g n := by
      gcongr
      rw [symmDiff_comm]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact symmDiff_add_le_tail g n k
    _ = g n ⊔ symmDiffTail g n := sup_comm _ _

private theorem symmDiff_limit_le_tail (g : ℕ → B) (n : ℕ) :
    g n ∆ symmDiffLimit g ≤ symmDiffTail g n := by
  apply symmDiff_le
  · calc
      g n ≤ symmDiffTail g n ⊔ (g n \ symmDiffTail g n) := le_sup_sdiff
      _ ≤ symmDiffTail g n ⊔ symmDiffLimit g := by
        gcongr
        exact SigmaCompleteBooleanAlgebra.le_sSup_of_countable
          (Set.countable_range fun m ↦ g m \ symmDiffTail g m) ⟨n, rfl⟩
      _ = symmDiffLimit g ⊔ symmDiffTail g n := sup_comm _ _
  · apply SigmaCompleteBooleanAlgebra.sSup_le_of_countable
      (Set.countable_range fun m ↦ g m \ symmDiffTail g m)
    rintro _ ⟨m, rfl⟩
    by_cases hmn : m ≤ n
    · exact (symmDiff_core_le_later g hmn).trans le_sup_left
    · exact symmDiff_core_le_later_sup_tail g (Nat.le_of_lt (lt_of_not_ge hmn))

private theorem measure_symmDiffTail_le (g : ℕ → B)
    (h : ∀ n, μ (g n ∆ g (n + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1)) (n : ℕ) :
    μ (symmDiffTail g n) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  calc
    μ (symmDiffTail g n) ≤ ∑' k, μ (g (n + k) ∆ g (n + k + 1)) :=
      μ.measure_iSup_le _
    _ ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ (n + k + 1) :=
      ENNReal.tsum_le_tsum fun k ↦ h (n + k)
    _ = (2⁻¹ : ℝ≥0∞) ^ n := by
      have hterm : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + k + 1) =
          (2⁻¹ : ℝ≥0∞) ^ n * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
        intro k
        rw [Nat.add_assoc, pow_add]
      simp_rw [hterm]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      have hcoef : (2⁻¹ : ℝ≥0∞) * (1 - 2⁻¹)⁻¹ = 1 := by
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      rw [hcoef, mul_one]

private theorem tendsto_symmDiffLimit (g : ℕ → B)
    (h : ∀ n, μ (g n ∆ g (n + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1)) :
    (letI := μ.toMetricSpace
     Filter.Tendsto g Filter.atTop (nhds (symmDiffLimit g))) := by
  letI := μ.toMetricSpace
  rw [tendsto_iff_dist_tendsto_zero]
  have hdist : ∀ n, dist (g n) (symmDiffLimit g) ≤
      ((2⁻¹ : ℝ≥0∞) ^ n).toReal := by
    intro n
    rw [dist_eq_measure_symmDiff]
    exact (ENNReal.toReal_mono (μ.measure_ne_top _)
      (μ.measure_mono (symmDiff_limit_le_tail g n))).trans
        (ENNReal.toReal_mono (by finiteness) (measure_symmDiffTail_le μ g h n))
  have hpow : Filter.Tendsto (fun n ↦ ((2⁻¹ : ℝ≥0∞) ^ n).toReal)
      Filter.atTop (nhds 0) := by
    simpa [ENNReal.toReal_pow, ENNReal.toReal_inv] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (2 : ℝ)⁻¹) (by positivity) (by norm_num))
  exact squeeze_zero (fun n ↦ dist_nonneg) hdist hpow

/-- A measure algebra is complete for its measure metric. -/
theorem completeSpace :
    letI := μ.toMetricSpace
    CompleteSpace B := by
  letI := μ.toMetricSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hbound_pos : ∀ n, 0 < ((2⁻¹ : ℝ≥0∞) ^ (n + 1)).toReal := by
    intro n
    apply ENNReal.toReal_pos (ENNReal.pow_ne_zero (by norm_num) _)
    finiteness
  obtain ⟨f, hf_mono, hf_bound⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n ↦ ((2⁻¹ : ℝ≥0∞) ^ (n + 1)).toReal) hbound_pos
  let g : ℕ → B := fun n ↦ u (f n)
  have hg_bound : ∀ n, μ (g n ∆ g (n + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 1) := by
    intro n
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal (μ.measure_ne_top _) (by finiteness)).mp
    simpa [g, dist_eq_measure_symmDiff, symmDiff_comm] using
      hf_bound n (f (n + 1)) (hf_mono.monotone (Nat.le_add_right n 1))
  refine ⟨symmDiffLimit g, tendsto_nhds_of_cauchySeq_of_subseq hu
    hf_mono.tendsto_atTop ?_⟩
  exact tendsto_symmDiffLimit μ g hg_bound

end MeasureAlgebra

/-! ## Extension from dense Boolean subalgebras -/

namespace MeasureAlgebra

variable {B : Type u} {C : Type v}
variable [SigmaCompleteBooleanAlgebra B] [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {ν : MeasureAlgebra C}

/-- A measure-preserving order isomorphism between Boolean subalgebras is an
isometry for the metrics induced by the ambient measure algebras. -/
private theorem isometry_coe_orderIso
    (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
    (e : A ≃o D) (he : ∀ a : A, ν (e a : C) = μ (a : B)) :
    letI := μ.toMetricSpace
    letI := ν.toMetricSpace
    Isometry (fun a : A ↦ (e a : C)) := by
  letI := μ.toMetricSpace
  letI := ν.toMetricSpace
  rw [isometry_iff_dist_eq]
  intro a b
  change (ν (symmDiff (e a : C) (e b : C))).toReal =
    (μ (symmDiff (a : B) (b : B))).toReal
  rw [show symmDiff (e a : C) (e b : C) = (e (symmDiff a b) : C) from
    congrArg Subtype.val (map_symmDiff' e a b).symm, he]
  rfl

/-- The continuous extension of an isometry from a dense Boolean subalgebra
into a complete measure algebra is an isometry. -/
private theorem isometry_extend
    (A : BooleanSubalgebra B)
    (hA :
      letI := μ.toMetricSpace
      Dense (A : Set B))
    (f : A → C)
    (hf :
      letI := μ.toMetricSpace
      letI := ν.toMetricSpace
      Isometry f) :
    letI := μ.toMetricSpace
    letI := ν.toMetricSpace
    letI := ν.completeSpace
    Isometry (hA.extend f) := by
  letI := μ.toMetricSpace
  letI := ν.toMetricSpace
  letI := ν.completeSpace
  rw [isometry_iff_dist_eq]
  apply isClosed_property2
    (p := fun a b : B ↦ dist (hA.extend f a) (hA.extend f b) = dist a b)
      hA.denseRange_val
  · exact isClosed_eq
      (continuous_dist.comp
        (((hA.uniformContinuous_extend hf.uniformContinuous).continuous.comp
          continuous_fst).prodMk
          ((hA.uniformContinuous_extend hf.uniformContinuous).continuous.comp
            continuous_snd)))
      continuous_dist
  · intro a b
    rw [hA.extend_of_ind hf.uniformContinuous, hA.extend_of_ind hf.uniformContinuous]
    exact hf.dist_eq a b

/-- If a uniformly continuous map on a dense Boolean subalgebra preserves
binary suprema, then its continuous extension preserves binary suprema. -/
private theorem extend_map_sup
    (A : BooleanSubalgebra B)
    (hA :
      letI := μ.toMetricSpace
      Dense (A : Set B))
    (f : A → C)
    (hf :
      letI := μ.toMetricSpace
      letI := ν.toMetricSpace
      UniformContinuous f)
    (hsup : ∀ a b : A, f (a ⊔ b) = f a ⊔ f b) :
    letI := μ.toMetricSpace
    letI := ν.toMetricSpace
    letI := ν.completeSpace
    ∀ a b : B, hA.extend f (a ⊔ b) = hA.extend f a ⊔ hA.extend f b := by
  letI := μ.toMetricSpace
  letI := ν.toMetricSpace
  letI := ν.completeSpace
  apply isClosed_property2
    (p := fun a b : B ↦ hA.extend f (a ⊔ b) = hA.extend f a ⊔ hA.extend f b)
      hA.denseRange_val
  · exact isClosed_eq
      (hA.uniformContinuous_extend hf |>.continuous.comp μ.lipschitzWith_sup.continuous)
      (ν.lipschitzWith_sup.continuous.comp
        (((hA.uniformContinuous_extend hf).continuous.comp continuous_fst).prodMk
          ((hA.uniformContinuous_extend hf).continuous.comp continuous_snd)))
  · intro a b
    rw [← show ((a ⊔ b : A) : B) = (a : B) ⊔ (b : B) by rfl]
    rw [hA.extend_of_ind hf, hA.extend_of_ind hf, hA.extend_of_ind hf]
    exact hsup a b

/-- A measure-preserving order isomorphism `e : A ≃o D` between dense Boolean
subalgebras extends to a measure-algebra equivalence `f` with `f(a) = e(a)` for `a ∈ A`. -/
theorem exists_measureAlgebraEquiv_of_dense_booleanSubalgebra_orderIso
    (A : BooleanSubalgebra B)
    (D : BooleanSubalgebra C)
    (hA :
      letI := μ.toMetricSpace
      Dense (A : Set B))
    (hD :
      letI := ν.toMetricSpace
      Dense (D : Set C))
    (e : A ≃o D)
    (he : ∀ a : A, ν (e a : C) = μ (a : B)) :
    ∃ f : MeasureAlgebraEquiv μ ν,
      ∀ a : A, f (a : B) = (e a : C) := by
  letI := μ.toMetricSpace
  letI := ν.toMetricSpace
  letI := μ.completeSpace
  letI := ν.completeSpace
  have h_iso : Isometry (fun a : A ↦ (e a : C)) := by
    exact isometry_coe_orderIso A D e he
  have he_symm (d : D) : μ (e.symm d : B) = ν (d : C) := by
    simpa using (he (e.symm d)).symm
  have h_iso_symm : Isometry (fun d : D ↦ (e.symm d : B)) := by
    exact isometry_coe_orderIso (μ := ν) (ν := μ) D A e.symm he_symm
  let F : B → C := hA.extend (fun a : A ↦ (e a : C))
  let G : C → B := hD.extend (fun d : D ↦ (e.symm d : B))
  have hF_iso : Isometry F := by
    exact isometry_extend A hA (fun a : A ↦ (e a : C)) h_iso
  have hG_iso : Isometry G := by
    exact isometry_extend (μ := ν) (ν := μ) D hD
      (fun d : D ↦ (e.symm d : B)) h_iso_symm
  have hF_uc : UniformContinuous F := by
    exact hF_iso.uniformContinuous
  have hG_uc : UniformContinuous G := by
    exact hG_iso.uniformContinuous
  have hF (a : A) : F a = (e a : C) := by
    exact hA.extend_of_ind h_iso.uniformContinuous a
  have hG (d : D) : G d = (e.symm d : B) := by
    exact hD.extend_of_ind h_iso_symm.uniformContinuous d
  have hGF : G ∘ F = id := by
    apply hA.denseRange_val.equalizer (hG_uc.comp hF_uc).continuous continuous_id
    funext a
    change G (F a) = (a : B)
    rw [hF a, hG (e a), e.symm_apply_apply]
  have hFG : F ∘ G = id := by
    apply hD.denseRange_val.equalizer (hF_uc.comp hG_uc).continuous continuous_id
    funext d
    change F (G d) = (d : C)
    rw [hG d, hF (e.symm d), e.apply_symm_apply]
  let equiv : B ≃ C :=
    { toFun := F
      invFun := G
      left_inv := fun b ↦ congrFun hGF b
      right_inv := fun c ↦ congrFun hFG c }
  have hF_sup : ∀ a b : B, F (a ⊔ b) = F a ⊔ F b := by
    exact extend_map_sup A hA (fun a : A ↦ (e a : C)) h_iso.uniformContinuous
      fun a b ↦ congrArg Subtype.val (e.map_sup a b)
  have hG_sup : ∀ c d : C, G (c ⊔ d) = G c ⊔ G d := by
    exact extend_map_sup (μ := ν) (ν := μ) D hD
      (fun d : D ↦ (e.symm d : B)) h_iso_symm.uniformContinuous
      fun c d ↦ congrArg Subtype.val (e.symm.map_sup c d)
  have hF_mono : Monotone F := by
    intro a b hab
    rw [← sup_eq_right.2 hab, hF_sup]
    exact le_sup_left
  have hG_mono : Monotone G := by
    intro c d hcd
    rw [← sup_eq_right.2 hcd, hG_sup]
    exact le_sup_left
  let orderIso : B ≃o C := equiv.toOrderIso hF_mono hG_mono
  have hF_bot : F ⊥ = ⊥ := by
    calc
      F ⊥ = (e (⊥ : A) : C) := hF ⊥
      _ = ⊥ := congrArg Subtype.val e.map_bot
  have hmeasure (b : B) : ν (F b) = μ b := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ν.measure_ne_top _) (μ.measure_ne_top _)).mp
    calc
      (ν (F b)).toReal = dist (F b) ⊥ := (ν.dist_bot (F b)).symm
      _ = dist (F b) (F ⊥) := by rw [hF_bot]
      _ = dist b ⊥ := hF_iso.dist_eq b ⊥
      _ = (μ b).toReal := μ.dist_bot b
  let e' : MeasureAlgebraEquiv μ ν := { orderIso with map_measure' := hmeasure }
  refine ⟨e', ?_⟩
  intro a
  exact hF a

/-- A measure-preserving order isomorphism between dense Boolean subalgebras
extends to a measure-algebra equivalence of the ambient algebras. -/
theorem nonempty_measureAlgebraEquiv_of_dense_booleanSubalgebra_orderIso
    (A : BooleanSubalgebra B)
    (D : BooleanSubalgebra C)
    (hA :
      letI := μ.toMetricSpace
      Dense (A : Set B))
    (hD :
      letI := ν.toMetricSpace
      Dense (D : Set C))
    (e : A ≃o D)
    (he : ∀ a : A, ν (e a : C) = μ (a : B)) :
    Nonempty (MeasureAlgebraEquiv μ ν) := by
  obtain ⟨f, _⟩ :=
    exists_measureAlgebraEquiv_of_dense_booleanSubalgebra_orderIso A D hA hD e he
  exact ⟨f⟩

end MeasureAlgebra
