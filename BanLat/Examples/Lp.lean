import BanLat.ALSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Order.Sublattice

/-!
# Lp spaces as Banach lattices

For a measure space `(α, μ)` and `1 ≤ p`, the space `Lp ℝ p μ` of real-valued
Lp functions is a Banach lattice under the pointwise order and the Lp norm.
When `p = 1` the norm is additive on the positive cone, making `L₁(μ)` an
AL-space. For `1 ≤ p < ∞` the space has no strong units.
-/

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Lattice and order structure

Mathlib provides `Lattice (Lp ℝ p μ)`, `IsOrderedAddMonoid (Lp ℝ p μ)`,
`HasSolidNorm (Lp ℝ p μ)`, `NormedAddCommGroup (Lp ℝ p μ)`, and
`CompleteSpace (Lp ℝ p μ)` via `MeasureTheory.Lp.instLattice`,
`MeasureTheory.Lp.instHasSolidNorm`, and
`MeasureTheory.Lp.instCompleteSpace`.
-/

/-! ### Vector lattice -/

/-- `Lp ℝ p μ` is a vector lattice: a real module whose positive cone is
closed under scalar multiplication by non-negative reals. -/
noncomputable instance instVectorLatticeLp : VectorLattice (Lp ℝ p μ) where
  smul_le_smul_of_nonneg_left a ha x y hxy := by
    rw [← Lp.coeFn_le] at hxy ⊢
    filter_upwards [Lp.coeFn_smul a x, Lp.coeFn_smul a y, hxy] with i h1 h2 h3
    rw [h1, h2]
    exact smul_le_smul_of_nonneg_left h3 ha

/-! ### Normed vector lattice -/

/-- `Lp ℝ p μ` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeLp :
    NormedVectorLattice (Lp ℝ p μ) where

/-! ### Banach lattice -/

/-- `Lp ℝ p μ` is a Banach lattice: a complete normed vector lattice. -/
noncomputable instance instBanachLatticeLp : BanachLattice (Lp ℝ p μ) where

/-! ### Closed sublattices of Lp

For `1 ≤ p < ∞` and a finite measure `μ`, the norm-closed sublattices of
`Lp ℝ p μ` that contain the constant function `𝟙` are exactly the subspaces
`lpMeas ℝ ℝ m p μ` of functions measurable with respect to a sub-σ-algebra
`m ≤ m₀`.
-/

section ClosedSublattices

variable {Ω : Type} {m₀ : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω} {p : ENNReal} [Fact (1 ≤ p)]

/-
Outline of the proof. Let `m := {A ∈ m₀ : 1_A ∈ L}`. This family is a
sub-σ-algebra of `m₀`: closure under complements uses `1_{Aᶜ} = 1 - 1_A`
and closure under countable unions uses order continuity of the `Lp` norm
together with norm-closure of `L`. One then shows that `L`, viewed as a
submodule of `Lp ℝ p μ`, coincides with `lpMeas ℝ ℝ m p μ`: the forward
inclusion follows because `m`-simple functions are dense in `lpMeas` and
their indicators belong to `L`; the reverse inclusion follows because, for
`f ∈ L`, every superlevel set `{f > λ}` lies in `m` (via
`(n · (f - λ1)⁺ ∧ 1) ↑ 1_{f > λ}` in norm). The Banach-lattice equivalence
with `Lp ℝ p (μ.trim h)` is then obtained from `lpMeasToLpTrimLie` together
with preservation of the pointwise lattice operations.
-/

namespace exists_Lp_banachLatEquiv_aux

/-- The family of `m₀`-measurable sets `A` whose indicator function
`1_A ∈ L p μ` lies in the sublattice `L`. This family will be shown to be a
sub-σ-algebra of `m₀`. -/
private def indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ)) : Set (Set Ω) :=
  {A | ∃ hA : MeasurableSet A,
    indicatorConstLp p hA (measure_ne_top μ A) (1 : ℝ) ∈ L.toSubmodule}

omit [Fact (1 ≤ p)] in
/-- The empty set belongs to `indicatorFamily` since `1_∅ = 0 ∈ L`. -/
private lemma empty_mem_indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ)) :
    ∅ ∈ indicatorFamily (μ := μ) (p := p) L := by
  exact ⟨MeasurableSet.empty, by
    rw [indicatorConstLp_empty]; exact L.toSubmodule.zero_mem⟩

omit [Fact (1 ≤ p)] in
/-- `indicatorFamily` is closed under complements: if `1_A ∈ L`, then
`1_{Aᶜ} = 1 - 1_A ∈ L`. -/
private lemma compl_mem_indicatorFamily [IsFiniteMeasure μ]
    (L : VectorSublattice (Lp ℝ p μ))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) {A : Set Ω}
    (hA : A ∈ indicatorFamily (μ := μ) (p := p) L) :
    Aᶜ ∈ indicatorFamily (μ := μ) (p := p) L := by
  obtain ⟨hAm, hAL⟩ := hA
  refine ⟨hAm.compl, ?_⟩
  have h : indicatorConstLp p hAm.compl (measure_ne_top μ Aᶜ) (1:ℝ)
      = Lp.const p μ (1:ℝ) - indicatorConstLp p hAm (measure_ne_top μ A) 1 := by
    rw [Lp.ext_iff]
    filter_upwards [indicatorConstLp_coeFn (hs := hAm.compl)
        (hμs := measure_ne_top μ Aᶜ) (c := (1:ℝ)),
      Lp.coeFn_sub (Lp.const p μ (1:ℝ))
        (indicatorConstLp p hAm (measure_ne_top μ A) (1:ℝ)),
      Lp.coeFn_const p μ (1:ℝ),
      indicatorConstLp_coeFn (hs := hAm) (hμs := measure_ne_top μ A)
        (c := (1:ℝ))] with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4, Set.indicator_compl]
    rfl
  rw [h]
  exact L.toSubmodule.sub_mem hone hAL

omit [Fact (1 ≤ p)] in
/-- In `Lp`, the indicator of a union of two measurable sets is the supremum
of the individual indicators. -/
private lemma indicatorConstLp_union_eq_sup [IsFiniteMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    indicatorConstLp p (hA.union hB) (measure_ne_top μ _) (1 : ℝ)
      = indicatorConstLp p hA (measure_ne_top μ _) (1 : ℝ)
        ⊔ indicatorConstLp p hB (measure_ne_top μ _) (1 : ℝ) := by
  rw [Lp.ext_iff]
  filter_upwards [indicatorConstLp_coeFn (hs := hA.union hB)
      (hμs := measure_ne_top μ (A ∪ B)) (c := (1:ℝ)),
    Lp.coeFn_sup (indicatorConstLp p hA (measure_ne_top μ A) (1:ℝ))
      (indicatorConstLp p hB (measure_ne_top μ B) (1:ℝ)),
    indicatorConstLp_coeFn (hs := hA) (hμs := measure_ne_top μ A) (c := (1:ℝ)),
    indicatorConstLp_coeFn (hs := hB) (hμs := measure_ne_top μ B) (c := (1:ℝ))]
    with x h1 h2 h3 h4
  rw [h1, h2, Pi.sup_apply, h3, h4]
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxA, hxB,
      Set.mem_union, sup_of_le_left, sup_of_le_right]

/-- `indicatorFamily` is closed under countable unions. For a monotone
sequence this follows from order continuity of the `Lp` norm together with
norm-closure of `L`; the general case is reduced to the monotone case in the
usual way. -/
private lemma iUnion_mem_indicatorFamily [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    {f : ℕ → Set Ω}
    (hf : ∀ i, f i ∈ indicatorFamily (μ := μ) (p := p) L) :
    (⋃ i, f i) ∈ indicatorFamily (μ := μ) (p := p) L := by
  have hfm : ∀ i, MeasurableSet (f i) := fun i => (hf i).1
  have hfL : ∀ i, indicatorConstLp p (hfm i) (measure_ne_top μ (f i)) (1:ℝ)
                ∈ L.toSubmodule := fun i => (hf i).2
  let A : ℕ → Set Ω := Set.accumulate f
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hfm i))
  have hAmono : Monotone A := Set.monotone_accumulate
  have hAunion : ⋃ n, A n = ⋃ i, f i := Set.iUnion_accumulate
  have hAL : ∀ n, indicatorConstLp p (hAm n) (measure_ne_top μ (A n)) (1:ℝ)
                ∈ L.toSubmodule := by
    intro n
    induction n with
    | zero =>
      have hA0 : A 0 = f 0 := Set.accumulate_zero_nat f
      have : indicatorConstLp p (hAm 0) (measure_ne_top μ (A 0)) (1:ℝ)
           = indicatorConstLp p (hfm 0) (measure_ne_top μ (f 0)) (1:ℝ) := by
        congr 1
      rw [this]; exact hfL 0
    | succ n ih =>
      have hAsucc : A (n+1) = A n ∪ f (n+1) := Set.accumulate_succ f n
      have : indicatorConstLp p (hAm (n+1)) (measure_ne_top μ (A (n+1))) (1:ℝ)
           = indicatorConstLp p ((hAm n).union (hfm (n+1)))
               (measure_ne_top μ _) (1:ℝ) := by
        congr 1
      rw [this, indicatorConstLp_union_eq_sup (hAm n) (hfm (n+1))]
      exact L.sup_mem ih (hfL (n+1))
  have hUm : MeasurableSet (⋃ i, f i) :=
    MeasurableSet.iUnion hfm
  refine ⟨hUm, ?_⟩
  have htendsto : Filter.Tendsto
      (fun n => indicatorConstLp p (hAm n) (measure_ne_top μ (A n)) (1:ℝ))
      Filter.atTop (nhds (indicatorConstLp p hUm (measure_ne_top μ _) (1:ℝ))) := by
    refine tendsto_indicatorConstLp_set (ht := hAm)
      (hμt := fun n => measure_ne_top μ (A n)) hp_ne_top ?_
    -- μ (symmDiff (A n) (⋃ i, f i)) → 0
    have hAsub : ∀ n, A n ⊆ ⋃ i, f i := fun n =>
      (Set.accumulate_subset_iUnion n)
    have hsymm : ∀ n, symmDiff (A n) (⋃ i, f i) = (⋃ i, f i) \ A n := by
      intro n
      rw [symmDiff_def]
      simp [Set.diff_eq_empty.mpr (hAsub n)]
    simp_rw [hsymm]
    -- μ((⋃ i, f i) \ A n) = μ(⋃ i, f i) - μ(A n) → 0
    have hmtendsto : Filter.Tendsto (fun n => μ (A n)) Filter.atTop
        (nhds (μ (⋃ i, f i))) := by
      have := tendsto_measure_iUnion_atTop (μ := μ) hAmono
      rw [hAunion] at this
      exact this
    have hsub : ∀ n, μ ((⋃ i, f i) \ A n) = μ (⋃ i, f i) - μ (A n) := fun n =>
      measure_diff (hAsub n) (hAm n).nullMeasurableSet (measure_ne_top μ _)
    simp_rw [hsub]
    have hfin : μ (⋃ i, f i) ≠ ⊤ := measure_ne_top μ _
    have hsub_tendsto : Filter.Tendsto
        (fun n => μ (⋃ i, f i) - μ (A n)) Filter.atTop
        (nhds (μ (⋃ i, f i) - μ (⋃ i, f i))) :=
      ENNReal.tendsto_sub (Or.inr hfin) |>.comp
        (Filter.Tendsto.prodMk_nhds tendsto_const_nhds hmtendsto)
    rw [tsub_self] at hsub_tendsto
    exact hsub_tendsto
  exact hclosed.isSeqClosed (fun n => hAL n) htendsto

/-- The sub-σ-algebra of `m₀` induced by the sublattice `L`. -/
private def sigmaAlgebra [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) : MeasurableSpace Ω where
  MeasurableSet' A := A ∈ indicatorFamily (μ := μ) (p := p) L
  measurableSet_empty := empty_mem_indicatorFamily L
  measurableSet_compl _ hA := compl_mem_indicatorFamily L hone hA
  measurableSet_iUnion _ := iUnion_mem_indicatorFamily hp_ne_top L hclosed

/-- The induced σ-algebra is coarser than `m₀`. -/
private lemma sigmaAlgebra_le [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    sigmaAlgebra hp_ne_top L hclosed hone ≤ m₀ := by
  intro A hA
  exact hA.1

/-- Every `m`-simple function lies in `L`: the indicator of every set in
`indicatorFamily` is in `L`, and `L` is a real subspace. -/
private lemma simpleFunc_mem_sublattice [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (f : Lp ℝ p μ)
    (hf : AEStronglyMeasurable[sigmaAlgebra hp_ne_top L hclosed hone] f μ) :
    f ∈ L.toSubmodule := by
  sorry

/-- Conversely, if `f ∈ L` then every superlevel set `{f > λ}` lies in
`indicatorFamily`: `(n · f⁺ ∧ 1) ↑ 1_{f > 0}` in the `Lp`-norm (by order
continuity), and `L` is norm-closed and a sublattice. -/
private lemma aeStronglyMeasurable_of_mem_sublattice [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) {f : Lp ℝ p μ}
    (hf : f ∈ L.toSubmodule) :
    AEStronglyMeasurable[sigmaAlgebra hp_ne_top L hclosed hone] f μ := by
  sorry

/-- The sublattice `L` coincides, as a submodule of `Lp ℝ p μ`, with
`lpMeas ℝ ℝ m p μ` for the induced sub-σ-algebra `m`. -/
private lemma toSubmodule_eq_lpMeas [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    L.toSubmodule =
      lpMeas ℝ ℝ (sigmaAlgebra hp_ne_top L hclosed hone) p μ := by
  sorry

/-- The restricted finite measure on the induced σ-algebra. -/
private noncomputable def trimmedMeasure [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    @MeasureTheory.Measure Ω (sigmaAlgebra hp_ne_top L hclosed hone) :=
  μ.trim (sigmaAlgebra_le hp_ne_top L hclosed hone)

private instance [IsFiniteMeasure μ] {hp_ne_top : p ≠ ⊤}
    {L : VectorSublattice (Lp ℝ p μ)}
    {hclosed : IsClosed (L : Set (Lp ℝ p μ))}
    {hone : Lp.const p μ (1 : ℝ) ∈ L} :
    IsFiniteMeasure (trimmedMeasure hp_ne_top L hclosed hone) := by
  unfold trimmedMeasure; infer_instance

/-- The linear isometric equivalence between `↥L.toSubmodule` and
`Lp ℝ p (μ.trim h)`, obtained from `lpMeasToLpTrimLie` by identifying the
sublattice with `lpMeas`. -/
private noncomputable def linearIsometryEquiv [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    ↥L.toSubmodule ≃ₗᵢ[ℝ]
      Lp ℝ p (trimmedMeasure hp_ne_top L hclosed hone) :=
  sorry

/-- The above linear isometry preserves the pointwise supremum. -/
private lemma linearIsometryEquiv_map_sup [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (x y : ↥L.toSubmodule) :
    linearIsometryEquiv hp_ne_top L hclosed hone (x ⊔ y) =
      linearIsometryEquiv hp_ne_top L hclosed hone x ⊔
        linearIsometryEquiv hp_ne_top L hclosed hone y := by
  sorry

/-- The above linear isometry preserves the pointwise infimum. -/
private lemma linearIsometryEquiv_map_inf [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L)
    (x y : ↥L.toSubmodule) :
    linearIsometryEquiv hp_ne_top L hclosed hone (x ⊓ y) =
      linearIsometryEquiv hp_ne_top L hclosed hone x ⊓
        linearIsometryEquiv hp_ne_top L hclosed hone y := by
  sorry

/-- Assemble the Banach lattice equivalence from the linear isometric
equivalence and the two lattice-preservation lemmas. -/
private noncomputable def banachLatEquiv [IsFiniteMeasure μ]
    (hp_ne_top : p ≠ ⊤) (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
    BanachLatEquiv ↥L.toSubmodule
      (Lp ℝ p (trimmedMeasure hp_ne_top L hclosed hone)) :=
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
  { toLinearIsometryEquiv := linearIsometryEquiv hp_ne_top L hclosed hone
    map_sup' := linearIsometryEquiv_map_sup hp_ne_top L hclosed hone
    map_inf' := linearIsometryEquiv_map_inf hp_ne_top L hclosed hone }

end exists_Lp_banachLatEquiv_aux

/-- A norm-closed vector sublattice of `Lp ℝ p μ` (with `1 ≤ p < ∞` and `μ` a
finite measure) that contains the constant function `1` is Banach-lattice
isomorphic to `Lp ℝ p ν` for a finite measure `ν` on some measurable space. -/
theorem exists_Lp_banachLatEquiv_of_closed_sublattice_containing_one
    [IsFiniteMeasure μ] (hp_ne_top : p ≠ ⊤)
    (L : VectorSublattice (Lp ℝ p μ))
    (hclosed : IsClosed (L : Set (Lp ℝ p μ)))
    (hone : Lp.const p μ (1 : ℝ) ∈ L) :
    letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (ν : MeasureTheory.Measure Ω')
      (_ : IsFiniteMeasure ν),
      Nonempty (BanachLatEquiv ↥L.toSubmodule (Lp ℝ p ν)) := by
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hclosed
  refine ⟨Ω,
    exists_Lp_banachLatEquiv_aux.sigmaAlgebra hp_ne_top L hclosed hone,
    exists_Lp_banachLatEquiv_aux.trimmedMeasure hp_ne_top L hclosed hone,
    inferInstance,
    ⟨exists_Lp_banachLatEquiv_aux.banachLatEquiv hp_ne_top L hclosed hone⟩⟩

end ClosedSublattices

/-! ### AL-space structure of L₁

The `L₁` norm is additive on the positive cone:
`‖f + g‖ = ‖f‖ + ‖g‖` for `f, g ≥ 0`. This makes `L₁(μ)` an AL-space.
-/

/-- The `L₁` norm is additive on the positive cone: `‖f + g‖₁ = ‖f‖₁ + ‖g‖₁`
whenever `0 ≤ f` and `0 ≤ g`. -/
theorem Lp.norm_add_of_nonneg {f g : Lp ℝ 1 μ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    ‖f + g‖ = ‖f‖ + ‖g‖ := by
  have hfae : 0 ≤ᵐ[μ] ⇑f := (Lp.coeFn_nonneg f).mpr hf
  have hgae : 0 ≤ᵐ[μ] ⇑g := (Lp.coeFn_nonneg g).mpr hg
  have hf_int : ∫⁻ x, ‖f x‖ₑ ∂μ = ENNReal.ofReal ‖f‖ := by
    rw [Lp.norm_def, ← eLpNorm_one_eq_lintegral_enorm,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  have hg_int : ∫⁻ x, ‖g x‖ₑ ∂μ = ENNReal.ofReal ‖g‖ := by
    rw [Lp.norm_def, ← eLpNorm_one_eq_lintegral_enorm,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)]
  have hfg_int : ∫⁻ x, ‖(f + g) x‖ₑ ∂μ = ENNReal.ofReal ‖f + g‖ := by
    rw [Lp.norm_def, ← eLpNorm_one_eq_lintegral_enorm,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (f + g))]
  have hfm : AEMeasurable (fun x => ‖f x‖ₑ) μ := (Lp.aestronglyMeasurable f).enorm
  have hsum : ∫⁻ x, ‖(f + g) x‖ₑ ∂μ
      = (∫⁻ x, ‖f x‖ₑ ∂μ) + ∫⁻ x, ‖g x‖ₑ ∂μ := by
    rw [← lintegral_add_left' hfm]
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g, hfae, hgae] with x hx hxf hxg
    rw [hx, Pi.add_apply, Real.enorm_of_nonneg hxf, Real.enorm_of_nonneg hxg,
      Real.enorm_of_nonneg (add_nonneg hxf hxg), ENNReal.ofReal_add hxf hxg]
  rw [hfg_int, hf_int, hg_int, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)] at hsum
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsum

/-- `L₁(μ)` is an AL-space: the norm satisfies `‖f + g‖ = ‖f‖ + ‖g‖`
for all non-negative `f` and `g`. -/
noncomputable instance instALSpaceLp1 : ALSpace (Lp ℝ 1 μ) where
  norm_add_eq_of_nonneg hf hg := Lp.norm_add_of_nonneg hf hg

