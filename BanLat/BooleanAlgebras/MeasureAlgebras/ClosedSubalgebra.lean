/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Adjoin
import BanLat.BooleanAlgebras.MeasureAlgebras.Metric
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Closed subalgebras of measure algebras

This file studies Boolean subalgebras `A` that are closed for the canonical metric
`d(a, b) = μ(a ∆ b)` of a measure algebra `(B, μ )`. It introduces the measure algebra
obtaining by the restriction of `μ` to a `σ`-complete Boolean subalgebra.

Moreover, it shows that the following conditions are equivalent:
* `A` is closed under countable suprema.
* `A` is a closed subset of `B` with respecto to `d`.

The **metric closure** of a Boolean subalgebra is introduced and shown to agree with
the `σ`-complete closure. The file then gives density-character bounds for closures,
adjoin algebras, and closures of unions.

It also extends measure-preserving order isomorphisms to closures.
-/

universe u v

namespace MeasureAlgebra

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-! ## Basic definitions -/

/-- A Boolean subalgebra of a measure algebra is closed if its carrier is
closed for the canonical measure metric. -/
def IsClosedSubalgebra (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) : Prop :=
  letI := μ.toMetricSpace
  IsClosed (A : Set B)

/-- The density character of a Boolean subalgebra, using the induced metric. -/
noncomputable def subalgebraDensityCharacter
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) : Cardinal :=
  letI := μ.toMetricSpace
  TopologicalSpace.densityCharacter A

/-! ## Restricted measure algebras -/

/-- The metric of a restricted measure algebra is the metric induced by the
ambient measure algebra. -/
@[nolint unusedArguments]
theorem restrictToSubalgebra_dist_eq (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (a b : A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := μ.toMetricSpace
    letI := (μ.restrictToSubalgebra A hA).toMetricSpace
    dist a b = dist (a : B) (b : B) := by
  rfl

/-- The metric of a restricted measure algebra is the metric induced on the
subtype by the ambient measure metric. -/
theorem restrictToSubalgebra_metricSpace_eq_induced
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := μ.toMetricSpace
    (μ.restrictToSubalgebra A hA).toMetricSpace =
      (inferInstance : MetricSpace A) := by
  apply MetricSpace.ext
  rfl

/-- The inclusion of a `σ`-complete Boolean subalgebra into its ambient
measure algebra is an isometry for the restricted measure. -/
theorem isometry_subtype_restrictToSubalgebra (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    @Isometry A B
      (@PseudoMetricSpace.toPseudoEMetricSpace A
        (@MetricSpace.toPseudoMetricSpace A
          (μ.restrictToSubalgebra A hA).toMetricSpace))
      (@PseudoMetricSpace.toPseudoEMetricSpace B
        (@MetricSpace.toPseudoMetricSpace B μ.toMetricSpace))
      ((↑) : A → B) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := μ.toMetricSpace
  rw [μ.restrictToSubalgebra_metricSpace_eq_induced A hA]
  exact isometry_subtype_coe

/-- The restricted measure algebra and the corresponding metric subtype have
the same density character. -/
theorem restrictToSubalgebra_densityCharacter_eq
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := μ.toMetricSpace
    (μ.restrictToSubalgebra A hA).densityCharacter =
      TopologicalSpace.densityCharacter A := by
  unfold densityCharacter
  rw [μ.restrictToSubalgebra_metricSpace_eq_induced A hA]

/-- The density character of a restricted measure algebra is the density
character induced on its underlying Boolean subalgebra. -/
theorem restrictToSubalgebra_densityCharacter_eq_subalgebraDensityCharacter
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (μ.restrictToSubalgebra A hA).densityCharacter =
      μ.subalgebraDensityCharacter A := by
  rw [μ.restrictToSubalgebra_densityCharacter_eq A hA]
  rfl

/-- Density in a restricted measure algebra agrees with density for the
subtype topology induced by the ambient measure algebra. -/
theorem dense_restrictToSubalgebra_iff
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) (S : Set A) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    (letI := (μ.restrictToSubalgebra A hA).toMetricSpace;
      Dense S) ↔
    (letI := μ.toMetricSpace;
      Dense S) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := μ.toMetricSpace
  rw [μ.restrictToSubalgebra_metricSpace_eq_induced A hA]

/-- A `σ`-complete Boolean subalgebra is complete for the metric induced by
the ambient measure algebra. -/
theorem completeSpace_restrictToSubalgebra_induced
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B)
    (hA : A.IsSigmaComplete) :
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := μ.toMetricSpace
    @CompleteSpace A (inferInstance : UniformSpace A) := by
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := μ.toMetricSpace
  have hmetric := μ.restrictToSubalgebra_metricSpace_eq_induced A hA
  have huniform := congrArg
    (fun m : MetricSpace A ↦
      m.toPseudoMetricSpace.toPseudoEMetricSpace.toUniformSpace) hmetric
  have hcomplete : @CompleteSpace A
      ((μ.restrictToSubalgebra A hA).toMetricSpace.toPseudoMetricSpace
        |>.toPseudoEMetricSpace.toUniformSpace) :=
    (μ.restrictToSubalgebra A hA).completeSpace
  exact Eq.mp (congrArg (fun u : UniformSpace A ↦ @CompleteSpace A u) huniform) hcomplete

/-! ## Closed subalgebras and metric closure -/

/-- A Boolean subalgebra of a measure algebra is closed in the measure metric
if and only if it is `σ`-complete. -/
theorem isClosedSubalgebra_iff_isSigmaComplete (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) :
    μ.IsClosedSubalgebra A ↔ A.IsSigmaComplete := by
  constructor
  · intro hA
    rw [BooleanSubalgebra.isSigmaComplete_iff_iSup_mem]
    intro a ha
    letI := μ.toMetricSpace
    change IsClosed (A : Set B) at hA
    apply hA.mem_of_tendsto (μ.tendsto_partialSups a)
    apply Filter.Eventually.of_forall
    intro n
    induction n with
    | zero =>
      rw [partialSups_zero]
      change a 0 ∈ A
      exact ha 0
    | succ n ih =>
      change partialSups a (Order.succ n) ∈ A
      rw [partialSups_succ]
      exact A.sup_mem ih (ha _)
  · intro hA
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := μ.toMetricSpace
    letI := μ.completeSpace_restrictToSubalgebra_induced A hA
    change IsClosed (A : Set B)
    rw [← @Subtype.range_coe B (A : Set B)]
    exact isometry_subtype_coe.isUniformInducing.isComplete_range.isClosed

/-- The closure of a Boolean subalgebra in the measure metric. -/
noncomputable def closure (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) :
    BooleanSubalgebra B := by
  letI := μ.toMetricSpace
  have hcompl : ∀ {a : B}, a ∈ _root_.closure (A : Set B) →
      aᶜ ∈ _root_.closure (A : Set B) := by
    intro a ha
    apply map_mem_closure μ.isometry_compl.continuous ha
    exact fun b hb ↦ A.compl_mem hb
  have hsup : SupClosed (_root_.closure (A : Set B)) := by
    intro a ha b hb
    apply map_mem_closure₂ μ.lipschitzWith_sup.continuous ha hb
    exact fun x hx y hy ↦ A.sup_mem hx hy
  refine
    { carrier := _root_.closure (A : Set B)
      supClosed' := hsup
      infClosed' := by
        intro a ha b hb
        have h := hcompl (hsup (hcompl ha) (hcompl hb))
        simpa only [compl_sup, compl_compl] using h
      compl_mem' := hcompl
      bot_mem' := subset_closure A.bot_mem }

/-- The carrier of the closure of a Boolean subalgebra is its topological
closure in the measure metric. -/
@[simp]
theorem coe_closure (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) :
    letI := μ.toMetricSpace
    (μ.closure A : Set B) = _root_.closure (A : Set B) := by
  rfl

/-- A Boolean subalgebra is contained in its closure for the measure metric. -/
theorem le_closure (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) :
    A ≤ μ.closure A := by
  letI := μ.toMetricSpace
  exact subset_closure

/-- The closure of a Boolean subalgebra is closed in the measure metric. -/
theorem isClosedSubalgebra_closure (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) :
    μ.IsClosedSubalgebra (μ.closure A) := by
  letI := μ.toMetricSpace
  change IsClosed (μ.closure A : Set B)
  rw [μ.coe_closure A]
  exact isClosed_closure

/-- Metric closure and `σ`-complete Boolean closure agree. -/
theorem closure_eq_sigmaCompleteClosure (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) :
    μ.closure A = BooleanSubalgebra.sigmaCompleteClosure (A : Set B) := by
  apply le_antisymm
  · letI := μ.toMetricSpace
    change _root_.closure (A : Set B) ⊆
      (BooleanSubalgebra.sigmaCompleteClosure (A : Set B) : Set B)
    apply closure_minimal
    · exact BooleanSubalgebra.subset_sigmaCompleteClosure (A : Set B)
    · change μ.IsClosedSubalgebra
        (BooleanSubalgebra.sigmaCompleteClosure (A : Set B))
      exact (μ.isClosedSubalgebra_iff_isSigmaComplete _).2
        (BooleanSubalgebra.isSigmaComplete_sigmaCompleteClosure (A : Set B))
  · apply (BooleanSubalgebra.sigmaCompleteClosure_le
      ((μ.isClosedSubalgebra_iff_isSigmaComplete (μ.closure A)).1
        (μ.isClosedSubalgebra_closure A))).2
    exact μ.le_closure A

/-- A Boolean subalgebra is dense in the measure metric if and only if it
`σ`-generates the ambient Boolean algebra. -/
theorem dense_iff_sigmaCompleteClosure_eq_top (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) :
    letI := μ.toMetricSpace
    Dense (A : Set B) ↔
      BooleanSubalgebra.sigmaCompleteClosure (A : Set B) = ⊤ := by
  letI := μ.toMetricSpace
  rw [dense_iff_closure_eq, ← μ.coe_closure A, μ.closure_eq_sigmaCompleteClosure A]
  simp

private noncomputable def subalgebraInClosure (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) : BooleanSubalgebra (μ.closure A) :=
  BooleanSubalgebra.comap (μ.closure A).subtype A

private noncomputable def orderIsoSubalgebraInClosure (μ : MeasureAlgebra B)
    (A : BooleanSubalgebra B) : A ≃o μ.subalgebraInClosure A := by
  refine
    { toFun := fun a ↦ ⟨⟨a, μ.le_closure A a.property⟩, a.property⟩
      invFun := fun a ↦ ⟨a, a.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }

/-! ## Density-character estimates -/

/-- Equal Boolean subalgebras have equal induced density character. -/
theorem subalgebraDensityCharacter_congr
    (μ : MeasureAlgebra B) (A D : BooleanSubalgebra B) (hAD : A = D) :
    μ.subalgebraDensityCharacter A = μ.subalgebraDensityCharacter D := by
  subst D
  rfl

/- `densityCharacter(A.adjoin b) ≤ densityCharacter(A) * densityCharacter(A)`. -/
private theorem subalgebraDensityCharacter_adjoin_le_mul
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) (b : B) :
    μ.subalgebraDensityCharacter (A.adjoin b) ≤
      μ.subalgebraDensityCharacter A * μ.subalgebraDensityCharacter A := by
  unfold subalgebraDensityCharacter
  letI := μ.toMetricSpace
  have hinf : Continuous (fun p : B × B ↦ p.1 ⊓ p.2) := by
    have h := μ.isometry_compl.continuous.comp <|
      μ.lipschitzWith_sup.continuous.comp <|
        (μ.isometry_compl.continuous.comp continuous_fst).prodMk
          (μ.isometry_compl.continuous.comp continuous_snd)
    convert h using 1
    ext p
    simp
  let f : A × A → A.adjoin b := fun p ↦
    ⟨(b ⊓ (p.1 : B)) ⊔ (bᶜ ⊓ (p.2 : B)), ⟨p, rfl⟩⟩
  have hcoe : Continuous ((↑) : A → B) := continuous_subtype_val
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact μ.lipschitzWith_sup.continuous.comp <|
      (hinf.comp (continuous_const.prodMk (hcoe.comp continuous_fst))).prodMk
        (hinf.comp (continuous_const.prodMk (hcoe.comp continuous_snd)))
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨p, hp⟩ := x.property
    exact ⟨p, Subtype.ext hp⟩
  let κ := TopologicalSpace.densityCharacter A
  obtain ⟨g, _, hg⟩ := TopologicalSpace.exists_injective_denseRange_densityCharacter A
  have hgprod : DenseRange (Prod.map g g) := hg.prodMap hg
  calc
    TopologicalSpace.densityCharacter (A.adjoin b) ≤
        TopologicalSpace.densityCharacter (A × A) :=
      TopologicalSpace.densityCharacter_le_of_continuous_surjective hf hfs
    _ ≤ Cardinal.mk (Set.range (Prod.map g g)) :=
      TopologicalSpace.densityCharacter_le_mk_of_dense hgprod
    _ ≤ Cardinal.mk (κ.out × κ.out) := Cardinal.mk_range_le
    _ = κ * κ := by
      rw [Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id]

/-- If `ℵ₀ ≤ κ` and `densityCharacter(A) < κ`, then `densityCharacter(A.adjoin b) < κ`
for every `b ∈ B`. -/
theorem subalgebraDensityCharacter_adjoin_lt
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) (b : B) {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ)
    (hAκ : μ.subalgebraDensityCharacter A < κ) :
    μ.subalgebraDensityCharacter (A.adjoin b) < κ := by
  exact (subalgebraDensityCharacter_adjoin_le_mul μ A b).trans_lt
    (Cardinal.mul_lt_of_lt hκ hAκ hAκ)

/-- If `ℵ₀ ≤ κ` and `densityCharacter(A) ≤ κ`, then `densityCharacter(A.adjoin b) ≤ κ`
for every `b ∈ B`. -/
theorem subalgebraDensityCharacter_adjoin_le
    (μ : MeasureAlgebra B) (A : BooleanSubalgebra B) (b : B) {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ)
    (hAκ : μ.subalgebraDensityCharacter A ≤ κ) :
    μ.subalgebraDensityCharacter (A.adjoin b) ≤ κ := by
  exact (subalgebraDensityCharacter_adjoin_le_mul μ A b).trans <|
    calc
      μ.subalgebraDensityCharacter A * μ.subalgebraDensityCharacter A ≤ κ * κ :=
        mul_le_mul' hAκ hAκ
      _ = κ := Cardinal.mul_eq_self hκ

private theorem subalgebraDensityCharacter_le_mk_of_le_closure
    (μ : MeasureAlgebra B) (A D : BooleanSubalgebra B)
    (hDA : D ≤ A) (hAD : A ≤ μ.closure D) :
    μ.subalgebraDensityCharacter A ≤ Cardinal.mk D := by
  unfold subalgebraDensityCharacter
  letI := μ.toMetricSpace
  let D' := BooleanSubalgebra.comap A.subtype D
  have hD_dense : Dense (D' : Set A) := by
    rw [Metric.dense_iff]
    intro a r hr
    have ha := hAD a.property
    letI := μ.toMetricSpace
    change (a : B) ∈ _root_.closure (D : Set B) at ha
    rw [Metric.mem_closure_iff] at ha
    obtain ⟨d, hd, hda⟩ := ha r hr
    refine ⟨⟨d, hDA hd⟩, ?_, hd⟩
    rw [Metric.mem_ball]
    change dist d (a : B) < r
    simpa only [dist_comm] using hda
  let e : D ≃o D' :=
    { toFun := fun d ↦ ⟨⟨d, hDA d.property⟩, d.property⟩
      invFun := fun d ↦ ⟨d, d.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }
  calc
    TopologicalSpace.densityCharacter A ≤ Cardinal.mk D' :=
      TopologicalSpace.densityCharacter_le_mk_of_dense hD_dense
    _ = Cardinal.mk D := Cardinal.mk_congr e.toEquiv.symm

/-- Let `A i ⊆ B` be Boolean subalgebras. If `#ι ≤ κ`, `ℵ₀ ≤ κ`, and every
`A i` has density character at most `κ`, then the `σ`-complete closure of
`⋃ i, A i` also has density character at most `κ`. -/
theorem subalgebraDensityCharacter_sigmaCompleteClosure_iUnion_le
    {ι : Type u} [Nonempty ι]
    (μ : MeasureAlgebra B) (A : ι → BooleanSubalgebra B)
    {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (hι : Cardinal.mk ι ≤ κ)
    (hden : ∀ i, μ.subalgebraDensityCharacter (A i) ≤ κ) :
    let F := BooleanSubalgebra.sigmaCompleteClosure (⋃ i, (A i : Set B))
    μ.subalgebraDensityCharacter F ≤ κ := by
  classical
  dsimp only
  unfold subalgebraDensityCharacter at hden ⊢
  letI := μ.toMetricSpace
  have hex (i : ι) : ∃ S : Set (A i),
      Dense S ∧ Cardinal.mk S ≤ κ := by
    exact TopologicalSpace.densityCharacter_le_iff_exists_dense_mk_le.mp (hden i)
  choose S hS_dense hS_card using hex
  let T : Set B := ⋃ i, Subtype.val '' S i
  have hT_card : Cardinal.mk T ≤ κ := by
    calc
      Cardinal.mk T ≤ Cardinal.sum (fun i ↦ Cardinal.mk (Subtype.val '' S i)) :=
        Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : ι ↦ κ) :=
        Cardinal.sum_le_sum _ _ fun i ↦
          Cardinal.mk_image_le.trans (hS_card i)
      _ = Cardinal.mk ι * κ := Cardinal.sum_const' ι κ
      _ = κ := Cardinal.mul_eq_right hκ hι
        (Cardinal.mk_ne_zero_iff.mpr inferInstance)
  let G := BooleanSubalgebra.closure T
  let F := BooleanSubalgebra.sigmaCompleteClosure (⋃ i, (A i : Set B))
  let hF := BooleanSubalgebra.isSigmaComplete_sigmaCompleteClosure
    (⋃ i, (A i : Set B))
  have hTG : T ⊆ G := BooleanSubalgebra.subset_closure
  have hTF : T ⊆ F := by
    intro b hb
    obtain ⟨i, a, haS, rfl⟩ := Set.mem_iUnion.mp hb
    exact BooleanSubalgebra.subset_sigmaCompleteClosure _
      (Set.mem_iUnion.2 ⟨i, a.property⟩)
  have hGF : G ≤ F := BooleanSubalgebra.closure_le.2 hTF
  have hAF (i : ι) : A i ≤ μ.closure G := by
    intro b hb
    change b ∈ _root_.closure (G : Set B)
    rw [Metric.mem_closure_iff]
    intro r hr
    have hdense := hS_dense i
    rw [Metric.dense_iff] at hdense
    obtain ⟨a, hai, haS⟩ := hdense ⟨b, hb⟩ r hr
    refine ⟨a, hTG (Set.mem_iUnion.2 ⟨i, ⟨a, haS, rfl⟩⟩), ?_⟩
    rw [Metric.mem_ball] at hai
    change dist (a : B) b < r at hai
    simpa only [dist_comm] using hai
  have hFG : F ≤ μ.closure G := by
    apply (BooleanSubalgebra.sigmaCompleteClosure_le
      ((μ.isClosedSubalgebra_iff_isSigmaComplete (μ.closure G)).1
        (μ.isClosedSubalgebra_closure G))).2
    intro b hb
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hb
    exact hAF i hi
  exact (subalgebraDensityCharacter_le_mk_of_le_closure μ F G hGF hFG).trans
      ((BooleanSubalgebra.cardinalMk_closure_le_max T).trans (max_le hT_card hκ))

/-! ## Extending isomorphisms to closures -/

/-- A measure-preserving order isomorphism `e : A ≃o D` extends uniquely on `A`
to a measure-algebra equivalence between the `σ`-complete closures of `A` and `D`. -/
private theorem exists_measureAlgebraEquiv_closure_extends
    {C : Type v} [SigmaCompleteBooleanAlgebra C]
    (μ : MeasureAlgebra B) (η : MeasureAlgebra C)
    (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
    (e : A ≃o D) (he : ∀ a : A, η (e a : C) = μ (a : B)) :
    let hA := (μ.isClosedSubalgebra_iff_isSigmaComplete (μ.closure A)).1
      (μ.isClosedSubalgebra_closure A)
    let hD := (η.isClosedSubalgebra_iff_isSigmaComplete (η.closure D)).1
      (η.isClosedSubalgebra_closure D)
    letI := hA.toSigmaCompleteBooleanAlgebra
    letI := hD.toSigmaCompleteBooleanAlgebra
    ∃ f : MeasureAlgebraEquiv
        (μ.restrictToSubalgebra (μ.closure A) hA)
        (η.restrictToSubalgebra (η.closure D) hD),
      ∀ a : A,
        ((f ⟨a, μ.le_closure A a.property⟩ : η.closure D) : C) = (e a : D) := by
  dsimp only
  let hA := (μ.isClosedSubalgebra_iff_isSigmaComplete (μ.closure A)).1
    (μ.isClosedSubalgebra_closure A)
  let hD := (η.isClosedSubalgebra_iff_isSigmaComplete (η.closure D)).1
    (η.isClosedSubalgebra_closure D)
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  let μA := μ.restrictToSubalgebra (μ.closure A) hA
  let ηD := η.restrictToSubalgebra (η.closure D) hD
  letI := μ.toMetricSpace
  letI := η.toMetricSpace
  let A' := μ.subalgebraInClosure A
  let D' := η.subalgebraInClosure D
  have hA_dense : Dense (A' : Set (μ.closure A)) := by
    rw [Metric.dense_iff]
    intro x r hr
    have hx := x.property
    change (x : B) ∈ _root_.closure (A : Set B) at hx
    rw [Metric.mem_closure_iff] at hx
    obtain ⟨a, ha, hax⟩ := hx r hr
    let a' : μ.closure A := ⟨a, μ.le_closure A ha⟩
    refine ⟨a', ?_, ha⟩
    rw [Metric.mem_ball]
    change dist a (x : B) < r
    simpa only [dist_comm] using hax
  have hD_dense : Dense (D' : Set (η.closure D)) := by
    rw [Metric.dense_iff]
    intro x r hr
    have hx := x.property
    change (x : C) ∈ _root_.closure (D : Set C) at hx
    rw [Metric.mem_closure_iff] at hx
    obtain ⟨d, hd, hdx⟩ := hx r hr
    let d' : η.closure D := ⟨d, η.le_closure D hd⟩
    refine ⟨d', ?_, hd⟩
    rw [Metric.mem_ball]
    change dist d (x : C) < r
    simpa only [dist_comm] using hdx
  let eA := μ.orderIsoSubalgebraInClosure A
  let eD := η.orderIsoSubalgebraInClosure D
  let e' : A' ≃o D' := eA.symm.trans (e.trans eD)
  have he' (a : A') : ηD (e' a : η.closure D) = μA (a : μ.closure A) := by
    change η (e (eA.symm a) : C) = μ (eA.symm a : B)
    exact he (eA.symm a)
  have hA_dense' : @Dense (μ.closure A)
      (μA.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        |>.toUniformSpace.toTopologicalSpace)
      (A' : Set (μ.closure A)) :=
    (μ.dense_restrictToSubalgebra_iff (μ.closure A) hA A').2 hA_dense
  have hD_dense' : @Dense (η.closure D)
      (ηD.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        |>.toUniformSpace.toTopologicalSpace)
      (D' : Set (η.closure D)) :=
    (η.dense_restrictToSubalgebra_iff (η.closure D) hD D').2 hD_dense
  obtain ⟨f, hf⟩ := exists_measureAlgebraEquiv_of_dense_booleanSubalgebra_orderIso
    A' D' hA_dense' hD_dense' e' he'
  refine ⟨f, ?_⟩
  intro a
  let a' : A' := eA a
  have hfa := hf a'
  exact congrArg Subtype.val hfa

namespace PartialEquiv

variable {C : Type v} [SigmaCompleteBooleanAlgebra C]
variable {μ : MeasureAlgebra B} {η : MeasureAlgebra C}

/-- The extension of a measure-preserving order isomorphism between Boolean subalgebras
to a partial measure-algebra equivalence between their closures. -/
noncomputable def ofOrderIsoClosure
    (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
    (e : A ≃o D) (he : ∀ a : A, η (e a : C) = μ (a : B)) :
    PartialEquiv μ η := by
  let hA := (μ.isClosedSubalgebra_iff_isSigmaComplete (μ.closure A)).1
    (μ.isClosedSubalgebra_closure A)
  let hD := (η.isClosedSubalgebra_iff_isSigmaComplete (η.closure D)).1
    (η.isClosedSubalgebra_closure D)
  letI := hA.toSigmaCompleteBooleanAlgebra
  letI := hD.toSigmaCompleteBooleanAlgebra
  let f := Classical.choose (exists_measureAlgebraEquiv_closure_extends μ η A D e he)
  exact
    { source := μ.closure A
      target := η.closure D
      source_isSigmaComplete := hA
      target_isSigmaComplete := hD
      toMeasureAlgebraEquiv := f }

@[simp]
theorem ofOrderIsoClosure_source
    (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
    (e : A ≃o D) (he : ∀ a : A, η (e a : C) = μ (a : B)) :
    (ofOrderIsoClosure A D e he).source = μ.closure A := rfl

@[simp]
theorem ofOrderIsoClosure_target
    (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
    (e : A ≃o D) (he : ∀ a : A, η (e a : C) = μ (a : B)) :
    (ofOrderIsoClosure A D e he).target = η.closure D := rfl

/-- The extension to the closures agrees with the original order isomorphism. -/
theorem ofOrderIsoClosure_apply
    (A : BooleanSubalgebra B) (D : BooleanSubalgebra C)
    (e : A ≃o D) (he : ∀ a : A, η (e a : C) = μ (a : B)) (a : A) :
    ((ofOrderIsoClosure A D e he).toOrderIso
      ⟨a, μ.le_closure A a.property⟩ : C) = (e a : C) := by
  exact Classical.choose_spec
    (exists_measureAlgebraEquiv_closure_extends μ η A D e he) a

/-! ## Unions of partial equivalences -/

/-- Let `ι` be a linearly ordered set and `(E i)_{i ∈ ι}` an increasing family of
partial measure-algebra equivalences between `(B, μ)` and `(D, ν)`. Set `A = ⋃ i, (E i).source`
and `D = ⋃ i, (E i).target`. Then these partial equivalences extend to an order isomorphism
`e : A ≃ D` that preserves the measure. -/
private theorem exists_orderIso_increasingUnion
    {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (E : ι → PartialEquiv μ η)
    (hE : ∀ i j, i ≤ j → (E i).Extends (E j)) :
    let hsource : Monotone (fun i ↦ (E i).source) :=
      fun _ _ hij ↦ (hE _ _ hij).source_le
    let htarget : Monotone (fun i ↦ (E i).target) :=
      fun _ _ hij ↦ (hE _ _ hij).target_le
    let A := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).source) hsource
    let D := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).target) htarget
    ∃ e : A ≃o D,
      (∀ i (a : (E i).source),
        ((e ⟨a, Set.mem_iUnion.2 ⟨i, a.property⟩⟩ : D) : C) =
          ((E i).toOrderIso a : (E i).target)) ∧
      ∀ a : A, η (e a : C) = μ (a : B) := by
  dsimp only
  let hsource : Monotone (fun i ↦ (E i).source) :=
    fun _ _ hij ↦ (hE _ _ hij).source_le
  let htarget : Monotone (fun i ↦ (E i).target) :=
    fun _ _ hij ↦ (hE _ _ hij).target_le
  let A := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).source) hsource
  let D := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).target) htarget
  have hcompat (i j) (hij : i ≤ j) (a : (E i).source) :
      (((E j).toOrderIso ⟨a, hsource hij a.property⟩ : (E j).target) : C) =
        ((E i).toOrderIso a : C) :=
    (hE i j hij).map_eq a
  let e := BooleanSubalgebra.increasingUnionOrderIso
    (fun i ↦ (E i).source) (fun i ↦ (E i).target) hsource htarget
    (fun i ↦ (E i).toOrderIso) hcompat
  have he_apply (i) (a : (E i).source) :
      ((e ⟨a, (BooleanSubalgebra.mem_increasingUnion
        (fun i ↦ (E i).source) hsource a).2 ⟨i, a.property⟩⟩ : D) : C) =
        ((E i).toOrderIso a : C) :=
    BooleanSubalgebra.increasingUnionOrderIso_apply
      (fun i ↦ (E i).source) (fun i ↦ (E i).target) hsource htarget
      (fun i ↦ (E i).toOrderIso) hcompat i a
  refine ⟨e, ?_, ?_⟩
  · intro i a
    exact he_apply i a
  · intro a
    obtain ⟨i, hi⟩ := (BooleanSubalgebra.mem_increasingUnion
      (fun i ↦ (E i).source) hsource (a : B)).1 a.property
    let a' : (E i).source := ⟨a, hi⟩
    have hea : (e a : C) = ((E i).toOrderIso a' : C) := by
      simpa [a'] using he_apply i a'
    rw [hea]
    exact (E i).map_measure a'

/-- Let `(E i)_{i ∈ ι}` be a linearly ordered family of partial measure-algebra
equivalences between `(B, μ)` and `(C, η)`, where `E j` extends `E i` whenever
`i ≤ j`. Then there is a partial measure-algebra equivalence `f` between
`σCompleteClosure (⋃ i, (E i).source)` and `σCompleteClosure (⋃ i, (E i).target)`
that extends all of them. -/
theorem exists_extension_iUnion
    {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (E : ι → PartialEquiv μ η)
    (hE : ∀ i j, i ≤ j → (E i).Extends (E j)) :
    ∃ f : PartialEquiv μ η,
      (∀ i, (E i).Extends f) ∧
        f.source = BooleanSubalgebra.sigmaCompleteClosure
          (⋃ i, ((E i).source : Set B)) ∧
        f.target = BooleanSubalgebra.sigmaCompleteClosure
          (⋃ i, ((E i).target : Set C)) := by
  let hsource : Monotone (fun i ↦ (E i).source) :=
    fun _ _ hij ↦ (hE _ _ hij).source_le
  let htarget : Monotone (fun i ↦ (E i).target) :=
    fun _ _ hij ↦ (hE _ _ hij).target_le
  let A := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).source) hsource
  let D := BooleanSubalgebra.increasingUnion (fun i ↦ (E i).target) htarget
  obtain ⟨e, he, hmeasure⟩ := exists_orderIso_increasingUnion E hE
  let F := ofOrderIsoClosure A D e hmeasure
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    have hsource_i : (E i).source ≤ μ.closure A := by
      intro a ha
      exact μ.le_closure A (Set.mem_iUnion.2 ⟨i, ha⟩)
    have htarget_i : (E i).target ≤ η.closure D := by
      intro d hd
      exact η.le_closure D (Set.mem_iUnion.2 ⟨i, hd⟩)
    refine ⟨hsource_i, htarget_i, ?_⟩
    intro a
    let a' : A := ⟨a, Set.mem_iUnion.2 ⟨i, a.property⟩⟩
    calc
      ((F.toOrderIso ⟨a, hsource_i a.property⟩ : F.target) : C) =
          (e a' : D) := ofOrderIsoClosure_apply A D e hmeasure a'
      _ = ((E i).toOrderIso a : (E i).target) := he i a
  · change μ.closure A = BooleanSubalgebra.sigmaCompleteClosure
      (⋃ i, ((E i).source : Set B))
    rw [μ.closure_eq_sigmaCompleteClosure A]
    congr 1
  · change η.closure D = BooleanSubalgebra.sigmaCompleteClosure
      (⋃ i, ((E i).target : Set C))
    rw [η.closure_eq_sigmaCompleteClosure D]
    congr 1

/-- Let `(E i)_{i ∈ ι}` be a linearly ordered family of partial measure-algebra
equivalences between `(B, μ)` and `(C, η)`, where `E j` extends `E i` whenever
`i ≤ j`. Suppose that `ℵ₀ ≤ κ`, `#ι ≤ κ`, and that the source and target of every
`E i` have density character at most `κ`. Then there is a partial measure-algebra
equivalence `f` extending every `E i` such that `densityCharacter(f.source) ≤ κ`
and `densityCharacter(f.target) ≤ κ`. -/
theorem exists_extension_iUnion_of_densityCharacter_le
    {C' : Type u} [SigmaCompleteBooleanAlgebra C']
    {ν : MeasureAlgebra C'}
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (E : ι → PartialEquiv μ ν)
    (hE : ∀ i j, i ≤ j → (E i).Extends (E j))
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hι : Cardinal.mk ι ≤ κ)
    (hsource : ∀ i, μ.subalgebraDensityCharacter (E i).source ≤ κ)
    (htarget : ∀ i, ν.subalgebraDensityCharacter (E i).target ≤ κ) :
    ∃ f : PartialEquiv μ ν,
      (∀ i, (E i).Extends f) ∧
        μ.subalgebraDensityCharacter f.source ≤ κ ∧
        ν.subalgebraDensityCharacter f.target ≤ κ := by
  obtain ⟨f, hf, hfsource, hftarget⟩ := exists_extension_iUnion E hE
  let S := BooleanSubalgebra.sigmaCompleteClosure
    (⋃ i, ((E i).source : Set B))
  let D := BooleanSubalgebra.sigmaCompleteClosure
    (⋃ i, ((E i).target : Set C'))
  have hsource' :=
    subalgebraDensityCharacter_sigmaCompleteClosure_iUnion_le
      μ (fun i ↦ (E i).source) hκ hι hsource
  have htarget' :=
    subalgebraDensityCharacter_sigmaCompleteClosure_iUnion_le
      ν (fun i ↦ (E i).target) hκ hι htarget
  have hsource_eq := subalgebraDensityCharacter_congr μ f.source S hfsource
  have htarget_eq := subalgebraDensityCharacter_congr ν f.target D hftarget
  refine ⟨f, hf, ?_, ?_⟩
  · exact hsource_eq.trans_le hsource'
  · exact htarget_eq.trans_le htarget'

end PartialEquiv

end MeasureAlgebra
