import BanLat.AMSpace
import BanLat.Dual
import BanLat.Preliminaries.Regularity
import BanLat.Examples.SignedMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Spaces of continuous functions as Banach lattices and AM-spaces

For a compact topological space `K`, the space `C(K, ℝ)` of continuous
real-valued functions equipped with the supremum norm and the pointwise order
is a Banach lattice. Its norm is an AM-norm, so `C(K, ℝ)` is an AM-space.
When `K` is nonempty the constant function `1` is a strong unit and the sup
norm agrees with the gauge norm, making `C(K, ℝ)` an AM-space with unit.
-/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-! ### Lattice and order structure

Mathlib provides `Lattice C(K, ℝ)` (pointwise, via
`ContinuousMap.instLatticeOfTopologicalLattice`) and `IsOrderedAddMonoid C(K, ℝ)`
(via `ContinuousMap.instIsOrderedAddMonoid`). The norm comes from
`ContinuousMap.instNormedAddCommGroup`.
-/

/-! ### Vector lattice -/

/-- `C(K, ℝ)` is a vector lattice: a real module whose positive cone is closed
under scalar multiplication by non-negative reals. -/
noncomputable instance instVectorLatticeCofK : VectorLattice C(K, ℝ) where
  smul_le_smul_of_nonneg_left {a} ha {b₁ b₂} hb := by
    rw [ContinuousMap.le_def] at hb ⊢
    intro x; simp only [ContinuousMap.smul_apply]
    exact smul_le_smul_of_nonneg_left (hb x) ha

/-! ### Normed vector lattice -/

/-- The sup norm on `C(K, ℝ)` is solid: `|f| ≤ |g|` pointwise implies
`‖f‖ ≤ ‖g‖`. -/
instance instHasSolidNormCofK : HasSolidNorm C(K, ℝ) where
  solid {f g} h := by
    simp only [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_mono ⟨‖g‖, Set.forall_mem_range.mpr
      (fun x => ContinuousMap.norm_coe_le_norm g x)⟩
    intro x
    have := ContinuousMap.le_def.mp h x
    rw [ContinuousMap.abs_apply, ContinuousMap.abs_apply] at this
    exact HasSolidNorm.solid this

/-- `C(K, ℝ)` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeCofK :
    NormedVectorLattice C(K, ℝ) where

/-! ### Banach lattice -/

/-- `C(K, ℝ)` is a Banach lattice: a complete normed vector lattice. -/
noncomputable instance instBanachLatticeCofK : BanachLattice C(K, ℝ) where

/-! ### AM-space -/

private theorem norm_coe_le_norm_nonneg
    {f : C(K, ℝ)} (hf : 0 ≤ f) (x : K) : f x ≤ ‖f‖ := by
  calc f x
      = |f x| := (abs_of_nonneg (ContinuousMap.le_def.mp hf x)).symm
    _ = ‖f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f x

/-- `C(K, ℝ)` is an AM-space: for non-negative `f, g`, the sup norm satisfies
`‖f ⊔ g‖ = max ‖f‖ ‖g‖`. -/
noncomputable instance instAMSpaceCofK : AMSpace C(K, ℝ) where
  norm_sup_eq_max_of_nonneg {f g} hf hg := by
    apply le_antisymm
    · apply (ContinuousMap.norm_le _
        (le_max_of_le_left (norm_nonneg f))).mpr
      intro x
      rw [ContinuousMap.sup_apply, Real.norm_eq_abs,
        abs_of_nonneg
          (le_sup_of_le_left (ContinuousMap.le_def.mp hf x))]
      exact max_le_max (norm_coe_le_norm_nonneg hf x)
        (norm_coe_le_norm_nonneg hg x)
    · exact max_le
        (HasSolidNorm.solid (by
          rw [abs_of_nonneg hf,
            abs_of_nonneg (le_sup_of_le_left hf)]
          exact le_sup_left))
        (HasSolidNorm.solid (by
          rw [abs_of_nonneg hg,
            abs_of_nonneg (le_sup_of_le_left hf)]
          exact le_sup_right))

/-! ### Strong unit and AM-space with unit -/

variable [Nonempty K]

/-- The constant function `1` is a strong unit in `C(K, ℝ)`. -/
instance instIsStrongUnitOne :
    IsStrongUnit C(K, ℝ) (ContinuousMap.const K (1 : ℝ)) where
  pos := by
    apply lt_of_le_of_ne
    · intro x; simp
    · intro h
      have := congr_fun
        (congr_arg ContinuousMap.toFun h)
        (Classical.arbitrary K)
      simp at this
  dominates f := by
    refine ⟨‖f‖ + 1, by linarith [norm_nonneg f], ?_⟩
    rw [ContinuousMap.le_def]
    intro x
    rw [ContinuousMap.abs_apply, ContinuousMap.smul_apply,
      ContinuousMap.const_apply, smul_eq_mul, mul_one]
    calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f x
      _ ≤ ‖f‖ + 1 := le_add_of_nonneg_right one_pos.le

omit [CompactSpace K] [Nonempty K] in
private theorem abs_const_one :
    |ContinuousMap.const K (1 : ℝ)| = ContinuousMap.const K 1 :=
  abs_of_nonneg (fun _ => by simp)

private theorem gauge_set_eq (f : C(K, ℝ)) :
    {c : ℝ | 0 ≤ c ∧
      |f| ≤ c • |ContinuousMap.const K (1 : ℝ)|}
    = {c : ℝ | ‖f‖ ≤ c} := by
  ext c; simp only [Set.mem_setOf_eq, abs_const_one]
  constructor
  · rintro ⟨_, hle⟩
    rw [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_le; intro x; rw [Real.norm_eq_abs]
    have := ContinuousMap.le_def.mp hle x
    rwa [ContinuousMap.abs_apply,
      ContinuousMap.smul_apply,
      ContinuousMap.const_apply,
      smul_eq_mul, mul_one] at this
  · intro hc
    refine ⟨le_trans (norm_nonneg f) hc, ?_⟩
    rw [ContinuousMap.le_def]; intro x
    rw [ContinuousMap.abs_apply,
      ContinuousMap.smul_apply,
      ContinuousMap.const_apply, smul_eq_mul, mul_one]
    calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f x
      _ ≤ c := hc

private theorem norm_eq_gaugeNorm_const (f : C(K, ℝ)) :
    ‖f‖ = OrderIdeal.gaugeNorm
      (ContinuousMap.const K (1 : ℝ)) f := by
  unfold OrderIdeal.gaugeNorm
  rw [gauge_set_eq]; exact csInf_Ici.symm

/-- `C(K, ℝ)` is an AM-space with unit `𝟙 = 1`. The sup norm agrees with the
gauge norm with respect to the constant function `1`. -/
noncomputable instance instAMSpaceWithUnitCofK :
    AMSpaceWithUnit C(K, ℝ) where
  unit := ContinuousMap.const K 1
  unit_pos := IsStrongUnit.pos
  norm_eq_gaugeNorm := norm_eq_gaugeNorm_const

/-! ### Riesz representation: the dual is a space of measures

For a compact Hausdorff space `K` equipped with its Borel σ-algebra, the
**Riesz–Markov–Kakutani representation theorem** identifies the norm dual of
`C(K, ℝ)` with the Banach lattice `M(K)` of *regular* signed Borel measures
on `K`. The Banach lattice structure on `M(K)` — as the closed sublattice of
`SignedMeasure K` cut out by regularity — is established in
`BanLat.Examples.MofK`; here we state the identification itself.

The map sends a measure `μ ∈ M(K)` to the continuous linear functional
`f ↦ ∫ x, f x ∂μ`, defined via the Jordan decomposition of `μ`. The map is
real-linear, isometric (`‖μ‖ = |μ|(K)`), and preserves the lattice operations
`⊔` and `⊓`, so it is a Banach lattice isomorphism.
-/

open MeasureTheory TopologicalSpace
open scoped CompactlySupported

section Riesz

variable [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- Integration of a continuous function on a compact Hausdorff space against
a finite signed Borel measure, defined via the Jordan decomposition of the
measure. -/
noncomputable def signedMeasureIntegral (μ : SignedMeasure K) (f : C(K, ℝ)) : ℝ :=
  ∫ x, f x ∂μ.toJordanDecomposition.posPart -
    ∫ x, f x ∂μ.toJordanDecomposition.negPart

omit [Nonempty K] [T2Space K] in
/-- A continuous function on a compact space is integrable against any finite
measure. -/
private theorem continuousMap_integrable (f : C(K, ℝ)) (ν : Measure K)
    [IsFiniteMeasure ν] : Integrable (fun x => f x) ν :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The underlying linear map of `signedMeasureFunctional`. -/
private noncomputable def signedMeasureLinearMap (μ : SignedMeasure K) :
    C(K, ℝ) →ₗ[ℝ] ℝ where
  toFun f := signedMeasureIntegral μ f
  map_add' f g := by
    unfold signedMeasureIntegral
    have h₁ : ∫ x, (f + g) x ∂μ.toJordanDecomposition.posPart =
        ∫ x, f x ∂μ.toJordanDecomposition.posPart +
          ∫ x, g x ∂μ.toJordanDecomposition.posPart := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (continuousMap_integrable f _) (continuousMap_integrable g _)
    have h₂ : ∫ x, (f + g) x ∂μ.toJordanDecomposition.negPart =
        ∫ x, f x ∂μ.toJordanDecomposition.negPart +
          ∫ x, g x ∂μ.toJordanDecomposition.negPart := by
      simp only [ContinuousMap.add_apply]
      exact integral_add (continuousMap_integrable f _) (continuousMap_integrable g _)
    rw [h₁, h₂]; ring
  map_smul' c f := by
    unfold signedMeasureIntegral
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      integral_const_mul]
    ring

omit [Nonempty K] [T2Space K] in
private theorem signedMeasureLinearMap_apply (μ : SignedMeasure K) (f : C(K, ℝ)) :
    signedMeasureLinearMap μ f = signedMeasureIntegral μ f := rfl

omit [Nonempty K] [T2Space K] in
/-- The bound `|⟨μ, f⟩| ≤ ‖μ‖ · ‖f‖∞`, the standard estimate from
`|∫ f dν| ≤ ν(K) · ‖f‖∞` applied to each Jordan part. -/
private theorem signedMeasureLinearMap_norm_bound (μ : SignedMeasure K) (f : C(K, ℝ)) :
    ‖signedMeasureLinearMap μ f‖ ≤ ‖μ‖ * ‖f‖ := by
  rw [signedMeasureLinearMap_apply]
  unfold signedMeasureIntegral
  have hbound : ∀ x, ‖f x‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f
  have h₁ : ‖∫ x, f x ∂μ.toJordanDecomposition.posPart‖ ≤
      ‖f‖ * (μ.toJordanDecomposition.posPart Set.univ).toReal :=
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)).trans_eq
      (by rw [Measure.real])
  have h₂ : ‖∫ x, f x ∂μ.toJordanDecomposition.negPart‖ ≤
      ‖f‖ * (μ.toJordanDecomposition.negPart Set.univ).toReal :=
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)).trans_eq
      (by rw [Measure.real])
  have hnorm : ‖μ‖ = (μ.toJordanDecomposition.posPart Set.univ).toReal +
      (μ.toJordanDecomposition.negPart Set.univ).toReal := by
    rw [SignedMeasure.norm_def, SignedMeasure.totalVariation, Measure.add_apply,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  calc ‖_ - _‖
      ≤ ‖∫ x, f x ∂μ.toJordanDecomposition.posPart‖ +
          ‖∫ x, f x ∂μ.toJordanDecomposition.negPart‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * (μ.toJordanDecomposition.posPart Set.univ).toReal +
          ‖f‖ * (μ.toJordanDecomposition.negPart Set.univ).toReal :=
        add_le_add h₁ h₂
    _ = ‖μ‖ * ‖f‖ := by rw [hnorm]; ring

/-- The bounded linear functional on `C(K, ℝ)` associated to a finite signed
Borel measure `μ` by integration. The boundedness constant is the total
variation `|μ|(K)`. The proof packages `signedMeasureIntegral μ` as a
continuous linear map: linearity follows from linearity of the Bochner
integral on each Jordan part, and the bound `|⟨μ, f⟩| ≤ |μ|(K) · ‖f‖∞` from
the standard estimate `|∫ f dν| ≤ ν(K) · ‖f‖∞` applied to each Jordan part. -/
noncomputable def signedMeasureFunctional (μ : SignedMeasure K) :
    NormDualSpace C(K, ℝ) :=
  (signedMeasureLinearMap μ).mkContinuous ‖μ‖ (signedMeasureLinearMap_norm_bound μ)

omit [Nonempty K] [T2Space K] in
/-- The functional associated to a signed measure agrees with
`signedMeasureIntegral`. -/
@[simp]
theorem signedMeasureFunctional_apply (μ : SignedMeasure K) (f : C(K, ℝ)) :
    signedMeasureFunctional μ f = signedMeasureIntegral μ f := rfl

omit [TopologicalSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] [T2Space K]
  in
/-- Each signed measure is the difference of its two Jordan parts viewed as
signed measures. -/
private theorem eq_jordan_diff (μ : SignedMeasure K) :
    μ = μ.toJordanDecomposition.posPart.toSignedMeasure
      - μ.toJordanDecomposition.negPart.toSignedMeasure :=
  (SignedMeasure.toSignedMeasure_toJordanDecomposition μ).symm

omit [Nonempty K] [T2Space K] in
/-- If a signed measure `μ` decomposes as `α.toSignedMeasure - β.toSignedMeasure` for
finite Borel measures `α, β` (not necessarily the Jordan decomposition), then
`signedMeasureIntegral μ f = ∫ f dα - ∫ f dβ`. The Jordan parts and `(α, β)` may
differ, but the rearrangement `μ⁺ + β = α + μ⁻` together with additivity of the
integral over measures forces the integrals to coincide. -/
private theorem signedMeasureIntegral_eq_sub_of_eq
    {μ : SignedMeasure K} {α β : Measure K}
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (h : μ = α.toSignedMeasure - β.toSignedMeasure) (f : C(K, ℝ)) :
    signedMeasureIntegral μ f = ∫ x, f x ∂α - ∫ x, f x ∂β := by
  have hjordan :
      μ.toJordanDecomposition.posPart.toSignedMeasure -
        μ.toJordanDecomposition.negPart.toSignedMeasure
      = α.toSignedMeasure - β.toSignedMeasure := by
    rw [show μ.toJordanDecomposition.posPart.toSignedMeasure -
        μ.toJordanDecomposition.negPart.toSignedMeasure
        = μ.toJordanDecomposition.toSignedMeasure from rfl,
      SignedMeasure.toSignedMeasure_toJordanDecomposition, h]
  have hadd : (μ.toJordanDecomposition.posPart + β).toSignedMeasure
      = (α + μ.toJordanDecomposition.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact sub_eq_sub_iff_add_eq_add.mp hjordan
  have hmeas : μ.toJordanDecomposition.posPart + β
      = α + μ.toJordanDecomposition.negPart :=
    Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp hadd
  have hint : ∫ x, f x ∂(μ.toJordanDecomposition.posPart + β)
      = ∫ x, f x ∂(α + μ.toJordanDecomposition.negPart) := by
    rw [hmeas]
  rw [integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _),
    integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _)] at hint
  unfold signedMeasureIntegral
  linarith

/-! #### From a continuous functional back to a signed measure

For each `φ : C(K, ℝ) →L[ℝ] ℝ`, decomposing `φ` into its positive and negative
parts in the order dual (`BanLat/Dual.lean`) yields two positive functionals.
Each positive functional is represented by a finite Borel measure via Mathlib's
`MeasureTheory.RealRMK.rieszMeasure`, and the difference of these two measures
is a signed measure. -/

/-- A non-negative continuous linear functional on `C(K, ℝ)`, viewed as a
positive linear map on the space `K →C_c ℝ` of compactly supported continuous
functions. Since `K` is compact, the two function spaces coincide. -/
private noncomputable def toCcPositive (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ) :
    (K →C_c ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => φ f.toContinuousMap
      map_add' := fun f g => by
        change φ (f + g).toContinuousMap = φ f.toContinuousMap + φ g.toContinuousMap
        rw [show (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap from rfl,
          map_add]
      map_smul' := fun c f => by
        change φ (c • f).toContinuousMap = c • φ f.toContinuousMap
        rw [show (c • f).toContinuousMap = c • f.toContinuousMap from rfl, map_smul] }
    (fun f hf => by
      change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace φ at hφ
      exact hφ f.toContinuousMap (by intro x; exact hf x))

omit [Nonempty K] [MeasurableSpace K] [BorelSpace K] [T2Space K] in
private theorem toCcPositive_apply (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ)
    (f : K →C_c ℝ) : toCcPositive φ hφ f = φ f.toContinuousMap := rfl

/-- The finite regular Borel measure on `K` representing a non-negative continuous
linear functional on `C(K, ℝ)`. -/
noncomputable def rieszMeasureOfNonneg (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ) :
    Measure K :=
  RealRMK.rieszMeasure (toCcPositive φ hφ)

omit [Nonempty K] in
instance rieszMeasureOfNonneg_isFinite (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ) :
    IsFiniteMeasure (rieszMeasureOfNonneg φ hφ) := by
  unfold rieszMeasureOfNonneg; infer_instance

omit [Nonempty K] in
instance rieszMeasureOfNonneg_regular (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ) :
    (rieszMeasureOfNonneg φ hφ).Regular := by
  unfold rieszMeasureOfNonneg; infer_instance

omit [Nonempty K] in
/-- Integration of a continuous function against the Riesz measure of a
non-negative functional recovers the functional. -/
theorem integral_rieszMeasureOfNonneg (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ)
    (f : C(K, ℝ)) : ∫ x, f x ∂(rieszMeasureOfNonneg φ hφ) = φ f := by
  have h := RealRMK.integral_rieszMeasure (toCcPositive φ hφ)
    (CompactlySupportedContinuousMap.continuousMapEquiv (β := ℝ) f)
  simpa [rieszMeasureOfNonneg, toCcPositive_apply,
    CompactlySupportedContinuousMap.continuousMapEquiv] using h

/-- The signed Borel measure associated to a continuous linear functional on
`C(K, ℝ)` by the Riesz–Markov–Kakutani representation theorem. -/
noncomputable def rieszSignedMeasure (φ : NormDualSpace C(K, ℝ)) :
    SignedMeasure K :=
  (rieszMeasureOfNonneg φ⁺ (posPart_nonneg _)).toSignedMeasure -
    (rieszMeasureOfNonneg φ⁻ (negPart_nonneg _)).toSignedMeasure

omit [Nonempty K] in
/-- Defining property of `rieszSignedMeasure`: integration recovers the
functional. Argument: by construction `rieszSignedMeasure φ` is the difference
of the two positive measures representing `φ⁺` and `φ⁻`, so integration
against it returns `φ⁺ f - φ⁻ f = φ f`. -/
theorem rieszSignedMeasure_integral (φ : NormDualSpace C(K, ℝ)) (f : C(K, ℝ)) :
    signedMeasureIntegral (rieszSignedMeasure φ) f = φ f := by
  rw [signedMeasureIntegral_eq_sub_of_eq (rfl : rieszSignedMeasure φ = _) f,
    integral_rieszMeasureOfNonneg, integral_rieszMeasureOfNonneg]
  exact congrArg (fun ψ : NormDualSpace C(K, ℝ) => ψ f) (posPart_sub_negPart φ)

/-! #### The two constructions are mutually inverse -/

omit [Nonempty K] in
theorem signedMeasureFunctional_rieszSignedMeasure
    (φ : NormDualSpace C(K, ℝ)) :
    signedMeasureFunctional (rieszSignedMeasure φ) = φ := by
  ext f
  rw [signedMeasureFunctional_apply, rieszSignedMeasure_integral]

omit [Nonempty K] in
/-- Injectivity of `signedMeasureFunctional` on regular signed measures:
integration against continuous functions determines a regular signed Borel
measure uniquely. This is the uniqueness half of Riesz–Markov–Kakutani, via
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`. -/
theorem signedMeasureFunctional_injective_of_regular
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular)
    (hfun : signedMeasureFunctional μ = signedMeasureFunctional ν) : μ = ν := by
  haveI := hμ.posPart_regular
  haveI := hμ.negPart_regular
  haveI := hν.posPart_regular
  haveI := hν.negPart_regular
  have hint : ∀ f : C(K, ℝ),
      ∫ x, f x ∂(μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) =
      ∫ x, f x ∂(ν.toJordanDecomposition.posPart + μ.toJordanDecomposition.negPart) := by
    intro f
    have := congrArg (fun ψ : NormDualSpace C(K, ℝ) => ψ f) hfun
    simp only [signedMeasureFunctional_apply, signedMeasureIntegral] at this
    rw [integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _),
      integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _)]
    linarith
  have hmeas : μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart =
      ν.toJordanDecomposition.posPart + μ.toJordanDecomposition.negPart := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    exact hint f.toContinuousMap
  have hsigned : μ.toJordanDecomposition.toSignedMeasure =
      ν.toJordanDecomposition.toSignedMeasure := by
    have heq : (μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart) =
        (ν.toJordanDecomposition.posPart + μ.toJordanDecomposition.negPart) := hmeas
    have heqs := Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr heq
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add] at heqs
    have h1 : μ.toJordanDecomposition.toSignedMeasure =
        μ.toJordanDecomposition.posPart.toSignedMeasure -
          μ.toJordanDecomposition.negPart.toSignedMeasure := rfl
    have h2 : ν.toJordanDecomposition.toSignedMeasure =
        ν.toJordanDecomposition.posPart.toSignedMeasure -
          ν.toJordanDecomposition.negPart.toSignedMeasure := rfl
    rw [h1, h2, sub_eq_sub_iff_add_eq_add]
    exact heqs
  rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ,
    ← SignedMeasure.toSignedMeasure_toJordanDecomposition ν, hsigned]

omit [TopologicalSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] [T2Space K] in
/-- The Jordan decomposition of `α.toSignedMeasure` for a finite positive
measure `α` is `(α, 0)`. -/
private theorem jordan_of_toSignedMeasure (α : Measure K) [IsFiniteMeasure α] :
    α.toSignedMeasure.toJordanDecomposition =
      { posPart := α
        negPart := 0
        mutuallySingular := Measure.MutuallySingular.zero_right } := by
  apply SignedMeasure.toJordanDecomposition_eq
  change α.toSignedMeasure =
    α.toSignedMeasure - (0 : Measure K).toSignedMeasure
  rw [Measure.toSignedMeasure_zero, sub_zero]

omit [CompactSpace K] [Nonempty K] [BorelSpace K] [T2Space K] in
/-- The signed measure associated by `toSignedMeasure` to a finite regular
Borel measure is itself regular. -/
theorem isRegular_toSignedMeasure {α : Measure K}
    [IsFiniteMeasure α] (hα : α.Regular) :
    α.toSignedMeasure.IsRegular := by
  have hja := jordan_of_toSignedMeasure α
  show α.toSignedMeasure.totalVariation.Regular
  rw [SignedMeasure.totalVariation, hja]
  show (α + 0).Regular
  rw [add_zero]; exact hα

omit [Nonempty K] in
/-- The Riesz signed measure associated to any continuous linear functional on
`C(K, ℝ)` is regular. Its Jordan parts are (sub-)Riesz measures of the lattice
parts `φ⁺`/`φ⁻`, each of which is automatically a regular Borel measure by
`RealRMK.regular_rieszMeasure`. -/
theorem rieszSignedMeasure_isRegular (φ : NormDualSpace C(K, ℝ)) :
    (rieszSignedMeasure φ).IsRegular :=
  SignedMeasure.IsRegular.sub
    (isRegular_toSignedMeasure (α := rieszMeasureOfNonneg φ⁺ (posPart_nonneg _))
      inferInstance)
    (isRegular_toSignedMeasure (α := rieszMeasureOfNonneg φ⁻ (negPart_nonneg _))
      inferInstance)

omit [Nonempty K] in
/-- The modulus of a regular signed measure is regular. -/
theorem MeasureTheory.SignedMeasure.IsRegular.abs {s : SignedMeasure K} (hs : s.IsRegular) :
    |s|.IsRegular := by
  haveI := hs.posPart_regular
  haveI := hs.negPart_regular
  set μ := s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart
  let j : JordanDecomposition K :=
    ⟨μ, 0, Measure.MutuallySingular.zero_right⟩
  have habs : |s| = j.toSignedMeasure := by
    rw [SignedMeasure.abs_eq_posPart_add_negPart]
    show s.toJordanDecomposition.posPart.toSignedMeasure +
        s.toJordanDecomposition.negPart.toSignedMeasure = j.toSignedMeasure
    show _ = j.posPart.toSignedMeasure - j.negPart.toSignedMeasure
    show _ = μ.toSignedMeasure - (0 : Measure K).toSignedMeasure
    rw [Measure.toSignedMeasure_zero, sub_zero, ← Measure.toSignedMeasure_add]
  have habs_jd : |s|.toJordanDecomposition = j :=
    SignedMeasure.toJordanDecomposition_eq habs
  show |s|.totalVariation.Regular
  rw [SignedMeasure.totalVariation, habs_jd]
  show (μ + 0).Regular
  rw [add_zero]; infer_instance

omit [Nonempty K] in
theorem rieszSignedMeasure_signedMeasureFunctional
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    rieszSignedMeasure (signedMeasureFunctional μ) = μ :=
  signedMeasureFunctional_injective_of_regular
    (rieszSignedMeasure_isRegular _) hμ
    (signedMeasureFunctional_rieszSignedMeasure (signedMeasureFunctional μ))

/-! #### Linearity, isometry, and lattice preservation -/

omit [Nonempty K] [T2Space K] in
theorem signedMeasureFunctional_add (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ + ν) =
      signedMeasureFunctional μ + signedMeasureFunctional ν := by
  ext f
  simp only [signedMeasureFunctional_apply, ContinuousLinearMap.add_apply]
  have hsum : (μ + ν : SignedMeasure K) =
      (μ.toJordanDecomposition.posPart + ν.toJordanDecomposition.posPart).toSignedMeasure
      - (μ.toJordanDecomposition.negPart + ν.toJordanDecomposition.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    conv_lhs => rw [eq_jordan_diff μ, eq_jordan_diff ν]
    abel
  rw [signedMeasureIntegral_eq_sub_of_eq hsum f,
    integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _),
    integral_add_measure (continuousMap_integrable f _) (continuousMap_integrable f _)]
  change _ = signedMeasureIntegral _ _ + signedMeasureIntegral _ _
  unfold signedMeasureIntegral
  ring

omit [CompactSpace K] [Nonempty K] [BorelSpace K] [T2Space K] in
/-- The integral against `c • μ` equals `c` times the integral against `μ`. The
case-split on the sign of `c` is needed because the Jordan decomposition swaps
positive and negative parts under negation. -/
private theorem signedMeasureIntegral_smul (c : ℝ) (μ : SignedMeasure K) (f : C(K, ℝ)) :
    signedMeasureIntegral (c • μ) f = c * signedMeasureIntegral μ f := by
  unfold signedMeasureIntegral
  rw [SignedMeasure.toJordanDecomposition_smul_real]
  rcases lt_or_ge c 0 with hc | hc
  · rw [JordanDecomposition.real_smul_posPart_neg _ _ hc,
      JordanDecomposition.real_smul_negPart_neg _ _ hc,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      NNReal.smul_def, NNReal.smul_def,
      Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ -c), smul_eq_mul, smul_eq_mul]
    ring
  · rw [JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
      JordanDecomposition.real_smul_negPart_nonneg _ _ hc,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      NNReal.smul_def, NNReal.smul_def, Real.coe_toNNReal _ hc, smul_eq_mul, smul_eq_mul]
    ring

omit [Nonempty K] [T2Space K] in
theorem signedMeasureFunctional_smul (c : ℝ) (μ : SignedMeasure K) :
    signedMeasureFunctional (c • μ) = c • signedMeasureFunctional μ := by
  ext f
  simp only [signedMeasureFunctional_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact signedMeasureIntegral_smul c μ f

omit [Nonempty K] [T2Space K] in
theorem signedMeasureFunctional_neg (μ : SignedMeasure K) :
    signedMeasureFunctional (-μ) = -signedMeasureFunctional μ := by
  rw [show (-μ : SignedMeasure K) = (-1 : ℝ) • μ from (neg_one_smul ℝ μ).symm,
    signedMeasureFunctional_smul, neg_one_smul]

omit [Nonempty K] [T2Space K] in
private theorem signedMeasureFunctional_zero :
    signedMeasureFunctional (0 : SignedMeasure K) = 0 := by
  ext f
  rw [signedMeasureFunctional_apply, signedMeasureIntegral,
    SignedMeasure.toJordanDecomposition_zero, JordanDecomposition.zero_posPart,
    JordanDecomposition.zero_negPart, integral_zero_measure, sub_zero]
  rfl

omit [Nonempty K] [T2Space K] in
theorem signedMeasureFunctional_sub (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ - ν) =
      signedMeasureFunctional μ - signedMeasureFunctional ν := by
  rw [sub_eq_add_neg, signedMeasureFunctional_add, signedMeasureFunctional_neg,
    sub_eq_add_neg]

/-! #### Positivity preservation

The forward direction `0 ≤ μ → 0 ≤ signedMeasureFunctional μ` is straightforward
from the Jordan decomposition. The backward direction follows from the bijection
together with the analogous statement for `rieszSignedMeasure`. -/

omit [TopologicalSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] [T2Space K]
    in
/-- For a non-negative signed measure `μ`, the Jordan negative part vanishes as
a measure (not just as a signed measure), allowing us to drop the second integral
in `signedMeasureIntegral`. -/
private theorem jordan_negPart_eq_zero
    {μ : SignedMeasure K} (hμ : 0 ≤ μ) :
    μ.toJordanDecomposition.negPart = 0 := by
  have h := SignedMeasure.nonneg_iff_negPart_eq_zero.mp hμ
  have h1 : (μ.toJordanDecomposition.negPart).toSignedMeasure
      = (0 : Measure K).toSignedMeasure := by
    rw [Measure.toSignedMeasure_zero]; exact h
  exact Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp h1

omit [Nonempty K] [T2Space K] in
/-- The forward direction of positivity preservation: integration against a
non-negative signed measure yields a non-negative functional. -/
theorem signedMeasureFunctional_nonneg
    {μ : SignedMeasure K} (hμ : 0 ≤ μ) :
    0 ≤ signedMeasureFunctional μ := by
  have hzero : μ.toJordanDecomposition.negPart = 0 := jordan_negPart_eq_zero hμ
  change NormDualSpace.toOrderDualSpace (0 : NormDualSpace _) ≤
    NormDualSpace.toOrderDualSpace (signedMeasureFunctional μ)
  intro f hf
  change (0 : ℝ) ≤ signedMeasureFunctional μ f
  rw [signedMeasureFunctional_apply, signedMeasureIntegral, hzero,
    integral_zero_measure, sub_zero]
  exact integral_nonneg (fun x => ContinuousMap.le_def.mp hf x)

omit [Nonempty K] in
/-- The Jordan decomposition of `(rieszMeasureOfNonneg φ hφ).toSignedMeasure` is
`(rieszMeasureOfNonneg φ hφ, 0)`, since the positive part of a positive signed
measure equals the underlying measure and the negative part vanishes. -/
private theorem jordan_of_rieszMeasure_toSignedMeasure
    (φ : NormDualSpace C(K, ℝ)) (hφ : 0 ≤ φ) :
    ((rieszMeasureOfNonneg φ hφ).toSignedMeasure).toJordanDecomposition =
      { posPart := rieszMeasureOfNonneg φ hφ
        negPart := 0
        mutuallySingular := Measure.MutuallySingular.zero_right } := by
  apply SignedMeasure.toJordanDecomposition_eq
  change (rieszMeasureOfNonneg φ hφ).toSignedMeasure =
    (rieszMeasureOfNonneg φ hφ).toSignedMeasure - (0 : Measure K).toSignedMeasure
  rw [Measure.toSignedMeasure_zero, sub_zero]

omit [Nonempty K] in
/-- The forward direction of positivity preservation for the inverse map: a
non-negative functional `φ` produces a non-negative signed measure. The proof
exhibits a non-negative signed measure `ν` whose `signedMeasureFunctional` is
`φ`, and concludes by injectivity of `signedMeasureFunctional`. -/
theorem rieszSignedMeasure_nonneg
    {φ : NormDualSpace C(K, ℝ)} (hφ : 0 ≤ φ) :
    0 ≤ rieszSignedMeasure φ := by
  set ν : SignedMeasure K := (rieszMeasureOfNonneg φ hφ).toSignedMeasure with hν_def
  have hν_nonneg : 0 ≤ ν := Measure.zero_le_toSignedMeasure _
  have hjd := jordan_of_rieszMeasure_toSignedMeasure φ hφ
  have hfunc : signedMeasureFunctional ν = φ := by
    ext g
    rw [signedMeasureFunctional_apply, signedMeasureIntegral]
    change ∫ x, g x ∂((ν).toJordanDecomposition.posPart) -
        ∫ x, g x ∂((ν).toJordanDecomposition.negPart) = φ g
    rw [show ν.toJordanDecomposition.posPart = rieszMeasureOfNonneg φ hφ from
        congrArg JordanDecomposition.posPart hjd,
      show ν.toJordanDecomposition.negPart = 0 from
        congrArg JordanDecomposition.negPart hjd,
      integral_zero_measure, sub_zero]
    exact integral_rieszMeasureOfNonneg φ hφ g
  have hν_reg : ν.IsRegular := by
    show ν.totalVariation.Regular
    rw [SignedMeasure.totalVariation, hjd]
    show (rieszMeasureOfNonneg φ hφ + 0).Regular
    rw [add_zero]; infer_instance
  have heq : rieszSignedMeasure φ = ν :=
    signedMeasureFunctional_injective_of_regular
      (rieszSignedMeasure_isRegular _) hν_reg
      (by rw [signedMeasureFunctional_rieszSignedMeasure, hfunc])
  rw [heq]
  exact hν_nonneg

omit [Nonempty K] in
/-- Positivity preservation for `signedMeasureFunctional`: for a regular signed
measure, non-negativity of the measure is equivalent to non-negativity of the
associated functional. -/
theorem signedMeasureFunctional_nonneg_iff
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    0 ≤ signedMeasureFunctional μ ↔ 0 ≤ μ := by
  refine ⟨fun h => ?_, signedMeasureFunctional_nonneg⟩
  have := rieszSignedMeasure_nonneg h
  rwa [rieszSignedMeasure_signedMeasureFunctional hμ] at this

omit [Nonempty K] in
/-- Order preservation: for regular signed measures, `signedMeasureFunctional`
is an order embedding. -/
theorem signedMeasureFunctional_le_iff
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular) :
    signedMeasureFunctional μ ≤ signedMeasureFunctional ν ↔ μ ≤ ν := by
  rw [← sub_nonneg (a := signedMeasureFunctional ν), ← signedMeasureFunctional_sub,
    signedMeasureFunctional_nonneg_iff (SignedMeasure.IsRegular.sub hν hμ), sub_nonneg]

omit [Nonempty K] in
/-- The positive part of a regular signed measure is regular: decompose as
`s⁺ = (1/2) • (s + |s|)` and combine the add, abs, and smul closure lemmas. -/
theorem isRegular_posPart {s : SignedMeasure K} (hs : s.IsRegular) :
    s⁺.IsRegular := by
  have key : s + |s| = (2 : ℕ) • s⁺ := add_abs_eq_two_nsmul_posPart s
  have h2 : s⁺ = (2 : ℝ)⁻¹ • (s + |s|) := by
    rw [key, ← Nat.cast_smul_eq_nsmul ℝ 2]
    simp only [Nat.cast_ofNat, smul_smul]
    rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  rw [h2]
  exact SignedMeasure.IsRegular.smul _
    (SignedMeasure.IsRegular.add hs (SignedMeasure.IsRegular.abs hs))

omit [Nonempty K] in
theorem isRegular_sup {μ ν : SignedMeasure K}
    (hμ : μ.IsRegular) (hν : ν.IsRegular) : (μ ⊔ ν).IsRegular := by
  rw [sup_eq_add_posPart]
  exact SignedMeasure.IsRegular.add hμ
    (isRegular_posPart (SignedMeasure.IsRegular.sub hν hμ))

omit [Nonempty K] in
theorem isRegular_inf {μ ν : SignedMeasure K}
    (hμ : μ.IsRegular) (hν : ν.IsRegular) : (μ ⊓ ν).IsRegular := by
  rw [inf_eq_sub_posPart]
  exact SignedMeasure.IsRegular.sub hμ
    (isRegular_posPart (SignedMeasure.IsRegular.sub hμ hν))

omit [Nonempty K] in
/-- Lattice preservation for the supremum on the regular sublattice. -/
theorem signedMeasureFunctional_sup
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular) :
    signedMeasureFunctional (μ ⊔ ν) =
      signedMeasureFunctional μ ⊔ signedMeasureFunctional ν := by
  set F := signedMeasureFunctional μ ⊔ signedMeasureFunctional ν with hF
  set σ := rieszSignedMeasure F with hσ
  have hσ_reg : σ.IsRegular := rieszSignedMeasure_isRegular F
  have hSσ : signedMeasureFunctional σ = F :=
    signedMeasureFunctional_rieszSignedMeasure F
  apply le_antisymm
  · have h1 : μ ≤ σ := (signedMeasureFunctional_le_iff hμ hσ_reg).mp
      (by rw [hSσ]; exact le_sup_left)
    have h2 : ν ≤ σ := (signedMeasureFunctional_le_iff hν hσ_reg).mp
      (by rw [hSσ]; exact le_sup_right)
    have h4 := (signedMeasureFunctional_le_iff (isRegular_sup hμ hν) hσ_reg).mpr
      (sup_le h1 h2)
    rw [hSσ] at h4; exact h4
  · refine sup_le ?_ ?_
    · exact (signedMeasureFunctional_le_iff hμ (isRegular_sup hμ hν)).mpr le_sup_left
    · exact (signedMeasureFunctional_le_iff hν (isRegular_sup hμ hν)).mpr le_sup_right

omit [Nonempty K] in
/-- Lattice preservation for the infimum on the regular sublattice. -/
theorem signedMeasureFunctional_inf
    {μ ν : SignedMeasure K} (hμ : μ.IsRegular) (hν : ν.IsRegular) :
    signedMeasureFunctional (μ ⊓ ν) =
      signedMeasureFunctional μ ⊓ signedMeasureFunctional ν := by
  have hid : μ ⊓ ν = μ + ν - (μ ⊔ ν) := eq_sub_of_add_eq (inf_add_sup μ ν)
  rw [hid, signedMeasureFunctional_sub, signedMeasureFunctional_add,
    signedMeasureFunctional_sup hμ hν]
  exact (eq_sub_of_add_eq (inf_add_sup (signedMeasureFunctional μ)
    (signedMeasureFunctional ν))).symm

omit [Nonempty K] in
/-- Modulus preservation: the absolute value of the functional equals the
functional of the absolute value. Reduces via `a⁺ + a⁻ = |a|` and supremum
preservation. -/
private theorem signedMeasureFunctional_abs
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    |signedMeasureFunctional μ| = signedMeasureFunctional |μ| := by
  have hpos : (signedMeasureFunctional μ)⁺ = signedMeasureFunctional μ⁺ := by
    rw [posPart_def, posPart_def,
      signedMeasureFunctional_sup hμ (SignedMeasure.IsRegular.zero),
      signedMeasureFunctional_zero]
  have hneg : (signedMeasureFunctional μ)⁻ = signedMeasureFunctional μ⁻ := by
    rw [negPart_def, negPart_def,
      signedMeasureFunctional_sup (SignedMeasure.IsRegular.neg hμ)
        (SignedMeasure.IsRegular.zero),
      signedMeasureFunctional_neg, signedMeasureFunctional_zero]
  rw [← posPart_add_negPart (signedMeasureFunctional μ), hpos, hneg,
    ← signedMeasureFunctional_add, posPart_add_negPart]

omit [T2Space K] in
/-- For a non-negative signed measure, the operator norm of the associated
functional equals the total variation. The lower bound is witnessed by the
constant function `1`: `signedMeasureFunctional μ 1 = μ(K) = ‖μ‖`. -/
theorem norm_signedMeasureFunctional_of_nonneg
    {μ : SignedMeasure K} (hμ : 0 ≤ μ) :
    ‖signedMeasureFunctional μ‖ = ‖μ‖ := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f =>
      signedMeasureLinearMap_norm_bound μ f)
    ?_
  have hzero : μ.toJordanDecomposition.negPart = 0 := jordan_negPart_eq_zero hμ
  have h1 : (1 : C(K, ℝ)) = ContinuousMap.const K 1 := rfl
  have hone_norm : ‖(1 : C(K, ℝ))‖ = 1 := norm_one
  have hjd : μ.toJordanDecomposition =
      ⟨μ.toJordanDecomposition.posPart, 0,
        Measure.MutuallySingular.zero_right⟩ := by
    apply JordanDecomposition.ext <;> simp [hzero]
  have heq : (μ.toJordanDecomposition.posPart.toSignedMeasure : SignedMeasure K) = μ := by
    rw [show μ.toJordanDecomposition.posPart.toSignedMeasure
        = μ.toJordanDecomposition.toSignedMeasure from by
        conv_rhs => rw [hjd]
        change _ = (_ : Measure K).toSignedMeasure - (0 : Measure K).toSignedMeasure
        rw [Measure.toSignedMeasure_zero, sub_zero],
      SignedMeasure.toSignedMeasure_toJordanDecomposition]
  have hval : signedMeasureFunctional μ 1 = ‖μ‖ := by
    rw [signedMeasureFunctional_apply, signedMeasureIntegral, hzero,
      integral_zero_measure, sub_zero, h1]
    simp only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one]
    rw [SignedMeasure.norm_of_nonneg hμ]
    conv_rhs => rw [← heq]
    rw [Measure.toSignedMeasure_apply, if_pos MeasurableSet.univ]
  have hbound : ‖μ‖ = ‖signedMeasureFunctional μ 1‖ := by
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hbound]
  calc ‖signedMeasureFunctional μ 1‖
      ≤ ‖signedMeasureFunctional μ‖ * ‖(1 : C(K, ℝ))‖ :=
        (signedMeasureFunctional μ).le_opNorm 1
    _ = ‖signedMeasureFunctional μ‖ := by rw [hone_norm, mul_one]

/-- The Riesz functional has operator norm equal to the total variation of the
underlying measure. Argument: pass to absolute values via `norm_abs_eq_norm`,
use modulus preservation to swap `|signedMeasureFunctional μ|` for
`signedMeasureFunctional |μ|`, then apply
`norm_signedMeasureFunctional_of_nonneg` to the non-negative `|μ|`. -/
theorem norm_signedMeasureFunctional
    {μ : SignedMeasure K} (hμ : μ.IsRegular) :
    ‖signedMeasureFunctional μ‖ = ‖μ‖ := by
  rw [← norm_abs_eq_norm (signedMeasureFunctional μ),
    signedMeasureFunctional_abs hμ,
    norm_signedMeasureFunctional_of_nonneg (abs_nonneg μ), norm_abs_eq_norm]

end Riesz
