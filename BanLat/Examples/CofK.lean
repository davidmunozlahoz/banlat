import BanLat.AMSpace
import BanLat.Dual
import BanLat.Examples.MofK
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

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
  unit_pos := by
    apply lt_of_le_of_ne
    · intro x; simp
    · intro h
      have := congr_fun
        (congr_arg ContinuousMap.toFun h)
        (Classical.arbitrary K)
      simp at this
  norm_eq_gaugeNorm := norm_eq_gaugeNorm_const

/-! ### Riesz representation: the dual is a space of measures

For a compact Hausdorff space `K` equipped with its Borel σ-algebra, the
**Riesz–Markov–Kakutani representation theorem** identifies the norm dual of
`C(K, ℝ)` with the space `M(K) = SignedMeasure K` of finite signed Borel
measures. The Banach lattice structure on `M(K)` is established in
`BanLat.Examples.MofK`; here we state the identification itself.

The map sends a measure `μ` to the continuous linear functional
`f ↦ ∫ x, f x ∂μ`, defined via the Jordan decomposition of `μ`. The map is
real-linear, isometric (`‖μ‖ = |μ|(K)`), and preserves the lattice operations
`⊔` and `⊓`, so it is a Banach lattice isomorphism.
-/

open MeasureTheory

section Riesz

variable [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- Integration of a continuous function on a compact Hausdorff space against
a finite signed Borel measure, defined via the Jordan decomposition of the
measure. -/
noncomputable def signedMeasureIntegral (μ : SignedMeasure K) (f : C(K, ℝ)) : ℝ :=
  ∫ x, f x ∂μ.toJordanDecomposition.posPart -
    ∫ x, f x ∂μ.toJordanDecomposition.negPart

/-- The bounded linear functional on `C(K, ℝ)` associated to a finite signed
Borel measure `μ` by integration. The boundedness constant is the total
variation `|μ|(K)`. The proof packages `signedMeasureIntegral μ` as a
continuous linear map: linearity follows from linearity of the Bochner
integral on each Jordan part, and the bound `|⟨μ, f⟩| ≤ |μ|(K) · ‖f‖∞` from
the standard estimate `|∫ f dν| ≤ ν(K) · ‖f‖∞` applied to each Jordan part. -/
noncomputable def signedMeasureFunctional (μ : SignedMeasure K) :
    NormDualSpace C(K, ℝ) :=
  sorry

/-- The functional associated to a signed measure agrees with
`signedMeasureIntegral`. -/
@[simp]
theorem signedMeasureFunctional_apply (μ : SignedMeasure K) (f : C(K, ℝ)) :
    signedMeasureFunctional μ f = signedMeasureIntegral μ f :=
  sorry

/-! #### From a continuous functional back to a signed measure

For each `φ : C(K, ℝ) →L[ℝ] ℝ`, decomposing `φ` into its positive and negative
parts in the order dual (`BanLat/Dual.lean`) yields two positive functionals.
Each positive functional is represented by a finite Borel measure via Mathlib's
`MeasureTheory.RealRMK.rieszMeasure`, and the difference of these two measures
is a signed measure. The mutual singularity needed for a genuine Jordan
decomposition is automatic from `φ⁺ ⊓ φ⁻ = 0`. -/

/-- The signed Borel measure associated to a continuous linear functional on
`C(K, ℝ)` by the Riesz–Markov–Kakutani representation theorem. -/
noncomputable def rieszSignedMeasure (φ : NormDualSpace C(K, ℝ)) :
    SignedMeasure K :=
  sorry

/-- Defining property of `rieszSignedMeasure`: integration recovers the
functional. Argument: by construction `rieszSignedMeasure φ` is the difference
of the two positive measures representing `φ⁺` and `φ⁻`, so integration
against it returns `φ⁺ f - φ⁻ f = φ f`. -/
theorem rieszSignedMeasure_integral (φ : NormDualSpace C(K, ℝ)) (f : C(K, ℝ)) :
    signedMeasureIntegral (rieszSignedMeasure φ) f = φ f :=
  sorry

/-! #### The two constructions are mutually inverse -/

private theorem rieszSignedMeasure_signedMeasureFunctional
    (μ : SignedMeasure K) :
    rieszSignedMeasure (signedMeasureFunctional μ) = μ :=
  sorry

private theorem signedMeasureFunctional_rieszSignedMeasure
    (φ : NormDualSpace C(K, ℝ)) :
    signedMeasureFunctional (rieszSignedMeasure φ) = φ :=
  sorry

/-! #### Linearity, isometry, and lattice preservation -/

private theorem signedMeasureFunctional_add (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ + ν) =
      signedMeasureFunctional μ + signedMeasureFunctional ν :=
  sorry

private theorem signedMeasureFunctional_smul (c : ℝ) (μ : SignedMeasure K) :
    signedMeasureFunctional (c • μ) = c • signedMeasureFunctional μ :=
  sorry

/-- The Riesz functional has operator norm equal to the total variation of the
underlying measure. Argument: for the upper bound, use
`|⟨μ, f⟩| ≤ |μ|(K) · ‖f‖∞`. For the lower bound, approximate the indicator of
a positive Hahn set from above by continuous functions (using regularity of the
total variation measure on a compact Hausdorff space) to make the integral get
arbitrarily close to `|μ|(K)`. -/
private theorem norm_signedMeasureFunctional (μ : SignedMeasure K) :
    ‖signedMeasureFunctional μ‖ = ‖μ‖ :=
  sorry

private theorem signedMeasureFunctional_sup (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ ⊔ ν) =
      signedMeasureFunctional μ ⊔ signedMeasureFunctional ν :=
  sorry

private theorem signedMeasureFunctional_inf (μ ν : SignedMeasure K) :
    signedMeasureFunctional (μ ⊓ ν) =
      signedMeasureFunctional μ ⊓ signedMeasureFunctional ν :=
  sorry

/-- **Riesz–Markov–Kakutani representation theorem** for `C(K, ℝ)`. For a
compact Hausdorff space `K`, integration against a finite signed Borel measure
is a Banach lattice isomorphism between `SignedMeasure K` and the norm dual of
`C(K, ℝ)`: it is a real-linear isometric equivalence that also preserves the
lattice operations `⊔` and `⊓`. -/
noncomputable def rieszEquiv :
    BanachLatEquiv (SignedMeasure K) (NormDualSpace C(K, ℝ)) :=
  sorry

@[simp]
theorem rieszEquiv_apply (μ : SignedMeasure K) (f : C(K, ℝ)) :
    rieszEquiv μ f = signedMeasureIntegral μ f :=
  sorry

/-- The Riesz isomorphism preserves positivity: a signed measure is non-negative
iff its associated functional is non-negative on `C(K, ℝ)`. This is a direct
consequence of `rieszEquiv` being a lattice isomorphism. -/
theorem rieszEquiv_nonneg_iff {μ : SignedMeasure K} :
    0 ≤ (rieszEquiv : BanachLatEquiv (SignedMeasure K) _) μ ↔ 0 ≤ μ :=
  sorry

end Riesz
