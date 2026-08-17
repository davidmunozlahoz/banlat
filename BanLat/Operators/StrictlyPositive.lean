import BanLat.Dual
import BanLat.OrderContinuous.Decomposition
import BanLat.OrderContinuous.MeyerNieberg
import BanLat.OrderContinuous.Basic
import BanLat.OrderUnit
import BanLat.Operators.Carrier
import BanLat.Operators.Positive
import BanLat.Substructures.Band.PPP

/-!
# Strictly positive operators

A linear map between vector lattices is **strictly positive** if it sends every
strictly positive element to a strictly positive element.
-/

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A linear map is *strictly positive* if it sends strictly positive elements to
strictly positive elements. -/
def StrictlyPositive (f : X →ₗ[ℝ] Y) : Prop :=
  ∀ x : X, 0 < x → 0 < f x

namespace StrictlyPositive

/-- Every strictly positive operator is positive. -/
theorem positive {f : X →ₗ[ℝ] Y} (hf : StrictlyPositive f) : Positive f := by
  intro x hx
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp
  · exact (hf x hx_pos).le

/-- The lattice norm associated to a strictly positive functional: `x ↦ φ |x|`. -/
def associatedNorm (φ : X →ₗ[ℝ] ℝ) (x : X) : ℝ :=
  φ |x|

@[simp]
theorem associatedNorm_zero (φ : X →ₗ[ℝ] ℝ) :
    associatedNorm φ (0 : X) = 0 := by
  simp [associatedNorm]

/-- The associated norm is non-negative. -/
theorem associatedNorm_nonneg {φ : X →ₗ[ℝ] ℝ} (hφ : StrictlyPositive φ) (x : X) :
    0 ≤ associatedNorm φ x :=
  hφ.positive |x| (abs_nonneg x)

/-- For a strictly positive functional, the associated norm vanishes only at zero. -/
theorem associatedNorm_eq_zero_iff {φ : X →ₗ[ℝ] ℝ} (hφ : StrictlyPositive φ)
    {x : X} :
    associatedNorm φ x = 0 ↔ x = 0 := by
  constructor
  · intro hx_norm
    by_contra hx
    have hx_abs_ne : |x| ≠ 0 := fun h => hx ((abs_eq_zero_iff_zero x).mp h)
    have hx_abs_pos : 0 < |x| :=
      lt_of_le_of_ne (abs_nonneg x) (Ne.symm hx_abs_ne)
    exact (ne_of_gt (hφ |x| hx_abs_pos)) hx_norm
  · intro hx
    subst hx
    simp [associatedNorm]

/-- The associated norm is additive on disjoint positive pieces. -/
theorem associatedNorm_add_eq_of_inf_eq_zero {φ : X →ₗ[ℝ] ℝ} (_hφ : StrictlyPositive φ)
    {x y : X} (hxy : x ⊓ y = 0) :
    associatedNorm φ (x + y) = associatedNorm φ x + associatedNorm φ y := by
  have hx : 0 ≤ x := by
    simpa [hxy] using (inf_le_left : x ⊓ y ≤ x)
  have hy : 0 ≤ y := by
    simpa [hxy] using (inf_le_right : x ⊓ y ≤ y)
  simp [associatedNorm, abs_of_nonneg hx, abs_of_nonneg hy,
    abs_of_nonneg (add_nonneg hx hy), map_add]

/-- The additive group norm induced by a strictly positive functional. -/
noncomputable def associatedAddGroupNorm (φ : X →ₗ[ℝ] ℝ)
    (hφ : StrictlyPositive φ) : AddGroupNorm X where
  toFun := associatedNorm φ
  map_zero' := associatedNorm_zero φ
  add_le' := by
    intro x y
    have hle : φ |x + y| ≤ φ (|x| + |y|) :=
      (Positive.monotone_iff.mpr hφ.positive) (abs_add_le x y)
    simpa [associatedNorm, map_add] using hle
  neg' := by
    intro x
    simp [associatedNorm]
  eq_zero_of_map_eq_zero' := by
    intro x hx
    exact (associatedNorm_eq_zero_iff hφ).mp hx

/-- The normed additive group structure induced by a strictly positive functional. -/
@[reducible]
noncomputable def associatedNormedAddCommGroup (φ : X →ₗ[ℝ] ℝ)
    (hφ : StrictlyPositive φ) : NormedAddCommGroup X := by
  exact (associatedAddGroupNorm φ hφ).toNormedAddCommGroup

/-- The norm in `associatedNormedAddCommGroup` is the associated norm `x ↦ φ |x|`. -/
theorem associatedNormedAddCommGroup_norm (φ : X →ₗ[ℝ] ℝ)
    (hφ : StrictlyPositive φ) (x : X) :
    letI : NormedAddCommGroup X := associatedNormedAddCommGroup φ hφ
    ‖x‖ = associatedNorm φ x := by
  rfl

/-- The associated norm is solid. -/
theorem associatedNorm_solid {φ : X →ₗ[ℝ] ℝ} (hφ : StrictlyPositive φ)
    {x y : X} (hxy : |x| ≤ |y|) :
    associatedNorm φ x ≤ associatedNorm φ y := by
  exact (Positive.monotone_iff.mpr hφ.positive) hxy

/-- The associated norm is homogeneous with respect to real scalar multiplication. -/
theorem associatedNorm_smul (φ : X →ₗ[ℝ] ℝ) (r : ℝ) (x : X) :
    associatedNorm φ (r • x) = ‖r‖ * associatedNorm φ x := by
  rw [associatedNorm, abs_smul', map_smul, associatedNorm, Real.norm_eq_abs, smul_eq_mul]

/-- The normed vector lattice structure induced by a strictly positive functional. -/
@[reducible]
noncomputable def associatedNormedVectorLattice (φ : X →ₗ[ℝ] ℝ)
    (hφ : StrictlyPositive φ) :
    @NormedVectorLattice X
      (associatedNormedAddCommGroup φ hφ)
      inferInstance inferInstance := by
  letI : NormedAddCommGroup X := associatedNormedAddCommGroup φ hφ
  let solidNorm : HasSolidNorm X := {
    solid := by
      intro x y hxy
      simpa [associatedNormedAddCommGroup_norm] using associatedNorm_solid hφ hxy
  }
  let normSmul : NormSMulClass ℝ X := {
    norm_smul := by
      intro r x
      simpa [associatedNormedAddCommGroup_norm] using associatedNorm_smul φ r x
  }
  exact @NormedVectorLattice.mk X
    (associatedNormedAddCommGroup φ hφ)
    inferInstance
    inferInstance
    inferInstance
    solidNorm
    normSmul

/-- The norm associated to a strictly positive functional has the AL additivity property. -/
theorem associatedNorm_add_eq_norm_add_of_inf_eq_zero (φ : X →ₗ[ℝ] ℝ)
    (hφ : StrictlyPositive φ) {x y : X} (hxy : x ⊓ y = 0) :
    letI : NormedAddCommGroup X := associatedNormedAddCommGroup φ hφ
    ‖x + y‖ = ‖x‖ + ‖y‖ := by
  simpa [associatedNormedAddCommGroup_norm] using
    associatedNorm_add_eq_of_inf_eq_zero hφ hxy

end StrictlyPositive

/-- If a vector lattice admits a strictly positive functional, then it is Archimedean. -/
theorem isVLArchimedean_of_exists_strictlyPositiveFunctional
    (hφ : ∃ φ : X →ₗ[ℝ] ℝ, StrictlyPositive φ) : IsVLArchimedean X := by
  obtain ⟨φ, hφ⟩ := hφ
  have hφ_pos : Positive φ := hφ.positive
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro x y hx hxy
  by_contra hx_zero
  have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx_zero)
  have hφx_pos : 0 < φ x := hφ x hx_pos
  obtain ⟨n, hn⟩ := exists_lt_nsmul hφx_pos (φ y)
  have hle : n • φ x ≤ φ y := by
    simpa using (Positive.monotone_iff.mpr hφ_pos) (hxy n)
  exact (not_le_of_gt hn) hle

private lemma positive_norming_apply_pos_of_near
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] {ψ : StrongDual ℝ X} {u x : X}
    (hψ_pos : 0 ≤ ψ) (hψ_norm : ‖ψ‖ ≤ 1) (hψ_apply : ψ |u| = ‖|u|‖)
    (hx_pos : 0 < x) (hux : ‖u - x‖ < ‖x‖ / 4) :
    0 < ψ x := by
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hpsi_positive : Positive ψ.toLinearMap :=
    StrongDual.nonneg_iff.mp hψ_pos
  have hpsi_mono : Monotone ψ.toLinearMap :=
    Positive.monotone_iff.mpr hpsi_positive
  have hpsi_abs_le_norm : ψ |u - x| ≤ ‖u - x‖ := by
    have hnonneg : 0 ≤ ψ |u - x| :=
      hpsi_positive |u - x| (abs_nonneg _)
    have hop := ψ.le_opNorm |u - x|
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, norm_abs_eq_norm] at hop
    have hmul : ‖ψ‖ * ‖u - x‖ ≤ ‖u - x‖ := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hψ_norm (norm_nonneg (u - x))
    exact hop.trans hmul
  have hpsi_x_lower : ‖u‖ - ‖u - x‖ ≤ ψ x := by
    have habs_le : |u| ≤ x + |u - x| := by
      calc
        |u| = |x + (u - x)| := by congr 1; abel
        _ ≤ |x| + |u - x| := abs_add_le x (u - x)
        _ = x + |u - x| := by rw [abs_of_nonneg hx_nonneg]
    have hle := hpsi_mono habs_le
    have hle' : ‖u‖ ≤ ψ x + ψ |u - x| := by
      simpa [map_add, hψ_apply, norm_abs_eq_norm] using hle
    linarith
  have hx_norm_le : ‖x‖ ≤ ‖u‖ + ‖u - x‖ := by
    calc
      ‖x‖ = ‖u - (u - x)‖ := by congr 1; abel
      _ = ‖u + -(u - x)‖ := by rw [sub_eq_add_neg]
      _ ≤ ‖u‖ + ‖-(u - x)‖ := norm_add_le u (-(u - x))
      _ = ‖u‖ + ‖u - x‖ := by rw [norm_neg]
  by_contra hnonpos
  have hpsi_nonpos : ψ x ≤ 0 := le_of_not_gt hnonpos
  have hu_norm_le : ‖u‖ ≤ ‖u - x‖ := by linarith
  have hx_norm_le_two : ‖x‖ ≤ 2 * ‖u - x‖ := by linarith
  linarith

/-- Every separable Banach lattice admits a strictly positive continuous linear functional. -/
theorem exists_strictlyPositiveFunctional_of_separable_banachLattice
    (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [TopologicalSpace.SeparableSpace X] :
    ∃ φ : StrongDual ℝ X, StrictlyPositive φ.toLinearMap := by
  classical
  haveI : Nonempty X := ⟨0⟩
  let u : ℕ → X := TopologicalSpace.denseSeq X
  have hu_dense : DenseRange u := TopologicalSpace.denseRange_denseSeq X
  have hnorming :
      ∀ n : ℕ, ∃ ψ : StrongDual ℝ X, 0 ≤ ψ ∧ ‖ψ‖ ≤ 1 ∧ ψ |u n| = ‖|u n|‖ :=
    fun n => StrongDual.exists_positive_dual_norming (abs_nonneg (u n))
  choose ψ hψ_pos hψ_norm hψ_apply using hnorming
  let c : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  let F : ℕ → StrongDual ℝ X := fun n => c n • ψ n
  have hc_pos : ∀ n, 0 < c n := fun n => pow_pos (by norm_num) n
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n => (hc_pos n).le
  have hc_summable : Summable c :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hF_bound : ∀ n, ‖F n‖ ≤ c n := fun n => by
    calc
      ‖F n‖ = c n * ‖ψ n‖ := by
        simp [F, norm_smul, Real.norm_of_nonneg (hc_nonneg n)]
      _ ≤ c n * 1 := mul_le_mul_of_nonneg_left (hψ_norm n) (hc_nonneg n)
      _ = c n := by rw [mul_one]
  have hF_summable : Summable F :=
    Summable.of_norm_bounded (g := c) hc_summable hF_bound
  refine ⟨∑' n, F n, ?_⟩
  intro x hx_pos
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  obtain ⟨n, hn⟩ := hu_dense.exists_dist_lt x (show 0 < ‖x‖ / 4 by positivity)
  have hdist : ‖u n - x‖ < ‖x‖ / 4 := by
    rw [dist_eq_norm] at hn
    calc
      ‖u n - x‖ = ‖-(x - u n)‖ := by congr 1; abel
      _ = ‖x - u n‖ := norm_neg _
      _ < ‖x‖ / 4 := hn
  have hpsi_x_pos : 0 < ψ n x :=
    positive_norming_apply_pos_of_near (hψ_pos n) (hψ_norm n) (hψ_apply n) hx_pos hdist
  have hF_nonneg : ∀ k, 0 ≤ F k := fun k => by
    exact smul_nonneg (hc_nonneg k) (hψ_pos k)
  have hscalar_pos : 0 < F n x := by
    exact mul_pos (hc_pos n) hpsi_x_pos
  have hterm_le_sum : F n ≤ ∑' k, F k := by
    simpa using
      (sum_le_hasSum ({n} : Finset ℕ) (fun k _ => hF_nonneg k) hF_summable.hasSum)
  exact hscalar_pos.trans_le (StrongDual.le_iff.mp hterm_le_sum x hx_nonneg)

private lemma disjointComplement_carrier_eq_null_of_orderContinuous
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] [IsVLArchimedean X] {T : OrderBoundedHom X ℝ}
    (hT : IsOrderContinuousOp T.toLinearMap) :
    (OrderBoundedHom.carrier T : Set X)ᵈ = (OrderBoundedHom.null T : Set X) := by
  obtain ⟨B, hB⟩ := OrderBoundedHom.exists_band_coe_eq_null_of_orderContinuous T hT
  change (((OrderBoundedHom.null T : Set X)ᵈ)ᵈ) = (OrderBoundedHom.null T : Set X)
  rw [← hB]
  exact Band.eq_disjointComplement_disjointComplement B

private lemma positive_functional_apply_weakOrderUnit_pos
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [IsOrderContinuousNorm X] {e : X} (he : WeakOrderUnit e)
    {φ : StrongDual ℝ X} (hφ_nonneg : 0 ≤ φ) (hφ_ne : φ ≠ 0) :
    0 < φ e := by
  have hφe_nonneg : 0 ≤ φ e := StrongDual.apply_nonneg_of_nonneg hφ_nonneg he.1
  refine lt_of_le_of_ne hφe_nonneg ?_
  intro hφe_eq_zero
  apply hφ_ne
  let T : OrderBoundedHom X ℝ := StrongDual.toOrderDualSpace φ
  have hT_nonneg : 0 ≤ T := by
    change 0 ≤ StrongDual.toOrderDualSpace φ
    exact hφ_nonneg
  have hT_oc : IsOrderContinuousOp T.toLinearMap :=
    OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm T
  obtain ⟨B, hB⟩ := OrderBoundedHom.exists_band_coe_eq_null_of_orderContinuous T hT_oc
  have he_null : e ∈ OrderBoundedHom.null T := by
    rw [OrderBoundedHom.mem_null]
    change (|T| : OrderBoundedHom X ℝ) |e| = 0
    rw [abs_of_nonneg hT_nonneg, abs_of_nonneg he.1]
    exact hφe_eq_zero.symm
  have he_B : e ∈ B := by
    change e ∈ (B : Set X)
    rw [hB]
    exact he_null
  have hgen_top : Band.generated ({e} : Set X) = (⊤ : Band X) :=
    (weakOrderUnit_iff_generated_singleton_eq_top he.1).mp he
  have htop_le_B : (⊤ : Band X) ≤ B := by
    rw [← hgen_top]
    exact Band.generated_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact he_B)
  ext x
  have hx_null : x ∈ OrderBoundedHom.null T := by
    change x ∈ (OrderBoundedHom.null T : Set X)
    rw [← hB]
    exact htop_le_B Band.mem_top
  have hx_abs_zero : T |x| = 0 := by
    have hx := OrderBoundedHom.mem_null.mp hx_null
    simpa [abs_of_nonneg hT_nonneg] using hx
  have h_abs_le : |φ x| ≤ φ |x| :=
    StrongDual.abs_apply_le_apply_abs hφ_nonneg x
  have hle_zero : |φ x| ≤ 0 := h_abs_le.trans_eq hx_abs_zero
  exact (abs_eq_zero_iff_zero (φ x)).mp (le_antisymm hle_zero (abs_nonneg _))

private lemma exists_apply_pos_of_isMaximalDisjoint_dual
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [IsOrderContinuousNorm X]
    {Λ : Set (StrongDual ℝ X)} (hΛ : IsMaximalDisjoint Λ)
    (hΛ_pos : ∀ φ ∈ Λ, 0 < φ) {x : X} (hx : 0 < x) :
    ∃ φ ∈ Λ, 0 < φ x := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨η, hη_nonneg, _hη_norm, hηx⟩ :=
    StrongDual.exists_positive_dual_norming (X := X) hx.le
  let P : ProjectionBand X := Band.principalProjectionBand x
  let Pclm : X →L[ℝ] X :=
    { toLinearMap := P.bandProjection
      cont := IsOrderBounded.continuous
        (Positive.isOrderBounded
          (Positive.zero_le_iff.mp P.bandProjection_nonneg)) }
  let g : StrongDual ℝ X := η.comp Pclm
  have hg_nonneg : 0 ≤ g := by
    rw [StrongDual.nonneg_iff]
    intro y hy
    exact StrongDual.apply_nonneg_of_nonneg hη_nonneg
      (Positive.zero_le_iff.mp P.bandProjection_nonneg y hy)
  have hx_mem_principal : x ∈ (Band.generated ({x} : Set X) : Set X) :=
    Band.subset_generated _ rfl
  have hPx : P.bandProjection x = x := by
    apply P.bandProjection_eq_of_mem
    change x ∈ (P : Set X)
    rw [Band.principalProjectionBand_coe]
    exact hx_mem_principal
  have hgx_pos : 0 < g x := by
    simpa [g, Pclm, hPx, hηx] using (norm_pos_iff.mpr (ne_of_gt hx))
  have hg_ne : g ≠ 0 := by
    intro hg_zero
    have : g x = 0 := by rw [hg_zero]; rfl
    exact (ne_of_gt hgx_pos) this
  have hg_order_nonneg : 0 ≤ StrongDual.toOrderDualSpace g := by
    change 0 ≤ g
    exact hg_nonneg
  have hg_oc : IsOrderContinuousOp (StrongDual.toOrderDualSpace g).toLinearMap :=
    OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm
      (StrongDual.toOrderDualSpace g)
  have hcarrier_g_subset_principal :
      (OrderBoundedHom.carrier (StrongDual.toOrderDualSpace g) : Set X) ⊆
        (Band.generated ({x} : Set X) : Set X) := by
    intro y hy
    have hy_dd : y ∈ ((Band.generated ({x} : Set X) : Set X)ᵈ)ᵈ := by
      intro z hz
      have hz_abs_dc : |z| ∈ (P : Set X)ᵈ := by
        have hz_abs : |z| ∈ (Band.generated ({x} : Set X) : Set X)ᵈ :=
          ((Band.disjointComplement (Band.generated ({x} : Set X) : Set X)).toOrderIdeal).abs_mem hz
        change |z| ∈ (P : Set X)ᵈ
        rwa [Band.principalProjectionBand_coe]
      have hPz_abs : P.bandProjection |z| = 0 :=
        P.bandProjection_eq_zero_of_mem_dc hz_abs_dc
      have hz_null : z ∈ OrderBoundedHom.null (StrongDual.toOrderDualSpace g) := by
        rw [OrderBoundedHom.mem_null]
        change (|StrongDual.toOrderDualSpace g| : OrderBoundedHom X ℝ) |z| = 0
        rw [abs_of_nonneg hg_order_nonneg]
        change g |z| = 0
        simp [g, Pclm, hPz_abs]
      exact OrderBoundedHom.mem_carrier.mp hy z hz_null
    change y ∈ (Band.generated ({x} : Set X) : Set X)
    rwa [Band.eq_disjointComplement_disjointComplement (Band.generated ({x} : Set X))] at hy_dd
  have hg_disj : ∀ φ ∈ Λ, IsVLDisjoint g φ := by
    intro φ hφΛ
    have hφ_nonneg : 0 ≤ φ := (hΛ_pos φ hφΛ).le
    have hφx_zero : φ x = 0 := by
      have hle : φ x ≤ 0 := hnone φ hφΛ
      exact le_antisymm hle (StrongDual.apply_nonneg_of_nonneg hφ_nonneg hx.le)
    let Tφ : OrderBoundedHom X ℝ := StrongDual.toOrderDualSpace φ
    have hTφ_nonneg : 0 ≤ Tφ := by
      change 0 ≤ φ
      exact hφ_nonneg
    have hTφ_oc : IsOrderContinuousOp Tφ.toLinearMap :=
      OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm Tφ
    have hx_null : x ∈ OrderBoundedHom.null Tφ := by
      rw [OrderBoundedHom.mem_null]
      change (|Tφ| : OrderBoundedHom X ℝ) |x| = 0
      rw [abs_of_nonneg hTφ_nonneg, abs_of_nonneg hx.le]
      exact hφx_zero
    obtain ⟨Bφ, hBφ⟩ :=
      OrderBoundedHom.exists_band_coe_eq_null_of_orderContinuous Tφ hTφ_oc
    have hx_Bφ : x ∈ Bφ := by
      change x ∈ (Bφ : Set X)
      rw [hBφ]
      exact hx_null
    have hprincipal_subset_null :
        (Band.generated ({x} : Set X) : Set X) ⊆
          (OrderBoundedHom.null Tφ : Set X) := by
      intro y hy
      rw [← hBφ]
      exact Band.generated_le (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hx_Bφ) hy
    have hcarrier_subset_null :
        (OrderBoundedHom.carrier (StrongDual.toOrderDualSpace g) : Set X) ⊆
          (OrderBoundedHom.null Tφ : Set X) :=
      fun y hy => hprincipal_subset_null (hcarrier_g_subset_principal hy)
    have hdisj_order : IsVLDisjoint (StrongDual.toOrderDualSpace g) Tφ :=
      ((OrderBoundedHom.nakano_theorem
        (StrongDual.toOrderDualSpace g) Tφ hg_oc hTφ_oc).out 1 0).mp hcarrier_subset_null
    unfold IsVLDisjoint at hdisj_order ⊢
    ext y
    have hy := congrArg (fun T : OrderBoundedHom X ℝ => T y) hdisj_order
    simpa [Tφ] using hy
  have hforall_zero :=
    (isMaximalDisjoint_iff_forall_eq_zero hΛ_pos hΛ.1).mp hΛ
  exact hg_ne (hforall_zero g hg_disj)

private lemma countable_of_isDisjointSet_dual_of_weakOrderUnit
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [IsOrderContinuousNorm X] {e : X} (he : WeakOrderUnit e)
    {Λ : Set (StrongDual ℝ X)} (hΛ_disj : IsDisjointSet Λ)
    (hΛ_pos : ∀ φ ∈ Λ, 0 < φ) :
    Λ.Countable := by
  classical
  letI : ConditionallyCompleteLattice X :=
    BanachLattice.conditionallyCompleteLatticeOfIsOrderContinuousNorm
  haveI : HasProjectionProperty X := inferInstance
  let T : Λ → OrderBoundedHom X ℝ := fun φ => StrongDual.toOrderDualSpace (φ : StrongDual ℝ X)
  let P : Λ → ProjectionBand X := fun φ =>
    (HasProjectionProperty.exists_projectionBand (OrderBoundedHom.carrier (T φ))).choose
  let u : Λ → X := fun φ => (P φ).bandProjection e
  have hP_coe : ∀ φ : Λ,
      (P φ : Set X) = (OrderBoundedHom.carrier (T φ) : Set X) := fun φ =>
    (HasProjectionProperty.exists_projectionBand (OrderBoundedHom.carrier (T φ))).choose_spec
  have hT_nonneg : ∀ φ : Λ, 0 ≤ T φ := fun φ => by
    change 0 ≤ (φ : StrongDual ℝ X)
    exact (hΛ_pos φ φ.2).le
  have hφ_nonneg : ∀ φ : Λ, 0 ≤ (φ : StrongDual ℝ X) := fun φ =>
    (hΛ_pos φ φ.2).le
  have hT_oc : ∀ φ : Λ, IsOrderContinuousOp (T φ).toLinearMap := fun φ =>
    OrderContinuousOp.functional_orderContinuous_of_orderContinuousNorm (T φ)
  have hφe_pos : ∀ φ : Λ, 0 < (φ : StrongDual ℝ X) e := fun φ =>
    positive_functional_apply_weakOrderUnit_pos he (hφ_nonneg φ)
      (ne_of_gt (hΛ_pos φ φ.2))
  have hu_nonneg : ∀ φ : Λ, 0 ≤ u φ := fun φ =>
    Positive.zero_le_iff.mp (P φ).bandProjection_nonneg e he.1
  have hu_le_e : ∀ φ : Λ, u φ ≤ e := fun φ =>
    Positive.le_iff.mp (P φ).bandProjection_le_id e he.1
  have hu_carrier : ∀ φ : Λ, u φ ∈ OrderBoundedHom.carrier (T φ) := fun φ => by
    change u φ ∈ (OrderBoundedHom.carrier (T φ) : Set X)
    rw [← hP_coe φ]
    exact (P φ).bandProjection_mem e
  have hu_ne : ∀ φ : Λ, u φ ≠ 0 := by
    intro φ hu_zero
    have hcomp_dc : e - u φ ∈ (OrderBoundedHom.carrier (T φ) : Set X)ᵈ := by
      change e - u φ ∈ (OrderBoundedHom.carrier (T φ) : Set X)ᵈ
      rw [← hP_coe φ]
      exact (P φ).id_sub_bandProjection_mem e
    have hcomp_null : e - u φ ∈ OrderBoundedHom.null (T φ) := by
      change e - u φ ∈ (OrderBoundedHom.null (T φ) : Set X)
      rw [← disjointComplement_carrier_eq_null_of_orderContinuous (T := T φ) (hT_oc φ)]
      exact hcomp_dc
    have hcomp_abs_zero : (φ : StrongDual ℝ X) |e - u φ| = 0 := by
      have hnull := OrderBoundedHom.mem_null.mp hcomp_null
      simpa [T, abs_of_nonneg (hT_nonneg φ)] using hnull
    have hcomp_zero : (φ : StrongDual ℝ X) (e - u φ) = 0 := by
      have hle := StrongDual.abs_apply_le_apply_abs (hφ_nonneg φ) (e - u φ)
      rw [hcomp_abs_zero] at hle
      exact (abs_eq_zero_iff_zero ((φ : StrongDual ℝ X) (e - u φ))).mp
        (le_antisymm hle (abs_nonneg _))
    have hφe_eq : (φ : StrongDual ℝ X) e = (φ : StrongDual ℝ X) (u φ) := by
      calc
        (φ : StrongDual ℝ X) e =
            (φ : StrongDual ℝ X) (u φ) + (φ : StrongDual ℝ X) (e - u φ) := by
              rw [← map_add]
              congr 1
              abel
        _ = (φ : StrongDual ℝ X) (u φ) := by rw [hcomp_zero, add_zero]
    have hφu_zero : (φ : StrongDual ℝ X) (u φ) = 0 := by rw [hu_zero, map_zero]
    exact (ne_of_gt (hφe_pos φ)) (by rw [hφe_eq, hφu_zero])
  have hu_disj : ∀ {φ ψ : Λ}, φ ≠ ψ → IsVLDisjoint (u φ) (u ψ) := by
    intro φ ψ hφψ
    have hdual_disj : IsVLDisjoint (T φ) (T ψ) := by
      have hstrong : IsVLDisjoint (φ : StrongDual ℝ X) (ψ : StrongDual ℝ X) :=
        hΛ_disj.2 φ.2 ψ.2 (fun h => hφψ (Subtype.ext h))
      unfold IsVLDisjoint at hstrong ⊢
      have h := congrArg StrongDual.toOrderDualSpace hstrong
      simpa [T] using h
    have hcarrier_sub_dc :
        (OrderBoundedHom.carrier (T φ) : Set X) ⊆
          (OrderBoundedHom.carrier (T ψ) : Set X)ᵈ :=
      ((OrderBoundedHom.nakano_theorem (T φ) (T ψ) (hT_oc φ) (hT_oc ψ)).out 0 3).mp
        hdual_disj
    exact hcarrier_sub_dc (hu_carrier φ) (u ψ) (hu_carrier ψ)
  have hu_inj : Function.Injective u := by
    intro φ ψ h_eq
    by_contra hne
    have hdisj := hu_disj hne
    rw [h_eq] at hdisj
    unfold IsVLDisjoint at hdisj
    rw [inf_idem] at hdisj
    exact hu_ne ψ ((abs_eq_zero_iff_zero (u ψ)).mp hdisj)
  let U : Set X := Set.range u
  have hU0 : ∀ y ∈ U, y ≠ 0 := by
    rintro y ⟨φ, rfl⟩
    exact hu_ne φ
  have hUdisj : U.Pairwise (fun y z => IsVLDisjoint y z) := by
    rintro y ⟨φ, rfl⟩ z ⟨ψ, rfl⟩ hyz
    have hφψ : φ ≠ ψ := fun h => hyz (by rw [h])
    exact hu_disj hφψ
  have hUbd : BddAbove ((fun y : X => |y|) '' U) := by
    refine ⟨e, ?_⟩
    rintro y ⟨z, ⟨φ, rfl⟩, rfl⟩
    change |u φ| ≤ e
    rw [abs_of_nonneg (hu_nonneg φ)]
    exact hu_le_e φ
  have hU_count : U.Countable :=
    BanachLattice.countable_of_pairwise_disjoint_bddAbove hU0 hUdisj hUbd
  haveI : Countable U := hU_count.to_subtype
  let f : Λ → U := fun φ => ⟨u φ, φ, rfl⟩
  have hf_inj : Function.Injective f := by
    intro φ ψ h
    exact hu_inj (congrArg Subtype.val h)
  haveI : Countable Λ := hf_inj.countable
  exact Set.countable_coe_iff.mp (inferInstance : Countable Λ)

/-- Every order-continuous Banach lattice with a weak unit admits a strictly positive
continuous linear functional. -/
theorem exists_strictlyPositiveFunctional_of_orderContinuousNorm_of_exists_weakOrderUnit
    (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [BanachLattice X] [IsOrderContinuousNorm X] (hwu : ∃ e : X, WeakOrderUnit e) :
    ∃ φ : StrongDual ℝ X, StrictlyPositive φ.toLinearMap := by
  classical
  obtain ⟨e, he⟩ := hwu
  obtain ⟨Λ, hΛ, hΛ_pos⟩ := exists_isMaximalDisjoint_pos (StrongDual ℝ X)
  have hΛ_count : Λ.Countable :=
    countable_of_isDisjointSet_dual_of_weakOrderUnit he hΛ.1 hΛ_pos
  haveI : Countable Λ := hΛ_count.to_subtype
  letI : Encodable Λ := Encodable.ofCountable Λ
  let c : Λ → ℝ := fun φ => (1 / 2 : ℝ) ^ Encodable.encode φ / ‖(φ : StrongDual ℝ X)‖
  let F : Λ → StrongDual ℝ X := fun φ => c φ • (φ : StrongDual ℝ X)
  have hweight_pos : ∀ φ : Λ, 0 < (1 / 2 : ℝ) ^ Encodable.encode φ := fun φ =>
    pow_pos (by norm_num) _
  have hnorm_pos : ∀ φ : Λ, 0 < ‖(φ : StrongDual ℝ X)‖ := fun φ =>
    norm_pos_iff.mpr (ne_of_gt (hΛ_pos φ φ.2))
  have hc_pos : ∀ φ : Λ, 0 < c φ := fun φ =>
    div_pos (hweight_pos φ) (hnorm_pos φ)
  have hweight_summable : Summable fun φ : Λ => (1 / 2 : ℝ) ^ Encodable.encode φ :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      Encodable.encode_injective
  have hF_bound : ∀ φ : Λ, ‖F φ‖ ≤ (1 / 2 : ℝ) ^ Encodable.encode φ := fun φ => by
    calc
      ‖F φ‖ = c φ * ‖(φ : StrongDual ℝ X)‖ := by
        simp [F, norm_smul, Real.norm_of_nonneg (hc_pos φ).le]
      _ = (1 / 2 : ℝ) ^ Encodable.encode φ := by
        dsimp [c]
        rw [div_mul_cancel₀ _ (hnorm_pos φ).ne']
      _ ≤ (1 / 2 : ℝ) ^ Encodable.encode φ := le_rfl
  have hF_summable : Summable F :=
    Summable.of_norm_bounded (g := fun φ : Λ => (1 / 2 : ℝ) ^ Encodable.encode φ)
      hweight_summable hF_bound
  refine ⟨∑' φ, F φ, ?_⟩
  intro x hx
  obtain ⟨ψ, hψΛ, hψx_pos⟩ :=
    exists_apply_pos_of_isMaximalDisjoint_dual hΛ hΛ_pos hx
  let ψΛ : Λ := ⟨ψ, hψΛ⟩
  have hF_nonneg : ∀ φ : Λ, 0 ≤ F φ := fun φ =>
    smul_nonneg (hc_pos φ).le (hΛ_pos φ φ.2).le
  have hterm_pos : 0 < F ψΛ x := by
    change 0 < (c ψΛ • (ψΛ : StrongDual ℝ X)) x
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (hc_pos ψΛ) hψx_pos
  have hterm_le_sum : F ψΛ ≤ ∑' φ, F φ := by
    simpa using
      (sum_le_hasSum ({ψΛ} : Finset Λ) (fun φ _ => hF_nonneg φ) hF_summable.hasSum)
  exact hterm_pos.trans_le (StrongDual.le_iff.mp hterm_le_sum x hx.le)
