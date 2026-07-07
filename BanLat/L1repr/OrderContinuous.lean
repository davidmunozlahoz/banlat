import BanLat.L1repr.HowItSeats
import BanLat.OrderUnit

/-!
# `L¹`-representations with an order continuous functional and a weak unit

A vector lattice `X` with an order continuous strictly positive functional `h` and a weak
order unit `e` admits a particularly concrete `L¹`-representation: the measure `μ` can be
chosen finite, with `e` realised as the constant function `1`. If `X` is moreover order
complete, then `X` contains a copy of `L∞(μ)` — the essentially bounded elements of
`L¹(μ)` all lie in the image of `X`, and the elements of `X` they account for form an
order dense ideal of `X`.
-/

open MeasureTheory

universe u

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Finite `L¹`-representation with a weak unit.** A vector lattice with an order
continuous strictly positive functional `h` and a weak order unit `e` admits an
`L¹`-representation over a finite measure in which `e` is realised as the constant
function `1`. -/
theorem exists_L1_representation_isFiniteMeasure_of_weakOrderUnit
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h) (hoc : IsOrderContinuousOp h)
    {e : X} (he : WeakOrderUnit e) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsFiniteMeasure μ)
      (T : VecLatHom X (Lp ℝ 1 μ)),
      Function.Injective (T : X → Lp ℝ 1 μ) ∧ DenseRange (T : X → Lp ℝ 1 μ) ∧
        (∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ) ∧ ∀ᵐ ω ∂μ, T e ω = 1 := by
  letI : NormedAddCommGroup X := StrictlyPositive.associatedNormedAddCommGroup h hh
  letI : NormedVectorLattice X := StrictlyPositive.associatedNormedVectorLattice h hh
  have hAL : ∀ x y : X, x ⊓ y = 0 → ‖x + y‖ = ‖x‖ + ‖y‖ :=
    fun x y hxy => StrictlyPositive.associatedNorm_add_eq_norm_add_of_inf_eq_zero h hh hxy
  letI : ALSpace (UniformSpace.Completion X) := ALSpace.completion hAL
  -- Any Banach lattice equivalence of the completion with an `L¹` space yields an
  -- `L¹`-representation of `X` by composition with the inclusion into the completion.
  have key : ∀ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀) (μ₀ : Measure Ω₀)
      (ψ : BanachLatEquiv (UniformSpace.Completion X) (Lp ℝ 1 μ₀)),
      Function.Injective ⇑(ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom) ∧
        DenseRange ⇑(ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom) ∧
        ∀ x : X, 0 ≤ x →
          h x = ∫ ω, (ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom) x ω ∂μ₀ := by
    intro Ω₀ m₀ μ₀ ψ
    have hTx : ∀ x : X, (ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom) x
        = ψ (↑x : UniformSpace.Completion X) := fun _ => rfl
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      rw [hTx a, hTx b] at hab
      exact isometry_toCompletionVecLatHom.injective (ψ.toLinearIsometryEquiv.injective hab)
    · have hcomp : ⇑(ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom)
          = ⇑ψ.toLinearIsometryEquiv ∘ ((↑) : X → UniformSpace.Completion X) := funext hTx
      rw [hcomp]
      exact (ψ.toLinearIsometryEquiv.surjective.denseRange).comp
        UniformSpace.Completion.denseRange_coe ψ.toLinearIsometryEquiv.continuous
    · intro x hx
      set T := ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom with hTdef
      have hTxnn : 0 ≤ T x := T.map_nonneg hx
      have hae : (0 : Ω₀ → ℝ) ≤ᵐ[μ₀] (T x) := (Lp.coeFn_nonneg (T x)).mpr hTxnn
      have hintegrand : (fun ω => ‖(T x) ω‖) =ᵐ[μ₀] (fun ω => (T x) ω) := by
        filter_upwards [hae] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg hω]
      have hnorm : ‖T x‖ = h x := by
        have e1 : ‖T x‖ = ‖(↑x : UniformSpace.Completion X)‖ := by
          rw [hTx x]; exact ψ.toLinearIsometryEquiv.norm_map _
        rw [e1, UniformSpace.Completion.norm_coe,
          StrictlyPositive.associatedNormedAddCommGroup_norm h hh]
        change h |x| = h x
        rw [abs_of_nonneg hx]
      rw [← hnorm, L1.norm_eq_integral_norm]
      exact integral_congr_ae hintegrand
  -- `e` becomes a weak order unit of the completion, since the copy of `X` is order dense.
  have hê_nn : (0 : UniformSpace.Completion X) ≤ ↑e := toCompletionVecLatHom.map_nonneg he.1
  have hê : WeakOrderUnit ((e : UniformSpace.Completion X)) := by
    refine ⟨hê_nn, fun w hw => ?_⟩
    by_contra hw0
    obtain ⟨Ω₀, m₀, μ₀, ⟨ψ⟩⟩ :=
      ALSpace.exists_L1_banachLatEquiv (X := UniformSpace.Completion X)
    obtain ⟨hT₀_inj, hT₀_dense, hT₀_rep⟩ := key Ω₀ m₀ μ₀ ψ
    have hOD : IsOrderDense
        (Set.range ⇑(ψ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom)) :=
      (isOrderDense_range_iff_isOrderContinuousOp h hh _ hT₀_inj hT₀_dense hT₀_rep).mpr hoc
    have hψ_inj : Function.Injective ⇑ψ.toVecLatEquiv.toVecLatHom :=
      ψ.toLinearIsometryEquiv.injective
    have habs_pos : 0 < |w| := by
      refine lt_of_le_of_ne (abs_nonneg w) fun h0 => ?_
      exact hw0 ((abs_eq_zero_iff_zero w).mp h0.symm)
    have hψw_pos : 0 < ψ.toVecLatEquiv.toVecLatHom |w| := by
      refine lt_of_le_of_ne (ψ.toVecLatEquiv.toVecLatHom.map_nonneg habs_pos.le)
        fun h0 => ?_
      have h1 : ψ.toVecLatEquiv.toVecLatHom |w| = ψ.toVecLatEquiv.toVecLatHom 0 := by
        rw [← h0, map_zero]
      exact habs_pos.ne' (hψ_inj h1)
    obtain ⟨p, ⟨z, rfl⟩, hp_pos, hp_le⟩ := hOD hψw_pos
    have hp_le' : ψ.toVecLatEquiv.toVecLatHom (↑z : UniformSpace.Completion X)
        ≤ ψ.toVecLatEquiv.toVecLatHom |w| := hp_le
    have hp_pos' : (0 : Lp ℝ 1 μ₀)
        < ψ.toVecLatEquiv.toVecLatHom (↑z : UniformSpace.Completion X) := hp_pos
    have hz_le : (↑z : UniformSpace.Completion X) ≤ |w| :=
      ψ.toVecLatEquiv.toVecLatHom.le_of_map_le hψ_inj hp_le'
    have hz_pos : (0 : UniformSpace.Completion X) < ↑z := by
      refine lt_of_le_of_ne ?_ fun h0 => ?_
      · refine ψ.toVecLatEquiv.toVecLatHom.le_of_map_le hψ_inj ?_
        rw [map_zero]
        exact hp_pos'.le
      · rw [← h0, map_zero] at hp_pos'
        exact hp_pos'.false
    have hinf0 : z ⊓ e = 0 := by
      apply isometry_toCompletionVecLatHom.injective
      rw [map_inf, map_zero]
      change (↑z : UniformSpace.Completion X) ⊓ (↑e : UniformSpace.Completion X) = 0
      refine le_antisymm ?_ (le_inf hz_pos.le hê_nn)
      calc (↑z : UniformSpace.Completion X) ⊓ ↑e ≤ |w| ⊓ ↑e := inf_le_inf_right _ hz_le
        _ = |w| ⊓ |(↑e : UniformSpace.Completion X)| := by rw [abs_of_nonneg hê_nn]
        _ = 0 := hw
    have hz0 : z = 0 := he.2 z (isVLDisjoint_of_inf_eq_zero hinf0)
    rw [hz0, UniformSpace.Completion.coe_zero] at hz_pos
    exact hz_pos.false
  -- Apply the weak-unit Kakutani representation of the completion.
  obtain ⟨Ω, mΩ, μ, hfin, φ, hφ⟩ :=
    ALSpace.exists_L1_banachLatEquiv_isFiniteMeasure_of_weakOrderUnit
      (X := UniformSpace.Completion X) hê
  obtain ⟨hT_inj, hT_dense, hT_rep⟩ := key Ω mΩ μ φ
  refine ⟨Ω, mΩ, μ, hfin, φ.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom,
    hT_inj, hT_dense, hT_rep, ?_⟩
  exact hφ

/-- **`L∞(μ)` sits inside `X`.** For an `L¹`-representation of an order complete vector
lattice `X` with an order continuous strictly positive functional `h`, in which some
element `e` of `X` is realised as the constant function `1`, every essentially bounded
element of `L¹(μ)` lies in the image of `X`. -/
theorem mem_range_of_ae_bounded {X : Type u} [AddCommGroup X]
    [ConditionallyCompleteLattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h) (hoc : IsOrderContinuousOp h)
    (T : VecLatHom X (Lp ℝ 1 μ))
    (hT_inj : Function.Injective (T : X → Lp ℝ 1 μ))
    (hT_dense : DenseRange (T : X → Lp ℝ 1 μ))
    (hT_rep : ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ)
    {e : X} (hT_one : ∀ᵐ ω ∂μ, T e ω = 1)
    (v : Lp ℝ 1 μ) (hv : ∃ C : ℝ, ∀ᵐ ω ∂μ, |v ω| ≤ C) :
    v ∈ Set.range (T : X → Lp ℝ 1 μ) := by
  obtain ⟨C, hC⟩ := hv
  -- The image of `X` is solid, and `v` is dominated by the image of `(C ⊔ 0) • e`.
  have hsolid := (solid_range_iff_isOrderContinuousOp_and_orderComplete h hh T hT_inj
    hT_dense hT_rep).mpr ⟨hoc, fun S hne hbdd => ⟨sSup S, isLUB_csSup hne (hb := hbdd)⟩⟩
  refine hsolid (T ((C ⊔ 0) • e)) v ⟨_, rfl⟩ ?_
  rw [map_smul T (C ⊔ 0) e, ← Lp.coeFn_le]
  filter_upwards [Lp.coeFn_abs v, Lp.coeFn_abs ((C ⊔ 0) • T e),
    Lp.coeFn_smul (C ⊔ 0) (T e), hC, hT_one] with ω h1 h2 h3 h4 h5
  rw [h1, h2, h3, Pi.smul_apply, h5, smul_eq_mul, mul_one,
    abs_of_nonneg (le_sup_right : (0 : ℝ) ≤ C ⊔ 0)]
  exact h4.trans le_sup_left

/-- **`L∞(μ)` is order dense in `X`.** If a vector lattice homomorphism `T : X → L¹(μ)`
realises the weak order unit `e` as the constant function `1`, then the elements of `X`
with essentially bounded image — those accounting for the copy of `L∞(μ)` — form an
order dense subset of `X`; this subset is an order ideal of `X`. -/
theorem isOrderDense_setOf_ae_bounded
    (T : VecLatHom X (Lp ℝ 1 μ)) {e : X} (he : WeakOrderUnit e)
    (hT_one : ∀ᵐ ω ∂μ, T e ω = 1) :
    IsOrderDense {x : X | ∃ C : ℝ, ∀ᵐ ω ∂μ, |T x ω| ≤ C} := by
  intro x hx
  refine ⟨x ⊓ e, ⟨1, ?_⟩, ?_, inf_le_left⟩
  · -- `T (x ⊓ e)` is squeezed between `0` and `T e`, which is a.e. equal to `1`.
    have h1 : (0 : Lp ℝ 1 μ) ≤ T (x ⊓ e) := T.map_nonneg (le_inf hx.le he.1)
    have h2 : T (x ⊓ e) ≤ T e := T.monotone inf_le_right
    filter_upwards [(Lp.coeFn_nonneg (T (x ⊓ e))).mpr h1, (Lp.coeFn_le _ _).mpr h2, hT_one]
      with ω h1ω h2ω heω
    rw [abs_of_nonneg h1ω]
    exact h2ω.trans heω.le
  · -- The infimum with a weak order unit is nonzero on positive elements.
    refine lt_of_le_of_ne (le_inf hx.le he.1) fun h0 => ?_
    have hdisj : IsVLDisjoint x e := isVLDisjoint_of_inf_eq_zero h0.symm
    exact hx.ne' (he.2 x hdisj)
