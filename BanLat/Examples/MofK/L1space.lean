import BanLat.Examples.MofK.Band
import BanLat.OrderContinuous.Decomposition

/-!
# `M(K)` as an `L¹` space
-/

open MeasureTheory

universe u

namespace MofK

namespace Band

private abbrev principalBand {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (a : X) : Band X :=
  Band.generated ({a} : Set X)

end Band

variable (X : Type u) [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X]

section SigmaGluing

/-- `Sigma.mk i` is a measurable embedding for the sigma measurable space. -/
private lemma measurableEmbedding_sigma_mk {ι : Type*}
    {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Sigma β) := by
  refine ⟨fun a b h => by cases h; rfl,
    measurable_iff_le_map.mpr (iInf_le _ i), fun s hs => ?_⟩
  change @MeasurableSet _
    (⨅ j, MeasurableSpace.map (Sigma.mk j) (mβ j)) _
  rw [MeasurableSpace.measurableSet_iInf]
  intro j
  change @MeasurableSet (β j) (mβ j)
    (Sigma.mk j ⁻¹' (Sigma.mk i '' s))
  by_cases hij : j = i
  · subst hij
    convert hs using 1
    ext b; constructor
    · rintro ⟨c, hc, h⟩; cases h; exact hc
    · intro hb; exact ⟨b, hb, rfl⟩
  · convert MeasurableSet.empty using 1
    ext b
    simp only [Set.mem_preimage, Set.mem_image,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨c, _, h⟩
    exact hij (Sigma.mk.inj h).1.symm

/-- A function on a sigma type is measurable if and only if each fiber
restriction is measurable. -/
private lemma measurable_sigma_of_fibers {ι : Type*}
    {α : ι → Type*} {β : Type*}
    [mα : ∀ i, MeasurableSpace (α i)] [MeasurableSpace β]
    {f : (Σ i, α i) → β}
    (hf : ∀ i, Measurable (f ∘ Sigma.mk i)) :
    Measurable f := by
  intro s hs
  change @MeasurableSet _
    (⨅ i, MeasurableSpace.map (Sigma.mk i) (mα i)) _
  rw [MeasurableSpace.measurableSet_iInf]
  intro i; exact hf i hs

end SigmaGluing

/-- In an AL-space, a hasSum of non-negative elements induces a hasSum of
their norms. -/
private lemma hasSum_norm_of_nonneg_hasSum
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [ALSpace Y] {ι : Type*} {f : ι → Y} {x : Y}
    (hf : ∀ i, 0 ≤ f i) (hs : HasSum f x) :
    HasSum (fun i => ‖f i‖) ‖x‖ := by
  let addCommMonoid : AddCommMonoid Y := inferInstance
  let latticeOrig : Lattice Y := inferInstance
  let orderedAddOrig : @IsOrderedAddMonoid Y addCommMonoid
      latticeOrig.toPartialOrder.toPreorder :=
    inferInstance
  letI : AddLeftMono Y := ⟨fun a {_ _} h =>
    @IsOrderedAddMonoid.add_le_add_right Y addCommMonoid
      latticeOrig.toPartialOrder.toPreorder orderedAddOrig _ _ h a⟩
  have hnorm_sum : ∀ (s : Finset ι),
      ‖∑ i ∈ s, f i‖ = ∑ i ∈ s, ‖f i‖ := by
    intro s; induction s using Finset.cons_induction with
    | empty => simp
    | cons a s has ih =>
      rw [Finset.sum_cons, Finset.sum_cons,
        ALSpace.norm_add_eq_of_nonneg (hf a)
          (Finset.sum_nonneg fun i _ => hf i), ih]
  rw [HasSum] at hs ⊢
  convert continuous_norm.continuousAt.tendsto.comp hs using 1
  ext F; simp only [Function.comp_def]; exact (hnorm_sum F).symm

/-- The norms of band projections over a maximal disjoint family are summable
with sum `‖x‖` in an AL-space. -/
private lemma hasSum_norm_principalBandProjection
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [ALSpace Y] {Λ : Set Y} (hΛ : IsMaximalDisjoint Λ)
    (hΛ_pos : ∀ z ∈ Λ, 0 < z) (x : Y) :
    HasSum (fun z : ↑Λ =>
      ‖Band.principalBandProjection (z : Y) x‖) ‖x‖ := by
  let addCommMonoid : AddCommMonoid Y := inferInstance
  let addGroup : AddGroup Y := inferInstance
  let latticeOrig : Lattice Y := inferInstance
  let orderedAddOrig : @IsOrderedAddMonoid Y addCommMonoid
      latticeOrig.toPartialOrder.toPreorder :=
    inferInstance
  let addLeftMono : @AddLeftMono Y inferInstance latticeOrig.toLE := ⟨fun a {_ _} h =>
    @IsOrderedAddMonoid.add_le_add_right Y addCommMonoid
      latticeOrig.toPartialOrder.toPreorder orderedAddOrig _ _ h a⟩
  letI : AddLeftMono Y := addLeftMono
  set P := fun z : ↑Λ => Band.principalBandProjection (z : Y) with hP_def
  set xp := x⁺; set xn := x⁻
  have hx_decomp : x = xp - xn := by
    change x = x⁺ - x⁻
    exact (@posPart_sub_negPart Y latticeOrig addGroup addLeftMono x).symm
  have hxp_nn : (0 : Y) ≤ xp := posPart_nonneg x
  have hxn_nn : (0 : Y) ≤ xn := negPart_nonneg x
  have hsp := hasSum_norm_of_nonneg_hasSum (Y := Y)
    (fun (z : ↑Λ) =>
      Positive.zero_le_iff.mp (Band.principalProjectionBand (z : Y)).bandProjection_nonneg
        xp hxp_nn)
    (BanachLattice.hasSum_principalBandProjection hΛ hΛ_pos xp)
  have hsn := hasSum_norm_of_nonneg_hasSum (Y := Y)
    (fun (z : ↑Λ) =>
      Positive.zero_le_iff.mp (Band.principalProjectionBand (z : Y)).bandProjection_nonneg
        xn hxn_nn)
    (BanachLattice.hasSum_principalBandProjection hΛ hΛ_pos xn)
  change HasSum (fun z : ↑Λ => ‖P z xp‖) ‖xp‖ at hsp
  change HasSum (fun z : ↑Λ => ‖P z xn‖) ‖xn‖ at hsn
  have hle : ∀ z : ↑Λ, ‖P z x‖ ≤ ‖P z xp‖ + ‖P z xn‖ := by
    intro z
    rw [hx_decomp, map_sub]
    exact norm_sub_le _ _
  have hsum : Summable (fun z => ‖P z x‖) :=
    .of_nonneg_of_le (fun z => norm_nonneg _) hle (hsp.summable.add hsn.summable)
  have hub : tsum (fun z => ‖P z x‖) ≤ ‖x‖ :=
    calc ∑' z, ‖P z x‖
        ≤ ∑' z, (‖P z xp‖ + ‖P z xn‖) :=
          hsum.tsum_le_tsum hle (hsp.summable.add hsn.summable)
      _ = ∑' z, ‖P z xp‖ + ∑' z, ‖P z xn‖ :=
          (hsp.summable.hasSum.add hsn.summable.hasSum).tsum_eq
      _ = ‖xp‖ + ‖xn‖ := by rw [hsp.tsum_eq, hsn.tsum_eq]
      _ = ‖x‖ := ALSpace.norm_posPart_add_norm_negPart x
  have hlb : ‖x‖ ≤ tsum (fun z => ‖P z x‖) := by
    conv_lhs => rw [← (BanachLattice.hasSum_principalBandProjection hΛ hΛ_pos x).tsum_eq]
    exact norm_tsum_le_tsum_norm hsum
  exact (le_antisymm hub hlb) ▸ hsum.hasSum

/-- **Locally L¹ implies L¹.** If every principal band of an AL-space is
Banach-lattice isometric to some `L¹(μ)`, then the whole space is
Banach-lattice isometric to some `L¹(ν)`. -/
theorem exists_L1_banachLatEquiv_of_principalBandModels [ALSpace X]
    (h : ∀ x : X, 0 ≤ x →
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
        Nonempty (BanachLatEquiv
          ↥(Band.principalBand x).toSubmodule (Lp ℝ 1 μ))) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (ν : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 ν)) := by
  classical
  obtain ⟨Λ, hΛ, hpos⟩ := exists_isMaximalDisjoint_pos X
  have hdisj : IsDisjointSet Λ := hΛ.prop
  choose Ω mΩ μ hT using fun (z : Λ) =>
    h z.1 (le_of_lt (hpos z.1 z.2))
  have T : ∀ z : Λ, BanachLatEquiv
      (Band.principalBand (z : X)).toSubmodule
      (Lp ℝ 1 (μ z)) :=
    fun z => (hT z).some
  letI : ∀ z : Λ, MeasurableSpace (Ω z) := mΩ
  refine ⟨(z : Λ) × Ω z, inferInstance,
    Measure.sum (fun z => (μ z).map (Sigma.mk z)), ?_⟩
  set ν := Measure.sum (fun z : Λ => (μ z).map (Sigma.mk z)) with hν_def
  have hP_mem : ∀ (z : Λ) (x : X),
      Band.principalBandProjection (z : X) x ∈
        (Band.principalBand (z : X)).toSubmodule :=
    fun z x => by
      change _root_.Band.principalBandProjection (z : X) x ∈
        (_root_.Band.generated ({(z : X)} : Set X) : Set X)
      rw [← _root_.Band.principalProjectionBand_coe (z : X)]
      exact (_root_.Band.principalProjectionBand (z : X)).bandProjection_mem x
  let fL (z : Λ) (x : X) : Lp ℝ 1 (μ z) :=
    T z ⟨Band.principalBandProjection (z : X) x, hP_mem z x⟩
  have hfL_add : ∀ z x y, fL z (x + y) = fL z x + fL z y := by
    intro z x y
    have heq : (⟨Band.principalBandProjection (z : X) (x + y),
        hP_mem z (x + y)⟩ : (Band.principalBand (z : X)).toSubmodule) =
      ⟨_, hP_mem z x⟩ + ⟨_, hP_mem z y⟩ := by ext; simp [map_add]
    change T z ⟨_, _⟩ = T z ⟨_, _⟩ + T z ⟨_, _⟩
    rw [heq]; exact (T z).toLinearIsometryEquiv.map_add _ _
  have hfL_smul : ∀ z (c : ℝ) x, fL z (c • x) = c • fL z x := by
    intro z c x
    have heq : (⟨Band.principalBandProjection (z : X) (c • x),
        hP_mem z (c • x)⟩ : (Band.principalBand (z : X)).toSubmodule) =
      c • ⟨_, hP_mem z x⟩ := by ext; simp [map_smul]
    change T z ⟨_, _⟩ = c • T z ⟨_, _⟩
    rw [heq]; exact (T z).toLinearIsometryEquiv.map_smul c _
  let φ (x : X) : (z : Λ) × Ω z → ℝ := fun ⟨z, ω⟩ => fL z x ω
  have hφ_meas : ∀ x, Measurable (φ x) := by
    intro x; apply measurable_sigma_of_fibers
    intro z; exact (Lp.stronglyMeasurable (fL z x)).measurable
  have heLpNorm : ∀ x, eLpNorm (φ x) 1 ν = ∑' z : Λ, ↑‖fL z x‖₊ := by
    intro x
    rw [eLpNorm_one_eq_lintegral_enorm, hν_def, lintegral_sum_measure]
    congr 1; ext z
    rw [(measurableEmbedding_sigma_mk z).lintegral_map,
      ← eLpNorm_one_eq_lintegral_enorm, Lp.nnnorm_def,
      ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top _)]
  have hfL_norm_eq : ∀ z x,
      ‖fL z x‖ = ‖Band.principalBandProjection (z : X) x‖ :=
    fun z x => (T z).toLinearIsometryEquiv.norm_map _
  have hfL_hasSum : ∀ x, HasSum (fun z : Λ => ‖fL z x‖) ‖x‖ := by
    intro x; simp_rw [hfL_norm_eq]
    exact hasSum_norm_principalBandProjection hΛ hpos x
  have hfL_nnsummable : ∀ x,
      Summable (fun z : Λ => ‖fL z x‖₊) :=
    fun x => NNReal.summable_coe.mp
      (by simp_rw [coe_nnnorm]; exact (hfL_hasSum x).summable)
  have hφ_memLp : ∀ x, MemLp (φ x) 1 ν := by
    intro x
    exact ⟨(hφ_meas x).stronglyMeasurable.aestronglyMeasurable,
      heLpNorm x ▸ (ENNReal.coe_tsum (hfL_nnsummable x)).symm ▸
        ENNReal.coe_lt_top⟩
  let Φ (x : X) : Lp ℝ 1 ν := (hφ_memLp x).toLp (φ x)
  have hΦ_norm : ∀ x, ‖Φ x‖ = ‖x‖ := by
    intro x; rw [Lp.norm_toLp, heLpNorm x]
    have : (∑' z : ↑Λ, (↑‖fL z x‖₊ : ENNReal)).toReal = ∑' z, ‖fL z x‖ := by
      rw [← ENNReal.coe_tsum (hfL_nnsummable x), ENNReal.coe_toReal,
          NNReal.coe_tsum]
      simp [coe_nnnorm]
    rw [this]; exact (hfL_hasSum x).tsum_eq
  have hae_of_fiber : ∀ {f g : (z : Λ) × Ω z → ℝ},
      Measurable f → Measurable g →
      (∀ z : Λ, (fun ω => f ⟨z, ω⟩) =ᵐ[μ z] fun ω => g ⟨z, ω⟩) →
      f =ᵐ[ν] g := by
    intro f g hfm hgm hfib
    rw [hν_def, Filter.EventuallyEq,
      Measure.ae_sum_iff' (measurableSet_eq_fun hfm hgm)]
    intro z
    rw [(measurableEmbedding_sigma_mk z).ae_map_iff]
    exact hfib z
  have hΦ_add : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    change (hφ_memLp (x + y)).toLp _ = (hφ_memLp x).toLp _ + (hφ_memLp y).toLp _
    rw [← MemLp.toLp_add]; apply MemLp.toLp_congr
    refine hae_of_fiber (hφ_meas _) ((hφ_meas _).add (hφ_meas _)) ?_
    intro z
    have := Lp.coeFn_add (fL z x) (fL z y)
    rw [← hfL_add] at this; exact this
  have hΦ_smul : ∀ (c : ℝ) (x : X), Φ (c • x) = c • Φ x := by
    intro c x
    change (hφ_memLp (c • x)).toLp _ = c • (hφ_memLp x).toLp _
    rw [← MemLp.toLp_const_smul]; apply MemLp.toLp_congr
    refine hae_of_fiber (hφ_meas _) ((hφ_meas x).const_smul c) ?_
    intro z
    have := Lp.coeFn_smul c (fL z x)
    rw [← hfL_smul] at this; exact this
  let li : X →ₗᵢ[ℝ] Lp ℝ 1 ν :=
    { toLinearMap := { toFun := Φ, map_add' := hΦ_add, map_smul' := hΦ_smul }
      norm_map' := hΦ_norm }
  have hΦ_surj : Function.Surjective li := by
    intro g
    have hg_fiber_sm : ∀ z : Λ, StronglyMeasurable
        (fun ω => (g : (z : Λ) × Ω z → ℝ) ⟨z, ω⟩) :=
      fun z => (Lp.stronglyMeasurable g).comp_measurable
        (measurableEmbedding_sigma_mk z).measurable
    have hg_fiber_memLp : ∀ z : Λ,
        MemLp (fun ω => (g : (z : Λ) × Ω z → ℝ) ⟨z, ω⟩) 1 (μ z) := by
      intro z; refine ⟨(hg_fiber_sm z).aestronglyMeasurable, ?_⟩
      calc eLpNorm (fun ω => (g : _ → ℝ) ⟨z, ω⟩) 1 (μ z)
          = ∫⁻ ω, ‖(g : _ → ℝ) ⟨z, ω⟩‖ₑ ∂(μ z) := eLpNorm_one_eq_lintegral_enorm
        _ = ∫⁻ a, ‖(g : _ → ℝ) a‖ₑ ∂((μ z).map (Sigma.mk z)) :=
            ((measurableEmbedding_sigma_mk (β := Ω) z).lintegral_map
              fun a => ‖(g : _ → ℝ) a‖ₑ).symm
        _ ≤ ∫⁻ a, ‖(g : _ → ℝ) a‖ₑ ∂ν :=
            lintegral_mono' (Measure.le_sum _ z) (le_refl _)
        _ = eLpNorm (↑g) 1 ν := eLpNorm_one_eq_lintegral_enorm.symm
        _ = ↑‖g‖₊ := by
              rw [Lp.nnnorm_def, ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top _)]
        _ < ⊤ := ENNReal.coe_lt_top
    let g_z (z : ↑Λ) : Lp ℝ 1 (μ z) := (hg_fiber_memLp z).toLp _
    let y (z : ↑Λ) :
        ↥(Band.principalBand (↑z : X)).toSubmodule :=
      (T z).toLinearIsometryEquiv.symm (g_z z)
    have hTy : ∀ z, T z (y z) = g_z z := fun z =>
      (T z).toLinearIsometryEquiv.apply_symm_apply (g_z z)
    have heLpNorm_decomp : eLpNorm (↑g) 1 ν =
        ∑' z : ↑Λ,
          eLpNorm (fun ω => (g : _ → ℝ) ⟨z, ω⟩) 1 (μ z) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      change ∫⁻ x, ‖(g : _ → ℝ) x‖ₑ ∂Measure.sum
          (fun z : ↑Λ => Measure.map (Sigma.mk z) (μ z)) = _
      rw [lintegral_sum_measure]
      congr 1; ext z
      rw [(measurableEmbedding_sigma_mk (β := Ω) z).lintegral_map
            (fun a => ‖(g : _ → ℝ) a‖ₑ),
          ← eLpNorm_one_eq_lintegral_enorm]
    have hg_z_eLpNorm : ∀ z : ↑Λ,
        eLpNorm (fun ω => (g : _ → ℝ) ⟨z, ω⟩) 1 (μ z) =
          ↑‖g_z z‖₊ := by
      intro z
      rw [Lp.nnnorm_toLp, ENNReal.coe_toNNReal ((hg_fiber_memLp z).eLpNorm_ne_top)]
    have hy_norm : ∀ z, ‖(y z).val‖ = ‖g_z z‖ := fun z =>
      (T z).toLinearIsometryEquiv.symm.norm_map (g_z z)
    have hy_norm_summable : Summable (fun z => ‖(y z).val‖) := by
      simp_rw [hy_norm]
      have hne : (∑' z : ↑Λ, (↑‖g_z z‖₊ : ENNReal)) ≠ ⊤ := by
        rw [show (fun z : ↑Λ => (↑‖g_z z‖₊ : ENNReal)) =
              (fun z => eLpNorm (fun ω => (g : _ → ℝ) ⟨z, ω⟩) 1 (μ z))
          from funext (fun z => (hg_z_eLpNorm z).symm), ← heLpNorm_decomp]
        exact Lp.eLpNorm_ne_top g
      have := ENNReal.summable_toReal hne
      simpa [ENNReal.coe_toReal] using this
    have hy_summable : Summable (fun z => (y z).val) :=
      Summable.of_norm hy_norm_summable
    refine ⟨∑' z, (y z).val, ?_⟩
    change Φ (∑' z, (y z).val) = g
    have hP_tsum : ∀ z' : ↑Λ,
        Band.principalBandProjection (↑z' : X) (∑' z, (y z).val) =
          (y z').val := by
      intro z'
      have hcont : Continuous (Band.principalBandProjection (↑z' : X)) :=
        AddMonoidHomClass.continuous_of_bound
          (Band.principalBandProjection (↑z' : X)) 1 (fun x => by
            rw [one_mul]
            exact le_hasSum (hasSum_norm_principalBandProjection hΛ hpos x) z'
              (fun _ _ => norm_nonneg _))
      have hmap_tsum : (Band.principalBandProjection (↑z' : X))
          (∑' z : ↑Λ, (y z).val) =
          ∑' z : ↑Λ, (Band.principalBandProjection (↑z' : X)) (y z).val :=
        hy_summable.map_tsum
          (Band.principalBandProjection (↑z' : X)).toAddMonoidHom hcont
      rw [hmap_tsum]
      have hzero : ∀ z : ↑Λ, z ≠ z' →
          (Band.principalBandProjection (↑z' : X)) (y z).val = 0 := by
        intro z hz
        refine ProjectionBand.bandProjection_eq_zero_of_mem_dc
          (Band.principalProjectionBand (↑z' : X)) ?_
        rw [_root_.mem_disjointComplement_iff]
        intro a ha
        have hzne : (↑z : X) ≠ (↑z' : X) := fun hzz =>
          hz (Subtype.ext hzz)
        have hzz' : IsVLDisjoint (↑z : X) (↑z' : X) := hdisj.2 z.2 z'.2 hzne
        have hyz : (y z).val ∈ (Band.principalBand (↑z : X) : Set X) := (y z).2
        have ha' : a ∈ (Band.principalBand (↑z' : X) : Set X) := by
          rwa [Band.principalProjectionBand_coe (↑z' : X)] at ha
        have hyz_disj_z' : IsVLDisjoint (y z).val (↑z' : X) := by
          have hz_in : (↑z : X) ∈ ({(↑z' : X)} : Set X)ᵈ := by
            intro c hc
            rw [Set.mem_singleton_iff] at hc; rw [hc]
            exact hzz'
          have hyz_bg :
              (y z).val ∈ (_root_.Band.generated ({(↑z : X)} : Set X) : Set X) :=
            hyz
          have h_in_dcB :
              (y z).val ∈
                (_root_.Band.disjointComplement ({(↑z' : X)} : Set X) : Set X) :=
            _root_.Band.generated_le
              (show ({(↑z : X)} : Set X) ⊆
                  (_root_.Band.disjointComplement ({(↑z' : X)} : Set X) : Set X)
                from fun c hc => by
                  rw [Set.mem_singleton_iff] at hc; rw [hc]; exact hz_in)
              hyz_bg
          exact h_in_dcB (↑z' : X) (Set.mem_singleton _)
        have ha_dd : a ∈ ((({(↑z' : X)} : Set X)ᵈ)ᵈ : Set X) := by
          rw [_root_.Band.disjointComplement_disjointComplement_eq_generated]
          exact ha'
        have hyz_in_sd : (y z).val ∈ ({(↑z' : X)} : Set X)ᵈ := by
          intro c hc
          rw [Set.mem_singleton_iff] at hc; rw [hc]
          exact hyz_disj_z'
        have hayz : IsVLDisjoint a (y z).val := ha_dd _ hyz_in_sd
        exact isVLDisjoint_comm.mp hayz
      rw [tsum_eq_single z' hzero]
      exact ProjectionBand.bandProjection_eq_of_mem
        (Band.principalProjectionBand (↑z' : X))
        (show (y z').val ∈
            ((Band.principalProjectionBand (↑z' : X)) : Set X) from
          Band.principalProjectionBand_coe (↑z' : X) ▸ (y z').2)
    have hfL_tsum : ∀ z' : ↑Λ,
        fL z' (∑' z, (y z).val) = g_z z' := by
      intro z'
      change T z' ⟨Band.principalBandProjection (↑z' : X)
          (∑' z, (y z).val), _⟩ = g_z z'
      have heq : (⟨Band.principalBandProjection (↑z' : X) (∑' z, (y z).val),
          hP_mem z' _⟩ : (Band.principalBand (↑z' : X)).toSubmodule) =
          y z' := Subtype.ext (hP_tsum z')
      rw [heq, hTy z']
    apply Lp.ext
    exact ((hφ_memLp (∑' z, (y z).val)).coeFn_toLp).trans
      (hae_of_fiber (hφ_meas _) (Lp.stronglyMeasurable g).measurable
        (fun z' => by
          have hfib : (fun ω => φ (∑' z : ↑Λ, (y z).val) ⟨z', ω⟩) =
              fun ω => (fL z' (∑' z : ↑Λ, (y z).val) : Ω z' → ℝ) ω := rfl
          rw [hfib, hfL_tsum z']
          exact (hg_fiber_memLp z').coeFn_toLp))
  have hΦ_sup : ∀ x y : X, li (x ⊔ y) = li x ⊔ li y := by
    intro x y
    have hfL_sup : ∀ z : ↑Λ, fL z (x ⊔ y) = fL z x ⊔ fL z y := by
      intro z
      have hP := (Band.principalProjectionBand (z : X)).bandProjection_isVecLatHom.map_sup' x y
      have hsub : (⟨Band.principalBandProjection (↑z : X) (x ⊔ y),
          hP_mem z (x ⊔ y)⟩ :
          (Band.principalBand (↑z : X)).toSubmodule) =
        ⟨_, hP_mem z x⟩ ⊔ ⟨_, hP_mem z y⟩ := Subtype.ext hP
      change T z ⟨_, _⟩ = T z ⟨_, _⟩ ⊔ T z ⟨_, _⟩
      rw [hsub]; exact (T z).map_sup' _ _
    change Φ (x ⊔ y) = Φ x ⊔ Φ y
    apply Lp.ext
    exact ((hφ_memLp (x ⊔ y)).coeFn_toLp).trans
      ((hae_of_fiber (hφ_meas _) ((hφ_meas _).max (hφ_meas _))
        (fun z => by
          have h := Lp.coeFn_sup (fL z x) (fL z y)
          rw [← hfL_sup z] at h; exact h)).trans
        (((hφ_memLp x).coeFn_toLp.symm.sup
          (hφ_memLp y).coeFn_toLp.symm).trans
          (Lp.coeFn_sup _ _).symm))
  have hΦ_inf : ∀ x y : X, li (x ⊓ y) = li x ⊓ li y := by
    intro x y
    have hfL_inf : ∀ z : ↑Λ, fL z (x ⊓ y) = fL z x ⊓ fL z y := by
      intro z
      have hP := (Band.principalProjectionBand (z : X)).bandProjection_isVecLatHom.map_inf' x y
      have hsub : (⟨Band.principalBandProjection (↑z : X) (x ⊓ y),
          hP_mem z (x ⊓ y)⟩ :
          (Band.principalBand (↑z : X)).toSubmodule) =
        ⟨_, hP_mem z x⟩ ⊓ ⟨_, hP_mem z y⟩ := Subtype.ext hP
      change T z ⟨_, _⟩ = T z ⟨_, _⟩ ⊓ T z ⟨_, _⟩
      rw [hsub]; exact (T z).map_inf' _ _
    change Φ (x ⊓ y) = Φ x ⊓ Φ y
    apply Lp.ext
    exact ((hφ_memLp (x ⊓ y)).coeFn_toLp).trans
      ((hae_of_fiber (hφ_meas _) ((hφ_meas _).min (hφ_meas _))
        (fun z => by
          have h := Lp.coeFn_inf (fL z x) (fL z y)
          rw [← hfL_inf z] at h; exact h)).trans
        (((hφ_memLp x).coeFn_toLp.symm.inf
          (hφ_memLp y).coeFn_toLp.symm).trans
          (Lp.coeFn_inf _ _).symm))
  exact ⟨BanachLatEquiv.mk (LinearIsometryEquiv.ofSurjective li hΦ_surj)
    (by intro a b; simp [LinearIsometryEquiv.ofSurjective, hΦ_sup a b])
    (by intro a b; simp [LinearIsometryEquiv.ofSurjective, hΦ_inf a b])⟩

variable {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- **`M(K)` is an `L¹` space.** The Banach lattice of regular signed Borel
measures on a compact Hausdorff space is Banach-lattice isometric to `L¹(ν)`
for some measure `ν`. -/
theorem exists_L1_banachLatEquiv :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (ν : Measure Ω),
      Nonempty (BanachLatEquiv (MofK K) (Lp ℝ 1 ν)) := by
  exact exists_L1_banachLatEquiv_of_principalBandModels (X := MofK K) fun μ _ => by
    obtain ⟨Ω, mΩ, ν, _hν, hT⟩ := MofK.exists_principalBand_banachLatEquivL1 μ
    exact ⟨Ω, mΩ, ν, hT⟩

end MofK
