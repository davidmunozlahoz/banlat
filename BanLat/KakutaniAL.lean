import BanLat.ALSpace
import BanLat.Bidual
import BanLat.Examples.Lp.Sublattice
import BanLat.Examples.MofK
import BanLat.Examples.SignedMeasure
import BanLat.KakutaniAM

/-!
# Kakutani's representation theorem for AL-spaces

Every AL-space is Banach-lattice isometrically isomorphic to `L¹(μ)` for some
measure `μ`. The proof reduces to L¹-representation of principal bands: one
embeds `X` as a closed sublattice of `M(K) ≅ L¹(μ)` via the duality
`X ↪ X** ≅ C(K)* ≅ M(K)` (using Kakutani's theorem for AM-spaces with unit
applied to `X*`), and then invokes a "locally L¹ ⇒ L¹" principle.
-/

open MeasureTheory

universe u

namespace ALSpace

/-! ### Preparatory lemmas

Every AL-space has an order continuous norm (`ALSpace.instIsOrderContinuousNorm`);
the remaining preparatory ingredients are stated below: a locally-L¹ to globally-L¹
principle, the L¹-representation of the Banach lattice of finite signed measures,
and the L¹-representation of a closed sublattice of `L¹(μ)` containing an a.e.
strictly positive element. -/

variable (X : Type u) [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X]

section SigmaGluing

/-! #### Sigma-type measure space infrastructure -/

open Band in
/-- Band projections for disjoint elements produce VL-disjoint results.
If `a ⊥ b`, then `Pₐ(x) ⊥ P_b(x)` for all `x`. -/
private lemma isVLDisjoint_principalBandProjection
    {X : Type*} [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    [IsVLArchimedean X] [HasPrincipalProjectionProperty X]
    {a b : X} (hdis : IsVLDisjoint a b) (x : X) :
    IsVLDisjoint (principalBandProjection a x)
      (principalBandProjection b x) := by
  have hPa : principalBandProjection a x ∈
      (principalBand a : Set X) := by
    have := (principalProjectionBand a).bandProjection_mem x
    rw [← principalProjectionBand_coe]; exact this
  have hPb_in_Bd : principalBandProjection b x ∈
      disjointComplement
        ((principalBand a : Band X) : Set X) := by
    have hPb : principalBandProjection b x ∈
        (principalBand b : Set X) := by
      have := (principalProjectionBand b).bandProjection_mem x
      rw [← principalProjectionBand_coe]; exact this
    have hb_mem : b ∈ disjointComplement
        ((principalBand a : Band X) : Set X) := by
      have hset : ((principalBand a : Band X) : Set X) =
          (({a} : Set X)ᵈ)ᵈ :=
        (disjointComplement_disjointComplement_eq_bandGenerated
          (A := ({a} : Set X))).symm
      rw [hset,
        disjointComplement_disjointComplement_disjointComplement]
      intro c hc; rw [Set.mem_singleton_iff] at hc; rw [hc]
      exact isVLDisjoint_comm.mp hdis
    exact bandGenerated_le (show {b} ⊆
        ((disjointComplementBand
          ((principalBand a : Band X) : Set X)) : Set X) from
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]
        exact hb_mem)
      hPb
  exact isVLDisjoint_comm.mpr (hPb_in_Bd _ hPa)

/-- For two non-negative VL-disjoint elements in an AL-space, their sum
equals their supremum. -/
private lemma add_eq_sup_of_disjoint_nonneg
    {X : Type*} [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] {a b : X}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hdis : IsVLDisjoint a b) :
    a + b = a ⊔ b := by
  have hinf : a ⊓ b = 0 :=
    inf_eq_zero_of_isVLDisjoint ha hb hdis
  have := inf_add_sup a b
  rw [hinf, zero_add] at this
  exact this.symm

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

/-- The band projection onto a projection band acts as the identity on elements
already in the band. -/
private lemma ProjectionBand.bandProjection_eq_of_mem
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    (P : ProjectionBand Y) {x : Y} (hx : x ∈ (P : Set Y)) :
    P.bandProjection x = x := by
  have : x ∈ Set.range P.bandProjection :=
    P.range_bandProjection ▸ hx
  obtain ⟨y, rfl⟩ := this
  rw [← LinearMap.comp_apply, P.bandProjection_sq]

/-- The band projection onto a projection band vanishes on elements of the
disjoint complement. -/
private lemma ProjectionBand.bandProjection_eq_zero_of_mem_dc
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    (P : ProjectionBand Y) {x : Y}
    (hx : x ∈ disjointComplement (P.toBand : Set Y)) :
    P.bandProjection x = 0 :=
  (P.decomposition_unique
    (P.bandProjection_mem x) (P.id_sub_bandProjection_mem x)
    (P.toBand.toSubmodule.zero_mem) hx
    (by abel) (zero_add x).symm).1

/-- In an AL-space, a hasSum of non-negative elements induces a hasSum of
their norms. -/
private lemma hasSum_norm_of_nonneg_hasSum
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [ALSpace Y] {ι : Type*} {f : ι → Y} {x : Y}
    (hf : ∀ i, 0 ≤ f i) (hs : HasSum f x) :
    HasSum (fun i => ‖f i‖) ‖x‖ := by
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

/-- Band projection membership in the principal band's submodule. -/
private lemma Band.principalBandProjection_mem_toSubmodule
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [BanachLattice Y] [IsOrderContinuousNorm Y] (a x : Y) :
    Band.principalBandProjection a x ∈
      (Band.principalBand a).toSubmodule := by
  have := (Band.principalProjectionBand a).bandProjection_mem x
  change _ ∈ ((Band.principalProjectionBand a : ProjectionBand Y) : Set Y) at this
  rw [Band.principalProjectionBand_coe] at this; exact this

/-- The norms of band projections over a maximal disjoint family are summable
with sum `‖x‖` in an AL-space. -/
private lemma hasSum_norm_principalBandProjection
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [ALSpace Y] {Λ : Set Y} (hΛ : IsMaximalDisjoint Λ) (x : Y) :
    HasSum (fun z : ↑Λ =>
      ‖Band.principalBandProjection (z : Y) x‖) ‖x‖ := by
  set P := fun z : ↑Λ => Band.principalBandProjection (z : Y) with hP_def
  set xp := x⁺; set xn := x⁻
  have hxp_nn : (0 : Y) ≤ xp := posPart_nonneg x
  have hxn_nn : (0 : Y) ≤ xn := negPart_nonneg x
  have hsp := hasSum_norm_of_nonneg_hasSum (Y := Y)
    (fun (z : ↑Λ) =>
      (Band.principalProjectionBand (z : Y)).bandProjection_nonneg hxp_nn)
    (BanachLattice.hasSum_principalBandProjection hΛ xp)
  have hsn := hasSum_norm_of_nonneg_hasSum (Y := Y)
    (fun (z : ↑Λ) =>
      (Band.principalProjectionBand (z : Y)).bandProjection_nonneg hxn_nn)
    (BanachLattice.hasSum_principalBandProjection hΛ xn)
  -- The types of hsp/hsn use principalProjectionBand.bandProjection;
  -- convert to principalBandProjection (which is the same definitionally)
  change HasSum (fun z : ↑Λ => ‖P z xp‖) ‖xp‖ at hsp
  change HasSum (fun z : ↑Λ => ‖P z xn‖) ‖xn‖ at hsn
  have hle : ∀ z : ↑Λ, ‖P z x‖ ≤ ‖P z xp‖ + ‖P z xn‖ := by
    intro z
    rw [show x = xp - xn from (posPart_sub_negPart x).symm, map_sub]
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
    conv_lhs => rw [← (BanachLattice.hasSum_principalBandProjection hΛ x).tsum_eq]
    exact norm_tsum_le_tsum_norm hsum
  exact (le_antisymm hub hlb) ▸ hsum.hasSum

/-- **Locally L¹ implies L¹.** If every principal band `B_x` of an AL-space `X`
is Banach-lattice isometric to some `L¹(μ)`, then `X` itself is Banach-lattice
isometric to some `L¹(ν)`. The proof picks a maximal disjoint family `Λ ⊆ X₊`,
decomposes each element of `X` as a countable disjoint sum of its projections
onto the principal bands of members of `Λ`, and glues the individual
L¹-representations along the disjoint union of their underlying measure
spaces. -/
theorem exists_L1_banachLatEquiv_of_principalBand [ALSpace X]
    (h : ∀ x : X, 0 ≤ x →
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
        Nonempty (BanachLatEquiv
          ↥(Band.principalBand x).toSubmodule (Lp ℝ 1 μ))) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (ν : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 ν)) := by
  classical
  -- Step 1: Choose a maximal disjoint family Λ ⊆ X₊
  obtain ⟨Λ, hΛ⟩ := exists_isMaximalDisjoint X
  have hpos : ∀ z ∈ Λ, 0 < z := hΛ.prop.1
  have hdisj : IsDisjointSet Λ := hΛ.prop.2
  -- Step 2: For each z ∈ Λ, choose an L¹-representation of B_z
  choose Ω mΩ μ hT using fun (z : Λ) =>
    h z.1 (le_of_lt (hpos z.1 z.2))
  have T : ∀ z : Λ, BanachLatEquiv
      (Band.principalBand (z : X)).toSubmodule
      (Lp ℝ 1 (μ z)) :=
    fun z => (hT z).some
  -- Step 3: Construct the sigma measure space
  letI : ∀ z : Λ, MeasurableSpace (Ω z) := mΩ
  -- Step 4: Witness
  refine ⟨(z : Λ) × Ω z, inferInstance,
    Measure.sum (fun z => (μ z).map (Sigma.mk z)), ?_⟩
  -- Abbreviation for the sum measure
  set ν := Measure.sum (fun z : Λ => (μ z).map (Sigma.mk z)) with hν_def
  -- Band projection membership
  have hP_mem : ∀ (z : Λ) (x : X),
      Band.principalBandProjection (z : X) x ∈
        (Band.principalBand (z : X)).toSubmodule :=
    fun z x => Band.principalBandProjection_mem_toSubmodule (z : X) x
  -- Fiber map: project onto B_z and apply T_z
  let fL (z : Λ) (x : X) : Lp ℝ 1 (μ z) :=
    T z ⟨Band.principalBandProjection (z : X) x, hP_mem z x⟩
  -- fL z is linear in x (as an Lp-valued map)
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
  -- The raw forward function on the sigma type
  let φ (x : X) : (z : Λ) × Ω z → ℝ := fun ⟨z, ω⟩ => fL z x ω
  -- Measurability: each fiber is an Lp function, hence strongly measurable
  have hφ_meas : ∀ x, Measurable (φ x) := by
    intro x; apply measurable_sigma_of_fibers
    intro z; exact (Lp.stronglyMeasurable (fL z x)).measurable
  -- eLpNorm identity: eLpNorm (φ x) 1 ν = Σ_z ‖fL z x‖₊ (ENNReal)
  have heLpNorm : ∀ x, eLpNorm (φ x) 1 ν = ∑' z : Λ, ↑‖fL z x‖₊ := by
    intro x
    rw [eLpNorm_one_eq_lintegral_enorm, hν_def, lintegral_sum_measure]
    congr 1; ext z
    rw [(measurableEmbedding_sigma_mk z).lintegral_map,
      ← eLpNorm_one_eq_lintegral_enorm, Lp.nnnorm_def,
      ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top _)]
  -- HasSum identity for norms: HasSum (fun z => ‖fL z x‖) ‖x‖
  have hfL_norm_eq : ∀ z x,
      ‖fL z x‖ = ‖Band.principalBandProjection (z : X) x‖ :=
    fun z x => (T z).toLinearIsometryEquiv.norm_map _
  have hfL_hasSum : ∀ x, HasSum (fun z : Λ => ‖fL z x‖) ‖x‖ := by
    intro x; simp_rw [hfL_norm_eq]
    exact hasSum_norm_principalBandProjection hΛ x
  -- NNReal summability helper
  have hfL_nnsummable : ∀ x,
      Summable (fun z : Λ => ‖fL z x‖₊) :=
    fun x => NNReal.summable_coe.mp
      (by simp_rw [coe_nnnorm]; exact (hfL_hasSum x).summable)
  -- MemLp: the forward function is in L¹
  have hφ_memLp : ∀ x, MemLp (φ x) 1 ν := by
    intro x
    exact ⟨(hφ_meas x).stronglyMeasurable.aestronglyMeasurable,
      heLpNorm x ▸ (ENNReal.coe_tsum (hfL_nnsummable x)).symm ▸
        ENNReal.coe_lt_top⟩
  -- Define the Lp-valued forward map
  let Φ (x : X) : Lp ℝ 1 ν := (hφ_memLp x).toLp (φ x)
  -- Norm identity: ‖Φ x‖ = ‖x‖
  have hΦ_norm : ∀ x, ‖Φ x‖ = ‖x‖ := by
    intro x; rw [Lp.norm_toLp, heLpNorm x]
    have : (∑' z : ↑Λ, (↑‖fL z x‖₊ : ENNReal)).toReal = ∑' z, ‖fL z x‖ := by
      rw [← ENNReal.coe_tsum (hfL_nnsummable x), ENNReal.coe_toReal,
          NNReal.coe_tsum]
      simp [coe_nnnorm]
    rw [this]; exact (hfL_hasSum x).tsum_eq
  -- a.e. equality on sigma type from fiber-wise a.e. equality
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
  -- Additivity: Φ(x + y) = Φ(x) + Φ(y)
  have hΦ_add : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    change (hφ_memLp (x + y)).toLp _ = (hφ_memLp x).toLp _ + (hφ_memLp y).toLp _
    rw [← MemLp.toLp_add]; apply MemLp.toLp_congr
    refine hae_of_fiber (hφ_meas _) ((hφ_meas _).add (hφ_meas _)) ?_
    intro z
    have := Lp.coeFn_add (fL z x) (fL z y)
    rw [← hfL_add] at this; exact this
  -- Scalar: Φ(c • x) = c • Φ(x)
  have hΦ_smul : ∀ (c : ℝ) (x : X), Φ (c • x) = c • Φ x := by
    intro c x
    change (hφ_memLp (c • x)).toLp _ = c • (hφ_memLp x).toLp _
    rw [← MemLp.toLp_const_smul]; apply MemLp.toLp_congr
    refine hae_of_fiber (hφ_meas _) ((hφ_meas x).const_smul c) ?_
    intro z
    have := Lp.coeFn_smul c (fL z x)
    rw [← hfL_smul] at this; exact this
  have hΦ_zero : Φ 0 = 0 := by
    have h0 := hΦ_add 0 0
    rwa [add_zero, left_eq_add] at h0
  -- Construct the linear isometry
  let li : X →ₗᵢ[ℝ] Lp ℝ 1 ν :=
    { toLinearMap := { toFun := Φ, map_add' := hΦ_add, map_smul' := hΦ_smul }
      norm_map' := hΦ_norm }
  -- Surjectivity
  have hΦ_surj : Function.Surjective li := by
    intro g
    -- For each z, restrict g to fiber z and show it's in Lp(μ z)
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
    -- Fiber Lp elements of g
    let g_z (z : ↑Λ) : Lp ℝ 1 (μ z) := (hg_fiber_memLp z).toLp _
    -- Preimage in each band via T⁻¹
    let y (z : ↑Λ) :
        ↥(Band.principalBand (↑z : X)).toSubmodule :=
      (T z).toLinearIsometryEquiv.symm (g_z z)
    -- T z maps y z back to g_z z
    have hTy : ∀ z, T z (y z) = g_z z := fun z =>
      (T z).toLinearIsometryEquiv.apply_symm_apply (g_z z)
    -- eLpNorm decomposition: eLpNorm g 1 ν = ∑' z, eLpNorm(g fiber z) 1 (μ z)
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
    -- Fiber eLpNorm as nnnorm of g_z
    have hg_z_eLpNorm : ∀ z : ↑Λ,
        eLpNorm (fun ω => (g : _ → ℝ) ⟨z, ω⟩) 1 (μ z) =
          ↑‖g_z z‖₊ := by
      intro z
      rw [Lp.nnnorm_toLp, ENNReal.coe_toNNReal ((hg_fiber_memLp z).eLpNorm_ne_top)]
    -- Norm of y z = norm of g_z z (isometry)
    have hy_norm : ∀ z, ‖(y z).val‖ = ‖g_z z‖ := fun z =>
      (T z).toLinearIsometryEquiv.symm.norm_map (g_z z)
    -- Summability of fiber norms
    have hy_norm_summable : Summable (fun z => ‖(y z).val‖) := by
      simp_rw [hy_norm]
      have hne : (∑' z : ↑Λ, (↑‖g_z z‖₊ : ENNReal)) ≠ ⊤ := by
        rw [show (fun z : ↑Λ => (↑‖g_z z‖₊ : ENNReal)) =
              (fun z => eLpNorm (fun ω => (g : _ → ℝ) ⟨z, ω⟩) 1 (μ z))
          from funext (fun z => (hg_z_eLpNorm z).symm), ← heLpNorm_decomp]
        exact Lp.eLpNorm_ne_top g
      have := ENNReal.summable_toReal hne
      simpa [ENNReal.coe_toReal] using this
    -- Summability in X
    have hy_summable : Summable (fun z => (y z).val) :=
      Summable.of_norm hy_norm_summable
    -- Candidate preimage
    refine ⟨∑' z, (y z).val, ?_⟩
    -- Show Φ(∑' z, (y z).val) = g
    change Φ (∑' z, (y z).val) = g
    -- Key: P_{z'}(∑' z, (y z).val) = (y z').val
    -- because P_{z'} is continuous linear and kills disjoint band elements
    have hP_tsum : ∀ z' : ↑Λ,
        Band.principalBandProjection (↑z' : X) (∑' z, (y z).val) =
          (y z').val := by
      intro z'
      -- P_{z'} commutes with tsum (continuous linear map)
      have hcont : Continuous (Band.principalBandProjection (↑z' : X)) :=
        AddMonoidHomClass.continuous_of_bound
          (Band.principalBandProjection (↑z' : X)) 1 (fun x => by
            rw [one_mul]
            exact le_hasSum (hasSum_norm_principalBandProjection hΛ x) z'
              (fun _ _ => norm_nonneg _))
      have hmap_tsum : (Band.principalBandProjection (↑z' : X))
          (∑' z : ↑Λ, (y z).val) =
          ∑' z : ↑Λ, (Band.principalBandProjection (↑z' : X)) (y z).val :=
        hy_summable.map_tsum
          (Band.principalBandProjection (↑z' : X)).toAddMonoidHom hcont
      rw [hmap_tsum]
      -- tsum of P_{z'}((y z).val) = (y z').val
      -- P_{z'}((y z).val) = (y z).val if z = z', 0 otherwise
      have hzero : ∀ z : ↑Λ, z ≠ z' →
          (Band.principalBandProjection (↑z' : X)) (y z).val = 0 := by
        intro z hz
        refine ProjectionBand.bandProjection_eq_zero_of_mem_dc
          (Band.principalProjectionBand (↑z' : X)) ?_
        -- Show (y z).val is disjoint from every element of principalBand z'
        rw [Band.mem_disjointComplement_iff]
        intro a ha
        -- z and z' are VL-disjoint
        have hzne : (↑z : X) ≠ (↑z' : X) := fun hzz =>
          hz (Subtype.ext hzz)
        have hzz' : IsVLDisjoint (↑z : X) (↑z' : X) := hdisj z.2 z'.2 hzne
        -- (y z).val ∈ principalBand z
        have hyz : (y z).val ∈ (Band.principalBand (↑z : X) : Set X) := (y z).2
        -- a ∈ principalBand z' (since principalProjectionBand's toBand is principalBand)
        have ha' : a ∈ (Band.principalBand (↑z' : X) : Set X) := by
          have heq : ((Band.principalProjectionBand (↑z' : X)).toBand : Set X) =
              (Band.principalBand (↑z' : X) : Set X) :=
            Band.principalProjectionBand_coe (↑z' : X)
          rwa [heq] at ha
        -- principalBand z ⊆ disjointComplement {z'}
        -- Since z ⊥ z', we have z ∈ {z'}ᵈ, so bandGenerated {z} ⊆ {z'}ᵈᵈᵈ = {z'}ᵈ.
        -- Thus (y z).val ∈ {z'}ᵈ (VL-disjoint from z')
        have hyz_disj_z' : IsVLDisjoint (y z).val (↑z' : X) := by
          have hz_in : (↑z : X) ∈ ({(↑z' : X)} : Set X)ᵈ := by
            intro c hc
            rw [Set.mem_singleton_iff] at hc; rw [hc]
            exact hzz'
          have hsub : ({(↑z : X)} : Set X) ⊆ ({(↑z' : X)} : Set X)ᵈ := by
            intro c hc
            rw [Set.mem_singleton_iff] at hc; rw [hc]; exact hz_in
          -- (y z).val ∈ bandGenerated {z} = principalBand z
          have hyz_bg : (y z).val ∈ (Band.bandGenerated ({(↑z : X)} : Set X) : Set X) :=
            hyz
          -- Since {z} ⊆ {z'}ᵈ, and {z'}ᵈ is a disjointComplementBand
          -- (hence closed under bandGenerated), we have
          -- bandGenerated {z} ⊆ ({z'}ᵈᵈ)ᵈ = {z'}ᵈ (by triple-complement).
          -- Via `disjointComplementBand` of the singleton ({z'}ᵈ as a band):
          have h_in_dcB :
              (y z).val ∈ (Band.disjointComplementBand ({(↑z' : X)} : Set X) : Set X) :=
            Band.bandGenerated_le
              (show ({(↑z : X)} : Set X) ⊆
                  (Band.disjointComplementBand ({(↑z' : X)} : Set X) : Set X)
                from fun c hc => by
                  rw [Set.mem_singleton_iff] at hc; rw [hc]; exact hz_in)
              hyz_bg
          -- Unfold the coercion
          exact h_in_dcB (↑z' : X) (Set.mem_singleton _)
        -- Now: a ∈ principalBand z' = {z'}ᵈᵈ. Since y z ∈ {z'}ᵈ,
        -- by triple-complement property a ⊥ y z, hence y z ⊥ a.
        have ha_dd : a ∈ ((({(↑z' : X)} : Set X)ᵈ)ᵈ : Set X) := by
          rw [Band.disjointComplement_disjointComplement_eq_bandGenerated]
          exact ha'
        -- y z ∈ {z'}ᵈ (singleton disjoint complement)
        have hyz_in_sd : (y z).val ∈ ({(↑z' : X)} : Set X)ᵈ := by
          intro c hc
          rw [Set.mem_singleton_iff] at hc; rw [hc]
          exact hyz_disj_z'
        -- a ⊥ (y z).val via triple complement
        have hayz : IsVLDisjoint a (y z).val := ha_dd _ hyz_in_sd
        exact isVLDisjoint_comm.mp hayz
      rw [tsum_eq_single z' hzero]
      -- P_{z'}((y z').val) = (y z').val
      exact ProjectionBand.bandProjection_eq_of_mem
        (Band.principalProjectionBand (↑z' : X))
        (show (y z').val ∈
            ((Band.principalProjectionBand (↑z' : X)) : Set X) from
          Band.principalProjectionBand_coe (↑z' : X) ▸ (y z').2)
    -- fL z'(∑' z, (y z).val) = T z' ⟨(y z').val, _⟩ = g_z z'
    have hfL_tsum : ∀ z' : ↑Λ,
        fL z' (∑' z, (y z).val) = g_z z' := by
      intro z'
      change T z' ⟨Band.principalBandProjection (↑z' : X)
          (∑' z, (y z).val), _⟩ = g_z z'
      have heq : (⟨Band.principalBandProjection (↑z' : X) (∑' z, (y z).val),
          hP_mem z' _⟩ : (Band.principalBand (↑z' : X)).toSubmodule) =
          y z' := Subtype.ext (hP_tsum z')
      rw [heq, hTy z']
    -- Φ(∑' z, (y z).val) = g via fiberwise a.e. equality
    apply Lp.ext
    exact ((hφ_memLp (∑' z, (y z).val)).coeFn_toLp).trans
      (hae_of_fiber (hφ_meas _) (Lp.stronglyMeasurable g).measurable
        (fun z' => by
          -- fiber z': φ(tsum ...) ⟨z', ω⟩ = (fL z' (tsum ...))(ω)
          --         =ᵐ (g_z z')(ω) = g ⟨z', ω⟩
          have hfib : (fun ω => φ (∑' z : ↑Λ, (y z).val) ⟨z', ω⟩) =
              fun ω => (fL z' (∑' z : ↑Λ, (y z).val) : Ω z' → ℝ) ω := rfl
          rw [hfib, hfL_tsum z']
          exact (hg_fiber_memLp z').coeFn_toLp))
  -- Lattice preservation
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

/-- The Banach lattice `SignedMeasure α` of finite signed measures on any
measurable space is lattice isometrically isomorphic to some `L¹(μ)`. Follows
from the Radon–Nikodym identification of each principal band with an `L¹`,
combined with `exists_L1_banachLatEquiv_of_principalBand`. -/
theorem exists_L1_banachLatEquiv_signedMeasure {α : Type u} [MeasurableSpace α] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv (SignedMeasure α) (Lp ℝ 1 μ)) :=
  exists_L1_banachLatEquiv_of_principalBand (SignedMeasure α) fun _ hs =>
    ⟨_, _, _, ⟨SignedMeasure.principalBandBanachLatEquivL1 hs⟩⟩

/-- **L¹-representation of `M(K)`.** For every nonempty compact Hausdorff
space `K`, the Banach lattice `M(K)` of regular signed Borel measures on `K`
is Banach-lattice isometrically isomorphic to some `L¹(μ)`. The proof
composes the identification `M(K) ≃ SignedMeasure (baire K)`
(`MofK.baireEquiv`) with the L¹-representation of `SignedMeasure`
(`exists_L1_banachLatEquiv_signedMeasure`). -/
theorem exists_L1_banachLatEquiv_MofK {K : Type u} [TopologicalSpace K]
    [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [Nonempty K] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv (MofK K) (Lp ℝ 1 μ)) := by
  obtain ⟨Ω, mΩ, μ, ⟨T⟩⟩ := @exists_L1_banachLatEquiv_signedMeasure K (baire K)
  refine ⟨Ω, mΩ, μ, ⟨?_⟩⟩
  exact {
    toLinearIsometryEquiv :=
      MofK.baireEquiv.toLinearIsometryEquiv.trans T.toLinearIsometryEquiv
    map_sup' := fun x y => by
      have hφ : MofK.baireEquiv (x ⊔ y) =
          MofK.baireEquiv x ⊔ MofK.baireEquiv y := MofK.baireEquiv.map_sup' x y
      have hT : T (MofK.baireEquiv x ⊔ MofK.baireEquiv y) =
          T (MofK.baireEquiv x) ⊔ T (MofK.baireEquiv y) := T.map_sup' _ _
      change T (MofK.baireEquiv (x ⊔ y)) =
        T (MofK.baireEquiv x) ⊔ T (MofK.baireEquiv y)
      rw [hφ]; exact hT
    map_inf' := fun x y => by
      have hφ : MofK.baireEquiv (x ⊓ y) =
          MofK.baireEquiv x ⊓ MofK.baireEquiv y := MofK.baireEquiv.map_inf' x y
      have hT : T (MofK.baireEquiv x ⊓ MofK.baireEquiv y) =
          T (MofK.baireEquiv x) ⊓ T (MofK.baireEquiv y) := T.map_inf' _ _
      change T (MofK.baireEquiv (x ⊓ y)) =
        T (MofK.baireEquiv x) ⊓ T (MofK.baireEquiv y)
      rw [hφ]; exact hT }

section WithDensityChangeOfMeasure

/-! #### Surjectivity and lattice preservation of `withDensitySMulLI`

When the density function `f_nn` is a.e. strictly positive, the linear isometry
`withDensitySMulLI μ hf_nn_meas : Lp ℝ 1 (μ.withDensity f_nn) →ₗᵢ[ℝ] Lp ℝ 1 μ`
is surjective and preserves the lattice operations `⊔`, `⊓`. -/

private lemma withDensitySMulLI_surjective_of_ae_pos
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f_nn : α → NNReal} (hf_nn_meas : Measurable f_nn)
    (hf_pos : ∀ᵐ ω ∂μ, (0 : ℝ) < f_nn ω) :
    Function.Surjective (withDensitySMulLI (E := ℝ) μ hf_nn_meas) := by
  intro g
  let h : α → ℝ := fun ω => (g ω) / (f_nn ω : ℝ)
  have hh_meas : Measurable h :=
    (Lp.stronglyMeasurable g).measurable.div
      (measurable_coe_nnreal_real.comp hf_nn_meas)
  have hmul_ae_μ : (fun ω => f_nn ω • h ω) =ᵐ[μ] ⇑g := by
    filter_upwards [hf_pos] with ω hω
    change (f_nn ω : ℝ) * (g ω / (f_nn ω : ℝ)) = g ω
    field_simp
  have hmul_int : Integrable (fun ω => f_nn ω • h ω) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp g)).congr hmul_ae_μ.symm
  have hh_int_ν :
      Integrable h (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal))) := by
    rw [integrable_withDensity_iff_integrable_smul hf_nn_meas]
    exact hmul_int
  have hh_memLp :
      MemLp h 1 (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal))) :=
    memLp_one_iff_integrable.mpr hh_int_ν
  refine ⟨hh_memLp.toLp h, ?_⟩
  rw [withDensitySMulLI_apply]
  apply Lp.ext
  have hh_toLp_ν :
      ⇑(hh_memLp.toLp h) =ᵐ[μ.withDensity
        (fun ω => ((f_nn ω : NNReal) : ENNReal))] h :=
    hh_memLp.coeFn_toLp
  have hh_toLp_μ : ∀ᵐ ω ∂μ,
      (f_nn ω : ENNReal) ≠ 0 → (hh_memLp.toLp h : α → ℝ) ω = h ω :=
    (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp hh_toLp_ν
  have hae : (fun x => f_nn x • (hh_memLp.toLp h : α → ℝ) x) =ᵐ[μ] ⇑g := by
    filter_upwards [hmul_ae_μ, hf_pos, hh_toLp_μ] with ω hmul hω hω_eq
    have hne : (f_nn ω : ENNReal) ≠ 0 := by exact_mod_cast hω.ne'
    rw [hω_eq hne]; exact hmul
  calc ⇑(MemLp.toLp (fun x => f_nn x • (hh_memLp.toLp h : α → ℝ) x) _)
      =ᵐ[μ] fun x => f_nn x • (hh_memLp.toLp h : α → ℝ) x := MemLp.coeFn_toLp _
    _ =ᵐ[μ] ⇑g := hae

private lemma withDensitySMulLI_map_sup
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f_nn : α → NNReal} (hf_nn_meas : Measurable f_nn)
    (v w : Lp ℝ 1 (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal)))) :
    withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊔ w) =
      withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊔
        withDensitySMulLI (E := ℝ) μ hf_nn_meas w := by
  apply Lp.ext
  have hLHS : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊔ w)) =ᵐ[μ]
      fun x => f_nn x • ((v ⊔ w : Lp ℝ 1 _) : α → ℝ) x := by
    rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
  have hRv : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v) =ᵐ[μ]
      fun x => f_nn x • (v : α → ℝ) x := by
    rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
  have hRw : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      fun x => f_nn x • (w : α → ℝ) x := by
    rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
  have hsup_coeFn :
      ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊔
          withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      (fun x => f_nn x • (v : α → ℝ) x) ⊔ (fun x => f_nn x • (w : α → ℝ) x) := by
    filter_upwards [Lp.coeFn_sup (withDensitySMulLI (E := ℝ) μ hf_nn_meas v)
      (withDensitySMulLI (E := ℝ) μ hf_nn_meas w), hRv, hRw] with ω h h1 h2
    rw [h]; exact congr_arg₂ _ h1 h2
  have hvw_μ : ∀ᵐ ω ∂μ, (f_nn ω : ENNReal) ≠ 0 →
      ((v ⊔ w : Lp ℝ 1 _) : α → ℝ) ω = max ((v : α → ℝ) ω) ((w : α → ℝ) ω) :=
    (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp (Lp.coeFn_sup v w)
  filter_upwards [hLHS, hsup_coeFn, hvw_μ] with ω hL hR hvw
  rw [hL, hR]
  by_cases hne : (f_nn ω : ENNReal) = 0
  · have hzero : f_nn ω = 0 := by exact_mod_cast hne
    simp [hzero]
  · rw [hvw hne]
    simp only [Pi.sup_apply]
    rw [NNReal.smul_def, NNReal.smul_def, NNReal.smul_def,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    exact mul_max_of_nonneg _ _ (NNReal.coe_nonneg _)

private lemma withDensitySMulLI_map_inf
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f_nn : α → NNReal} (hf_nn_meas : Measurable f_nn)
    (v w : Lp ℝ 1 (μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal)))) :
    withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊓ w) =
      withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊓
        withDensitySMulLI (E := ℝ) μ hf_nn_meas w := by
  apply Lp.ext
  have hLHS : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas (v ⊓ w)) =ᵐ[μ]
      fun x => f_nn x • ((v ⊓ w : Lp ℝ 1 _) : α → ℝ) x := by
    rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
  have hRv : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v) =ᵐ[μ]
      fun x => f_nn x • (v : α → ℝ) x := by
    rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
  have hRw : ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      fun x => f_nn x • (w : α → ℝ) x := by
    rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
  have hinf_coeFn :
      ⇑(withDensitySMulLI (E := ℝ) μ hf_nn_meas v ⊓
          withDensitySMulLI (E := ℝ) μ hf_nn_meas w) =ᵐ[μ]
      (fun x => f_nn x • (v : α → ℝ) x) ⊓ (fun x => f_nn x • (w : α → ℝ) x) := by
    filter_upwards [Lp.coeFn_inf (withDensitySMulLI (E := ℝ) μ hf_nn_meas v)
      (withDensitySMulLI (E := ℝ) μ hf_nn_meas w), hRv, hRw] with ω h h1 h2
    rw [h]; exact congr_arg₂ _ h1 h2
  have hvw_μ : ∀ᵐ ω ∂μ, (f_nn ω : ENNReal) ≠ 0 →
      ((v ⊓ w : Lp ℝ 1 _) : α → ℝ) ω = min ((v : α → ℝ) ω) ((w : α → ℝ) ω) :=
    (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp (Lp.coeFn_inf v w)
  filter_upwards [hLHS, hinf_coeFn, hvw_μ] with ω hL hR hvw
  rw [hL, hR]
  by_cases hne : (f_nn ω : ENNReal) = 0
  · have hzero : f_nn ω = 0 := by exact_mod_cast hne
    simp [hzero]
  · rw [hvw hne]
    simp only [Pi.inf_apply]
    rw [NNReal.smul_def, NNReal.smul_def, NNReal.smul_def,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    exact mul_min_of_nonneg _ _ (NNReal.coe_nonneg _)

end WithDensityChangeOfMeasure

/-- A Banach lattice `X` that lattice isometrically embeds into some `L¹(μ)`
with norm-closed range, and that contains an element `u ≥ 0` whose image is
a.e. strictly positive, is itself Banach-lattice isometric to some `L¹(ν)`.
The change-of-density map `v ↦ v / (T u)` identifies the closed sublattice
`Range T` with a closed sublattice of `L¹((T u) · μ)` containing the constant
function `1`, which by the sublattice Stone–Weierstrass theorem is all of
`L¹`. -/
theorem exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive.{v}
    [BanachLattice X]
    {α : Type v} [MeasurableSpace α] (μ : Measure α)
    (T : X →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (hsup : ∀ x y : X, T (x ⊔ y) = T x ⊔ T y)
    (hinf : ∀ x y : X, T (x ⊓ y) = T x ⊓ T y)
    (_hclosed : IsClosed (Set.range T))
    (u : X) (_hu_nn : 0 ≤ u)
    (hu_ae : ∀ᵐ a ∂μ, 0 < (T u : α → ℝ) a) :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (ν : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 ν)) := by
  -- Step 1: set up the density ρ := ⇑(T u) and f_nn := toNNReal ∘ ρ
  set ρ : α → ℝ := ⇑(T u) with hρ_def
  have hρ_meas : Measurable ρ := (Lp.stronglyMeasurable (T u)).measurable
  have hρ_memLp : MemLp ρ 1 μ := Lp.memLp (T u)
  set f_nn : α → NNReal := fun ω => Real.toNNReal (ρ ω) with hf_nn_def
  have hf_nn_meas : Measurable f_nn := hρ_meas.real_toNNReal
  have hf_pos : ∀ᵐ ω ∂μ, (0 : ℝ) < f_nn ω := by
    filter_upwards [hu_ae] with ω hω
    change (0 : ℝ) < (Real.toNNReal (ρ ω) : ℝ)
    rw [Real.coe_toNNReal _ hω.le]; exact hω
  have hf_nn_eq_ρ : ∀ᵐ ω ∂μ, (f_nn ω : ℝ) = ρ ω := by
    filter_upwards [hu_ae] with ω hω
    exact Real.coe_toNNReal _ hω.le
  -- Step 2: the new measure ν = μ.withDensity f_nn is finite
  set ν := μ.withDensity (fun ω => ((f_nn ω : NNReal) : ENNReal)) with hν_def
  have hν_finite : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [memLp_one_iff_integrable] at hρ_memLp
    calc ∫⁻ ω, ((f_nn ω : NNReal) : ENNReal) ∂μ
        ≤ ∫⁻ ω, ‖ρ ω‖ₑ ∂μ := by
          apply lintegral_mono
          intro ω
          change ((f_nn ω : NNReal) : ENNReal) ≤ ‖ρ ω‖ₑ
          rw [Real.enorm_eq_ofReal_abs,
            show ENNReal.ofReal |ρ ω| = (Real.toNNReal |ρ ω| : ENNReal) from rfl]
          exact_mod_cast Real.toNNReal_le_toNNReal (le_abs_self _)
      _ < ⊤ := hρ_memLp.2
  -- Step 3: construct the change-of-density isometry Φ and its inverse Ψ
  let Φ : Lp ℝ 1 ν →ₗᵢ[ℝ] Lp ℝ 1 μ := withDensitySMulLI μ hf_nn_meas
  have hΦ_surj : Function.Surjective Φ :=
    withDensitySMulLI_surjective_of_ae_pos μ hf_nn_meas hf_pos
  let Φ' : Lp ℝ 1 ν ≃ₗᵢ[ℝ] Lp ℝ 1 μ := LinearIsometryEquiv.ofSurjective Φ hΦ_surj
  let Ψ : Lp ℝ 1 μ ≃ₗᵢ[ℝ] Lp ℝ 1 ν := Φ'.symm
  -- Step 4: the pulled-back lattice-isometric embedding T' : X → Lp ℝ 1 ν
  let T' : X →ₗᵢ[ℝ] Lp ℝ 1 ν := Ψ.toLinearIsometry.comp T
  -- Step 5: Ψ preserves ⊔ and ⊓ (inherited from Φ via surjectivity)
  have hΨ_sup : ∀ a b : Lp ℝ 1 μ, Ψ (a ⊔ b) = Ψ a ⊔ Ψ b := by
    intro a b
    apply Φ'.injective
    rw [Φ'.apply_symm_apply]
    have h : Φ' (Ψ a ⊔ Ψ b) = Φ' (Ψ a) ⊔ Φ' (Ψ b) :=
      withDensitySMulLI_map_sup μ hf_nn_meas _ _
    rw [h]
    change a ⊔ b = Φ' (Φ'.symm a) ⊔ Φ' (Φ'.symm b)
    rw [Φ'.apply_symm_apply, Φ'.apply_symm_apply]
  have hΨ_inf : ∀ a b : Lp ℝ 1 μ, Ψ (a ⊓ b) = Ψ a ⊓ Ψ b := by
    intro a b
    apply Φ'.injective
    rw [Φ'.apply_symm_apply]
    have h : Φ' (Ψ a ⊓ Ψ b) = Φ' (Ψ a) ⊓ Φ' (Ψ b) :=
      withDensitySMulLI_map_inf μ hf_nn_meas _ _
    rw [h]
    change a ⊓ b = Φ' (Φ'.symm a) ⊓ Φ' (Φ'.symm b)
    rw [Φ'.apply_symm_apply, Φ'.apply_symm_apply]
  -- Step 6: T' preserves ⊔ and ⊓
  have hT'_sup : ∀ x y : X, T' (x ⊔ y) = T' x ⊔ T' y := by
    intro x y
    change Ψ (T (x ⊔ y)) = Ψ (T x) ⊔ Ψ (T y)
    rw [hsup]; exact hΨ_sup _ _
  have hT'_inf : ∀ x y : X, T' (x ⊓ y) = T' x ⊓ T' y := by
    intro x y
    change Ψ (T (x ⊓ y)) = Ψ (T x) ⊓ Ψ (T y)
    rw [hinf]; exact hΨ_inf _ _
  -- Step 7: T' sends u to the constant function 1 in Lp ℝ 1 ν
  have hT'u : T' u = Lp.const 1 ν (1 : ℝ) := by
    change Ψ (T u) = Lp.const 1 ν (1 : ℝ)
    apply Φ'.injective
    rw [Φ'.apply_symm_apply]
    change T u = withDensitySMulLI μ hf_nn_meas (Lp.const 1 ν (1 : ℝ))
    symm
    apply Lp.ext
    have hΦ_ae : ⇑(withDensitySMulLI μ hf_nn_meas (Lp.const 1 ν (1 : ℝ))) =ᵐ[μ]
        fun x => f_nn x • (Lp.const 1 ν (1 : ℝ) : α → ℝ) x := by
      rw [withDensitySMulLI_apply]; exact MemLp.coeFn_toLp _
    have hc_μ : ∀ᵐ ω ∂μ, (f_nn ω : ENNReal) ≠ 0 →
        (Lp.const 1 ν (1 : ℝ) : α → ℝ) ω = 1 :=
      (ae_withDensity_iff hf_nn_meas.coe_nnreal_ennreal).mp
        (Lp.coeFn_const 1 ν 1)
    filter_upwards [hΦ_ae, hc_μ, hf_nn_eq_ρ, hf_pos] with ω hΦ hc heq hω
    rw [hΦ]
    have hne : (f_nn ω : ENNReal) ≠ 0 := by exact_mod_cast hω.ne'
    rw [hc hne]
    change (f_nn ω : ℝ) * 1 = ρ ω
    rw [mul_one]; exact heq
  -- Step 8: the range of T' is a closed vector sublattice containing the 1
  let L : VectorSublattice (Lp ℝ 1 ν) :=
    { toSubmodule := LinearMap.range T'.toLinearMap
      sup_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        change T' x ⊔ T' y ∈ _
        rw [← hT'_sup]
        exact LinearMap.mem_range_self _ _ }
  have hL_closed : IsClosed (L : Set (Lp ℝ 1 ν)) := by
    change IsClosed (Set.range T')
    exact T'.isometry.isClosedEmbedding.isClosed_range
  have hL_one : Lp.const 1 ν (1 : ℝ) ∈ L := by
    rw [← hT'u]; exact LinearMap.mem_range_self _ _
  -- Step 9: apply the structural theorem for closed sublattices of Lp
  letI : Lattice ↥L.toSubmodule := L.instLatticeSubtype
  letI : IsOrderedAddMonoid ↥L.toSubmodule := L.instIsOrderedAddMonoidSubtype
  letI : BanachLattice ↥L.toSubmodule := L.instBanachLatticeSubtype hL_closed
  obtain ⟨Ω', mΩ', ν', _hν'_finite, ⟨φ⟩⟩ :=
    exists_Lp_banachLatEquiv_of_closed_sublattice_containing_one (μ := ν)
      (by norm_num : (1 : ENNReal) ≠ ⊤) L hL_closed hL_one
  -- Step 10: T'.equivRange preserves ⊔ and ⊓ (pointwise on the subtype)
  have hψ_sup : ∀ x y : X,
      T'.equivRange (x ⊔ y) = T'.equivRange x ⊔ T'.equivRange y := by
    intro x y; apply Subtype.ext
    change T' (x ⊔ y) = T' x ⊔ T' y; exact hT'_sup x y
  have hψ_inf : ∀ x y : X,
      T'.equivRange (x ⊓ y) = T'.equivRange x ⊓ T'.equivRange y := by
    intro x y; apply Subtype.ext
    change T' (x ⊓ y) = T' x ⊓ T' y; exact hT'_inf x y
  -- Step 11: assemble the final Banach-lattice equivalence
  refine ⟨Ω', mΩ', ν', ⟨?_⟩⟩
  refine {
    toLinearIsometryEquiv := T'.equivRange.trans φ.toLinearIsometryEquiv
    map_sup' := ?_
    map_inf' := ?_ }
  · intro x y
    change φ (T'.equivRange (x ⊔ y)) = φ (T'.equivRange x) ⊔ φ (T'.equivRange y)
    rw [hψ_sup]; exact φ.map_sup' _ _
  · intro x y
    change φ (T'.equivRange (x ⊓ y)) = φ (T'.equivRange x) ⊓ φ (T'.equivRange y)
    rw [hψ_inf]; exact φ.map_inf' _ _

/-! ### Kakutani's AL-representation theorem -/

section PrincipalBandRepresentation

/-- Bundling a `BanachLatEquiv` as a `VecLatHom`. -/
private def banachLatEquivToVecLatHom
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (ρ : BanachLatEquiv A B) : VecLatHom A B :=
  { toFun := ρ
    map_add' := ρ.map_add
    map_smul' := ρ.map_smul
    map_sup' := ρ.map_sup'
    map_inf' := ρ.map_inf' }

/-- A `BanachLatEquiv` preserves the absolute value. -/
private lemma banachLatEquiv_map_abs
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (ρ : BanachLatEquiv A B) (y : A) :
    ρ |y| = |ρ y| := (banachLatEquivToVecLatHom ρ).map_abs y

/-- A `BanachLatEquiv` sends a weak-order-unit-like element to a
weak-order-unit-like element. -/
private lemma banachLatEquiv_forall_isVLDisjoint_eq_zero
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (ρ : BanachLatEquiv A B)
    {a : A} (hwou : ∀ v : A, IsVLDisjoint v a → v = 0) :
    ∀ w : B, IsVLDisjoint w (ρ a) → w = 0 := by
  intro w hw
  set v : A := ρ.toLinearIsometryEquiv.symm w
  have hρv : ρ v = w := ρ.toLinearIsometryEquiv.apply_symm_apply w
  have hdisj : IsVLDisjoint v a := by
    unfold IsVLDisjoint at hw ⊢
    have hρ_inf : ρ (|v| ⊓ |a|) = |w| ⊓ |ρ a| := by
      calc ρ (|v| ⊓ |a|)
          = ρ |v| ⊓ ρ |a| := ρ.map_inf' _ _
        _ = |ρ v| ⊓ |ρ a| := by
          rw [banachLatEquiv_map_abs, banachLatEquiv_map_abs]
        _ = |w| ⊓ |ρ a| := by rw [hρv]
    have h1 : ρ (|v| ⊓ |a|) = 0 := by rw [hρ_inf]; exact hw
    have h2 : ρ (|v| ⊓ |a|) = ρ 0 := by
      rw [h1]; exact (ρ.toLinearIsometryEquiv.map_zero).symm
    exact ρ.toLinearIsometryEquiv.injective h2
  have hvz : v = 0 := hwou v hdisj
  have heqw : w = ρ 0 := by rw [← hρv, hvz]
  rw [heqw]; exact ρ.toLinearIsometryEquiv.map_zero

/-- An indicator function in `Lp ℝ 1 ν` (for a finite measure `ν`) is zero iff
the indicated measurable set is `ν`-null. -/
private lemma lp_indicatorConstLp_one_eq_zero_iff
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {E : Set α} (hEm : MeasurableSet E) :
    indicatorConstLp 1 hEm (measure_ne_top ν E) (1 : ℝ) = 0 ↔ ν E = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (indicatorConstLp 1 hEm (measure_ne_top ν E) (1 : ℝ) : α → ℝ)
        =ᵐ[ν] 0 := by rw [h]; exact Lp.coeFn_zero ℝ 1 ν
    have h2 : E.indicator (fun _ => (1 : ℝ)) =ᵐ[ν] 0 :=
      (indicatorConstLp_coeFn (p := 1) (hs := hEm)
        (hμs := measure_ne_top ν E) (c := (1 : ℝ))).symm.trans h1
    have h3 : ν (E ∩ Function.support (fun _ : α => (1 : ℝ))) = 0 :=
      (Set.indicator_ae_eq_zero (μ := ν)).mp h2
    have hsupp : Function.support (fun _ : α => (1 : ℝ)) = Set.univ := by
      ext; simp [Function.support]
    rw [hsupp, Set.inter_univ] at h3; exact h3
  · apply Lp.ext
    refine (indicatorConstLp_coeFn (p := 1) (hs := hEm)
      (hμs := measure_ne_top ν E) (c := (1 : ℝ))).trans ?_
    refine (indicator_meas_zero h).trans ?_
    exact (Lp.coeFn_zero ℝ 1 ν).symm

/-- In `Lp ℝ 1 ν` with `ν` finite, a non-negative weak-order-unit-like element
is `ν`-a.e. strictly positive. -/
private lemma lp_aePos_of_forall_isVLDisjoint_eq_zero
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {g : Lp ℝ 1 ν} (hg : 0 ≤ g)
    (hwou : ∀ v : Lp ℝ 1 ν, IsVLDisjoint v g → v = 0) :
    ∀ᵐ a ∂ν, 0 < (g : α → ℝ) a := by
  have hg_ae : 0 ≤ᵐ[ν] (g : α → ℝ) := (Lp.coeFn_nonneg g).mpr hg
  have hg_meas : Measurable (g : α → ℝ) := (Lp.stronglyMeasurable g).measurable
  set E : Set α := {a | (g : α → ℝ) a ≤ 0}
  have hEm : MeasurableSet E := hg_meas measurableSet_Iic
  set χE : Lp ℝ 1 ν := indicatorConstLp 1 hEm (measure_ne_top ν E) (1 : ℝ)
    with hχE_def
  have hχE_coe : (χE : α → ℝ) =ᵐ[ν] E.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn (p := 1) (hs := hEm)
      (hμs := measure_ne_top ν E) (c := (1 : ℝ))
  have hχE_nn : (0 : Lp ℝ 1 ν) ≤ χE := by
    rw [← Lp.coeFn_le]
    filter_upwards [Lp.coeFn_zero ℝ 1 ν, hχE_coe] with a h0 hχ
    rw [h0, hχ]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) a
  have h_inf_zero : χE ⊓ g = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_inf χE g, Lp.coeFn_zero ℝ 1 ν, hχE_coe, hg_ae]
      with a h1 h0 hχ hgnn
    rw [h1, h0]
    change min ((χE : α → ℝ) a) ((g : α → ℝ) a) = (0 : ℝ)
    rw [hχ]
    by_cases haE : a ∈ E
    · have hga_le : (g : α → ℝ) a ≤ 0 := haE
      have hga_eq : (g : α → ℝ) a = 0 := le_antisymm hga_le hgnn
      rw [hga_eq, min_comm, min_eq_left]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) a
    · rw [Set.indicator_of_notMem haE]; exact min_eq_left hgnn
  have hχE_disj : IsVLDisjoint χE g := by
    unfold IsVLDisjoint
    rw [abs_of_nonneg hχE_nn, abs_of_nonneg hg, h_inf_zero]
  have hχE_zero : χE = 0 := hwou χE hχE_disj
  have hEν : ν E = 0 := (lp_indicatorConstLp_one_eq_zero_iff hEm).mp hχE_zero
  have hae_notE : ∀ᵐ a ∂ν, a ∉ E := ae_iff.mpr (by simpa using hEν)
  filter_upwards [hae_notE, hg_ae] with a hnotE hnn
  rcases eq_or_lt_of_le hnn with heq | hlt
  · exfalso; apply hnotE
    change (g : α → ℝ) a ≤ 0
    have h_zero : (g : α → ℝ) a = 0 := heq.symm
    linarith
  · exact hlt

/-- A continuous linear map preserving `⊔` and `⊓` between Banach lattices
(source having an order-continuous norm) sends the principal band `B_a`
into `B_{T a}` for a non-negative `a`. -/
private lemma mem_principalBand_image_of_continuous_latticeHom
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    [IsOrderContinuousNorm A]
    [IsVLArchimedean A] [IsVLArchimedean B]
    (T : A →L[ℝ] B)
    (hsup : ∀ x y, T (x ⊔ y) = T x ⊔ T y)
    (hinf : ∀ x y, T (x ⊓ y) = T x ⊓ T y)
    {a z : A} (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hmem : z ∈ Band.principalBand a) :
    T z ∈ Band.principalBand (T a) := by
  have hTa_nn : 0 ≤ T a := by
    have heq : T a = T a ⊔ 0 := by
      rw [← map_zero T, ← hsup, sup_of_le_left ha]
    exact le_sup_right.trans heq.symm.le
  have hTz_nn : 0 ≤ T z := by
    have heq : T z = T z ⊔ 0 := by
      rw [← map_zero T, ← hsup, sup_of_le_left hz]
    exact le_sup_right.trans heq.symm.le
  have hlub : IsLUB (Set.range (fun n : ℕ => z ⊓ n • a)) z :=
    (Band.mem_principalBand_iff_isLUB ha hz).mp hmem
  set u : ℕ → A := fun n => z ⊓ n • a
  have hu_mono : Monotone u := by
    intro m n hmn; exact inf_le_inf_left z (nsmul_le_nsmul_left ha hmn)
  have hu_bdd : BddAbove (Set.range u) :=
    ⟨z, by rintro _ ⟨n, rfl⟩; exact inf_le_left⟩
  obtain ⟨z', hz'_lub, htend⟩ :=
    BanachLattice.tendsto_of_monotone_bddAbove hu_mono hu_bdd
  have hz'_eq : z' = z := IsLUB.unique hz'_lub hlub
  rw [hz'_eq] at htend
  have hTtend : Filter.Tendsto (fun n => T (u n)) Filter.atTop (nhds (T z)) :=
    T.continuous.tendsto z |>.comp htend
  have hT_u : ∀ n, T (u n) = T z ⊓ n • T a := by
    intro n
    change T (z ⊓ n • a) = T z ⊓ n • T a
    rw [hinf z (n • a), map_nsmul T n a]
  have hTu_mem : ∀ n, T (u n) ∈ (Band.principalBand (T a) : Set B) := by
    intro n
    rw [hT_u n]
    apply Band.principal_le_principalBand
    refine ⟨n, n.cast_nonneg, ?_⟩
    have h_nn : 0 ≤ T z ⊓ n • T a := le_inf hTz_nn (nsmul_nonneg hTa_nn n)
    rw [abs_of_nonneg h_nn, abs_of_nonneg hTa_nn, Nat.cast_smul_eq_nsmul]
    exact inf_le_right
  have hclosed : IsClosed ((Band.principalBand (T a) : Band B) : Set B) :=
    Band.isClosed_coe _
  exact hclosed.mem_of_tendsto hTtend (Filter.Eventually.of_forall hTu_mem)

/-- The inverse of a `BanachLatEquiv` preserves binary suprema. -/
private lemma banachLatEquiv_symm_map_sup
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) (b c : B) :
    γ.toLinearIsometryEquiv.symm (b ⊔ c) =
      γ.toLinearIsometryEquiv.symm b ⊔ γ.toLinearIsometryEquiv.symm c := by
  apply γ.toLinearIsometryEquiv.injective
  have h1 : γ (γ.toLinearIsometryEquiv.symm b ⊔ γ.toLinearIsometryEquiv.symm c) =
      γ (γ.toLinearIsometryEquiv.symm b) ⊔ γ (γ.toLinearIsometryEquiv.symm c) :=
    γ.map_sup' _ _
  rw [γ.toLinearIsometryEquiv.apply_symm_apply]
  change b ⊔ c = γ (γ.toLinearIsometryEquiv.symm b ⊔ γ.toLinearIsometryEquiv.symm c)
  rw [h1]
  change b ⊔ c = γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm b) ⊔
    γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm c)
  rw [γ.toLinearIsometryEquiv.apply_symm_apply,
    γ.toLinearIsometryEquiv.apply_symm_apply]

/-- The inverse of a `BanachLatEquiv` preserves binary infima. -/
private lemma banachLatEquiv_symm_map_inf
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) (b c : B) :
    γ.toLinearIsometryEquiv.symm (b ⊓ c) =
      γ.toLinearIsometryEquiv.symm b ⊓ γ.toLinearIsometryEquiv.symm c := by
  apply γ.toLinearIsometryEquiv.injective
  have h1 : γ (γ.toLinearIsometryEquiv.symm b ⊓ γ.toLinearIsometryEquiv.symm c) =
      γ (γ.toLinearIsometryEquiv.symm b) ⊓ γ (γ.toLinearIsometryEquiv.symm c) :=
    γ.map_inf' _ _
  rw [γ.toLinearIsometryEquiv.apply_symm_apply]
  change b ⊓ c = γ (γ.toLinearIsometryEquiv.symm b ⊓ γ.toLinearIsometryEquiv.symm c)
  rw [h1]
  change b ⊓ c = γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm b) ⊓
    γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm c)
  rw [γ.toLinearIsometryEquiv.apply_symm_apply,
    γ.toLinearIsometryEquiv.apply_symm_apply]

/-- The inverse of a `BanachLatEquiv` as a `BanachLatEquiv`. -/
private noncomputable def banachLatEquiv_symm
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) : BanachLatEquiv B A where
  toLinearIsometryEquiv := γ.toLinearIsometryEquiv.symm
  map_sup' := banachLatEquiv_symm_map_sup γ
  map_inf' := banachLatEquiv_symm_map_inf γ

/-- The inverse of a `BanachLatEquiv` sends non-negative elements to
non-negative elements. -/
private lemma banachLatEquiv_symm_nonneg
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) {b : B} (hb : 0 ≤ b) :
    0 ≤ γ.toLinearIsometryEquiv.symm b := by
  have h0 : γ.toLinearIsometryEquiv.symm 0 = 0 :=
    γ.toLinearIsometryEquiv.symm.map_zero
  have hs : γ.toLinearIsometryEquiv.symm (0 ⊔ b) =
      γ.toLinearIsometryEquiv.symm 0 ⊔ γ.toLinearIsometryEquiv.symm b :=
    banachLatEquiv_symm_map_sup γ 0 b
  rw [sup_eq_right.mpr hb, h0] at hs
  exact le_sup_left.trans hs.symm.le

/-- A `BanachLatEquiv` sends non-negative elements to non-negative elements. -/
private lemma banachLatEquiv_nonneg
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) {a : A} (ha : 0 ≤ a) :
    0 ≤ γ a := by
  have h0 : γ 0 = 0 := γ.toLinearIsometryEquiv.map_zero
  have hs : γ (0 ⊔ a) = γ 0 ⊔ γ a := γ.map_sup' 0 a
  rw [sup_eq_right.mpr ha, h0] at hs
  exact le_sup_left.trans hs.symm.le

/-- Pre-composition by a `BanachLatEquiv` preserves binary suprema in the norm
dual. For `γ : BanachLatEquiv A B` and `α, β ∈ NormDualSpace B`,
`(α ⊔ β) ∘L γ = (α ∘L γ) ⊔ (β ∘L γ)`. -/
private lemma banachLatEquiv_precomp_map_sup
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) (α β : NormDualSpace B) :
    (α ⊔ β).comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap =
      α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
        β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap := by
  have hposApp : ∀ (a : A), 0 ≤ a →
      (α ⊔ β) (γ a) =
      (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
        β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a := by
    intro a ha
    have hγa : 0 ≤ γ a := banachLatEquiv_nonneg γ ha
    have hLHS := OrderDualSpace.isLUB_sup_apply
      (φ := NormDualSpace.toOrderDualSpace α)
      (ψ := NormDualSpace.toOrderDualSpace β) hγa
    have hRHS := OrderDualSpace.isLUB_sup_apply
      (φ := NormDualSpace.toOrderDualSpace
          (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap))
      (ψ := NormDualSpace.toOrderDualSpace
          (β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)) ha
    have hset :
        {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = γ a ∧
            r = NormDualSpace.toOrderDualSpace α y +
                NormDualSpace.toOrderDualSpace β z} =
        {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = a ∧
            r = NormDualSpace.toOrderDualSpace
                  (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) y +
                NormDualSpace.toOrderDualSpace
                  (β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) z} := by
      ext r
      constructor
      · rintro ⟨y, z, hy, hz, hyz, hr⟩
        refine ⟨γ.toLinearIsometryEquiv.symm y, γ.toLinearIsometryEquiv.symm z,
          banachLatEquiv_symm_nonneg γ hy, banachLatEquiv_symm_nonneg γ hz, ?_, ?_⟩
        · have h : γ.toLinearIsometryEquiv.symm y +
              γ.toLinearIsometryEquiv.symm z =
              γ.toLinearIsometryEquiv.symm (y + z) :=
            (γ.toLinearIsometryEquiv.symm.map_add y z).symm
          rw [h, hyz]
          exact γ.toLinearIsometryEquiv.symm_apply_apply a
        · change _ = (NormDualSpace.toOrderDualSpace
            (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap))
              (γ.toLinearIsometryEquiv.symm y) +
            (NormDualSpace.toOrderDualSpace
              (β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap))
                (γ.toLinearIsometryEquiv.symm z)
          change _ = α (γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm y)) +
              β (γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm z))
          rw [γ.toLinearIsometryEquiv.apply_symm_apply,
              γ.toLinearIsometryEquiv.apply_symm_apply]
          exact hr
      · rintro ⟨y, z, hy, hz, hyz, hr⟩
        refine ⟨γ y, γ z, banachLatEquiv_nonneg γ hy,
          banachLatEquiv_nonneg γ hz, ?_, ?_⟩
        · have hadd : γ y + γ z = γ (y + z) :=
            (γ.toLinearIsometryEquiv.map_add y z).symm
          rw [hadd, hyz]
        · change _ = α (γ y) + β (γ z) at hr
          change _ = α (γ y) + β (γ z)
          exact hr
    rw [hset] at hLHS
    exact IsLUB.unique hLHS hRHS
  apply ContinuousLinearMap.ext
  intro a
  have h_pn : a = a⁺ - a⁻ := (posPart_sub_negPart a).symm
  have hap : 0 ≤ a⁺ := posPart_nonneg a
  have han : 0 ≤ a⁻ := negPart_nonneg a
  have hγ_sub : ∀ u v : A, γ (u - v) = γ u - γ v :=
    fun u v => γ.toLinearIsometryEquiv.map_sub u v
  calc (α ⊔ β).comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap a
      = (α ⊔ β) (γ a) := rfl
    _ = (α ⊔ β) (γ a⁺ - γ a⁻) := by rw [← hγ_sub, ← h_pn]
    _ = (α ⊔ β) (γ a⁺) - (α ⊔ β) (γ a⁻) := by
        exact map_sub (α ⊔ β) _ _
    _ = (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a⁺ -
        (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a⁻ := by
        rw [hposApp a⁺ hap, hposApp a⁻ han]
    _ = (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) (a⁺ - a⁻) := by
        exact (map_sub _ _ _).symm
    _ = (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a := by
        rw [← h_pn]

/-- A trivial `BanachLatEquiv` between two subsingleton Banach lattices. -/
private noncomputable def banachLatEquiv_of_subsingleton
    (A B : Type*)
    [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    [Subsingleton A] [Subsingleton B] : BanachLatEquiv A B :=
  { toLinearIsometryEquiv :=
      { toLinearEquiv :=
          { toFun := fun _ => 0
            invFun := fun _ => 0
            map_add' := fun _ _ => Subsingleton.elim _ _
            map_smul' := fun _ _ => Subsingleton.elim _ _
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun _ => Subsingleton.elim _ _ }
        norm_map' := fun a => by
          rw [show a = 0 from Subsingleton.elim _ _]
          simp }
    map_sup' := fun _ _ => Subsingleton.elim _ _
    map_inf' := fun _ _ => Subsingleton.elim _ _ }

/-- Pre-composition by a `BanachLatEquiv` preserves binary infima in the norm
dual. -/
private lemma banachLatEquiv_precomp_map_inf
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) (α β : NormDualSpace B) :
    (α ⊓ β).comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap =
      α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊓
        β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap := by
  have key : α ⊓ β = -(-α ⊔ -β) := by rw [neg_sup, neg_neg, neg_neg]
  have key2 : α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊓
      β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap =
      -(-(α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) ⊔
        -(β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)) := by
    rw [neg_sup, neg_neg, neg_neg]
  rw [key, key2]
  have hcomp_neg : ∀ η : NormDualSpace B,
      (-η).comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap =
        -(η.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) := by
    intro η; ext; simp
  rw [← hcomp_neg, ← hcomp_neg, ← banachLatEquiv_precomp_map_sup γ]
  ext a; simp

/-- Precomposition by the underlying continuous linear map of a linear isometric
equivalence preserves the operator norm. -/
private lemma norm_comp_linearIsometryEquiv
    {A B G : Type*}
    [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup G]
    [NormedSpace ℝ A] [NormedSpace ℝ B] [NormedSpace ℝ G]
    (r : A ≃ₗᵢ[ℝ] B) (f : B →L[ℝ] G) :
    ‖f.comp r.toLinearIsometry.toContinuousLinearMap‖ = ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_
    calc ‖(f.comp r.toLinearIsometry.toContinuousLinearMap) a‖
        = ‖f (r a)‖ := rfl
      _ ≤ ‖f‖ * ‖r a‖ := f.le_opNorm _
      _ = ‖f‖ * ‖a‖ := by rw [r.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun b => ?_
    calc ‖f b‖
        = ‖f (r (r.symm b))‖ := by rw [r.apply_symm_apply]
      _ = ‖(f.comp r.toLinearIsometry.toContinuousLinearMap) (r.symm b)‖ := rfl
      _ ≤ ‖f.comp r.toLinearIsometry.toContinuousLinearMap‖ * ‖r.symm b‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖f.comp r.toLinearIsometry.toContinuousLinearMap‖ * ‖b‖ := by
          rw [r.symm.norm_map]

/-- An element of a principal band that is disjoint from the band's generator
is zero. -/
private lemma eq_zero_of_mem_principalBand_of_isVLDisjoint
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] [IsVLArchimedean Y]
    {a v : Y} (hv_mem : v ∈ Band.principalBand a) (hv_dis : IsVLDisjoint v a) :
    v = 0 := by
  have hv_in_d : v ∈ (({a} : Set Y)ᵈ) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc; rw [hc]; exact hv_dis
  have hv_in_dd : v ∈ ((({a} : Set Y)ᵈ)ᵈ) := by
    rw [Band.disjointComplement_disjointComplement_eq_bandGenerated]
    exact hv_mem
  exact Set.mem_singleton_iff.mp
    (disjointComplement_inter_eq_zero _ ⟨hv_in_d, hv_in_dd⟩)

end PrincipalBandRepresentation

set_option maxHeartbeats 1600000 in
-- The composite X ↪ X** → M(K) together with the L¹-representation of the
-- principal band of the image forces a deep unification chain through three
-- `let`-bound intermediate maps, exhausting the default heartbeat budget.
/-- Every principal band of an AL-space is Banach-lattice isometric to some
`L¹(μ)`. The argument identifies `X* ≅ C(K, ℝ)` via Kakutani's AM-space theorem,
dualises to `X** ≅ M(K)`, and then embeds `X ↪ X**` as a closed sublattice of
`M(K)`; for each positive `x`, the principal band `B_x` lives inside the
principal band of the image of `x`, which is an L¹-space with `x` as an a.e.
strictly positive element. -/
private lemma exists_L1_banachLatEquiv_principalBand_of_ALSpace
    [ALSpace X] (x : X) (hx : 0 ≤ x) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv
        ↥(Band.principalBand x).toSubmodule (Lp ℝ 1 μ)) := by
  classical
  by_cases hntriv : Nontrivial X
  · -- Nontrivial case: carry out the full Bidual + Kakutani + Riesz argument
    haveI : Nontrivial X := hntriv
    set K : Type u := AMSpaceWithUnit.LatticeCharacter (NormDualSpace X) with hK_def
    letI mK : MeasurableSpace K := borel K
    haveI : BorelSpace K := ⟨rfl⟩
    -- Kakutani AM equivalence ρ : NormDualSpace X ≅ C(K, ℝ)
    let ρ : BanachLatEquiv (NormDualSpace X) C(K, ℝ) :=
      AMSpaceWithUnit.kakutaniEquiv (NormDualSpace X)
    -- Inverse of ρ as BanachLatEquiv and CLM
    let γ_sym : BanachLatEquiv C(K, ℝ) (NormDualSpace X) := banachLatEquiv_symm ρ
    let γ_sym_clm : C(K, ℝ) →L[ℝ] NormDualSpace X :=
      γ_sym.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
    -- Φ : X → MofK K, the composite X ↪ X** → M(K)
    let Φ : X → MofK K := fun a =>
      rieszEquiv.toLinearIsometryEquiv.symm
        ((BidualSpace.inclusion a).comp γ_sym_clm)
    have hΦ_zero : Φ 0 = 0 := by
      change rieszEquiv.toLinearIsometryEquiv.symm _ = _
      rw [map_zero, ContinuousLinearMap.zero_comp, map_zero]
    have hΦ_add : ∀ a b : X, Φ (a + b) = Φ a + Φ b := by
      intro a b
      change rieszEquiv.toLinearIsometryEquiv.symm
          ((BidualSpace.inclusion (a + b)).comp γ_sym_clm) = _
      rw [map_add BidualSpace.inclusion, ContinuousLinearMap.add_comp, map_add]
    have hΦ_smul : ∀ (r : ℝ) (a : X), Φ (r • a) = r • Φ a := by
      intro r a
      change rieszEquiv.toLinearIsometryEquiv.symm
          ((BidualSpace.inclusion (r • a)).comp γ_sym_clm) = _
      rw [map_smul BidualSpace.inclusion, ContinuousLinearMap.smul_comp, map_smul]
    have hΦ_norm : ∀ a : X, ‖Φ a‖ = ‖a‖ := by
      intro a
      change ‖rieszEquiv.toLinearIsometryEquiv.symm
          ((BidualSpace.inclusion a).comp γ_sym_clm)‖ = ‖a‖
      rw [LinearIsometryEquiv.norm_map]
      change ‖(BidualSpace.inclusion a).comp
          ρ.toLinearIsometryEquiv.symm.toLinearIsometry.toContinuousLinearMap‖ = ‖a‖
      rw [norm_comp_linearIsometryEquiv ρ.toLinearIsometryEquiv.symm,
        BidualSpace.norm_inclusion]
    have hΦ_sup : ∀ a b : X, Φ (a ⊔ b) = Φ a ⊔ Φ b := by
      intro a b
      change rieszEquiv.toLinearIsometryEquiv.symm
          ((BidualSpace.inclusion (a ⊔ b)).comp γ_sym_clm) = _
      rw [BidualSpace.inclusion_sup, banachLatEquiv_precomp_map_sup γ_sym]
      exact banachLatEquiv_symm_map_sup _ _ _
    have hΦ_inf : ∀ a b : X, Φ (a ⊓ b) = Φ a ⊓ Φ b := by
      intro a b
      change rieszEquiv.toLinearIsometryEquiv.symm
          ((BidualSpace.inclusion (a ⊓ b)).comp γ_sym_clm) = _
      rw [BidualSpace.inclusion_inf, banachLatEquiv_precomp_map_inf γ_sym]
      exact banachLatEquiv_symm_map_inf _ _ _
    -- Package Φ as a LinearIsometry
    let Φ_li : X →ₗᵢ[ℝ] MofK K :=
      { toLinearMap :=
          { toFun := Φ
            map_add' := hΦ_add
            map_smul' := hΦ_smul }
        norm_map' := hΦ_norm }
    -- Principal band membership: Φ sends B_x into B_{Φ x}
    have hΦ_mem : ∀ z : X, z ∈ (Band.principalBand x).toSubmodule →
        Φ z ∈ (Band.principalBand (Φ x)).toSubmodule := by
      intro z hz
      have hz_pos_mem : z⁺ ∈ Band.principalBand x := by
        rw [posPart_def]
        exact (Band.principalBand x).sup_mem hz
          (Band.principalBand x).toSubmodule.zero_mem
      have hz_neg_mem : z⁻ ∈ Band.principalBand x := by
        rw [negPart_def]
        exact (Band.principalBand x).sup_mem
          ((Band.principalBand x).toSubmodule.neg_mem hz)
          (Band.principalBand x).toSubmodule.zero_mem
      set T_clm := Φ_li.toContinuousLinearMap with hT_clm_def
      have hT_sup : ∀ a b : X, T_clm (a ⊔ b) = T_clm a ⊔ T_clm b := hΦ_sup
      have hT_inf : ∀ a b : X, T_clm (a ⊓ b) = T_clm a ⊓ T_clm b := hΦ_inf
      have h1 := mem_principalBand_image_of_continuous_latticeHom
        T_clm hT_sup hT_inf hx (posPart_nonneg z) hz_pos_mem
      have h2 := mem_principalBand_image_of_continuous_latticeHom
        T_clm hT_sup hT_inf hx (negPart_nonneg z) hz_neg_mem
      have hdiff : Φ z = Φ z⁺ - Φ z⁻ := by
        conv_lhs => rw [← posPart_sub_negPart z]
        exact map_sub Φ_li.toLinearMap _ _
      rw [hdiff]
      exact (Band.principalBand (Φ x)).toSubmodule.sub_mem h1 h2
    -- Φ x ≥ 0
    have hΦx_nn : (0 : MofK K) ≤ Φ x := by
      have h1 : Φ (0 ⊔ x) = Φ 0 ⊔ Φ x := hΦ_sup 0 x
      rw [sup_eq_right.mpr hx, hΦ_zero] at h1
      calc (0 : MofK K) ≤ 0 ⊔ Φ x := le_sup_left
        _ = Φ x := h1.symm
    -- L¹ representation of the principal band of Φ x in MofK K
    obtain ⟨Ω, mΩ, ν, hν_fin, ⟨φ_eq⟩⟩ :=
      MofK.exists_principalBand_banachLatEquivL1 hΦx_nn
    -- x as element of the principal band of x
    have hx_mem : x ∈ (Band.principalBand x).toSubmodule :=
      Band.subset_bandGenerated _ (Set.mem_singleton _)
    let x_band : ↥(Band.principalBand x).toSubmodule := ⟨x, hx_mem⟩
    have hx_band_nn : (0 : ↥(Band.principalBand x).toSubmodule) ≤ x_band := hx
    -- Φ x as element of the principal band of Φ x
    let Φx_band : ↥(Band.principalBand (Φ x)).toSubmodule :=
      ⟨Φ x, hΦ_mem x hx_mem⟩
    have hΦx_band_nn : (0 : ↥(Band.principalBand (Φ x)).toSubmodule) ≤ Φx_band :=
      hΦx_nn
    -- Restrict Φ_li to the principal band of x
    let Φ_restr : ↥(Band.principalBand x).toSubmodule →ₗᵢ[ℝ]
        ↥(Band.principalBand (Φ x)).toSubmodule :=
      { toLinearMap :=
          { toFun := fun v => ⟨Φ v.val, hΦ_mem v.val v.property⟩
            map_add' := fun a b => Subtype.ext (hΦ_add a.val b.val)
            map_smul' := fun r a => Subtype.ext (hΦ_smul r a.val) }
        norm_map' := fun v => hΦ_norm v.val }
    -- φ_eq as LinearIsometry
    let φ_li : ↥(Band.principalBand (Φ x)).toSubmodule →ₗᵢ[ℝ] Lp ℝ 1 ν :=
      φ_eq.toLinearIsometryEquiv.toLinearIsometry
    -- Composite T : B_x →ₗᵢ Lp ℝ 1 ν
    let T : ↥(Band.principalBand x).toSubmodule →ₗᵢ[ℝ] Lp ℝ 1 ν :=
      φ_li.comp Φ_restr
    -- T(x_band) = φ_eq Φx_band
    have hT_x : T x_band = φ_eq Φx_band := rfl
    -- T(x_band) ≥ 0
    have hTx_nn : (0 : Lp ℝ 1 ν) ≤ T x_band := by
      rw [hT_x]; exact banachLatEquiv_nonneg φ_eq hΦx_band_nn
    -- Every w ⊥ Φx_band in the subtype is zero
    have hΦx_band_wou : ∀ u : ↥(Band.principalBand (Φ x)).toSubmodule,
        IsVLDisjoint u Φx_band → u = 0 := by
      intro u hudis
      apply Subtype.ext
      have hu_disj : IsVLDisjoint u.val (Φ x) := by
        have h := congrArg Subtype.val hudis
        exact h
      exact eq_zero_of_mem_principalBand_of_isVLDisjoint u.property hu_disj
    -- Every w ⊥ T x_band in Lp is zero
    have hTx_wou : ∀ w : Lp ℝ 1 ν, IsVLDisjoint w (T x_band) → w = 0 := by
      intro w hw
      rw [hT_x] at hw
      exact banachLatEquiv_forall_isVLDisjoint_eq_zero φ_eq hΦx_band_wou w hw
    -- T(x_band) is a.e. strictly positive
    have hTx_ae : ∀ᵐ a ∂ν, 0 < (T x_band : Ω → ℝ) a :=
      lp_aePos_of_forall_isVLDisjoint_eq_zero hTx_nn hTx_wou
    -- T has closed range (isometric embedding from complete space)
    have hT_closed : IsClosed (Set.range T) :=
      T.isometry.isClosedEmbedding.isClosed_range
    -- T preserves ⊔
    have hΦ_restr_sup : ∀ v w : ↥(Band.principalBand x).toSubmodule,
        Φ_restr (v ⊔ w) = Φ_restr v ⊔ Φ_restr w := fun v w =>
      Subtype.ext (hΦ_sup v.val w.val)
    have hΦ_restr_inf : ∀ v w : ↥(Band.principalBand x).toSubmodule,
        Φ_restr (v ⊓ w) = Φ_restr v ⊓ Φ_restr w := fun v w =>
      Subtype.ext (hΦ_inf v.val w.val)
    have hT_sup : ∀ v w : ↥(Band.principalBand x).toSubmodule,
        T (v ⊔ w) = T v ⊔ T w := fun v w => by
      change φ_eq (Φ_restr (v ⊔ w)) = φ_eq (Φ_restr v) ⊔ φ_eq (Φ_restr w)
      rw [hΦ_restr_sup]; exact φ_eq.map_sup' _ _
    have hT_inf : ∀ v w : ↥(Band.principalBand x).toSubmodule,
        T (v ⊓ w) = T v ⊓ T w := fun v w => by
      change φ_eq (Φ_restr (v ⊓ w)) = φ_eq (Φ_restr v) ⊓ φ_eq (Φ_restr w)
      rw [hΦ_restr_inf]; exact φ_eq.map_inf' _ _
    -- Apply the main theorem
    exact exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive
      (X := ↥(Band.principalBand x).toSubmodule)
      ν T hT_sup hT_inf hT_closed x_band hx_band_nn hTx_ae
  · -- Trivial case: X is subsingleton, so B_x is trivial
    haveI hssX : Subsingleton X := not_nontrivial_iff_subsingleton.mp hntriv
    haveI : Subsingleton ↥(Band.principalBand x).toSubmodule :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    refine ⟨PUnit.{u+1}, (⊤ : MeasurableSpace PUnit.{u+1}), 0, ⟨?_⟩⟩
    haveI hss_lp : Subsingleton (Lp ℝ 1 (0 : @MeasureTheory.Measure PUnit.{u+1} ⊤)) := by
      refine ⟨fun f g => Lp.ext ?_⟩
      rw [Filter.EventuallyEq, MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    exact banachLatEquiv_of_subsingleton _ _

/-- **Kakutani's AL-representation theorem.** Every AL-space `X` is
Banach-lattice isometrically isomorphic to `L¹(μ)` for some positive
measure `μ`. -/
theorem exists_L1_banachLatEquiv [ALSpace X] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 μ)) :=
  exists_L1_banachLatEquiv_of_principalBand X
    (exists_L1_banachLatEquiv_principalBand_of_ALSpace X)

end ALSpace
