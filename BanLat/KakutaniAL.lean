import BanLat.ALSpace
import BanLat.Examples.Lp
import BanLat.Examples.MofK
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
    show T z ⟨_, _⟩ = T z ⟨_, _⟩ + T z ⟨_, _⟩
    rw [heq]; exact (T z).toLinearIsometryEquiv.map_add _ _
  have hfL_smul : ∀ z (c : ℝ) x, fL z (c • x) = c • fL z x := by
    intro z c x
    have heq : (⟨Band.principalBandProjection (z : X) (c • x),
        hP_mem z (c • x)⟩ : (Band.principalBand (z : X)).toSubmodule) =
      c • ⟨_, hP_mem z x⟩ := by ext; simp [map_smul]
    show T z ⟨_, _⟩ = c • T z ⟨_, _⟩
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
      (by simp_rw [NNReal.coe_nnnorm]; exact (hfL_hasSum x).summable)
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
    sorry
  -- a.e. equality on sigma type from fiber-wise a.e. equality
  have hae_of_fiber : ∀ {f g : (z : Λ) × Ω z → ℝ},
      (∀ z : Λ, (fun ω => f ⟨z, ω⟩) =ᵐ[μ z] fun ω => g ⟨z, ω⟩) →
      f =ᵐ[ν] g := by
    intro f g hfib
    have hzero : ∀ z : Λ,
        ((μ z).map (Sigma.mk z)) {p | ¬(f p = g p)} = 0 := by
      intro z
      rw [(measurableEmbedding_sigma_mk z).map_apply]
      exact ae_iff.mp (hfib z)
    have : ν {p | ¬(f p = g p)} = 0 :=
      nonpos_iff_eq_zero.mp <|
        calc ν {p | ¬(f p = g p)}
            ≤ ∑' z : Λ, ((μ z).map (Sigma.mk z)) {p | ¬(f p = g p)} :=
              hν_def ▸ Measure.sum_apply_le _
          _ = 0 := by simp [hzero]
    exact ae_iff.mpr this
  -- Additivity: Φ(x + y) = Φ(x) + Φ(y)
  have hΦ_add : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    show (hφ_memLp (x + y)).toLp _ = (hφ_memLp x).toLp _ + (hφ_memLp y).toLp _
    rw [← MemLp.toLp_add]; apply MemLp.toLp_congr
    apply hae_of_fiber; intro z
    have := Lp.coeFn_add (fL z x) (fL z y)
    rw [← hfL_add] at this; exact this
  -- Scalar: Φ(c • x) = c • Φ(x)
  have hΦ_smul : ∀ c x, Φ (c • x) = c • Φ x := by
    intro c x
    show (hφ_memLp (c • x)).toLp _ = c • (hφ_memLp x).toLp _
    rw [← MemLp.toLp_const_smul]; apply MemLp.toLp_congr
    apply hae_of_fiber; intro z
    have := Lp.coeFn_smul c (fL z x)
    rw [← hfL_smul] at this; exact this
  have hΦ_zero : Φ 0 = 0 := by
    have h0 := hΦ_add 0 0; simp at h0; exact h0
  -- Construct the linear isometry
  let li : X →ₗᵢ[ℝ] Lp ℝ 1 ν :=
    ⟨⟨⟨⟨Φ, hΦ_add⟩, hΦ_zero⟩, hΦ_smul⟩, hΦ_norm⟩
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
            ((measurableEmbedding_sigma_mk z).lintegral_map _ _).symm
        _ ≤ ∫⁻ a, ‖(g : _ → ℝ) a‖ₑ ∂ν :=
            lintegral_mono_measure (Measure.le_sum _ z)
        _ = eLpNorm (↑g) 1 ν := eLpNorm_one_eq_lintegral_enorm.symm
        _ = ↑‖g‖₊ := by rw [Lp.nnnorm_def]
        _ < ⊤ := ENNReal.coe_lt_top
    sorry
  -- Lattice preservation
  have hΦ_sup : ∀ x y : X, li (x ⊔ y) = li x ⊔ li y := by sorry
  have hΦ_inf : ∀ x y : X, li (x ⊓ y) = li x ⊓ li y := by sorry
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
  exists_L1_banachLatEquiv_of_principalBand (SignedMeasure α) fun s hs =>
    ⟨_, _, _, ⟨SignedMeasure.principalBandBanachLatEquivL1 hs⟩⟩

/-- A Banach lattice `X` that lattice isometrically embeds into some `L¹(μ)`
with norm-closed range, and that contains an element `u ≥ 0` whose image is
a.e. strictly positive, is itself Banach-lattice isometric to some `L¹(ν)`.
The change-of-density map `v ↦ v / (T u)` identifies the closed sublattice
`Range T` with a closed sublattice of `L¹((T u) · μ)` containing the constant
function `1`, which by the sublattice Stone–Weierstrass theorem is all of
`L¹`. -/
theorem exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive
    [NormedVectorLattice X] [BanachLattice X]
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (T : X →ₗᵢ[ℝ] Lp ℝ 1 μ)
    (_hsup : ∀ x y : X, T (x ⊔ y) = T x ⊔ T y)
    (_hinf : ∀ x y : X, T (x ⊓ y) = T x ⊓ T y)
    (_hclosed : IsClosed (Set.range T))
    (u : X) (_hu_nn : 0 ≤ u)
    (_hu_ae : ∀ᵐ a ∂μ, 0 < (T u : α → ℝ) a) :
    ∃ (Ω : Type*) (_ : MeasurableSpace Ω) (ν : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 ν)) := by
  sorry

/-! ### Kakutani's AL-representation theorem -/

/-- **Kakutani's AL-representation theorem.** Every AL-space `X` is
Banach-lattice isometrically isomorphic to `L¹(μ)` for some positive
measure `μ`.

**Proof outline.** Since `X*` is an AM-space with unit, Kakutani's AM-space
representation identifies `X* ≅ C(K)` for some compact Hausdorff `K`, and the
Riesz–Markov–Kakutani theorem identifies `X** ≅ C(K)* ≅ SignedMeasure K`. The
latter is an L¹-space, so the canonical embedding `X ↪ X**` realises `X` as
a closed sublattice of some `L¹(μ)`. For each `0 ≤ x ∈ X`, the principal band
`B_x` of `X` sits inside the principal band of `x` in `L¹(μ)` and contains
`x` as an a.e. strictly positive element, so it is an L¹-space by
`exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive`. Finally
`exists_L1_banachLatEquiv_of_principalBand` glues these band-level
representations into an L¹-representation of `X`. -/
theorem exists_L1_banachLatEquiv [ALSpace X] :
    ∃ (Ω : Type*) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 μ)) := by
  sorry

end ALSpace
