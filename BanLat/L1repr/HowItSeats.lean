import BanLat.ALSpace.OrderContinuous
import BanLat.Examples.Lp.Basic
import BanLat.L1repr.Basic
import BanLat.OrderDense
import BanLat.Operators.OrderContinuous

/-!
# How a vector lattice sits inside its `L¹`-representation

Refinements of the `L¹`-representation theorem. Given an `L¹`-representation of a vector
lattice `X` with a strictly positive functional `h` — an injective vector lattice
homomorphism `T : X → L¹(μ)` with dense range realising `h` as integration against `μ` on
the positive cone — the order-theoretic position of the image of `X` inside `L¹(μ)` is
governed by order continuity of `h`:

* the image of `X` is order dense in `L¹(μ)` iff `h` is order continuous;
* the image of `X` is a regular sublattice of `L¹(μ)` — equivalently, `T` is order
  continuous — iff `h` is order continuous;
* the image of `X` is an order ideal of `L¹(μ)` iff `h` is order continuous and `X` is
  order complete.
-/

open MeasureTheory

universe u v w

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Auxiliary lemmas -/

/-- In a normed vector lattice, the multiples `2⁻ᵏ • g` of a non-negative element
decrease to zero. -/
private theorem isGLB_range_pow_smul {Z : Type*} [NormedAddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [NormedVectorLattice Z] {g : Z} (hg : 0 ≤ g) :
    IsGLB (Set.range fun k : ℕ => (2 : ℝ)⁻¹ ^ k • g) 0 := by
  constructor
  · rintro _ ⟨k, rfl⟩
    exact smul_nonneg (by positivity) hg
  · intro w hw
    have hple : ∀ n : ℕ, n • w⁺ ≤ g := by
      intro n
      have h2 : w⁺ ≤ (2 : ℝ)⁻¹ ^ n • g := by
        rw [posPart_def]
        exact sup_le (hw ⟨n, rfl⟩) (smul_nonneg (by positivity) hg)
      have h3 := smul_le_smul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)
      rw [smul_smul, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, one_smul] at h3
      have h4 : ((n : ℝ)) • w⁺ ≤ ((2 : ℝ) ^ n) • w⁺ :=
        smul_le_smul_of_nonneg_right
          (by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le) (posPart_nonneg w)
      calc n • w⁺ = ((n : ℝ)) • w⁺ := (Nat.cast_smul_eq_nsmul ℝ n w⁺).symm
        _ ≤ ((2 : ℝ) ^ n) • w⁺ := h4
        _ ≤ g := h3
    calc w ≤ w⁺ := le_posPart w
      _ = 0 := IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le (posPart_nonneg w) hple

/-- A real-valued net that order converges also converges in the usual sense, whatever
the universe of its index type. -/
private theorem tendsto_of_orderConvergesTo_real {κ : Type v} [Preorder κ]
    [IsDirected κ (· ≤ ·)] [Nonempty κ] {f : κ → ℝ} {a : ℝ}
    (hf : OrderConvergesTo f a) : Filter.Tendsto f Filter.atTop (nhds a) := by
  obtain ⟨κt, ht1, ht2, ht3, t, htanti, htnn, htglb, htev⟩ := hf
  letI := ht1; letI := ht2; letI := ht3
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hex : ∃ j, t j < ε := by
    by_contra hcon
    push Not at hcon
    have h1 : ε ≤ 0 := htglb.2 (by rintro _ ⟨j, rfl⟩; exact hcon j)
    linarith
  obtain ⟨j, hj⟩ := hex
  filter_upwards [htev j] with i hi
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hi hj

/-- If a positive functional `h` sends some regulator net of `x →o a` to a null net of
reals, then `h ∘ x` order converges to `h a`, regulated by the harmonic sequence. -/
private theorem orderConvergesTo_apply_of_tendsto_zero (h : X →ₗ[ℝ] ℝ) (hpos : Positive h)
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {κ : Type w} [Preorder κ] [IsDirected κ (· ≤ ·)] [Nonempty κ]
    {x : ι → X} {a : X} {r : κ → X} (hrnn : ∀ k, 0 ≤ r k)
    (hrev : ∀ k, ∀ᶠ i in Filter.atTop, |x i - a| ≤ r k)
    (htend : Filter.Tendsto (fun k => h (r k)) Filter.atTop (nhds 0)) :
    OrderConvergesTo (fun i => h (x i)) (h a) := by
  have hmono : Monotone h := Positive.monotone_iff.mpr hpos
  have hharm_anti : Antitone fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    intro n m hnm
    have h1 : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hnm
      linarith
    exact one_div_le_one_div_of_le (by positivity) h1
  refine ⟨ℕ, inferInstance, inferInstance, inferInstance,
    fun n => 1 / ((n : ℝ) + 1), hharm_anti, fun n => by positivity,
    isGLB_of_tendsto_atTop hharm_anti tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  intro n
  have hex : ∃ k, h (r k) < 1 / ((n : ℝ) + 1) := by
    have h2 := (Metric.tendsto_nhds.mp htend) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨k, hk⟩ := h2.exists
    refine ⟨k, ?_⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hpos _ (hrnn k))] at hk
  obtain ⟨k, hk⟩ := hex
  filter_upwards [hrev k] with i hi
  have h1 : |h (x i) - h a| ≤ h (r k) := by
    rw [← map_sub]
    exact (Positive.abs_le_map_abs hpos _).trans (hmono hi)
  exact h1.trans hk.le

/-- For an `L¹`-representation `T : X → L¹(μ)` of a vector lattice `X` with a strictly
positive functional `h`, the image of `X` is order dense in `L¹(μ)` if and only if `h` is
order continuous. -/
theorem isOrderDense_range_iff_isOrderContinuousOp
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h) (T : VecLatHom X (Lp ℝ 1 μ))
    (hT_inj : Function.Injective (T : X → Lp ℝ 1 μ))
    (hT_dense : DenseRange (T : X → Lp ℝ 1 μ))
    (hT_rep : ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ) :
    IsOrderDense (Set.range (T : X → Lp ℝ 1 μ)) ↔ IsOrderContinuousOp h := by
  have hmono : Monotone h := Positive.monotone_iff.mpr hh.positive
  have hnormT : ∀ x : X, 0 ≤ x → ‖T x‖ = h x := fun x hx => by
    rw [norm_map_eq_apply_abs h T hT_rep x, abs_of_nonneg hx]
  constructor
  · -- Order density of the image forces `h` to be order continuous.
    intro hOD ι ipre idir inon x a hxa
    obtain ⟨κ, hκ1, hκ2, hκ3, r, hranti, hrnn, hrglb, hrev⟩ := hxa
    letI := hκ1; letI := hκ2; letI := hκ3
    -- The regulator net maps to a net decreasing to zero in `L¹(μ)`.
    have hTr_glb : IsGLB (Set.range fun k => T (r k)) (0 : Lp ℝ 1 μ) := by
      constructor
      · rintro _ ⟨k, rfl⟩
        exact T.map_nonneg (hrnn k)
      · intro w hw
        have hwp_lb : ∀ k, w⁺ ≤ T (r k) := fun k => by
          rw [posPart_def]
          exact sup_le (hw ⟨k, rfl⟩) (T.map_nonneg (hrnn k))
        by_cases hwp : w⁺ = 0
        · calc w ≤ w⁺ := le_posPart w
            _ = 0 := hwp
        · exfalso
          obtain ⟨y, ⟨z, rfl⟩, hy_pos, hy_le⟩ :=
            hOD (lt_of_le_of_ne (posPart_nonneg w) (Ne.symm hwp))
          have hz_pos : 0 < z := by
            refine lt_of_le_of_ne (T.le_of_map_le hT_inj ?_) ?_
            · rw [map_zero]
              exact hy_pos.le
            · rintro rfl
              rw [map_zero] at hy_pos
              exact lt_irrefl _ hy_pos
          have hz_lb : z ∈ lowerBounds (Set.range r) := by
            rintro _ ⟨k, rfl⟩
            exact T.le_of_map_le hT_inj (hy_le.trans (hwp_lb k))
          exact (hz_pos.trans_le (hrglb.2 hz_lb)).false
    -- Order continuity of the `L¹` norm turns this into norm convergence.
    have hTr_tend : Filter.Tendsto (fun k => T (r k)) Filter.atTop (nhds (0 : Lp ℝ 1 μ)) :=
      IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero
        (fun _ _ hkk' => T.monotone (hranti hkk')) (fun k => T.map_nonneg (hrnn k)) hTr_glb
    have hhr_tend : Filter.Tendsto (fun k => h (r k)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k => ‖T (r k)‖) Filter.atTop (nhds 0) := by
        simpa using hTr_tend.norm
      exact h1.congr fun k => hnormT (r k) (hrnn k)
    exact orderConvergesTo_apply_of_tendsto_zero h hh.positive hrnn hrev hhr_tend
  · -- Order continuity of `h` forces the image to be order dense.
    intro hoc u hu
    -- A fast norm-approximating sequence for `u` from the dense image.
    have hex : ∀ k : ℕ, ∃ x' : X, dist u (T x') < (4 : ℝ)⁻¹ ^ k := fun k =>
      Metric.denseRange_iff.mp hT_dense u _ (by positivity)
    choose xr hxr using hex
    set xs : ℕ → X := fun k => (xr k)⁺ with hxs_def
    set v : ℕ → Lp ℝ 1 μ := fun k => T (xs k) with hv_def
    have hxs_nn : ∀ k, 0 ≤ xs k := fun k => posPart_nonneg _
    have hv_nn : ∀ k, 0 ≤ v k := fun k => T.map_nonneg (hxs_nn k)
    have hv_close : ∀ k, ‖v k - u‖ ≤ (4 : ℝ)⁻¹ ^ k := by
      intro k
      have h1 : v k = (T (xr k))⁺ := T.map_posPart (xr k)
      have h2 : u⁺ = u := by rw [posPart_def]; exact sup_eq_left.mpr hu.le
      have h3 : |(T (xr k))⁺ - u⁺| ≤ |T (xr k) - u| := by
        rw [posPart_def, posPart_def]
        exact abs_sup_sub_sup_le_abs _ _ _
      calc ‖v k - u‖ = ‖(T (xr k))⁺ - u⁺‖ := by rw [h1, h2]
        _ ≤ ‖T (xr k) - u‖ := norm_le_norm_of_abs_le_abs h3
        _ ≤ (4 : ℝ)⁻¹ ^ k := by
            rw [← dist_eq_norm, dist_comm]
            exact (hxr k).le
    -- The geometric regulator `g` controls the approximation.
    have hsum : Summable fun k : ℕ => (2 : ℝ) ^ k • |v k - u| := by
      refine Summable.of_norm_bounded (g := fun k : ℕ => (2 : ℝ)⁻¹ ^ k)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
      intro k
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k),
        norm_abs_eq_norm]
      calc (2 : ℝ) ^ k * ‖v k - u‖ ≤ (2 : ℝ) ^ k * (4 : ℝ)⁻¹ ^ k :=
            mul_le_mul_of_nonneg_left (hv_close k) (by positivity)
        _ = (2 : ℝ)⁻¹ ^ k := by
            rw [← mul_pow]
            norm_num
    set g : Lp ℝ 1 μ := ∑' k : ℕ, (2 : ℝ) ^ k • |v k - u| with hg_def
    have hg_nn : 0 ≤ g := tsum_nonneg fun k => smul_nonneg (by positivity) (abs_nonneg _)
    have hv_reg : ∀ k, |v k - u| ≤ (2 : ℝ)⁻¹ ^ k • g := by
      intro k
      have h1 : (2 : ℝ) ^ k • |v k - u| ≤ g :=
        hsum.le_tsum k fun j _ => smul_nonneg (by positivity) (abs_nonneg _)
      have h2 := smul_le_smul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ k)
      rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_smul] at h2
    have hg_glb := isGLB_range_pow_smul (Z := Lp ℝ 1 μ) hg_nn
    -- Since `0 < u`, some scale of the regulator fails to dominate `u`.
    have hk0 : ∃ k0 : ℕ, ¬ u ≤ (2 : ℝ)⁻¹ ^ k0 • g := by
      by_contra hcon
      push Not at hcon
      exact (hu.trans_le (hg_glb.2 (by rintro _ ⟨k, rfl⟩; exact hcon k))).false
    obtain ⟨k0, hk0⟩ := hk0
    set c : Lp ℝ 1 μ := (u - (2 : ℝ)⁻¹ ^ k0 • g)⁺ with hc_def
    have hc_pos : 0 < c := by
      refine lt_of_le_of_ne (posPart_nonneg _) fun h0 => ?_
      exact hk0 (sub_nonpos.mp (posPart_eq_zero.mp h0.symm))
    have hc_le_v : ∀ k, k0 ≤ k → c ≤ v k := by
      intro k hk
      have h1 : u - v k ≤ (2 : ℝ)⁻¹ ^ k0 • g := by
        calc u - v k ≤ |u - v k| := le_abs_self _
          _ = |v k - u| := abs_sub_comm _ _
          _ ≤ (2 : ℝ)⁻¹ ^ k • g := hv_reg k
          _ ≤ (2 : ℝ)⁻¹ ^ k0 • g :=
              smul_le_smul_of_nonneg_right
                (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hg_nn
      rw [hc_def, posPart_def]
      exact sup_le (sub_le_comm.mp h1) (hv_nn k)
    -- The key claim: some element of the image is positive and below the tail of `v`.
    have hclaim : ∃ z : X, 0 < T z ∧ ∀ k, k0 ≤ k → T z ≤ v k := by
      by_contra hno
      push Not at hno
      set s : ℕ → X := fun m =>
        (Finset.Icc k0 (k0 + m)).inf' (Finset.nonempty_Icc.mpr (Nat.le_add_right k0 m)) xs
        with hs_def
      have hs_anti : Antitone s := by
        intro m m' hmm'
        refine Finset.le_inf' _ _ fun j hj => ?_
        exact Finset.inf'_le _ (Finset.Icc_subset_Icc_right (by omega) hj)
      have hs_nn : ∀ m, 0 ≤ s m := fun m => Finset.le_inf' _ _ fun j _ => hxs_nn j
      have hTs_eq : ∀ m, T (s m) = (Finset.Icc k0 (k0 + m)).inf'
          (Finset.nonempty_Icc.mpr (Nat.le_add_right k0 m)) fun j => T (xs j) := fun m =>
        map_finset_inf' T _ xs
      have hc_le_Ts : ∀ m, c ≤ T (s m) := by
        intro m
        rw [hTs_eq m]
        exact Finset.le_inf' _ _ fun j hj => hc_le_v j (Finset.mem_Icc.mp hj).1
      -- If no such element exists, the partial infima decrease to zero in `X`.
      have hs_glb : IsGLB (Set.range s) (0 : X) := by
        constructor
        · rintro _ ⟨m, rfl⟩
          exact hs_nn m
        · intro w hw
          have hwp_le : ∀ k, k0 ≤ k → w⁺ ≤ xs k := by
            intro k hk
            have h1 : w ≤ s (k - k0) := hw ⟨k - k0, rfl⟩
            have h2 : s (k - k0) ≤ xs k :=
              Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hk, by omega⟩)
            rw [posPart_def]
            exact sup_le (h1.trans h2) (hxs_nn k)
          by_cases hwp : w⁺ = 0
          · calc w ≤ w⁺ := le_posPart w
              _ = 0 := hwp
          · exfalso
            have hTwp_pos : 0 < T w⁺ := by
              refine lt_of_le_of_ne (T.map_nonneg (posPart_nonneg w)) fun h0 => ?_
              exact hwp (hT_inj (h0.symm.trans (map_zero T).symm))
            obtain ⟨k, hk, hnle⟩ := hno w⁺ hTwp_pos
            exact hnle (T.monotone (hwp_le k hk))
      -- Order continuity of `h` then forces `h (s m) → 0`, contradicting `c > 0`.
      have hs_oconv : OrderConvergesTo (fun m : ULift.{u} ℕ => s m.down) (0 : X) := by
        refine orderConvergesTo_of_antitone_isGLB (fun _ _ hab => hs_anti (by exact hab)) ?_
        have hrange : Set.range (fun m : ULift.{u} ℕ => s m.down) = Set.range s := by
          ext w
          exact ⟨fun ⟨m, hm⟩ => ⟨m.down, hm⟩, fun ⟨m, hm⟩ => ⟨⟨m⟩, hm⟩⟩
        rw [hrange]
        exact hs_glb
      have hhs := hoc hs_oconv
      rw [map_zero] at hhs
      obtain ⟨κt, ht1, ht2, ht3, t, htanti, htnn, htglb, htev⟩ := hhs
      letI := ht1; letI := ht2; letI := ht3
      have hcnorm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_pos.ne'
      have hex_t : ∃ k, t k < ‖c‖ := by
        by_contra hcon
        push Not at hcon
        have h1 : ‖c‖ ≤ 0 := htglb.2 (by rintro _ ⟨k, rfl⟩; exact hcon k)
        linarith
      obtain ⟨k, hkt⟩ := hex_t
      obtain ⟨i, hi⟩ := (htev k).exists
      have hlow : ‖c‖ ≤ h (s i.down) := by
        have h1 : ‖c‖ ≤ ‖T (s i.down)‖ := by
          refine norm_le_norm_of_abs_le_abs ?_
          rw [abs_of_nonneg hc_pos.le, abs_of_nonneg (T.map_nonneg (hs_nn i.down))]
          exact hc_le_Ts i.down
        rwa [hnormT _ (hs_nn i.down)] at h1
      rw [sub_zero] at hi
      have hup : h (s i.down) ≤ t k := (le_abs_self _).trans hi
      linarith
    obtain ⟨z, hz_pos, hz_le⟩ := hclaim
    -- The witness lies below `u` because the regulator decreases to zero.
    have hall : ∀ k : ℕ, (T z - u)⁺ ≤ (2 : ℝ)⁻¹ ^ k • g := by
      have hbase : ∀ k, k0 ≤ k → (T z - u)⁺ ≤ (2 : ℝ)⁻¹ ^ k • g := by
        intro k hk
        rw [posPart_def]
        refine sup_le ?_ (smul_nonneg (by positivity) hg_nn)
        calc T z - u ≤ v k - u := sub_le_sub_right (hz_le k hk) u
          _ ≤ |v k - u| := le_abs_self _
          _ ≤ (2 : ℝ)⁻¹ ^ k • g := hv_reg k
      intro k
      rcases Nat.lt_or_ge k k0 with hk | hk
      · exact (hbase k0 le_rfl).trans (smul_le_smul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk.le) hg_nn)
      · exact hbase k hk
    have hzu : T z ≤ u := by
      have h1 : (T z - u)⁺ ≤ 0 := hg_glb.2 (by rintro _ ⟨k, rfl⟩; exact hall k)
      exact sub_nonpos.mp (posPart_eq_zero.mp (le_antisymm h1 (posPart_nonneg _)))
    exact ⟨T z, Set.mem_range_self z, hz_pos, hzu⟩

/-- A vector lattice homomorphism `T : X → L¹(μ)` realising the strictly positive
functional `h` as integration against `μ` on the positive cone is order continuous if and
only if `h` is order continuous. For an `L¹`-representation this says that the image of
`X` is a regular sublattice of `L¹(μ)` precisely when `h` is order continuous; neither
injectivity nor density of the image is needed for the equivalence. -/
theorem isOrderContinuousOp_toLinearMap_iff_isOrderContinuousOp
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h) (T : VecLatHom X (Lp ℝ 1 μ))
    (hT_rep : ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ) :
    IsOrderContinuousOp T.toLinearMap ↔ IsOrderContinuousOp h := by
  have hnormT : ∀ x : X, 0 ≤ x → ‖T x‖ = h x := fun x hx => by
    rw [norm_map_eq_apply_abs h T hT_rep x, abs_of_nonneg hx]
  constructor
  · -- If `T` is order continuous, so is `h = ‖T ·‖` on the positive cone.
    intro hToc ι ipre idir inon x a hxa
    obtain ⟨κ, hκ1, hκ2, hκ3, r, hranti, hrnn, hrglb, hrev⟩ := hxa
    letI := hκ1; letI := hκ2; letI := hκ3
    have hr0 : OrderConvergesTo r (0 : X) := orderConvergesTo_of_antitone_isGLB hranti hrglb
    have hTr0 : OrderConvergesTo (fun k => T.toLinearMap (r k)) (0 : Lp ℝ 1 μ) := by
      have h1 := hToc hr0
      rwa [map_zero] at h1
    have hTr_tend : Filter.Tendsto (fun k => T (r k)) Filter.atTop (nhds (0 : Lp ℝ 1 μ)) :=
      tendsto_of_orderConvergesTo_of_isOrderContinuousNorm hTr0
    have hhr_tend : Filter.Tendsto (fun k => h (r k)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k => ‖T (r k)‖) Filter.atTop (nhds 0) := by
        simpa using hTr_tend.norm
      exact h1.congr fun k => hnormT (r k) (hrnn k)
    exact orderConvergesTo_apply_of_tendsto_zero h hh.positive hrnn hrev hhr_tend
  · -- If `h` is order continuous, the image of a regulator net is again a regulator.
    intro hoc ι ipre idir inon x a hxa
    obtain ⟨κ, hκ1, hκ2, hκ3, r, hranti, hrnn, hrglb, hrev⟩ := hxa
    letI := hκ1; letI := hκ2; letI := hκ3
    have hr0 : OrderConvergesTo r (0 : X) := orderConvergesTo_of_antitone_isGLB hranti hrglb
    have hhr_tend : Filter.Tendsto (fun k => h (r k)) Filter.atTop (nhds 0) := by
      refine tendsto_of_orderConvergesTo_real ?_
      have h1 := hoc hr0
      rwa [map_zero] at h1
    have hTr_tend : Filter.Tendsto (fun k => T (r k)) Filter.atTop (nhds (0 : Lp ℝ 1 μ)) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact hhr_tend.congr fun k => (hnormT (r k) (hrnn k)).symm
    have hTr_glb : IsGLB (Set.range fun k => T (r k)) (0 : Lp ℝ 1 μ) := by
      constructor
      · rintro _ ⟨k, rfl⟩
        exact T.map_nonneg (hrnn k)
      · intro w hw
        exact ge_of_tendsto hTr_tend (Filter.Eventually.of_forall fun k => hw ⟨k, rfl⟩)
    refine ⟨κ, hκ1, hκ2, hκ3, fun k => T (r k), fun _ _ hkk' => T.monotone (hranti hkk'),
      fun k => T.map_nonneg (hrnn k), hTr_glb, ?_⟩
    intro k
    filter_upwards [hrev k] with i hi
    have h1 : T |x i - a| ≤ T (r k) := T.monotone hi
    rw [T.map_abs, map_sub] at h1
    exact h1

/-- For an `L¹`-representation `T : X → L¹(μ)` of a vector lattice `X` with a strictly
positive functional `h`, the image of `X` is solid in `L¹(μ)` — hence an order ideal —
if and only if `h` is order continuous and `X` is order complete. -/
theorem solid_range_iff_isOrderContinuousOp_and_orderComplete
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h) (T : VecLatHom X (Lp ℝ 1 μ))
    (hT_inj : Function.Injective (T : X → Lp ℝ 1 μ))
    (hT_dense : DenseRange (T : X → Lp ℝ 1 μ))
    (hT_rep : ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ) :
    (∀ u v : Lp ℝ 1 μ, u ∈ Set.range (T : X → Lp ℝ 1 μ) → |v| ≤ |u| →
        v ∈ Set.range (T : X → Lp ℝ 1 μ)) ↔
      IsOrderContinuousOp h ∧ ∀ S : Set X, S.Nonempty → BddAbove S → ∃ a, IsLUB S a := by
  constructor
  · -- A solid image forces order continuity of `h` and order completeness of `X`.
    intro hsolid
    have hToc : IsOrderContinuousOp T.toLinearMap := by
      intro ι ipre idir inon x a hxa
      obtain ⟨κ, hκ1, hκ2, hκ3, r, hranti, hrnn, hrglb, hrev⟩ := hxa
      letI := hκ1; letI := hκ2; letI := hκ3
      -- Solidity puts positive lower bounds of the image net back in the image.
      have hTr_glb : IsGLB (Set.range fun k => T (r k)) (0 : Lp ℝ 1 μ) := by
        constructor
        · rintro _ ⟨k, rfl⟩
          exact T.map_nonneg (hrnn k)
        · intro w hw
          have hwp_lb : ∀ k, w⁺ ≤ T (r k) := fun k => by
            rw [posPart_def]
            exact sup_le (hw ⟨k, rfl⟩) (T.map_nonneg (hrnn k))
          obtain ⟨k₀⟩ := (inferInstance : Nonempty κ)
          obtain ⟨z, hz⟩ := hsolid (T (r k₀)) w⁺ ⟨r k₀, rfl⟩ (by
            rw [abs_of_nonneg (posPart_nonneg w), abs_of_nonneg (T.map_nonneg (hrnn k₀))]
            exact hwp_lb k₀)
          have hz_lb : z ∈ lowerBounds (Set.range r) := by
            rintro _ ⟨k, rfl⟩
            exact T.le_of_map_le hT_inj (by rw [hz]; exact hwp_lb k)
          have hwp0 : w⁺ = 0 := by
            refine le_antisymm ?_ (posPart_nonneg w)
            rw [← hz]
            have h1 := T.monotone (hrglb.2 hz_lb)
            rwa [map_zero] at h1
          calc w ≤ w⁺ := le_posPart w
            _ = 0 := hwp0
      refine ⟨κ, hκ1, hκ2, hκ3, fun k => T (r k), fun _ _ hkk' => T.monotone (hranti hkk'),
        fun k => T.map_nonneg (hrnn k), hTr_glb, ?_⟩
      intro k
      filter_upwards [hrev k] with i hi
      have h1 : T |x i - a| ≤ T (r k) := T.monotone hi
      rw [T.map_abs, map_sub] at h1
      exact h1
    refine ⟨(isOrderContinuousOp_toLinearMap_iff_isOrderContinuousOp h hh T hT_rep).mp hToc,
      ?_⟩
    -- Order completeness: pull the supremum in `L¹(μ)` back through the solid image.
    intro S hSne hSbdd
    obtain ⟨s₀, hs₀⟩ := hSne
    obtain ⟨b, hb⟩ := hSbdd
    have hTS_ne : ((T : X → Lp ℝ 1 μ) '' S).Nonempty := ⟨T s₀, ⟨s₀, hs₀, rfl⟩⟩
    have hTS_bdd : BddAbove ((T : X → Lp ℝ 1 μ) '' S) := by
      refine ⟨T b, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact T.monotone (hb hs)
    have hexists : ∃ w, IsLUB ((T : X → Lp ℝ 1 μ) '' S) w := by
      letI : ConditionallyCompleteLattice (Lp ℝ 1 μ) :=
        BanachLattice.conditionallyCompleteLatticeOfIsOrderContinuousNorm (X := Lp ℝ 1 μ)
      exact ⟨sSup ((T : X → Lp ℝ 1 μ) '' S), isLUB_csSup hTS_ne (hb := hTS_bdd)⟩
    obtain ⟨w, hw⟩ := hexists
    have h1 : T s₀ ≤ w := hw.1 ⟨s₀, hs₀, rfl⟩
    have h2 : w ≤ T b := by
      refine hw.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      exact T.monotone (hb hs)
    obtain ⟨c, hc⟩ := hsolid (T (|s₀| ⊔ |b|)) w ⟨_, rfl⟩ (by
      rw [abs_of_nonneg (T.map_nonneg (le_trans (abs_nonneg s₀) le_sup_left)), map_sup,
        T.map_abs, T.map_abs, abs]
      refine sup_le (h2.trans ((le_abs_self (T b)).trans le_sup_right)) ?_
      exact (neg_le_neg h1).trans ((neg_le_abs (T s₀)).trans le_sup_left))
    refine ⟨c, ?_, ?_⟩
    · intro s hs
      exact T.le_of_map_le hT_inj (by rw [hc]; exact hw.1 ⟨s, hs, rfl⟩)
    · intro c' hc'
      refine T.le_of_map_le hT_inj ?_
      rw [hc]
      refine hw.2 ?_
      rintro _ ⟨s, hs, rfl⟩
      exact T.monotone (hc' hs)
  · -- Order continuity and order completeness make the image solid.
    rintro ⟨hoc, hcomp⟩
    have hOD : IsOrderDense (Set.range (T : X → Lp ℝ 1 μ)) :=
      (isOrderDense_range_iff_isOrderContinuousOp h hh T hT_inj hT_dense hT_rep).mpr hoc
    have hToc : IsOrderContinuousOp T.toLinearMap :=
      (isOrderContinuousOp_toLinearMap_iff_isOrderContinuousOp h hh T hT_rep).mpr hoc
    -- The positive case: `0 ≤ w ≤ T y` puts `w` in the image.
    have hkey : ∀ (y : X) (w : Lp ℝ 1 μ), 0 ≤ w → w ≤ T y →
        w ∈ Set.range (T : X → Lp ℝ 1 μ) := by
      intro y w hw_nn hw_le
      set A : Set X := {x : X | 0 ≤ x ∧ T x ≤ w} with hA_def
      have hA_ne : A.Nonempty := ⟨0, le_rfl, by rw [map_zero]; exact hw_nn⟩
      have hA_bdd : BddAbove A := ⟨y, fun x hx => T.le_of_map_le hT_inj (hx.2.trans hw_le)⟩
      obtain ⟨c, hc⟩ := hcomp A hA_ne hA_bdd
      -- `w` is the least upper bound of the image of `A`, by order density.
      have hlub_w : IsLUB ((T : X → Lp ℝ 1 μ) '' A) w := by
        constructor
        · rintro _ ⟨x, hx, rfl⟩
          exact hx.2
        · intro q hq
          by_contra hwq
          have hpos : 0 < w - q ⊓ w := by
            refine lt_of_le_of_ne (sub_nonneg.mpr inf_le_right) fun h0 => ?_
            exact hwq ((le_of_eq (sub_eq_zero.mp h0.symm)).trans inf_le_left)
          obtain ⟨p, ⟨d, rfl⟩, hp_pos, hp_le⟩ := hOD hpos
          have hd_nn : 0 ≤ d :=
            T.le_of_map_le hT_inj (by rw [map_zero]; exact hp_pos.le)
          have hstep : ∀ x, x ∈ A → d + x ∈ A := by
            intro x hx
            refine ⟨add_nonneg hd_nn hx.1, ?_⟩
            rw [map_add]
            have hxq : T x ≤ q ⊓ w := le_inf (hq ⟨x, hx, rfl⟩) hx.2
            calc T d + T x ≤ (w - q ⊓ w) + q ⊓ w := add_le_add hp_le hxq
              _ = w := by abel
          have hnd : ∀ n : ℕ, (n • d) ∈ A := by
            intro n
            induction n with
            | zero =>
              rw [zero_nsmul]
              exact ⟨le_rfl, by rw [map_zero]; exact hw_nn⟩
            | succ n ih =>
              have h2 := hstep _ ih
              have h3 : (n + 1) • d = d + n • d := by rw [succ_nsmul, add_comm]
              rwa [h3]
          have hTd_le : ∀ n : ℕ, n • T d ≤ w := by
            intro n
            have h4 := (hnd n).2
            rwa [map_nsmul] at h4
          exact hp_pos.ne'
            (IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le hp_pos.le hTd_le)
      -- `T c` is also its least upper bound, by order continuity along the net `A`.
      haveI : Nonempty ↥A := hA_ne.to_subtype
      haveI : IsDirected ↥A (· ≤ ·) := by
        refine ⟨fun a b => ?_⟩
        refine ⟨⟨(a : X) ⊔ (b : X), le_trans a.2.1 le_sup_left, ?_⟩, le_sup_left, le_sup_right⟩
        rw [map_sup]
        exact sup_le a.2.2 b.2.2
      have hval_lub : IsLUB (Set.range ((↑) : ↥A → X)) c := by
        rw [Subtype.range_coe]
        exact hc
      have hconv : OrderConvergesTo ((↑) : ↥A → X) c :=
        orderConvergesTo_of_monotone_isLUB (fun _ _ hab => hab) hval_lub
      have hTconv := hToc hconv
      have hTc_le : T c ≤ w := hTconv.le_of_forall_le fun a => a.2.2
      have hw_le : w ≤ T c := by
        refine hlub_w.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact T.monotone (hc.1 hx)
      exact ⟨c, le_antisymm hTc_le hw_le⟩
    -- Reduce the general case to the positive one via `v = v⁺ - v⁻`.
    intro u v hu hvu
    obtain ⟨z, rfl⟩ := hu
    have hvu' : |v| ≤ T |z| := by rwa [T.map_abs]
    have hvp : v⁺ ∈ Set.range (T : X → Lp ℝ 1 μ) := by
      refine hkey |z| v⁺ (posPart_nonneg v) (le_trans ?_ hvu')
      rw [posPart_def]
      exact sup_le (le_abs_self v) (abs_nonneg v)
    have hvn : v⁻ ∈ Set.range (T : X → Lp ℝ 1 μ) := by
      refine hkey |z| v⁻ (negPart_nonneg v) (le_trans ?_ hvu')
      rw [negPart_def]
      exact sup_le (neg_le_abs v) (abs_nonneg v)
    obtain ⟨zp, hzp⟩ := hvp
    obtain ⟨zn, hzn⟩ := hvn
    exact ⟨zp - zn, by rw [map_sub, hzp, hzn, posPart_sub_negPart]⟩
