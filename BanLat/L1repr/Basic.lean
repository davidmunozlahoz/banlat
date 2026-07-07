import BanLat.ALSpace.Kakutani
import BanLat.Operators.StrictlyPositive

/-!
# `L¹`-representation of a vector lattice with a strictly positive functional

A vector lattice `X` carrying a strictly positive linear functional `h` embeds as a dense
sublattice into `L¹(μ)` for some measure `μ`, in such a way that `h` is realised as
integration against `μ` on the positive cone: `h x = ∫ T x dμ` for every `x ≥ 0`.
-/

open MeasureTheory

universe u

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]

/-- **`L¹`-representation.** A vector lattice with a strictly positive functional `h`
embeds as a dense sublattice into an `L¹` space: there is a measure `μ` and an injective
vector lattice homomorphism `T : X → L¹(μ)` with dense range such that `h x = ∫ T x dμ`
for every `x ≥ 0`. -/
theorem exists_L1_representation_of_strictlyPositive
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (T : VecLatHom X (Lp ℝ 1 μ)),
      Function.Injective (T : X → Lp ℝ 1 μ) ∧ DenseRange (T : X → Lp ℝ 1 μ) ∧
        ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ := by
  letI : NormedAddCommGroup X := StrictlyPositive.associatedNormedAddCommGroup h hh
  letI : NormedVectorLattice X := StrictlyPositive.associatedNormedVectorLattice h hh
  have hAL : ∀ x y : X, x ⊓ y = 0 → ‖x + y‖ = ‖x‖ + ‖y‖ :=
    fun x y hxy => StrictlyPositive.associatedNorm_add_eq_norm_add_of_inf_eq_zero h hh hxy
  letI : ALSpace (UniformSpace.Completion X) := ALSpace.completion hAL
  obtain ⟨Ω, mΩ, μ, ⟨e⟩⟩ := ALSpace.exists_L1_banachLatEquiv (X := UniformSpace.Completion X)
  have hTx : ∀ x : X, (e.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom) x
      = e (↑x : UniformSpace.Completion X) := fun _ => rfl
  refine ⟨Ω, mΩ, μ, (e.toVecLatEquiv.toVecLatHom).comp toCompletionVecLatHom, ?_, ?_, ?_⟩
  · intro a b hab
    rw [hTx a, hTx b] at hab
    exact isometry_toCompletionVecLatHom.injective (e.toLinearIsometryEquiv.injective hab)
  · have hcomp : ⇑(e.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom)
        = ⇑e.toLinearIsometryEquiv ∘ ((↑) : X → UniformSpace.Completion X) := funext hTx
    rw [hcomp]
    exact (e.toLinearIsometryEquiv.surjective.denseRange).comp
      UniformSpace.Completion.denseRange_coe e.toLinearIsometryEquiv.continuous
  · intro x hx
    set T := e.toVecLatEquiv.toVecLatHom.comp toCompletionVecLatHom with hTdef
    have hTxnn : 0 ≤ T x := T.map_nonneg hx
    have hae : (0 : Ω → ℝ) ≤ᵐ[μ] (T x) := (Lp.coeFn_nonneg (T x)).mpr hTxnn
    have hintegrand : (fun ω => ‖(T x) ω‖) =ᵐ[μ] (fun ω => (T x) ω) := by
      filter_upwards [hae] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω]
    have hnorm : ‖T x‖ = h x := by
      have e1 : ‖T x‖ = ‖(↑x : UniformSpace.Completion X)‖ := by
        rw [hTx x]; exact e.toLinearIsometryEquiv.norm_map _
      rw [e1, UniformSpace.Completion.norm_coe,
        StrictlyPositive.associatedNormedAddCommGroup_norm h hh]
      change h |x| = h x
      rw [abs_of_nonneg hx]
    rw [← hnorm, L1.norm_eq_integral_norm]
    exact integral_congr_ae hintegrand

/-- The strictly positive functional `h`, viewed as an element of the order dual of `X`,
is strictly positive whenever `X` is non-trivial. -/
private theorem ofPositive_pos_of_strictlyPositive [Nontrivial X] {h : X →ₗ[ℝ] ℝ}
    (hh : StrictlyPositive h) :
    (0 : OrderDualSpace X) < OrderBoundedHom.ofPositive h hh.positive := by
  refine lt_of_le_of_ne ?_ (fun hcontra => ?_)
  · rw [OrderDualSpace.nonneg_iff]
    intro x hx
    simpa using hh.positive x hx
  · obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have habs_ne : |x| ≠ 0 := fun h0 => hx ((abs_eq_zero_iff_zero x).mp h0)
    have habs_pos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm habs_ne)
    have hzero : OrderBoundedHom.ofPositive h hh.positive |x| = 0 := by rw [← hcontra]; rfl
    rw [OrderBoundedHom.ofPositive_apply] at hzero
    exact (ne_of_gt (hh |x| habs_pos)) hzero

/-- Precomposition by a linear isometry equivalence `e : A ≃ₗᵢ B` is an isometric linear
equivalence `StrongDual ℝ B ≃ₗᵢ StrongDual ℝ A`. -/
noncomputable def dualLIE {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℝ A] [NormedSpace ℝ B] (e : A ≃ₗᵢ[ℝ] B) :
    StrongDual ℝ B ≃ₗᵢ[ℝ] StrongDual ℝ A where
  toFun φ := φ.comp (e : A →L[ℝ] B)
  invFun ψ := ψ.comp (e.symm : B →L[ℝ] A)
  map_add' φ ψ := by ext a; simp
  map_smul' r φ := by ext a; simp
  left_inv φ := by ext a; simp
  right_inv ψ := by ext b; simp
  norm_map' φ := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv φ e

@[simp]
theorem dualLIE_apply {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℝ A] [NormedSpace ℝ B] (e : A ≃ₗᵢ[ℝ] B) (φ : StrongDual ℝ B) (a : A) :
    dualLIE e φ a = φ (e a) := rfl

/-- The **contravariant dual** of a Banach lattice isometry `e : A ≃ B`: precomposition
`φ ↦ φ ∘ e` is a Banach lattice isometry `StrongDual ℝ B ≃ StrongDual ℝ A`. -/
noncomputable def banachLatEquivDual {A B : Type*}
    [NormedAddCommGroup A] [NormedAddCommGroup B] [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B] [BanachLattice A] [BanachLattice B]
    (e : BanachLatEquiv A B) : BanachLatEquiv (StrongDual ℝ B) (StrongDual ℝ A) := by
  have hmono : ∀ {φ ψ : StrongDual ℝ B}, φ ≤ ψ →
      dualLIE e.toLinearIsometryEquiv φ ≤ dualLIE e.toLinearIsometryEquiv ψ := by
    intro φ ψ hφψ
    rw [StrongDual.le_iff]
    intro a ha
    rw [dualLIE_apply, dualLIE_apply]
    exact (StrongDual.le_iff.mp hφψ) (e a) (e.toVecLatEquiv.toVecLatHom.map_nonneg ha)
  have hrefl : ∀ {φ ψ : StrongDual ℝ B}, dualLIE e.toLinearIsometryEquiv φ ≤
      dualLIE e.toLinearIsometryEquiv ψ → φ ≤ ψ := by
    intro φ ψ hφψ
    rw [StrongDual.le_iff]
    intro b hb
    have key := (StrongDual.le_iff.mp hφψ) (e.toLinearIsometryEquiv.symm b)
      (e.symm.toVecLatEquiv.toVecLatHom.map_nonneg hb)
    rwa [dualLIE_apply, dualLIE_apply, LinearIsometryEquiv.apply_symm_apply] at key
  set D := dualLIE e.toLinearIsometryEquiv with hD
  have hmono_symm : ∀ {χ χ' : StrongDual ℝ A}, χ ≤ χ' → D.symm χ ≤ D.symm χ' := by
    intro χ χ' h
    apply hrefl
    rw [D.apply_symm_apply, D.apply_symm_apply]
    exact h
  exact
  { toLinearIsometryEquiv := D
    map_sup' := fun φ ψ => by
      refine le_antisymm ?_ (sup_le (hmono le_sup_left) (hmono le_sup_right))
      have hφ : φ ≤ D.symm (D φ ⊔ D ψ) := by
        have h := hmono_symm (le_sup_left : D φ ≤ D φ ⊔ D ψ)
        rwa [D.symm_apply_apply] at h
      have hψ : ψ ≤ D.symm (D φ ⊔ D ψ) := by
        have h := hmono_symm (le_sup_right : D ψ ≤ D φ ⊔ D ψ)
        rwa [D.symm_apply_apply] at h
      calc D (φ ⊔ ψ) ≤ D (D.symm (D φ ⊔ D ψ)) := hmono (sup_le hφ hψ)
        _ = D φ ⊔ D ψ := D.apply_symm_apply _
    map_inf' := fun φ ψ => by
      refine le_antisymm (le_inf (hmono inf_le_left) (hmono inf_le_right)) ?_
      have hφ : D.symm (D φ ⊓ D ψ) ≤ φ := by
        have h := hmono_symm (inf_le_left : D φ ⊓ D ψ ≤ D φ)
        rwa [D.symm_apply_apply] at h
      have hψ : D.symm (D φ ⊓ D ψ) ≤ ψ := by
        have h := hmono_symm (inf_le_right : D φ ⊓ D ψ ≤ D ψ)
        rwa [D.symm_apply_apply] at h
      calc D φ ⊓ D ψ = D (D.symm (D φ ⊓ D ψ)) := (D.apply_symm_apply _).symm
        _ ≤ D (φ ⊓ ψ) := hmono (le_inf hφ hψ) }

/-- If `T : X → L¹(μ)` is a vector lattice homomorphism realising `h` as integration against
`μ` on the positive cone, then `‖T x‖ = h |x|` for every `x`; that is, `T` preserves the
AL-type norm `‖x‖ = h |x|` associated to `h`. -/
theorem norm_map_eq_apply_abs {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : X →ₗ[ℝ] ℝ) (T : VecLatHom X (Lp ℝ 1 μ))
    (hT_rep : ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ) (x : X) :
    ‖T x‖ = h |x| := by
  have hnn : 0 ≤ T |x| := T.map_nonneg (abs_nonneg x)
  have hae : (0 : Ω → ℝ) ≤ᵐ[μ] (T |x|) := (Lp.coeFn_nonneg (T |x|)).mpr hnn
  have hintegrand : (fun ω => ‖(T |x|) ω‖) =ᵐ[μ] (fun ω => (T |x|) ω) := by
    filter_upwards [hae] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω]
  calc ‖T x‖ = ‖T |x|‖ := by rw [T.map_abs]; exact (norm_abs_eq_norm (T x)).symm
    _ = ∫ ω, ‖(T |x|) ω‖ ∂μ := L1.norm_eq_integral_norm _
    _ = ∫ ω, (T |x|) ω ∂μ := integral_congr_ae hintegrand
    _ = h |x| := (hT_rep |x| (abs_nonneg x)).symm

/-- The strong dual of the completion of a normed vector lattice `X` whose norm is given by
`‖x‖ = ĥ |x|` for a strictly positive order-bounded functional `ĥ` is lattice isometric to
the principal ideal generated by `ĥ` in the order dual of `X`, equipped with its gauge
norm. The isometry is restriction along the inclusion `X → X̂`. -/
private theorem banachLatEquiv_strongDual_completion_principal
    {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] {ĥ : OrderDualSpace X} (hĥ : 0 < ĥ)
    (hnorm : ∀ x : X, ‖x‖ = ĥ |x|) :
    letI : IsUniformlyCompleteVectorLattice (OrderDualSpace X) :=
      isUniformlyCompleteVectorLattice_of_sigmaConditionallyCompleteLattice (OrderDualSpace X)
    letI := OrderIdeal.principalNormedAddCommGroup ĥ (ne_of_gt hĥ)
    letI : Lattice ↥(OrderIdeal.principal ĥ) := OrderIdeal.instLatticePrincipal _
    letI : IsOrderedAddMonoid ↥(OrderIdeal.principal ĥ) :=
      OrderIdeal.instIsOrderedAddMonoidPrincipal _
    letI : AMSpaceWithUnit ↥(OrderIdeal.principal ĥ) :=
      OrderIdeal.principalAMSpaceWithUnit hĥ.le (ne_of_gt hĥ)
        (IsUniformlyCompleteVectorLattice.complete_principal _ hĥ)
    Nonempty (BanachLatEquiv (StrongDual ℝ (UniformSpace.Completion X))
      ↥(OrderIdeal.principal ĥ)) := by
  letI : IsUniformlyCompleteVectorLattice (OrderDualSpace X) :=
    isUniformlyCompleteVectorLattice_of_sigmaConditionallyCompleteLattice (OrderDualSpace X)
  letI := OrderIdeal.principalNormedAddCommGroup ĥ (ne_of_gt hĥ)
  letI : Lattice ↥(OrderIdeal.principal ĥ) := OrderIdeal.instLatticePrincipal _
  letI : IsOrderedAddMonoid ↥(OrderIdeal.principal ĥ) :=
    OrderIdeal.instIsOrderedAddMonoidPrincipal _
  letI : AMSpaceWithUnit ↥(OrderIdeal.principal ĥ) :=
    OrderIdeal.principalAMSpaceWithUnit hĥ.le (ne_of_gt hĥ)
      (IsUniformlyCompleteVectorLattice.complete_principal _ hĥ)
  have hĥ_nonneg : (0 : OrderDualSpace X) ≤ ĥ := hĥ.le
  -- The fundamental bound: the restriction of `φ` to `X` has modulus at most `‖φ‖ • ĥ`.
  have hb : ∀ φ : StrongDual ℝ (UniformSpace.Completion X),
      |StrongDual.toOrderDualSpace (φ.comp UniformSpace.Completion.toComplL)| ≤ ‖φ‖ • ĥ := by
    intro φ
    rw [OrderDualSpace.le_iff]
    intro x hx
    refine (OrderDualSpace.isLUB_abs_apply
      (φ := StrongDual.toOrderDualSpace (φ.comp UniformSpace.Completion.toComplL)) hx).2 ?_
    rintro r ⟨y, hyx, rfl⟩
    have hyle : ‖y‖ ≤ ‖x‖ :=
      norm_le_norm_of_abs_le_abs (by rw [abs_of_nonneg hx]; exact hyx)
    calc |StrongDual.toOrderDualSpace (φ.comp UniformSpace.Completion.toComplL) y|
        = ‖φ (y : UniformSpace.Completion X)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ‖ * ‖(y : UniformSpace.Completion X)‖ := φ.le_opNorm _
      _ = ‖φ‖ * ‖y‖ := by rw [UniformSpace.Completion.norm_coe]
      _ ≤ ‖φ‖ * ‖x‖ := by gcongr
      _ = ‖φ‖ * ĥ x := by rw [hnorm x, abs_of_nonneg hx]
      _ = (‖φ‖ • ĥ) x := rfl
  have hmem : ∀ φ : StrongDual ℝ (UniformSpace.Completion X),
      StrongDual.toOrderDualSpace (φ.comp UniformSpace.Completion.toComplL) ∈
        OrderIdeal.principal ĥ := fun φ =>
    OrderIdeal.mem_principal.mpr
      ⟨‖φ‖, norm_nonneg φ, by rw [abs_of_nonneg hĥ_nonneg]; exact hb φ⟩
  -- The restriction map `res φ = φ ∘ ι`, valued in the principal ideal `I_ĥ`.
  let res : StrongDual ℝ (UniformSpace.Completion X) →ₗ[ℝ]
      ↥(OrderIdeal.principal ĥ) :=
    { toFun := fun φ => ⟨StrongDual.toOrderDualSpace
        (φ.comp UniformSpace.Completion.toComplL), hmem φ⟩
      map_add' := fun φ φ' => by
        apply Subtype.ext
        ext z
        rfl
      map_smul' := fun r φ => by
        apply Subtype.ext
        ext z
        rfl }
  have hres_apply : ∀ (φ : StrongDual ℝ (UniformSpace.Completion X)) (x : X),
      (res φ : OrderDualSpace X) x = φ (x : UniformSpace.Completion X) := fun _ _ => rfl
  have hinj : Function.Injective res := by
    intro φ ψ hφψ
    have hxeq : ∀ x : X,
        φ (x : UniformSpace.Completion X) = ψ (x : UniformSpace.Completion X) := by
      intro x
      have hval : (res φ : OrderDualSpace X) x = (res ψ : OrderDualSpace X) x :=
        congrArg (fun a : ↥(OrderIdeal.principal ĥ) => (a : OrderDualSpace X) x) hφψ
      rwa [hres_apply, hres_apply] at hval
    ext z
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq φ.continuous ψ.continuous) ?_
    exact hxeq
  -- Surjectivity: an element of `I_ĥ` is norm bounded on `X`, so it extends to `X̂`.
  have hsurj : Function.Surjective res := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨c, hc, hcle⟩ := OrderIdeal.mem_principal.mp hψ
    rw [abs_of_nonneg hĥ_nonneg] at hcle
    have hbnd : ∀ x : X, ‖ψ.toLinearMap x‖ ≤ c * ‖x‖ := by
      intro x
      rw [Real.norm_eq_abs]
      have h1 : |ψ x| ≤ |ψ| |x| :=
        (OrderDualSpace.isLUB_abs_apply (abs_nonneg x)).1 ⟨x, le_rfl, rfl⟩
      have h2 : |ψ| |x| ≤ (c • ĥ) |x| :=
        OrderDualSpace.le_iff.mp hcle |x| (abs_nonneg x)
      calc |ψ.toLinearMap x| = |ψ x| := rfl
        _ ≤ |ψ| |x| := h1
        _ ≤ c * ĥ |x| := h2
        _ = c * ‖x‖ := by rw [hnorm x]
    refine ⟨(LinearMap.mkContinuous ψ.toLinearMap c hbnd).extend
      UniformSpace.Completion.toComplL, ?_⟩
    apply Subtype.ext
    ext x
    change ((LinearMap.mkContinuous ψ.toLinearMap c hbnd).extend
      UniformSpace.Completion.toComplL) (x : UniformSpace.Completion X) = ψ x
    exact ContinuousLinearMap.extend_eq (e := UniformSpace.Completion.toComplL)
      (LinearMap.mkContinuous ψ.toLinearMap c hbnd)
      UniformSpace.Completion.denseRange_coe
      (UniformSpace.Completion.isUniformInducing_coe X) x
  -- `res` is an isometry for the gauge norm on `I_ĥ`.
  have hnorm_map : ∀ φ : StrongDual ℝ (UniformSpace.Completion X), ‖res φ‖ = ‖φ‖ := by
    intro φ
    refine le_antisymm ?_ ?_
    · change OrderIdeal.gaugeNorm ĥ ((res φ : OrderDualSpace X)) ≤ ‖φ‖
      refine OrderIdeal.gaugeNorm_le_of_abs_le ĥ (norm_nonneg φ) ?_
      rw [abs_of_nonneg hĥ_nonneg]
      exact hb φ
    · have habs : |(res φ : OrderDualSpace X)| ≤ ‖res φ‖ • ĥ := by
        have h1 := OrderIdeal.abs_le_gaugeNorm_smul_abs ĥ (res φ).2
        rwa [abs_of_nonneg hĥ_nonneg] at h1
      refine φ.opNorm_le_bound (norm_nonneg _) ?_
      intro z
      refine UniformSpace.Completion.induction_on z
        (isClosed_le φ.continuous.norm (continuous_const.mul continuous_norm)) ?_
      intro x
      have h1 : |φ (x : UniformSpace.Completion X)| ≤ |(res φ : OrderDualSpace X)| |x| := by
        rw [← hres_apply φ x]
        exact (OrderDualSpace.isLUB_abs_apply (abs_nonneg x)).1 ⟨x, le_rfl, rfl⟩
      have h2 : |(res φ : OrderDualSpace X)| |x| ≤ (‖res φ‖ • ĥ) |x| :=
        OrderDualSpace.le_iff.mp habs |x| (abs_nonneg x)
      calc ‖φ (x : UniformSpace.Completion X)‖
          = |φ (x : UniformSpace.Completion X)| := Real.norm_eq_abs _
        _ ≤ (‖res φ‖ • ĥ) |x| := h1.trans h2
        _ = ‖res φ‖ * ĥ |x| := rfl
        _ = ‖res φ‖ * ‖x‖ := by rw [hnorm x]
        _ = ‖res φ‖ * ‖(x : UniformSpace.Completion X)‖ := by
            rw [UniformSpace.Completion.norm_coe]
  -- `res` is an order isomorphism: monotone with monotone inverse.
  have hmono : ∀ {φ ψ : StrongDual ℝ (UniformSpace.Completion X)},
      φ ≤ ψ → res φ ≤ res ψ := by
    intro φ ψ hφψ
    change (res φ : OrderDualSpace X) ≤ (res ψ : OrderDualSpace X)
    rw [OrderDualSpace.le_iff]
    intro x hx
    rw [hres_apply, hres_apply]
    exact StrongDual.le_iff.mp hφψ _ (toCompletionVecLatHom.map_nonneg hx)
  have hrefl : ∀ {φ ψ : StrongDual ℝ (UniformSpace.Completion X)},
      res φ ≤ res ψ → φ ≤ ψ := by
    intro φ ψ hle
    have hle' : (res φ : OrderDualSpace X) ≤ (res ψ : OrderDualSpace X) := hle
    have key : ∀ w : UniformSpace.Completion X, φ (w ⊔ 0) ≤ ψ (w ⊔ 0) := by
      intro w
      refine UniformSpace.Completion.induction_on w
        (isClosed_le (φ.continuous.comp (continuous_id.sup continuous_const))
          (ψ.continuous.comp (continuous_id.sup continuous_const))) ?_
      intro x
      have hcoe : ((x ⊔ 0 : X) : UniformSpace.Completion X)
          = (x : UniformSpace.Completion X) ⊔ 0 := by
        rw [coe_sup_completion, UniformSpace.Completion.coe_zero]
      rw [← hcoe, ← hres_apply φ, ← hres_apply ψ]
      exact OrderDualSpace.le_iff.mp hle' (x ⊔ 0) le_sup_right
    rw [StrongDual.le_iff]
    intro z hz
    have h := key z
    rwa [sup_eq_left.mpr hz] at h
  -- Assemble the Banach lattice isometry.
  let D : StrongDual ℝ (UniformSpace.Completion X) ≃ₗᵢ[ℝ] ↥(OrderIdeal.principal ĥ) :=
    { toLinearEquiv := LinearEquiv.ofBijective res ⟨hinj, hsurj⟩
      norm_map' := hnorm_map }
  have hmono_symm : ∀ {χ χ' : ↥(OrderIdeal.principal ĥ)},
      χ ≤ χ' → D.symm χ ≤ D.symm χ' := by
    intro χ χ' hcc
    refine hrefl ?_
    have h1 : res (D.symm χ) = χ := D.apply_symm_apply χ
    have h2 : res (D.symm χ') = χ' := D.apply_symm_apply χ'
    rw [h1, h2]
    exact hcc
  refine ⟨{ toLinearIsometryEquiv := D
            map_sup' := fun φ ψ => ?_
            map_inf' := fun φ ψ => ?_ }⟩
  · refine le_antisymm ?_ (sup_le (hmono le_sup_left) (hmono le_sup_right))
    have hφ : φ ≤ D.symm (D φ ⊔ D ψ) := by
      have h := hmono_symm (le_sup_left : D φ ≤ D φ ⊔ D ψ)
      rwa [D.symm_apply_apply] at h
    have hψ : ψ ≤ D.symm (D φ ⊔ D ψ) := by
      have h := hmono_symm (le_sup_right : D ψ ≤ D φ ⊔ D ψ)
      rwa [D.symm_apply_apply] at h
    calc D (φ ⊔ ψ) ≤ D (D.symm (D φ ⊔ D ψ)) := hmono (sup_le hφ hψ)
      _ = D φ ⊔ D ψ := D.apply_symm_apply _
  · refine le_antisymm (le_inf (hmono inf_le_left) (hmono inf_le_right)) ?_
    have hφ : D.symm (D φ ⊓ D ψ) ≤ φ := by
      have h := hmono_symm (inf_le_left : D φ ⊓ D ψ ≤ D φ)
      rwa [D.symm_apply_apply] at h
    have hψ : D.symm (D φ ⊓ D ψ) ≤ ψ := by
      have h := hmono_symm (inf_le_right : D φ ⊓ D ψ ≤ D ψ)
      rwa [D.symm_apply_apply] at h
    calc D φ ⊓ D ψ = D (D.symm (D φ ⊓ D ψ)) := (D.apply_symm_apply _).symm
      _ ≤ D (φ ⊓ ψ) := hmono (le_inf hφ hψ)

/-- **The dual of an `L¹`-representation.** For any `L¹`-representation of a non-trivial
vector lattice `X` with strictly positive functional `h` — that is, for any measure `μ`
and injective vector lattice homomorphism `T : X → L¹(μ)` with dense range realising `h`
as integration against `μ` on the positive cone, as produced by
`exists_L1_representation_of_strictlyPositive` — the strong dual of `L¹(μ)` is lattice
isometric to the (principal) ideal generated in the order dual of `X` by `h`, equipped
with its gauge norm as an AM-space with unit `h`. -/
theorem banachLatEquiv_strongDual_of_L1_representation [Nontrivial X]
    (h : X →ₗ[ℝ] ℝ) (hh : StrictlyPositive h)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : VecLatHom X (Lp ℝ 1 μ))
    (hT_dense : DenseRange (T : X → Lp ℝ 1 μ))
    (hT_rep : ∀ x : X, 0 ≤ x → h x = ∫ ω, T x ω ∂μ) :
    letI : IsUniformlyCompleteVectorLattice (OrderDualSpace X) :=
      isUniformlyCompleteVectorLattice_of_sigmaConditionallyCompleteLattice (OrderDualSpace X)
    letI := OrderIdeal.principalNormedAddCommGroup (OrderBoundedHom.ofPositive h hh.positive)
      (ne_of_gt (ofPositive_pos_of_strictlyPositive hh))
    letI : Lattice ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive)) :=
      OrderIdeal.instLatticePrincipal _
    letI : IsOrderedAddMonoid ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive)) :=
      OrderIdeal.instIsOrderedAddMonoidPrincipal _
    letI : AMSpaceWithUnit ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive)) :=
      OrderIdeal.principalAMSpaceWithUnit (ofPositive_pos_of_strictlyPositive hh).le
        (ne_of_gt (ofPositive_pos_of_strictlyPositive hh))
        (IsUniformlyCompleteVectorLattice.complete_principal _
          (ofPositive_pos_of_strictlyPositive hh))
    Nonempty (BanachLatEquiv (StrongDual ℝ (Lp ℝ 1 μ))
      ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive))) := by
  letI : IsUniformlyCompleteVectorLattice (OrderDualSpace X) :=
    isUniformlyCompleteVectorLattice_of_sigmaConditionallyCompleteLattice (OrderDualSpace X)
  letI := OrderIdeal.principalNormedAddCommGroup (OrderBoundedHom.ofPositive h hh.positive)
    (ne_of_gt (ofPositive_pos_of_strictlyPositive hh))
  letI : Lattice ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive)) :=
    OrderIdeal.instLatticePrincipal _
  letI : IsOrderedAddMonoid ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive)) :=
    OrderIdeal.instIsOrderedAddMonoidPrincipal _
  letI : AMSpaceWithUnit ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive)) :=
    OrderIdeal.principalAMSpaceWithUnit (ofPositive_pos_of_strictlyPositive hh).le
      (ne_of_gt (ofPositive_pos_of_strictlyPositive hh))
      (IsUniformlyCompleteVectorLattice.complete_principal _
        (ofPositive_pos_of_strictlyPositive hh))
  -- Endow `X` with the AL-type norm `‖x‖ = h |x|` associated to `h`, so that its
  -- completion `X̂` is an AL-space into which `T` is an isometric dense embedding.
  letI : NormedAddCommGroup X := StrictlyPositive.associatedNormedAddCommGroup h hh
  letI : NormedVectorLattice X := StrictlyPositive.associatedNormedVectorLattice h hh
  -- Step 1: `L¹(μ)` is lattice-isometric to the completion `X̂`, hence so are their duals.
  have d1 : Nonempty (BanachLatEquiv (StrongDual ℝ (Lp ℝ 1 μ))
      (StrongDual ℝ (UniformSpace.Completion X))) := by
    have hT_norm : ∀ x : X, ‖T x‖ = ‖x‖ := fun x => by
      rw [StrictlyPositive.associatedNormedAddCommGroup_norm h hh]
      exact norm_map_eq_apply_abs h T hT_rep x
    exact ⟨banachLatEquivDual (banachLatEquivCompletionOfDenseIsometry T hT_norm hT_dense)⟩
  -- Step 2: the dual of `X̂` is the principal ideal generated by `h` in the order dual of `X`.
  have d2 : Nonempty (BanachLatEquiv (StrongDual ℝ (UniformSpace.Completion X))
      ↥(OrderIdeal.principal (OrderBoundedHom.ofPositive h hh.positive))) := by
    have hnorm : ∀ x : X, ‖x‖ = OrderBoundedHom.ofPositive h hh.positive |x| := by
      intro x
      rw [StrictlyPositive.associatedNormedAddCommGroup_norm h hh]
      rfl
    exact banachLatEquiv_strongDual_completion_principal
      (ofPositive_pos_of_strictlyPositive hh) hnorm
  obtain ⟨e1⟩ := d1
  obtain ⟨e2⟩ := d2
  exact ⟨e1.trans e2⟩
