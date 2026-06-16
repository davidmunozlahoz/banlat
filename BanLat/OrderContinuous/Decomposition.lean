import BanLat.OrderContinuous.Nakano
import BanLat.Substructures.Band.Decomposition

/-!
# Decomposition lemma

In an order continuous Banach lattice, for any maximal disjoint family `Λ`
of strictly positive elements and any `x : X`, the family of principal band
projections `(P_a x)_{a ∈ Λ}` is unconditionally summable with sum `x`.
-/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

namespace BanachLattice

variable [BanachLattice X]

/-- An order continuous Banach lattice has the principal projection property. -/
instance (priority := 100) hasPrincipalProjectionProperty_of_isOrderContinuousNorm
    [IsOrderContinuousNorm X] : HasPrincipalProjectionProperty X := by
  let latticeOrig : Lattice X := inferInstance
  let orderedAddOrig : @IsOrderedAddMonoid X inferInstance
      latticeOrig.toPartialOrder.toPreorder :=
    inferInstance
  let vectorOrig : @VectorLattice X inferInstance latticeOrig orderedAddOrig :=
    inferInstance
  letI : ConditionallyCompleteLattice X :=
    conditionallyCompleteLatticeOf_isOrderContinuousNorm
  letI scl : SigmaConditionallyCompleteLattice X :=
    ConditionallyCompleteLattice.toSigmaConditionallyCompleteLattice
  letI orderedAdd : @IsOrderedAddMonoid X inferInstance
      scl.toLattice.toPartialOrder.toPreorder :=
    orderedAddOrig
  letI vector : @VectorLattice X inferInstance scl.toLattice orderedAdd :=
    vectorOrig
  exact @HasPrincipalProjectionProperty.of_isSigmaOrderComplete X
    inferInstance scl orderedAdd vector

private lemma principalBand_subset_disjointComplement
    {a b : X} (hab : IsVLDisjoint a b) :
    (Band.generated ({a} : Set X) : Set X) ⊆
      disjointComplement (Band.generated ({b} : Set X) : Set X) := by
  have h₁ : (Band.generated ({b} : Set X) : Set X) ⊆ ({a} : Set X)ᵈ :=
    Band.generated_le (B := Band.disjointComplement ({a} : Set X)) (by
      intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
      intro c hc; rw [Set.mem_singleton_iff] at hc; subst hc
      exact isVLDisjoint_comm.mp hab)
  have ha_mem : a ∈ disjointComplement (Band.generated ({b} : Set X) : Set X) :=
    fun y hy => isVLDisjoint_comm.mp (h₁ hy a (Set.mem_singleton _))
  exact Band.generated_le
    (B := Band.disjointComplement (Band.generated ({b} : Set X) : Set X))
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact ha_mem)

private lemma principalBandProjection_isVLDisjoint
    [HasPrincipalProjectionProperty X]
    {a b : X} (hab : IsVLDisjoint a b) (x : X) :
    IsVLDisjoint (Band.principalBandProjection a x) (Band.principalBandProjection b x) := by
  have hPa : Band.principalBandProjection a x ∈
      (Band.generated ({a} : Set X) : Set X) := by
    have := (Band.principalProjectionBand a).bandProjection_mem x
    change _ ∈ (Band.principalProjectionBand a : Set X) at this
    rw [Band.principalProjectionBand_coe] at this; exact this
  have hPb : Band.principalBandProjection b x ∈
      (Band.generated ({b} : Set X) : Set X) := by
    have := (Band.principalProjectionBand b).bandProjection_mem x
    change _ ∈ (Band.principalProjectionBand b : Set X) at this
    rw [Band.principalProjectionBand_coe] at this; exact this
  exact principalBand_subset_disjointComplement hab hPa _ hPb

omit [BanachLattice X] in
private lemma inf_finset_sum_eq_zero {ι : Type*}
    {f : ι → X} {y : X} (F : Finset ι)
    (hy : 0 ≤ y) (hf : ∀ i ∈ F, 0 ≤ f i)
    (hdis : ∀ i ∈ F, y ⊓ f i = 0) :
    y ⊓ ∑ i ∈ F, f i = 0 := by
  induction F using Finset.cons_induction with
  | empty => simp [inf_of_le_right hy]
  | cons a F haF ih =>
    rw [Finset.sum_cons]
    apply le_antisymm _ (le_inf hy (add_nonneg (hf a (Finset.mem_cons_self a F))
      (Finset.sum_nonneg fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))))
    calc y ⊓ (f a + ∑ i ∈ F, f i)
        ≤ y ⊓ f a + y ⊓ ∑ i ∈ F, f i :=
          inf_le_inf_add_inf_of_nonneg y _ _ hy (hf a (Finset.mem_cons_self a F))
            (Finset.sum_nonneg fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))
      _ = 0 := by rw [hdis a (Finset.mem_cons_self a F),
          ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))
            (fun i hi => hdis i (Finset.mem_cons.mpr (Or.inr hi))), add_zero]

private lemma finset_sum_principalBandProjection_le
    [HasPrincipalProjectionProperty X]
    {Λ : Set X} (hΛ : IsMaximalDisjoint Λ)
    {x : X} (hx : 0 ≤ x) (F : Finset Λ) :
    ∑ a ∈ F, Band.principalBandProjection (a : X) x ≤ x := by
  induction F using Finset.cons_induction with
  | empty => simpa
  | cons a F haF ih =>
    rw [Finset.sum_cons]
    have ha_nn := Positive.zero_le_iff.mp
      (Band.principalProjectionBand (a : X)).bandProjection_nonneg _ hx
    have ha_le := Positive.le_iff.mp
      (Band.principalProjectionBand (a : X)).bandProjection_le_id _ hx
    have hsum_nn := Finset.sum_nonneg fun i (_ : i ∈ F) =>
      Positive.zero_le_iff.mp
        (Band.principalProjectionBand (i : X)).bandProjection_nonneg _ hx
    have hdisj : Band.principalBandProjection (a : X) x ⊓
        ∑ i ∈ F, Band.principalBandProjection (i : X) x = 0 := by
      refine inf_finset_sum_eq_zero F ha_nn
        (fun i _ => Positive.zero_le_iff.mp
          (Band.principalProjectionBand (i : X)).bandProjection_nonneg _ hx)
        (fun i hi => ?_)
      have hab : IsVLDisjoint (a : X) (i : X) :=
        hΛ.prop.2 a.prop i.prop (fun h => haF (Subtype.val_injective h ▸ hi))
      have hdisij := principalBandProjection_isVLDisjoint hab x
      unfold IsVLDisjoint at hdisij
      have hPa_nn := ha_nn
      have hPi_nn := Positive.zero_le_iff.mp
        (Band.principalProjectionBand (i : X)).bandProjection_nonneg _ hx
      change 0 ≤ (Band.principalBandProjection (a : X)) x at hPa_nn
      change 0 ≤ (Band.principalBandProjection (i : X)) x at hPi_nn
      rwa [abs_of_nonneg hPa_nn, abs_of_nonneg hPi_nn] at hdisij
    have := inf_add_sup (Band.principalBandProjection (a : X) x)
      (∑ i ∈ F, Band.principalBandProjection (i : X) x)
    rw [hdisj, zero_add] at this
    rw [this.symm]
    exact sup_le ha_le ih

/-- **Decomposition Lemma.** In an order continuous Banach lattice, for any
maximal disjoint family `Λ` of positive elements and any `x : X`, the
family `(Pₐ x)_{a ∈ Λ}` is unconditionally summable with sum `x`. -/
private lemma hasSum_principalBandProjection_of_nonneg
    [IsOrderContinuousNorm X]
    {Λ : Set X} (hΛ : IsMaximalDisjoint Λ) (hΛ_pos : ∀ a ∈ Λ, 0 < a)
    {y : X} (hy : 0 ≤ y) :
    HasSum (fun a : Λ => Band.principalBandProjection (a : X) y) y := by
  -- HasSum is Tendsto of partial sums over Finset Λ
  -- The antitone net: F ↦ y - ∑_{a∈F} Pa y
  set g : Finset Λ → X := fun F =>
    y - ∑ a ∈ F, Band.principalBandProjection (a : X) y with hg_def
  suffices htend : Filter.Tendsto g Filter.atTop (nhds 0) by
    have : Filter.Tendsto (fun F => y - g F) Filter.atTop (nhds (y - 0)) :=
      tendsto_const_nhds.sub htend
    simp only [hg_def, sub_sub_cancel, sub_zero] at this
    exact this
  -- g is antitone
  have hg_anti : Antitone g := fun F G hFG => sub_le_sub_left
    (Finset.sum_le_sum_of_subset_of_nonneg hFG fun a _ _ =>
      Positive.zero_le_iff.mp
        (Band.principalProjectionBand (a : X)).bandProjection_nonneg _ hy) y
  -- g is nonneg
  have hg_nn : ∀ F, 0 ≤ g F := fun F =>
    sub_nonneg.mpr (finset_sum_principalBandProjection_le hΛ hy F)
  -- IsGLB (range g) 0
  have hg_glb : IsGLB (Set.range g) 0 := by
    refine ⟨fun _ ⟨F, hF⟩ => hF ▸ hg_nn F, fun w hw => ?_⟩
    -- For singleton F = {a}: w ≤ y - Pa y, hence Pa y ≤ y - w
    have hub : y - w ∈ upperBounds (Set.range fun a : Λ =>
        Band.principalBandProjection (a : X) y) := by
      rintro _ ⟨a, rfl⟩
      have := hw ⟨{a}, rfl⟩
      simp only [hg_def, Finset.sum_singleton] at this
      exact le_sub_comm.mp this
    -- y = LUB of {Pa y}, so y ≤ y - w, hence w ≤ 0
    have hlub := isLUB_principalBandProjection_of_isMaximalDisjoint hΛ hΛ_pos hy
    have hyw := hlub.2 hub
    rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at hyw
  -- Apply order continuity of the norm
  exact IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hg_anti hg_nn hg_glb

/-- **Decomposition Lemma.** In an order continuous Banach lattice, for any
maximal disjoint family `Λ` of positive elements and any `x : X`, the
family `(Pₐ x)_{a ∈ Λ}` is unconditionally summable with sum `x`. -/
theorem hasSum_principalBandProjection
    [IsOrderContinuousNorm X]
    {Λ : Set X} (hΛ : IsMaximalDisjoint Λ) (hΛ_pos : ∀ a ∈ Λ, 0 < a) (x : X) :
    HasSum (fun a : Λ =>
      Band.principalBandProjection (a : X) x) x := by
  -- Decompose x = x⁺ - x⁻ and use linearity
  set xp : X := x ⊔ 0
  set xn : X := (-x) ⊔ 0
  have hxeq : x = xp - xn := by
    simp only [xp, xn]
    rw [show (-x) ⊔ 0 = -(x ⊓ 0) from by rw [neg_inf, neg_zero], sub_neg_eq_add, add_comm]
    rw [show x ⊓ 0 + (x ⊔ 0) = x from by rw [inf_add_sup, add_zero]]
  have hfun : (fun a : Λ => Band.principalBandProjection (a : X) x) =
      (fun a : Λ => Band.principalBandProjection (a : X) xp -
        Band.principalBandProjection (a : X) xn) := by
    funext ⟨a, _⟩
    change (Band.principalBandProjection a) x =
      (Band.principalBandProjection a) xp - (Band.principalBandProjection a) xn
    rw [← LinearMap.map_sub, ← hxeq]
  rw [hfun, hxeq]
  exact (hasSum_principalBandProjection_of_nonneg hΛ hΛ_pos le_sup_right).sub
    (hasSum_principalBandProjection_of_nonneg hΛ hΛ_pos le_sup_right)

end BanachLattice
