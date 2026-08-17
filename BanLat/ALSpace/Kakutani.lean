import BanLat.ALSpace.Dual
import BanLat.ALSpace.OrderContinuous
import BanLat.AMSpace.Kakutani
import BanLat.Bidual
import BanLat.Examples.CofK.Dual
import BanLat.Examples.Lp.Sublattice
import BanLat.Examples.MofK.L1space

/-!
# Kakutani's representation theorem for AL-spaces

Every AL-space is Banach-lattice isometrically isomorphic to an `L¹` space.
-/

open MeasureTheory

noncomputable section

universe u

namespace ALSpace

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

namespace Band

private abbrev principalBand {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (a : X) : Band X :=
  Band.generated ({a} : Set X)

end Band

private lemma banachLatEquiv_forall_isVLDisjoint_eq_zero
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B] [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B] (ρ : BanachLatEquiv A B)
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
        _ = |ρ v| ⊓ |ρ a| :=
          congrArg₂ (· ⊓ ·)
            (ρ.toVecLatEquiv.toVecLatHom.map_abs v)
            (ρ.toVecLatEquiv.toVecLatHom.map_abs a)
        _ = |w| ⊓ |ρ a| := by rw [hρv]
    have h1 : ρ (|v| ⊓ |a|) = 0 := by rw [hρ_inf]; exact hw
    have h2 : ρ (|v| ⊓ |a|) = ρ 0 := by
      rw [h1]; exact (ρ.toLinearIsometryEquiv.map_zero).symm
    exact ρ.toLinearIsometryEquiv.injective h2
  have hvz : v = 0 := hwou v hdisj
  have heqw : w = ρ 0 := by rw [← hρv, hvz]
  rw [heqw]; exact ρ.toLinearIsometryEquiv.map_zero

private lemma mem_principalBand_image_of_continuous_latticeHom
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B] [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B] [IsOrderContinuousNorm A]
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
    (Band.mem_generated_singleton_iff_isLUB_inf_nsmul ha hz).mp hmem
  set w : ℕ → A := fun n => z ⊓ n • a
  have hw_mono : Monotone w := by
    intro m n hmn
    exact inf_le_inf_left z (nsmul_le_nsmul_left ha hmn)
  have hw_bdd : BddAbove (Set.range w) :=
    ⟨z, by rintro _ ⟨n, rfl⟩; exact inf_le_left⟩
  obtain ⟨z', hz'_lub, htend⟩ :=
    BanachLattice.tendsto_of_monotone_bddAbove hw_mono hw_bdd
  have hz'_eq : z' = z := IsLUB.unique hz'_lub hlub
  rw [hz'_eq] at htend
  have hTtend : Filter.Tendsto (fun n => T (w n)) Filter.atTop (nhds (T z)) :=
    T.continuous.tendsto z |>.comp htend
  have hT_w : ∀ n, T (w n) = T z ⊓ n • T a := by
    intro n
    change T (z ⊓ n • a) = T z ⊓ n • T a
    rw [hinf z (n • a), map_nsmul T n a]
  have hTw_mem : ∀ n, T (w n) ∈ (Band.principalBand (T a) : Set B) := by
    intro n
    rw [hT_w n]
    have h_nn : 0 ≤ T z ⊓ n • T a := le_inf hTz_nn (nsmul_nonneg hTa_nn n)
    refine (Band.principalBand (T a)).solid
      ((Band.principalBand (T a)).toSubmodule.nsmul_mem
        (Band.subset_generated ({T a} : Set B) rfl) n) ?_ ?_
    · exact h_nn
    · exact inf_le_right
  have hclosed : IsClosed ((Band.principalBand (T a) : Band B) : Set B) :=
    Band.isClosed_coe _
  exact hclosed.mem_of_tendsto hTtend (Filter.Eventually.of_forall hTw_mem)

private lemma banachLatEquiv_precomp_map_sup
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B] [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) (α β : StrongDual ℝ B) :
    (α ⊔ β).comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap =
      α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
        β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap := by
  have hposApp : ∀ (a : A), 0 ≤ a →
      (α ⊔ β) (γ a) =
      (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
        β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a := by
    intro a ha
    have hγa : 0 ≤ γ a := γ.toVecLatEquiv.toVecLatHom.map_nonneg ha
    have hLHS := OrderDualSpace.isLUB_sup_apply
      (φ := StrongDual.toOrderDualSpace α)
      (ψ := StrongDual.toOrderDualSpace β) hγa
    have hRHS := OrderDualSpace.isLUB_sup_apply
      (φ := StrongDual.toOrderDualSpace
          (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap))
      (ψ := StrongDual.toOrderDualSpace
          (β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap)) ha
    have hset :
        {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = γ a ∧
            r = StrongDual.toOrderDualSpace α y + StrongDual.toOrderDualSpace β z} =
        {r : ℝ | ∃ y z, 0 ≤ y ∧ 0 ≤ z ∧ y + z = a ∧
            r = StrongDual.toOrderDualSpace
                  (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) y +
                StrongDual.toOrderDualSpace
                  (β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) z} := by
      ext r
      constructor
      · rintro ⟨y, z, hy, hz, hyz, hr⟩
        refine ⟨γ.toLinearIsometryEquiv.symm y, γ.toLinearIsometryEquiv.symm z,
          γ.toVecLatEquiv.symm.toVecLatHom.map_nonneg hy,
          γ.toVecLatEquiv.symm.toVecLatHom.map_nonneg hz, ?_, ?_⟩
        · have h : γ.toLinearIsometryEquiv.symm y +
              γ.toLinearIsometryEquiv.symm z =
              γ.toLinearIsometryEquiv.symm (y + z) :=
            (γ.toLinearIsometryEquiv.symm.map_add y z).symm
          rw [h, hyz]
          exact γ.toLinearIsometryEquiv.symm_apply_apply a
        · change _ = α (γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm y)) +
              β (γ.toLinearIsometryEquiv (γ.toLinearIsometryEquiv.symm z))
          rw [γ.toLinearIsometryEquiv.apply_symm_apply,
              γ.toLinearIsometryEquiv.apply_symm_apply]
          exact hr
      · rintro ⟨y, z, hy, hz, hyz, hr⟩
        refine ⟨γ y, γ z, γ.toVecLatEquiv.toVecLatHom.map_nonneg hy,
          γ.toVecLatEquiv.toVecLatHom.map_nonneg hz, ?_, ?_⟩
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
    _ = (α ⊔ β) (γ a⁺) - (α ⊔ β) (γ a⁻) := map_sub (α ⊔ β) _ _
    _ = (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a⁺ -
        (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a⁻ := by
        rw [hposApp a⁺ hap, hposApp a⁻ han]
    _ = (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) (a⁺ - a⁻) :=
        (map_sub _ _ _).symm
    _ = (α.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap ⊔
          β.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) a := by
        rw [← h_pn]

private lemma banachLatEquiv_precomp_map_inf
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B] [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    (γ : BanachLatEquiv A B) (α β : StrongDual ℝ B) :
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
  have hcomp_neg : ∀ η : StrongDual ℝ B,
      (-η).comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap =
        -(η.comp γ.toLinearIsometryEquiv.toLinearIsometry.toContinuousLinearMap) := by
    intro η
    ext
    simp
  rw [← hcomp_neg, ← hcomp_neg, ← banachLatEquiv_precomp_map_sup γ]
  ext a
  simp

private noncomputable def banachLatEquiv_of_subsingleton
    (A B : Type*) [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B] [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B] [Subsingleton A] [Subsingleton B] :
    BanachLatEquiv A B :=
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

private lemma eq_zero_of_mem_principalBand_of_isVLDisjoint
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [VectorLattice Y] [IsVLArchimedean Y]
    {a v : Y} (hv_mem : v ∈ Band.principalBand a) (hv_dis : IsVLDisjoint v a) :
    v = 0 := by
  have hv_in_d : v ∈ (({a} : Set Y)ᵈ) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    rw [hc]
    exact hv_dis
  have hv_in_dd : v ∈ ((({a} : Set Y)ᵈ)ᵈ) := by
    rw [Band.disjointComplement_disjointComplement_eq_generated]
    exact hv_mem
  exact Set.mem_singleton_iff.mp
    (disjointComplement_inter_eq_zero _ ⟨hv_in_d, hv_in_dd⟩)

private abbrev CharacterSpace (X : Type u) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [ALSpace X] [Nontrivial X] : Type u :=
  AMSpaceWithUnit.LatticeCharacter (StrongDual ℝ X)

private noncomputable instance instMeasurableSpaceCharacterSpace
    [ALSpace X] [Nontrivial X] : MeasurableSpace (CharacterSpace X) :=
  borel (CharacterSpace X)

private instance instBorelSpaceCharacterSpace [ALSpace X] [Nontrivial X] :
    BorelSpace (CharacterSpace X) :=
  ⟨rfl⟩

private noncomputable def dualKakutaniEquiv [ALSpace X] [Nontrivial X] :
    BanachLatEquiv (StrongDual ℝ X) C(CharacterSpace X, ℝ) :=
  AMSpaceWithUnit.kakutaniEquiv (StrongDual ℝ X)

private noncomputable def cofkToDual [ALSpace X] [Nontrivial X] :
    C(CharacterSpace X, ℝ) →L[ℝ] StrongDual ℝ X :=
  (((BanachLatEquiv.symm (dualKakutaniEquiv
    (X := X))).toLinearIsometryEquiv).toLinearIsometry.toContinuousLinearMap)

private noncomputable def intoMofK [ALSpace X] [Nontrivial X] :
    X → MofK (CharacterSpace X) :=
  fun a =>
    (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion a).comp (cofkToDual (X := X)))

private lemma intoMofK_zero [ALSpace X] [Nontrivial X] :
    intoMofK (X := X) 0 = 0 := by
  change (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion 0).comp (cofkToDual (X := X))) = 0
  rw [map_zero BidualSpace.inclusion, ContinuousLinearMap.zero_comp]
  exact (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm.map_zero

private lemma intoMofK_add [ALSpace X] [Nontrivial X] (a b : X) :
    intoMofK (X := X) (a + b) = intoMofK (X := X) a + intoMofK (X := X) b := by
  change (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion (a + b)).comp (cofkToDual (X := X))) = _
  rw [map_add BidualSpace.inclusion, ContinuousLinearMap.add_comp, map_add]
  rfl

private lemma intoMofK_smul [ALSpace X] [Nontrivial X] (r : ℝ) (a : X) :
    intoMofK (X := X) (r • a) = r • intoMofK (X := X) a := by
  change (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion (r • a)).comp (cofkToDual (X := X))) = _
  rw [map_smul BidualSpace.inclusion, ContinuousLinearMap.smul_comp, map_smul]
  rfl

private lemma intoMofK_norm [ALSpace X] [Nontrivial X] (a : X) :
    ‖intoMofK (X := X) a‖ = ‖a‖ := by
  change ‖(MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion a).comp (cofkToDual (X := X)))‖ = ‖a‖
  rw [LinearIsometryEquiv.norm_map]
  change ‖(BidualSpace.inclusion a).comp
      (((dualKakutaniEquiv
        (X := X)).toLinearIsometryEquiv.symm).toLinearIsometry.toContinuousLinearMap)‖ =
      ‖a‖
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    BidualSpace.norm_inclusion]

private lemma intoMofK_sup [ALSpace X] [Nontrivial X] (a b : X) :
    intoMofK (X := X) (a ⊔ b) = intoMofK (X := X) a ⊔ intoMofK (X := X) b := by
  change (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion (a ⊔ b)).comp (cofkToDual (X := X))) = _
  dsimp only [cofkToDual]
  rw [BidualSpace.inclusion_sup,
    banachLatEquiv_precomp_map_sup (BanachLatEquiv.symm (dualKakutaniEquiv (X := X)))]
  exact (BanachLatEquiv.symm (MofK.dualEquiv (K := CharacterSpace X))).map_sup' _ _

private lemma intoMofK_inf [ALSpace X] [Nontrivial X] (a b : X) :
    intoMofK (X := X) (a ⊓ b) = intoMofK (X := X) a ⊓ intoMofK (X := X) b := by
  change (MofK.dualEquiv (K := CharacterSpace X)).toLinearIsometryEquiv.symm
      ((BidualSpace.inclusion (a ⊓ b)).comp (cofkToDual (X := X))) = _
  dsimp only [cofkToDual]
  rw [BidualSpace.inclusion_inf,
    banachLatEquiv_precomp_map_inf (BanachLatEquiv.symm (dualKakutaniEquiv (X := X)))]
  exact (BanachLatEquiv.symm (MofK.dualEquiv (K := CharacterSpace X))).map_inf' _ _

private lemma intoMofK_nonneg [ALSpace X] [Nontrivial X] {a : X} (ha : 0 ≤ a) :
    0 ≤ intoMofK (X := X) a := by
  have h1 : intoMofK (X := X) a = 0 ⊔ intoMofK (X := X) a := by
    calc
      intoMofK (X := X) a = intoMofK (X := X) (0 ⊔ a) := by rw [sup_eq_right.mpr ha]
      _ = intoMofK (X := X) 0 ⊔ intoMofK (X := X) a := intoMofK_sup 0 a
      _ = 0 ⊔ intoMofK (X := X) a := by rw [intoMofK_zero]
  exact le_sup_left.trans h1.symm.le

private noncomputable def intoMofKLi [ALSpace X] [Nontrivial X] :
    X →ₗᵢ[ℝ] MofK (CharacterSpace X) :=
  { toLinearMap :=
      { toFun := intoMofK (X := X)
        map_add' := intoMofK_add
        map_smul' := intoMofK_smul }
    norm_map' := intoMofK_norm }

private lemma intoMofK_posPart_sub_negPart [ALSpace X] [Nontrivial X] (z : X) :
    intoMofK (X := X) z = intoMofK (X := X) z⁺ - intoMofK (X := X) z⁻ := by
  let addCommMonoid : AddCommMonoid X := inferInstance
  let addGroup : AddGroup X := inferInstance
  let latticeOrig : Lattice X := inferInstance
  let orderedAddOrig : @IsOrderedAddMonoid X addCommMonoid
      latticeOrig.toPartialOrder.toPreorder :=
    inferInstance
  let addLeftMono : @AddLeftMono X inferInstance latticeOrig.toLE := ⟨fun a {_ _} h =>
    @IsOrderedAddMonoid.add_le_add_right X addCommMonoid
      latticeOrig.toPartialOrder.toPreorder orderedAddOrig _ _ h a⟩
  calc
    intoMofK (X := X) z = intoMofK (X := X) (z⁺ + -z⁻) := by
      rw [← sub_eq_add_neg, @posPart_sub_negPart X latticeOrig addGroup addLeftMono]
    _ = intoMofK (X := X) z⁺ + intoMofK (X := X) (-z⁻) :=
      intoMofK_add (X := X) z⁺ (-z⁻)
    _ = intoMofK (X := X) z⁺ + -intoMofK (X := X) z⁻ := by
      rw [show intoMofK (X := X) (-z⁻) = -intoMofK (X := X) z⁻ by
        simpa using intoMofK_smul (X := X) (-1 : ℝ) z⁻]
    _ = intoMofK (X := X) z⁺ - intoMofK (X := X) z⁻ := by rw [sub_eq_add_neg]

private lemma intoMofK_posPart_mem_principalBand [ALSpace X] [Nontrivial X] {x z : X}
    (hx : 0 ≤ x) (hz : z ∈ (Band.principalBand x).toSubmodule) :
    intoMofK (X := X) z⁺ ∈
      (Band.principalBand (intoMofK (X := X) x)).toSubmodule := by
  have hz_pos_mem : z⁺ ∈ Band.principalBand x := by
    rw [posPart_def]
    exact (Band.principalBand x).sup_mem hz (Band.principalBand x).toSubmodule.zero_mem
  exact mem_principalBand_image_of_continuous_latticeHom
    (intoMofKLi (X := X)).toContinuousLinearMap
    (fun a b => intoMofK_sup (X := X) a b)
    (fun a b => intoMofK_inf (X := X) a b)
    hx (posPart_nonneg z) hz_pos_mem

private lemma intoMofK_negPart_mem_principalBand [ALSpace X] [Nontrivial X] {x z : X}
    (hx : 0 ≤ x) (hz : z ∈ (Band.principalBand x).toSubmodule) :
    intoMofK (X := X) z⁻ ∈
      (Band.principalBand (intoMofK (X := X) x)).toSubmodule := by
  have hz_neg_mem : z⁻ ∈ Band.principalBand x := by
    rw [negPart_def]
    exact (Band.principalBand x).sup_mem
      ((Band.principalBand x).toSubmodule.neg_mem hz)
      (Band.principalBand x).toSubmodule.zero_mem
  exact mem_principalBand_image_of_continuous_latticeHom
    (intoMofKLi (X := X)).toContinuousLinearMap
    (fun a b => intoMofK_sup (X := X) a b)
    (fun a b => intoMofK_inf (X := X) a b)
    hx (negPart_nonneg z) hz_neg_mem

private lemma intoMofK_mem_principalBand [ALSpace X] [Nontrivial X] {x z : X}
    (hx : 0 ≤ x) (hz : z ∈ (Band.principalBand x).toSubmodule) :
    intoMofK (X := X) z ∈ (Band.principalBand (intoMofK (X := X) x)).toSubmodule := by
  have h1 := intoMofK_posPart_mem_principalBand (X := X) hx hz
  have h2 := intoMofK_negPart_mem_principalBand (X := X) hx hz
  rw [intoMofK_posPart_sub_negPart (X := X) z]
  exact (Band.principalBand (intoMofK (X := X) x)).toSubmodule.sub_mem h1 h2

private noncomputable def intoMofKPrincipalBandLi [ALSpace X] [Nontrivial X]
    {x : X} (hx : 0 ≤ x) :
    ↥(Band.principalBand x).toSubmodule →ₗᵢ[ℝ]
      ↥(Band.principalBand (intoMofK (X := X) x)).toSubmodule :=
  { toLinearMap :=
      { toFun := fun v => ⟨intoMofK (X := X) v.val,
          intoMofK_mem_principalBand (X := X) hx v.property⟩
        map_add' := fun a b => Subtype.ext (intoMofK_add (X := X) a.val b.val)
        map_smul' := fun r a => Subtype.ext (intoMofK_smul (X := X) r a.val) }
    norm_map' := fun v => intoMofK_norm (X := X) v.val }

private lemma intoMofKPrincipalBandLi_map_sup [ALSpace X] [Nontrivial X]
    {x : X} (hx : 0 ≤ x) (v w : ↥(Band.principalBand x).toSubmodule) :
    intoMofKPrincipalBandLi (X := X) hx (v ⊔ w) =
      intoMofKPrincipalBandLi (X := X) hx v ⊔
        intoMofKPrincipalBandLi (X := X) hx w :=
  Subtype.ext (intoMofK_sup (X := X) v.val w.val)

private lemma intoMofKPrincipalBandLi_map_inf [ALSpace X] [Nontrivial X]
    {x : X} (hx : 0 ≤ x) (v w : ↥(Band.principalBand x).toSubmodule) :
    intoMofKPrincipalBandLi (X := X) hx (v ⊓ w) =
      intoMofKPrincipalBandLi (X := X) hx v ⊓
        intoMofKPrincipalBandLi (X := X) hx w :=
  Subtype.ext (intoMofK_inf (X := X) v.val w.val)

private lemma exists_L1_banachLatEquiv_principalBand_of_nontrivial_ALSpace
    [ALSpace X] [Nontrivial X] (x : X) (hx : 0 ≤ x) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv
        ↥(Band.principalBand x).toSubmodule (Lp ℝ 1 μ)) := by
  let Φ : X → MofK (CharacterSpace X) := intoMofK (X := X)
  have hΦ_mem : ∀ z : X, z ∈ (Band.principalBand x).toSubmodule →
      Φ z ∈ (Band.principalBand (Φ x)).toSubmodule :=
    fun z hz => intoMofK_mem_principalBand (X := X) hx hz
  have hΦx_nn : (0 : MofK (CharacterSpace X)) ≤ Φ x :=
    intoMofK_nonneg (X := X) hx
  obtain ⟨Ω, mΩ, ν, _hν_fin, ⟨φ_eq⟩⟩ :=
    MofK.exists_principalBand_banachLatEquivL1 (Φ x)
  have hx_mem : x ∈ (Band.principalBand x).toSubmodule :=
    Band.subset_generated ({x} : Set X) (Set.mem_singleton _)
  let x_band : ↥(Band.principalBand x).toSubmodule := ⟨x, hx_mem⟩
  have hx_band_nn : (0 : ↥(Band.principalBand x).toSubmodule) ≤ x_band := hx
  let Φx_band : ↥(Band.principalBand (Φ x)).toSubmodule :=
    ⟨Φ x, hΦ_mem x hx_mem⟩
  have hΦx_band_nn : (0 : ↥(Band.principalBand (Φ x)).toSubmodule) ≤ Φx_band :=
    hΦx_nn
  let Φ_restr := intoMofKPrincipalBandLi (X := X) hx
  let φ_li : ↥(Band.principalBand (Φ x)).toSubmodule →ₗᵢ[ℝ] Lp ℝ 1 ν :=
    φ_eq.toLinearIsometryEquiv.toLinearIsometry
  let T : ↥(Band.principalBand x).toSubmodule →ₗᵢ[ℝ] Lp ℝ 1 ν :=
    φ_li.comp Φ_restr
  have hT_x : T x_band = φ_eq Φx_band := rfl
  have hTx_nn : (0 : Lp ℝ 1 ν) ≤ T x_band := by
    rw [hT_x]
    exact φ_eq.toVecLatEquiv.toVecLatHom.map_nonneg hΦx_band_nn
  have hΦx_band_wou : ∀ u : ↥(Band.principalBand (Φ x)).toSubmodule,
      IsVLDisjoint u Φx_band → u = 0 := fun u hudis =>
    Subtype.ext (eq_zero_of_mem_principalBand_of_isVLDisjoint u.property
      (congrArg Subtype.val hudis))
  have hTx_wou : ∀ w : Lp ℝ 1 ν, IsVLDisjoint w (T x_band) → w = 0 := by
    intro w hw
    rw [hT_x] at hw
    exact banachLatEquiv_forall_isVLDisjoint_eq_zero φ_eq hΦx_band_wou w hw
  have hT_closed : IsClosed (Set.range T) :=
    T.isometry.isClosedEmbedding.isClosed_range
  have hT_sup : ∀ v w : ↥(Band.principalBand x).toSubmodule,
      T (v ⊔ w) = T v ⊔ T w := fun v w => by
    change φ_eq (Φ_restr (v ⊔ w)) = φ_eq (Φ_restr v) ⊔ φ_eq (Φ_restr w)
    rw [intoMofKPrincipalBandLi_map_sup]
    exact φ_eq.map_sup' _ _
  have hT_inf : ∀ v w : ↥(Band.principalBand x).toSubmodule,
      T (v ⊓ w) = T v ⊓ T w := fun v w => by
    change φ_eq (Φ_restr (v ⊓ w)) = φ_eq (Φ_restr v) ⊓ φ_eq (Φ_restr w)
    rw [intoMofKPrincipalBandLi_map_inf]
    exact φ_eq.map_inf' _ _
  obtain ⟨Ω', mΩ', ν', _, φ, _⟩ := exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive
    (X := ↥(Band.principalBand x).toSubmodule) ν T hT_sup hT_inf hT_closed
    x_band hx_band_nn (lp_aePos_of_forall_isVLDisjoint_eq_zero hTx_nn hTx_wou)
  exact ⟨Ω', mΩ', ν', ⟨φ⟩⟩

private lemma exists_L1_banachLatEquiv_principalBand_of_ALSpace
    [ALSpace X] (x : X) (hx : 0 ≤ x) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv
        ↥(Band.principalBand x).toSubmodule (Lp ℝ 1 μ)) := by
  classical
  by_cases hntriv : Nontrivial X
  · haveI : Nontrivial X := hntriv
    exact exists_L1_banachLatEquiv_principalBand_of_nontrivial_ALSpace x hx
  · haveI hssX : Subsingleton X := not_nontrivial_iff_subsingleton.mp hntriv
    haveI : Subsingleton ↥(Band.principalBand x).toSubmodule :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    refine ⟨PUnit.{u+1}, (⊤ : MeasurableSpace PUnit.{u+1}), 0, ⟨?_⟩⟩
    haveI : Subsingleton (Lp ℝ 1 (0 : @Measure PUnit.{u+1} ⊤)) := by
      refine ⟨fun f g => Lp.ext ?_⟩
      rw [Filter.EventuallyEq, MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    exact banachLatEquiv_of_subsingleton _ _

/-- **Kakutani's representation theorem for AL-spaces.** Every AL-space is
Banach-lattice isometrically isomorphic to `L¹(μ)` for some measure `μ`. -/
theorem exists_L1_banachLatEquiv [ALSpace X] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      Nonempty (BanachLatEquiv X (Lp ℝ 1 μ)) :=
  MofK.exists_L1_banachLatEquiv_of_principalBandModels (X := X)
    fun x hx => exists_L1_banachLatEquiv_principalBand_of_ALSpace x hx

/-- **Kakutani representation with a weak unit.** An AL-space with a weak order unit `e`
is Banach-lattice isometric to `L¹(μ)` for a finite measure `μ`, in such a way that `e`
corresponds to the constant function `1`. -/
theorem exists_L1_banachLatEquiv_isFiniteMeasure_of_weakOrderUnit [ALSpace X] {e : X}
    (he : WeakOrderUnit e) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsFiniteMeasure μ)
      (φ : BanachLatEquiv X (Lp ℝ 1 μ)), ∀ᵐ ω ∂μ, (φ e : Ω → ℝ) ω = 1 := by
  classical
  rcases subsingleton_or_nontrivial X with hss | hnt
  · -- In the trivial case the zero measure on a point works.
    haveI := hss
    haveI : Subsingleton (Lp ℝ 1 (0 : @Measure PUnit.{u+1} ⊤)) := by
      refine ⟨fun f g => Lp.ext ?_⟩
      rw [Filter.EventuallyEq, MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    refine ⟨PUnit.{u+1}, (⊤ : MeasurableSpace PUnit.{u+1}), 0, inferInstance,
      banachLatEquiv_of_subsingleton _ _, ?_⟩
    rw [MeasureTheory.ae_zero]
    exact Filter.eventually_bot
  · -- The weak unit generates the whole space as a band, so the principal band
    -- model for `intoMofK e` is a model for all of `X`.
    haveI : Nontrivial X := hnt
    have hband : Band.principalBand e = ⊤ :=
      (weakOrderUnit_iff_generated_singleton_eq_top he.1).mp he
    have hmem_top : ∀ z : X, z ∈ (Band.principalBand e).toSubmodule := fun z => by
      rw [hband]
      exact Submodule.mem_top
    obtain ⟨Ω, mΩ, ν, hν_fin, ⟨φ_eq⟩⟩ :=
      MofK.exists_principalBand_banachLatEquivL1 (intoMofK (X := X) e)
    haveI : IsFiniteMeasure ν := hν_fin
    have hΦe_nn : (0 : MofK (CharacterSpace X)) ≤ intoMofK (X := X) e :=
      intoMofK_nonneg (X := X) he.1
    let Φ_X : X →ₗᵢ[ℝ] ↥(Band.principalBand (intoMofK (X := X) e)).toSubmodule :=
      { toLinearMap :=
          { toFun := fun z => ⟨intoMofK (X := X) z,
              intoMofK_mem_principalBand (X := X) he.1 (hmem_top z)⟩
            map_add' := fun a b => Subtype.ext (intoMofK_add (X := X) a b)
            map_smul' := fun r a => Subtype.ext (intoMofK_smul (X := X) r a) }
        norm_map' := fun v => intoMofK_norm (X := X) v }
    let φ_li : ↥(Band.principalBand (intoMofK (X := X) e)).toSubmodule →ₗᵢ[ℝ] Lp ℝ 1 ν :=
      φ_eq.toLinearIsometryEquiv.toLinearIsometry
    let T : X →ₗᵢ[ℝ] Lp ℝ 1 ν := φ_li.comp Φ_X
    have hT_sup : ∀ v w : X, T (v ⊔ w) = T v ⊔ T w := by
      intro v w
      change φ_eq (Φ_X (v ⊔ w)) = φ_eq (Φ_X v) ⊔ φ_eq (Φ_X w)
      have h1 : Φ_X (v ⊔ w) = Φ_X v ⊔ Φ_X w := Subtype.ext (intoMofK_sup (X := X) v w)
      rw [h1]
      exact φ_eq.map_sup' _ _
    have hT_inf : ∀ v w : X, T (v ⊓ w) = T v ⊓ T w := by
      intro v w
      change φ_eq (Φ_X (v ⊓ w)) = φ_eq (Φ_X v) ⊓ φ_eq (Φ_X w)
      have h1 : Φ_X (v ⊓ w) = Φ_X v ⊓ Φ_X w := Subtype.ext (intoMofK_inf (X := X) v w)
      rw [h1]
      exact φ_eq.map_inf' _ _
    have hT_closed : IsClosed (Set.range T) := T.isometry.isClosedEmbedding.isClosed_range
    have hTe_eq : T e = φ_eq (Φ_X e) := rfl
    have hTe_nn : (0 : Lp ℝ 1 ν) ≤ T e := by
      rw [hTe_eq]
      exact φ_eq.toVecLatEquiv.toVecLatHom.map_nonneg hΦe_nn
    have hband_wou : ∀ u : ↥(Band.principalBand (intoMofK (X := X) e)).toSubmodule,
        IsVLDisjoint u (Φ_X e) → u = 0 := fun u hudis =>
      Subtype.ext (eq_zero_of_mem_principalBand_of_isVLDisjoint u.property
        (congrArg Subtype.val hudis))
    have hTe_wou : ∀ w : Lp ℝ 1 ν, IsVLDisjoint w (T e) → w = 0 := by
      intro w hw
      rw [hTe_eq] at hw
      exact banachLatEquiv_forall_isVLDisjoint_eq_zero φ_eq hband_wou w hw
    exact exists_L1_banachLatEquiv_of_embeds_in_L1_with_aePositive (X := X) ν T hT_sup
      hT_inf hT_closed e he.1 (lp_aePos_of_forall_isVLDisjoint_eq_zero hTe_nn hTe_wou)

end ALSpace

end
