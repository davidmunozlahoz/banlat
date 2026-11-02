/-
Authors: Pedro Tradacete
-/

import BanLat.ALSpace.Sublattice
import BanLat.ALSpace.WeakUnit
import BanLat.Examples.Lp.Amalgamation
import BanLat.L1repr.Positive
import BanLat.Pushout.Construction

/-!
# Isometric amalgamation of Banach lattices

The canonical maps into a push-out of lattice isometries are themselves isometries.
Consequently, Banach lattices have the isometric amalgamation property, expressed
by `BanachLattice.exists_isometric_amalgam`. The proof uses measure-algebra amalgamation
for probability `L¹` spaces and positive-functional models of general Banach lattices.
-/

noncomputable section

open MeasureTheory

universe u v

namespace ALSpace

section Units

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [ALSpace X]

private lemma probability_model {e : X} (he : WeakOrderUnit e) (hne : ‖e‖ = 1) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (φ : BanachLatEquiv X (Lp ℝ 1 μ)), φ e = Lp.const 1 μ (1 : ℝ) := by
  obtain ⟨Ω, mΩ, μ, hμ, φ, hφ⟩ :=
    exists_L1_banachLatEquiv_isFiniteMeasure_of_weakOrderUnit he
  let := hμ
  have hconst : φ e = Lp.const 1 μ (1 : ℝ) :=
    Lp.ext (Filter.EventuallyEq.trans hφ
      (Lp.coeFn_const (p := 1) (μ := μ) (c := (1 : ℝ))).symm)
  have hnorm : (μ Set.univ).toReal = 1 := by
    rw [← MeasureAlgebra.ofMeasure_top μ, ← Lp.norm_algebraIndicator,
      Lp.algebraIndicator_top, ← hconst]
    exact (φ.toLinearIsometryEquiv.norm_map e).trans hne
  have hprob : IsProbabilityMeasure μ :=
    ⟨(ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ Set.univ) ENNReal.one_ne_top).mp
      (hnorm.trans ENNReal.toReal_one.symm)⟩
  exact ⟨Ω, mΩ, μ, hprob, φ, hconst⟩

private lemma probability_model_hom {Y Ω₀ : Type u}
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [ALSpace Y]
    [MeasurableSpace Ω₀] {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    (φ₀ : BanachLatEquiv X (Lp ℝ 1 μ₀)) (T : VecLatHom X Y) (hT : Isometry T)
    {e : X} (hne : ‖e‖ = 1) (he : WeakOrderUnit (T e))
    (hφ₀ : φ₀ e = Lp.const 1 μ₀ (1 : ℝ)) :
    ∃ (Ω₁ : Type u) (_ : MeasurableSpace Ω₁) (μ₁ : Measure Ω₁) (_ : IsProbabilityMeasure μ₁)
      (φ₁ : BanachLatEquiv Y (Lp ℝ 1 μ₁)) (R : VecLatHom (Lp ℝ 1 μ₀) (Lp ℝ 1 μ₁)),
      Isometry R ∧ R (Lp.const 1 μ₀ (1 : ℝ)) = Lp.const 1 μ₁ (1 : ℝ) ∧
        R.comp φ₀.toVecLatEquiv.toVecLatHom = φ₁.toVecLatEquiv.toVecLatHom.comp T := by
  obtain ⟨Ω₁, m₁, μ₁, hμ₁, φ₁, hφ₁⟩ :=
    probability_model he ((hT.norm_map_of_map_zero (map_zero T) e).trans hne)
  let R := φ₁.toVecLatEquiv.toVecLatHom.comp (T.comp φ₀.symm.toVecLatEquiv.toVecLatHom)
  have hR : Isometry R := φ₁.toLinearIsometryEquiv.isometry.comp
    (hT.comp φ₀.toLinearIsometryEquiv.symm.isometry)
  have hback : φ₀.symm (Lp.const 1 μ₀ (1 : ℝ)) = e :=
    (congrArg φ₀.symm hφ₀.symm).trans (φ₀.toLinearIsometryEquiv.symm_apply_apply e)
  refine ⟨Ω₁, m₁, μ₁, hμ₁, φ₁, R, hR,
    (congrArg (fun x ↦ φ₁ (T x)) hback).trans hφ₁, ?_⟩
  exact DFunLike.ext _ _ fun x ↦
    congrArg (fun z ↦ φ₁ (T z)) (φ₀.toLinearIsometryEquiv.symm_apply_apply x)

@[instance_reducible]
private def bandALSpace (B : Band X) : ALSpace B.toVectorSublattice :=
  ofClosedSublattice B.toVectorSublattice B.isClosed_coe

private def principalProjectionHom (e : X) :
    VecLatHom X (Band.principal e).toVectorSublattice where
  toFun x := ⟨Band.principalBandProjection e x, by
    change Band.principalBandProjection e x ∈ Band.generated {e}
    rw [← SetLike.mem_coe, ← Band.principalProjectionBand_coe]
    exact (Band.principalProjectionBand e).bandProjection_mem x⟩
  map_add' x y := Subtype.ext (map_add (Band.principalBandProjection e) x y)
  map_smul' r x := Subtype.ext (map_smul (Band.principalBandProjection e) r x)
  map_sup' x y :=
    Subtype.ext ((Band.principalProjectionBand e).bandProjection_isVecLatHom.map_sup' x y)
  map_inf' x y :=
    Subtype.ext ((Band.principalProjectionBand e).bandProjection_isVecLatHom.map_inf' x y)

variable {X₀ X₁ X₂ : Type u}
  [NormedAddCommGroup X₀] [Lattice X₀] [IsOrderedAddMonoid X₀] [ALSpace X₀]
  [NormedAddCommGroup X₁] [Lattice X₁] [IsOrderedAddMonoid X₁] [ALSpace X₁]
  [NormedAddCommGroup X₂] [Lattice X₂] [IsOrderedAddMonoid X₂] [ALSpace X₂]

/-- Isometric lattice embeddings that carry a normalized weak order unit to weak
order units admit a commuting amalgam by isometric lattice embeddings. -/
private lemma exists_isometric_amalgam_of_weakOrderUnit
    (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂)
    (h₁ : Isometry T₁) (h₂ : Isometry T₂) {e : X₀} (he : WeakOrderUnit e)
    (hne : ‖e‖ = 1) (he₁ : WeakOrderUnit (T₁ e)) (he₂ : WeakOrderUnit (T₂ e)) :
    ∃ (κ : Cardinal.{u})
      (S₁ : VecLatHom X₁ (Lp ℝ 1 (MeasureAlgebra.cubeMeasure κ)))
      (S₂ : VecLatHom X₂ (Lp ℝ 1 (MeasureAlgebra.cubeMeasure κ))),
      Isometry S₁ ∧ Isometry S₂ ∧ S₁.comp T₁ = S₂.comp T₂ := by
  obtain ⟨Ω₀, m₀, μ₀, hμ₀, φ₀, hφ₀⟩ := probability_model he hne
  obtain ⟨Ω₁, m₁, μ₁, hμ₁, φ₁, R₁, hR₁, hR₁one, hR₁comp⟩ :=
    probability_model_hom φ₀ T₁ h₁ hne he₁ hφ₀
  obtain ⟨Ω₂, m₂, μ₂, hμ₂, φ₂, R₂, hR₂, hR₂one, hR₂comp⟩ :=
    probability_model_hom φ₀ T₂ h₂ hne he₂ hφ₀
  obtain ⟨κ, U₁, U₂, hU₁, hU₂, hU⟩ :=
    Lp.exists_isometric_amalgam_of_map_const R₁ R₂ hR₁ hR₂ hR₁one hR₂one
  refine ⟨κ, U₁.comp φ₁.toVecLatEquiv.toVecLatHom,
    U₂.comp φ₂.toVecLatEquiv.toVecLatHom,
    hU₁.comp φ₁.toLinearIsometryEquiv.isometry,
    hU₂.comp φ₂.toLinearIsometryEquiv.isometry, ?_⟩
  apply DFunLike.ext
  intro x
  have hx := DFunLike.congr_fun hU (φ₀ x)
  have hx₁ : R₁ (φ₀ x) = φ₁ (T₁ x) := DFunLike.congr_fun hR₁comp x
  have hx₂ : R₂ (φ₀ x) = φ₂ (T₂ x) := DFunLike.congr_fun hR₂comp x
  exact (congrArg U₁ hx₁).symm.trans (hx.trans (congrArg U₂ hx₂))

end Units

section BinarySum

variable (A B : Type u)

private def sumFamily : Bool → Type u := fun b ↦ cond b A B

private instance [NormedAddCommGroup A] [NormedAddCommGroup B] :
    ∀ b, NormedAddCommGroup (sumFamily A B b) := by
  intro b
  cases b
  · exact inferInstanceAs (NormedAddCommGroup B)
  · exact inferInstanceAs (NormedAddCommGroup A)

private instance [Lattice A] [Lattice B] : ∀ b, Lattice (sumFamily A B b) := by
  intro b
  cases b
  · exact inferInstanceAs (Lattice B)
  · exact inferInstanceAs (Lattice A)

variable [NormedAddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [BanachLattice A]
  [NormedAddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [BanachLattice B]

private instance : ∀ b, IsOrderedAddMonoid (sumFamily A B b) := by
  intro b
  cases b
  · exact inferInstanceAs (IsOrderedAddMonoid B)
  · exact inferInstanceAs (IsOrderedAddMonoid A)

private instance : ∀ b, BanachLattice (sumFamily A B b) := by
  intro b
  cases b
  · exact inferInstanceAs (BanachLattice B)
  · exact inferInstanceAs (BanachLattice A)

variable {A B} {Z : Type u} [NormedAddCommGroup Z] [Lattice Z]
  [IsOrderedAddMonoid Z] [BanachLattice Z]

private def pairHom (f : VecLatHom Z A) (g : VecLatHom Z B) :
    VecLatHom Z (PiLp 1 (sumFamily A B)) where
  toFun z := WithLp.toLp 1 (fun b ↦ Bool.rec (g z) (f z) b)
  map_add' x y := WithLp.ofLp_injective 1
    (funext (fun b ↦ Bool.rec (map_add g x y) (map_add f x y) b))
  map_smul' r x := WithLp.ofLp_injective 1
    (funext (fun b ↦ Bool.rec (map_smul g r x) (map_smul f r x) b))
  map_sup' x y := WithLp.ofLp_injective 1
    (funext (fun b ↦ Bool.rec (g.map_sup' x y) (f.map_sup' x y) b))
  map_inf' x y := WithLp.ofLp_injective 1
    (funext (fun b ↦ Bool.rec (g.map_inf' x y) (f.map_inf' x y) b))

private lemma norm_pairHom (f : VecLatHom Z A) (g : VecLatHom Z B) (z : Z) :
    ‖pairHom f g z‖ = ‖f z‖ + ‖g z‖ := by
  simp only [PiLp.norm_eq_sum (by simp : 0 < (1 : ENNReal).toReal),
    ENNReal.toReal_one, Real.rpow_one, div_self one_ne_zero, Fintype.sum_bool]
  rfl

end BinarySum

section PrincipalBands

attribute [local instance] bandALSpace

variable {X Y : Type u}
  [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [ALSpace X]
  [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [ALSpace Y]

private lemma map_mem_principalBand (T : VecLatHom X Y) {e : X}
    (he : WeakOrderUnit e) (x : X) : T x ∈ Band.principal (T e) := by
  refine (quasiInteriorPoint_iff_weakOrderUnit.mpr he).2.induction ?_
    ((Band.isClosed_coe _).preimage T.toContinuousLinearMap.continuous) x
  rintro y ⟨c, hc, hy⟩
  have hb : c • |T e| ∈ Band.principal (T e) :=
    (Band.principal (T e)).toSubmodule.smul_mem c
      ((Band.principal (T e)).abs_mem (Band.subset_generated _ rfl))
  apply (Band.principal (T e)).mem_of_abs_le_abs hb
  rw [abs_of_nonneg (smul_nonneg hc (abs_nonneg (T e)))]
  simpa only [map_smul, T.map_abs] using T.monotone hy

private def principalRestriction (T : VecLatHom X Y) {e : X} (he : WeakOrderUnit e) :
    VecLatHom X (Band.principal (T e)).toVectorSublattice where
  toFun x := ⟨T x, map_mem_principalBand T he x⟩
  map_add' x y := Subtype.ext (map_add T x y)
  map_smul' r x := Subtype.ext (map_smul T r x)
  map_sup' x y := Subtype.ext (T.map_sup' x y)
  map_inf' x y := Subtype.ext (T.map_inf' x y)

private lemma weakOrderUnit_principalRestriction (T : VecLatHom X Y) {e : X}
    (he : WeakOrderUnit e) : WeakOrderUnit (principalRestriction T he e) :=
  quasiInteriorPoint_iff_weakOrderUnit.mp (quasiInteriorPoint_principal (T.map_nonneg he.1))

private def complementProjectionHom (e : X) : VecLatHom X X :=
  VecLatHom.ofIsVecLatHom (Band.principalProjectionBand e)ᶜ.bandProjection
    (Band.principalProjectionBand e)ᶜ.bandProjection_isVecLatHom

private lemma complementProjectionHom_apply (e x : X) :
    complementProjectionHom e x = x - (principalProjectionHom e x : X) :=
  congrArg (fun f : X →ₗ[ℝ] X ↦ f x)
    (ProjectionBand.bandProjection_compl (Band.principalProjectionBand e))

private lemma norm_projection_add_complement (e x : X) :
    ‖principalProjectionHom e x‖ + ‖complementProjectionHom e x‖ = ‖x‖ := by
  rw [complementProjectionHom_apply]
  have hd := (Band.principalProjectionBand e).id_sub_bandProjection_mem x
    _ ((Band.principalProjectionBand e).bandProjection_mem x)
  have hn := ALpSpace.norm_add_rpow_eq_of_isVLDisjoint (p := (1 : NNReal)) hd
  simp only [NNReal.coe_one, Real.rpow_one, sub_add_cancel] at hn
  exact (add_comm _ _).trans hn.symm

private lemma principalProjectionHom_eq (e x : X) (hx : x ∈ Band.principal e) :
    (principalProjectionHom e x : X) = x := by
  apply (Band.principalProjectionBand e).bandProjection_eq_of_mem
  rwa [← SetLike.mem_coe, Band.principalProjectionBand_coe]

variable {X₀ X₁ X₂ : Type u}
  [NormedAddCommGroup X₀] [Lattice X₀] [IsOrderedAddMonoid X₀] [ALSpace X₀]
  [NormedAddCommGroup X₁] [Lattice X₁] [IsOrderedAddMonoid X₁] [ALSpace X₁]
  [NormedAddCommGroup X₂] [Lattice X₂] [IsOrderedAddMonoid X₂] [ALSpace X₂]

private lemma pairHom_comp_eq {Z : Type u} [NormedAddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [BanachLattice Z]
    (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂) {e : X₀} (he : WeakOrderUnit e)
    (U₁ : VecLatHom (Band.principal (T₁ e)).toVectorSublattice Z)
    (U₂ : VecLatHom (Band.principal (T₂ e)).toVectorSublattice Z) (R : VecLatHom X₂ X₁)
    (hU : U₁.comp (principalRestriction T₁ he) = U₂.comp (principalRestriction T₂ he))
    (hR : ∀ x, R (T₂ x) = 0) :
    (pairHom (U₁.comp (principalProjectionHom (T₁ e)))
      (complementProjectionHom (T₁ e))).comp T₁ =
        (pairHom (U₂.comp (principalProjectionHom (T₂ e))) R).comp T₂ := by
  apply DFunLike.ext
  intro x
  have hx₁ : principalProjectionHom (T₁ e) (T₁ x) = principalRestriction T₁ he x :=
    Subtype.ext (principalProjectionHom_eq _ _ (map_mem_principalBand T₁ he x))
  have hx₂ : principalProjectionHom (T₂ e) (T₂ x) = principalRestriction T₂ he x :=
    Subtype.ext (principalProjectionHom_eq _ _ (map_mem_principalBand T₂ he x))
  apply WithLp.ofLp_injective 1
  funext b
  cases b
  · change complementProjectionHom (T₁ e) (T₁ x) = R (T₂ x)
    rw [hR x]
    rw [complementProjectionHom_apply, principalProjectionHom_eq _ _
      (map_mem_principalBand T₁ he x), sub_self]
  · change U₁ (principalProjectionHom (T₁ e) (T₁ x)) =
      U₂ (principalProjectionHom (T₂ e) (T₂ x))
    rw [hx₁, hx₂]
    exact congrArg (fun F ↦ F x) hU

private lemma exists_contracting_amalgam_of_weakOrderUnit
    (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂)
    (h₁ : Isometry T₁) (h₂ : Isometry T₂) {e : X₀} (he : WeakOrderUnit e)
    (hne : ‖e‖ = 1) :
    ∃ (Z : Type u) (_ : NormedAddCommGroup Z) (_ : Lattice Z)
      (_ : IsOrderedAddMonoid Z) (_ : BanachLattice Z)
      (S₁ : VecLatHom X₁ Z) (S₂ : VecLatHom X₂ Z),
      Isometry S₁ ∧ (∀ y, ‖S₂ y‖ ≤ ‖y‖) ∧ S₁.comp T₁ = S₂.comp T₂ := by
  have hi₁ : Isometry (principalRestriction T₁ he) := h₁
  have hi₂ : Isometry (principalRestriction T₂ he) := h₂
  obtain ⟨κ, U₁, U₂, hU₁, hU₂, hU⟩ := exists_isometric_amalgam_of_weakOrderUnit
    (principalRestriction T₁ he) (principalRestriction T₂ he) hi₁ hi₂ he hne
    (weakOrderUnit_principalRestriction T₁ he) (weakOrderUnit_principalRestriction T₂ he)
  let zeroHom : VecLatHom X₂ X₁ := VecLatHom.ofAbs 0 (by intro x; simp)
  let S₁ := pairHom (U₁.comp (principalProjectionHom (T₁ e))) (complementProjectionHom (T₁ e))
  let S₂ := pairHom (U₂.comp (principalProjectionHom (T₂ e))) zeroHom
  refine ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, S₁, S₂, ?_, ?_, ?_⟩
  · apply AddMonoidHomClass.isometry_of_norm S₁.toLinearMap
    intro x
    change ‖pairHom _ _ x‖ = ‖x‖
    rw [norm_pairHom]
    change ‖U₁ (principalProjectionHom (T₁ e) x)‖ + _ = _
    rw [hU₁.norm_map_of_map_zero (map_zero U₁)]
    exact norm_projection_add_complement (T₁ e) x
  · intro y
    change ‖pairHom _ _ y‖ ≤ ‖y‖
    rw [norm_pairHom]
    change ‖U₂ (principalProjectionHom (T₂ e) y)‖ + ‖(0 : X₁)‖ ≤ ‖y‖
    rw [hU₂.norm_map_of_map_zero (map_zero U₂), norm_zero, add_zero]
    exact (le_add_of_nonneg_right (norm_nonneg (complementProjectionHom (T₂ e) y))).trans_eq
      (norm_projection_add_complement (T₂ e) y)
  · exact pairHom_comp_eq T₁ T₂ he U₁ U₂ zeroHom hU (fun _ ↦ rfl)

/-- Isometric embeddings of an AL-space with a weak order unit have a commuting
amalgam that is isometric on the first space and contractive on the second. -/
private lemma exists_contracting_amalgam
    (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂)
    (h₁ : Isometry T₁) (h₂ : Isometry T₂) (he : ∃ e : X₀, WeakOrderUnit e) :
    ∃ (Z : Type u) (_ : NormedAddCommGroup Z) (_ : Lattice Z)
      (_ : IsOrderedAddMonoid Z) (_ : BanachLattice Z)
      (S₁ : VecLatHom X₁ Z) (S₂ : VecLatHom X₂ Z),
      Isometry S₁ ∧ (∀ y, ‖S₂ y‖ ≤ ‖y‖) ∧ S₁.comp T₁ = S₂.comp T₂ := by
  obtain ⟨e, he⟩ := he
  by_cases he0 : e = 0
  · have hx (x : X₀) : x = 0 := he.2 x (he0 ▸ isVLDisjoint_zero_right x)
    let S₂ : VecLatHom X₂ X₁ := VecLatHom.ofAbs 0 (by intro x; simp)
    refine ⟨X₁, inferInstance, inferInstance, inferInstance, inferInstance,
      VecLatHom.id, S₂, isometry_id,
      fun y ↦ (norm_zero : ‖(0 : X₁)‖ = 0).le.trans (norm_nonneg y), ?_⟩
    apply DFunLike.ext
    intro x
    change T₁ x = 0
    rw [hx x, map_zero]
  · have hnorm : 0 < ‖e‖ := norm_pos_iff.mpr he0
    have he' : WeakOrderUnit (‖e‖⁻¹ • e) := by
      refine ⟨smul_nonneg (inv_nonneg.mpr hnorm.le) he.1, ?_⟩
      intro x hx
      apply he.2 x
      have hd := hx.smul_right ‖e‖
      simpa only [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul] using hd
    apply exists_contracting_amalgam_of_weakOrderUnit T₁ T₂ h₁ h₂ he'
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']

end PrincipalBands

end ALSpace

namespace BanachLattice

attribute [local instance] ALSpace.bandALSpace

variable {X Y : Type u}
  [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X]
  [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]

private lemma norm_model_le (φ : StrongDual ℝ X) (T : VecLatHom X Y)
    (hT : ∀ x, ‖T x‖ = φ |x|) (hφ : ‖φ‖ ≤ 1) (x : X) : ‖T x‖ ≤ ‖x‖ := by
  rw [hT]
  calc φ |x| ≤ ‖φ |x|‖ := Real.le_norm_self _
    _ ≤ ‖φ‖ * ‖|x|‖ := φ.le_opNorm |x|
    _ ≤ 1 * ‖x‖ := mul_le_mul hφ (norm_abs_eq_norm x).le (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

private lemma exists_norming_model {x : X} (hx : 0 ≤ x) :
    ∃ (Z : Type u) (_ : NormedAddCommGroup Z) (_ : Lattice Z)
      (_ : IsOrderedAddMonoid Z) (_ : ALSpace Z) (T : VecLatHom X Z),
      DenseRange T ∧ (∀ y, ‖T y‖ ≤ ‖y‖) ∧ ‖T x‖ = ‖x‖ ∧ ∃ e : Z, WeakOrderUnit e := by
  obtain ⟨φ, hφpos, hφnorm, hφx⟩ := StrongDual.exists_positive_dual_norming hx
  obtain ⟨Ω, mΩ, μ, T, hdense, hnorm⟩ :=
    exists_L1_representation_of_positive φ.toLinearMap (StrongDual.nonneg_iff.mp hφpos)
  let P := ALSpace.principalProjectionHom (T x)
  have hPsurj : Function.Surjective P := by
    intro y
    exact ⟨(y : Lp ℝ 1 μ), Subtype.ext (ALSpace.principalProjectionHom_eq _ _ y.property)⟩
  refine ⟨(Band.principal (T x)).toVectorSublattice, inferInstance, inferInstance,
    inferInstance, inferInstance, P.comp T, ?_, ?_, ?_, ?_⟩
  · exact hPsurj.denseRange.comp hdense P.toContinuousLinearMap.continuous
  · intro y
    exact ((le_add_of_nonneg_right
      (norm_nonneg (ALSpace.complementProjectionHom (T x) (T y)))).trans_eq
        (ALSpace.norm_projection_add_complement (T x) (T y))).trans
          (norm_model_le φ T hnorm hφnorm y)
  · change ‖(ALSpace.principalProjectionHom (T x) (T x) : Lp ℝ 1 μ)‖ = ‖x‖
    rw [ALSpace.principalProjectionHom_eq _ _ (Band.subset_generated _ rfl)]
    rw [hnorm, abs_of_nonneg hx]
    exact hφx
  · exact ⟨_, quasiInteriorPoint_iff_weakOrderUnit.mp
      (quasiInteriorPoint_principal (T.map_nonneg hx))⟩

private lemma norm_posPart_add_le (y z : Y) : ‖(y + z)⁺‖ ≤ ‖y⁺‖ + ‖z⁺‖ := by
  have hle : |(y + z)⁺| ≤ |y⁺ + z⁺| := by
    simpa only [abs_of_nonneg (posPart_nonneg (y + z)),
      abs_of_nonneg (add_nonneg (posPart_nonneg y) (posPart_nonneg z))]
      using posPart_add_le y z
  exact (norm_le_norm_of_abs_le_abs hle).trans (norm_add_le _ _)

private lemma norm_le_of_posPart_bound (g : Y →ₗ[ℝ] ℝ)
    (hg : ∀ y, g y ≤ ‖y⁺‖) (y : Y) : ‖g y‖ ≤ ‖y‖ := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  refine ⟨?_, (hg y).trans (NormedVectorLattice.norm_posPart_le y)⟩
  have h := (hg (-y)).trans (NormedVectorLattice.norm_posPart_le (-y))
  simpa only [map_neg, norm_neg, neg_le] using h

private lemma exists_posPart_dominated_extension (T : VecLatHom X Y) (hT : Isometry T)
    (φ : StrongDual ℝ X) (hφ : Positive φ.toLinearMap) (hφnorm : ‖φ‖ ≤ 1) :
    ∃ g : Y →ₗ[ℝ] ℝ, (∀ x, g (T x) = φ x) ∧ ∀ y, g y ≤ ‖y⁺‖ := by
  let E : X →ₗᵢ[ℝ] Y :=
    ⟨T.toLinearMap, hT.norm_map_of_map_zero (map_zero T)⟩
  let φp := φ.comp E.equivRange.toContinuousLinearEquiv.symm.toContinuousLinearMap
  let f : Y →ₗ.[ℝ] ℝ := ⟨LinearMap.range E.toLinearMap, φp⟩
  have hNhom (c : ℝ) (hc : 0 < c) (y : Y) : ‖(c • y)⁺‖ = c * ‖y⁺‖ := by
    simp only [posPart_smul_nonneg hc.le, norm_smul, Real.norm_of_nonneg hc.le]
  have hf : ∀ y : f.domain, f y ≤ ‖(y : Y)⁺‖ := by
    intro y
    let x : X := E.equivRange.symm y
    have hy : (y : Y) = T x :=
      (congrArg Subtype.val (E.equivRange.apply_symm_apply y)).symm
    change φ x ≤ ‖(y : Y)⁺‖
    rw [hy, ← T.map_posPart, hT.norm_map_of_map_zero (map_zero T)]
    calc φ x ≤ φ x⁺ := Positive.monotone_iff.mpr hφ (le_posPart x)
      _ ≤ ‖φ x⁺‖ := Real.le_norm_self _
      _ ≤ ‖φ‖ * ‖x⁺‖ := φ.le_opNorm _
      _ ≤ 1 * ‖x⁺‖ := mul_le_mul_of_nonneg_right hφnorm (norm_nonneg _)
      _ = ‖x⁺‖ := one_mul _
  obtain ⟨g, hg_eq, hg_le⟩ := exists_extension_of_le_sublinear f
    (fun y ↦ ‖y⁺‖) hNhom norm_posPart_add_le hf
  exact ⟨g, fun x ↦ (hg_eq (E.equivRange x)).trans
    (congrArg φ (E.equivRange.symm_apply_apply x)), hg_le⟩

private lemma exists_positive_extension (T : VecLatHom X Y) (hT : Isometry T)
    (φ : StrongDual ℝ X) (hφ : Positive φ.toLinearMap) (hφnorm : ‖φ‖ ≤ 1) :
    ∃ ψ : StrongDual ℝ Y, Positive ψ.toLinearMap ∧ ‖ψ‖ ≤ 1 ∧ ∀ x, ψ (T x) = φ x := by
  obtain ⟨g, hg_eq, hg_le⟩ := exists_posPart_dominated_extension T hT φ hφ hφnorm
  let ψ := g.mkContinuous 1 (fun y ↦ by
    simpa only [one_mul] using norm_le_of_posPart_bound g hg_le y)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro y hy
    have hn := hg_le (-y)
    change 0 ≤ g y
    simpa only [map_neg, posPart_eq_zero.mpr (neg_nonpos.mpr hy), norm_zero, neg_nonpos]
      using hn
  · exact g.mkContinuous_norm_le zero_le_one (fun y ↦ by
      simpa only [one_mul] using norm_le_of_posPart_bound g hg_le y)
  · exact hg_eq

private lemma exists_isometric_factor {Z : Type u} [NormedAddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [BanachLattice Z]
    (j : VecLatHom X Y) (f : VecLatHom X Z) (hd : DenseRange j)
    (hn : ∀ x, ‖f x‖ = ‖j x‖) :
    ∃ U : VecLatHom Y Z, Isometry U ∧ U.comp j = f := by
  let U := f.toLinearMap.extendOfNorm j.toLinearMap
  have hU (x : X) : U (j x) = f x :=
    LinearMap.extendOfNorm_eq hd ⟨1, fun x ↦ (hn x).le.trans_eq (one_mul _).symm⟩ x
  have hUnorm (y : Y) : ‖U y‖ = ‖y‖ := by
    refine hd.induction_on y (isClosed_eq U.continuous.norm continuous_norm) ?_
    exact fun x ↦ (congrArg norm (hU x)).trans (hn x)
  have hUabs (y : Y) : U |y| = |U y| := by
    refine hd.induction_on y (isClosed_eq
      (U.continuous.comp NormedVectorLattice.lipschitzWith_abs.continuous)
      (NormedVectorLattice.lipschitzWith_abs.continuous.comp U.continuous)) ?_
    intro x
    rw [← j.map_abs, hU, hU, f.map_abs]
  exact ⟨VecLatHom.ofAbs U.toLinearMap hUabs,
    AddMonoidHomClass.isometry_of_norm U.toLinearMap hUnorm, DFunLike.ext _ _ hU⟩

private lemma exists_model_functional {Z : Type u} [NormedAddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [ALSpace Z] (S : VecLatHom X Z)
    (hS : ∀ x, ‖S x‖ ≤ ‖x‖) :
    ∃ φ : StrongDual ℝ X, Positive φ.toLinearMap ∧ ‖φ‖ ≤ 1 ∧ ∀ x, ‖S x‖ = φ |x| := by
  let φ := (ALSpace.dualUnit Z).comp S.toContinuousLinearMap
  have hn (x : X) : ‖S x‖ = φ |x| := by
    change ‖S x‖ = ALSpace.dualUnit Z (S |x|)
    rw [S.map_abs, ALSpace.dualUnit_apply_of_nonneg (abs_nonneg _), norm_abs_eq_norm]
  have hφ : Positive φ.toLinearMap := fun x hx ↦
    StrongDual.nonneg_iff.mp ALSpace.dualUnit_nonneg (S x) (S.map_nonneg hx)
  refine ⟨φ, hφ, φ.opNorm_le_bound zero_le_one ?_, hn⟩
  intro x
  rw [one_mul, Real.norm_eq_abs]
  exact ((Positive.abs_le_map_abs hφ x).trans_eq (hn x).symm).trans (hS x)

variable {X₀ X₁ X₂ : Type u}
  [NormedAddCommGroup X₀] [Lattice X₀] [IsOrderedAddMonoid X₀] [BanachLattice X₀]
  [NormedAddCommGroup X₁] [Lattice X₁] [IsOrderedAddMonoid X₁] [BanachLattice X₁]
  [NormedAddCommGroup X₂] [Lattice X₂] [IsOrderedAddMonoid X₂] [BanachLattice X₂]

private lemma exists_norming_amalgam (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂)
    (h₁ : ∀ z, ‖T₁ z‖ ≤ ‖z‖) (h₂ : Isometry T₂) {x : X₁} (hx : 0 ≤ x) :
    ∃ (Z : Type u) (_ : NormedAddCommGroup Z) (_ : Lattice Z)
      (_ : IsOrderedAddMonoid Z) (_ : BanachLattice Z)
      (R₁ : VecLatHom X₁ Z) (R₂ : VecLatHom X₂ Z),
      (∀ y, ‖R₁ y‖ ≤ ‖y‖) ∧ (∀ y, ‖R₂ y‖ ≤ ‖y‖) ∧
        ‖R₁ x‖ = ‖x‖ ∧ R₁.comp T₁ = R₂.comp T₂ := by
  obtain ⟨Z₁, _, _, _, _, M₁, _, hM₁, hM₁x, e₁, he₁⟩ := exists_norming_model hx
  obtain ⟨φ₀, hφ₀pos, hφ₀norm, hφ₀⟩ := exists_model_functional (M₁.comp T₁)
    (fun z ↦ (hM₁ (T₁ z)).trans (h₁ z))
  obtain ⟨φ₂, hφ₂pos, hφ₂norm, hφ₂⟩ := exists_positive_extension T₂ h₂ φ₀ hφ₀pos hφ₀norm
  obtain ⟨Ω₀, m₀, μ₀, M₀, hd₀, hn₀⟩ := exists_L1_representation_of_positive φ₀.toLinearMap hφ₀pos
  obtain ⟨Ω₂, m₂, μ₂, M₂, _, hn₂⟩ := exists_L1_representation_of_positive φ₂.toLinearMap hφ₂pos
  obtain ⟨E₁, hE₁, hE₁comp⟩ := exists_isometric_factor M₀ (M₁.comp T₁) hd₀
    (fun z ↦ (hφ₀ z).trans (hn₀ z).symm)
  have hn₂T (z : X₀) : ‖(M₂.comp T₂) z‖ = ‖M₀ z‖ := by
    change ‖M₂ (T₂ z)‖ = ‖M₀ z‖
    rw [hn₂, ← T₂.map_abs, hn₀]
    exact hφ₂ |z|
  obtain ⟨E₂, hE₂, hE₂comp⟩ := exists_isometric_factor M₀ (M₂.comp T₂) hd₀ hn₂T
  have hunit := ALSpace.exists_weakOrderUnit_of_injective E₁ hE₁.injective he₁
  obtain ⟨Z, _, _, _, _, V₁, V₂, hV₁, hV₂, hV⟩ :=
    ALSpace.exists_contracting_amalgam E₁ E₂ hE₁ hE₂ hunit
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance,
    V₁.comp M₁, V₂.comp M₂, ?_, ?_, ?_, ?_⟩
  · exact fun y ↦ (hV₁.norm_map_of_map_zero (map_zero V₁) (M₁ y)).le.trans (hM₁ y)
  · exact fun y ↦ (hV₂ (M₂ y)).trans (norm_model_le φ₂ M₂ hn₂ hφ₂norm y)
  · exact (hV₁.norm_map_of_map_zero (map_zero V₁) (M₁ x)).trans hM₁x
  · apply DFunLike.ext
    intro z
    have hz₁ : E₁ (M₀ z) = M₁ (T₁ z) := DFunLike.congr_fun hE₁comp z
    have hz₂ : E₂ (M₀ z) = M₂ (T₂ z) := DFunLike.congr_fun hE₂comp z
    exact (congrArg V₁ hz₁).symm.trans
      ((DFunLike.congr_fun hV (M₀ z)).trans (congrArg V₂ hz₂))

variable {P : Type v} [NormedAddCommGroup P] [Lattice P]
  [IsOrderedAddMonoid P] [BanachLattice P]
  {T₁ : VecLatHom X₀ X₁} {T₂ : VecLatHom X₀ X₂}
  {S₁ : VecLatHom X₁ P} {S₂ : VecLatHom X₂ P}

private lemma norm_le_inl_of_nonneg (h : IsPushout.{u, u, u, v, u} T₁ T₂ S₁ S₂)
    (h₁ : ‖T₁.toContinuousLinearMap‖ ≤ 1) (h₂ : Isometry T₂) {x : X₁} (hx : 0 ≤ x) :
    ‖x‖ ≤ ‖S₁ x‖ := by
  obtain ⟨Z, _, _, _, _, R₁, R₂, hR₁, hR₂, hRx, hR⟩ := exists_norming_amalgam T₁ T₂
    (fun z ↦ (T₁.toContinuousLinearMap.le_of_opNorm_le h₁ z).trans_eq (one_mul _)) h₂ hx
  obtain ⟨R, hRS₁, _, hRn, _⟩ := h.exists_lift Z R₁ R₂ hR
  have hR₁n : ‖R₁.toContinuousLinearMap‖ ≤ 1 :=
    R₁.toContinuousLinearMap.opNorm_le_bound zero_le_one
      (fun z ↦ (hR₁ z).trans_eq (one_mul _).symm)
  have hR₂n : ‖R₂.toContinuousLinearMap‖ ≤ 1 :=
    R₂.toContinuousLinearMap.opNorm_le_bound zero_le_one
      (fun z ↦ (hR₂ z).trans_eq (one_mul _).symm)
  have hRn' : ‖R.toContinuousLinearMap‖ ≤ 1 := hRn.trans (max_le hR₁n hR₂n)
  have hxR : R (S₁ x) = R₁ x := DFunLike.congr_fun hRS₁ x
  calc ‖x‖ = ‖R (S₁ x)‖ := hRx.symm.trans (congrArg norm hxR).symm
    _ ≤ 1 * ‖S₁ x‖ := R.toContinuousLinearMap.le_of_opNorm_le hRn' _
    _ = ‖S₁ x‖ := one_mul _

/-- In a push-out, the first outgoing map is an isometry when the first input
map is contractive and the second input map is an isometry. -/
theorem IsPushout.isometry_inl (h : IsPushout.{u, u, u, v, u} T₁ T₂ S₁ S₂)
    (h₁ : ‖T₁.toContinuousLinearMap‖ ≤ 1) (h₂ : Isometry T₂) : Isometry S₁ := by
  apply AddMonoidHomClass.isometry_of_norm S₁.toLinearMap
  intro x
  apply le_antisymm
  · exact (S₁.toContinuousLinearMap.le_of_opNorm_le h.norm_inl_le x).trans_eq (one_mul _)
  · change ‖x‖ ≤ ‖S₁ x‖
    simpa only [S₁.map_abs, norm_abs_eq_norm] using
      norm_le_inl_of_nonneg h h₁ h₂ (abs_nonneg x)

/-- In a push-out, the second outgoing map is an isometry when the first input
map is an isometry and the second input map is contractive. -/
theorem IsPushout.isometry_inr (h : IsPushout.{u, u, u, v, u} T₁ T₂ S₁ S₂)
    (h₁ : Isometry T₁) (h₂ : ‖T₂.toContinuousLinearMap‖ ≤ 1) : Isometry S₂ :=
  h.swap.isometry_inl h₂ h₁

/-- Both outgoing maps of a push-out of lattice isometries are isometries. -/
theorem IsPushout.isometries (h : IsPushout.{u, u, u, v, u} T₁ T₂ S₁ S₂)
    (h₁ : Isometry T₁) (h₂ : Isometry T₂) : Isometry S₁ ∧ Isometry S₂ := by
  refine ⟨h.isometry_inl ?_ h₂, h.isometry_inr h₁ ?_⟩
  · exact T₁.toContinuousLinearMap.opNorm_le_bound zero_le_one
      (fun x ↦ (h₁.norm_map_of_map_zero (map_zero T₁) x).le.trans_eq (one_mul _).symm)
  · exact T₂.toContinuousLinearMap.opNorm_le_bound zero_le_one
      (fun x ↦ (h₂.norm_map_of_map_zero (map_zero T₂) x).le.trans_eq (one_mul _).symm)

/-- The canonical first map into a push-out of lattice isometries is an isometry. -/
theorem Pushout.isometry_inl (h₁ : Isometry T₁) (h₂ : Isometry T₂) :
    Isometry (Pushout.inl T₁ T₂) :=
  ((Pushout.is_pushout T₁ T₂).isometries h₁ h₂).1

/-- The canonical second map into a push-out of lattice isometries is an isometry. -/
theorem Pushout.isometry_inr (h₁ : Isometry T₁) (h₂ : Isometry T₂) :
    Isometry (Pushout.inr T₁ T₂) :=
  ((Pushout.is_pushout T₁ T₂).isometries h₁ h₂).2

/-- Banach lattices have the isometric amalgamation property: two lattice isometries
with a common domain embed into a common Banach lattice with equal compositions. -/
theorem exists_isometric_amalgam (T₁ : VecLatHom X₀ X₁) (T₂ : VecLatHom X₀ X₂)
    (h₁ : Isometry T₁) (h₂ : Isometry T₂) :
    ∃ (Z : Type u) (_ : NormedAddCommGroup Z) (_ : Lattice Z)
      (_ : IsOrderedAddMonoid Z) (_ : BanachLattice Z)
      (S₁ : VecLatHom X₁ Z) (S₂ : VecLatHom X₂ Z),
      Isometry S₁ ∧ Isometry S₂ ∧ S₁.comp T₁ = S₂.comp T₂ :=
  ⟨Pushout T₁ T₂, inferInstance, inferInstance, inferInstance, inferInstance,
    Pushout.inl T₁ T₂, Pushout.inr T₁ T₂, Pushout.isometry_inl h₁ h₂,
    Pushout.isometry_inr h₁ h₂, Pushout.commutes T₁ T₂⟩

end BanachLattice
