/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.AMSpace.Complex.Basic
import BanLat.ComplexBanachLattice.Complexification.Hom
import BanLat.Examples.CofK.Basic

/-!
# Complex-valued continuous functions as complex vector and Banach lattices

For any topological space `K`, the space `C(K, ℂ)` is a complex vector lattice with pointwise
modulus. When `K` is compact, it is a complex Banach lattice identified with the canonical
complexification of `C(K, ℝ)` and a complex AM-space with the constant-one function as unit.
-/

open scoped ComplexStarModule

namespace ContinuousMap

variable {K : Type*} [TopologicalSpace K]

private theorem selfAdjoint_apply_re (f : selfAdjoint C(K, ℂ)) (t : K) :
    ((f.1 t).re : ℂ) = f.1 t := by
  have hf : star (f.1 t) = f.1 t := by
    simpa only [ContinuousMap.star_apply] using
      congrArg (fun g : C(K, ℂ) ↦ g t) f.property.star_eq
  exact Complex.conj_eq_iff_re.mp (by simpa only [Complex.star_def] using hf)

/-- The self-adjoint complex-valued continuous functions are real-linearly
equivalent to the real-valued continuous functions. -/
noncomputable def selfAdjointRealLinearEquiv :
    selfAdjoint C(K, ℂ) ≃ₗ[ℝ] C(K, ℝ) := by
  exact
    { toFun := fun f ↦
        ⟨fun t ↦ (f.1 t).re, Complex.continuous_re.comp f.1.continuous⟩
      invFun := fun f ↦
        ⟨⟨fun t ↦ (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩,
          isSelfAdjoint_iff.mpr (ContinuousMap.ext (fun t ↦ by
            simp [ContinuousMap.star_apply]))⟩
      left_inv := fun f ↦ Subtype.ext (ContinuousMap.ext (selfAdjoint_apply_re f))
      right_inv := fun f ↦ ContinuousMap.ext (fun t ↦ Complex.ofReal_re (f t))
      map_add' := fun f g ↦ ContinuousMap.ext (fun t ↦ Complex.add_re (f.1 t) (g.1 t))
      map_smul' := fun r f ↦ ContinuousMap.ext (fun t ↦ by simp) }

/-! ### The self-adjoint part as a real vector lattice -/

/-- The lattice structure on self-adjoint continuous functions is transported
through the equivalence with real-valued continuous functions. -/
noncomputable instance instLatticeSelfAdjoint :
    Lattice (selfAdjoint C(K, ℂ)) := by
  exact selfAdjointRealLinearEquiv.toEquiv.lattice

/-- Addition on self-adjoint continuous functions respects the transported order. -/
instance instIsOrderedAddMonoidSelfAdjoint :
    IsOrderedAddMonoid (selfAdjoint C(K, ℂ)) := by
  exact Function.Injective.isOrderedAddMonoid selfAdjointRealLinearEquiv
    selfAdjointRealLinearEquiv.map_add Iff.rfl

/-- The self-adjoint continuous functions form a real vector lattice. -/
noncomputable instance instVectorLatticeSelfAdjoint :
    VectorLattice (selfAdjoint C(K, ℂ)) := by
  exact
    { smul_le_smul_of_nonneg_left := fun a ha x y hxy ↦ by
        change selfAdjointRealLinearEquiv (a • x) ≤ selfAdjointRealLinearEquiv (a • y)
        change selfAdjointRealLinearEquiv x ≤ selfAdjointRealLinearEquiv y at hxy
        rw [map_smul, map_smul]
        rw [ContinuousMap.le_def] at hxy ⊢
        intro t
        simp only [ContinuousMap.smul_apply]
        exact smul_le_smul_of_nonneg_left (hxy t) ha }

private theorem selfAdjoint_rotationRange_isLUB (x y : selfAdjoint C(K, ℂ)) :
    IsLUB (VectorLattice.rotationRange x y)
      (selfAdjointRealLinearEquiv.symm
        (continuousMapModulus (selfAdjointRealLinearEquiv x)
          (selfAdjointRealLinearEquiv y))) := by
  let e : selfAdjoint C(K, ℂ) ≃o C(K, ℝ) :=
    { selfAdjointRealLinearEquiv.toEquiv with map_rel_iff' := Iff.rfl }
  apply e.isLUB_image.mp
  change IsLUB (selfAdjointRealLinearEquiv '' VectorLattice.rotationRange x y)
    (continuousMapModulus (selfAdjointRealLinearEquiv x) (selfAdjointRealLinearEquiv y))
  simpa only [VectorLattice.rotationRange, ← Set.range_comp, Function.comp_def,
    map_add, map_smul] using continuousMapModulus_isLUB
      (selfAdjointRealLinearEquiv x) (selfAdjointRealLinearEquiv y)

/-- Complex-valued continuous functions form a complex vector lattice. -/
noncomputable instance instComplexVectorLattice : ComplexVectorLattice C(K, ℂ) := by
  exact
    { toVectorLattice := instVectorLatticeSelfAdjoint
      coe_smul := fun _ _ ↦ rfl
      exists_isLUB_rotationRange := fun x y ↦
        ⟨selfAdjointRealLinearEquiv.symm
          (continuousMapModulus (selfAdjointRealLinearEquiv x)
            (selfAdjointRealLinearEquiv y)), selfAdjoint_rotationRange_isLUB x y⟩ }

/-- The real coordinate of the abstract real part of a complex-valued function is its
pointwise real part. -/
@[simp]
theorem realPart_apply_re
    (f : C(K, ℂ)) (t : K) :
    ((ℜ f : C(K, ℂ)) t).re = (f t).re := by
  rw [realPart_apply_coe]
  simp [ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.star_apply]
  ring

/-- The real coordinate of the abstract imaginary part of a complex-valued function is its
pointwise imaginary part. -/
@[simp]
theorem imaginaryPart_apply_re
    (f : C(K, ℂ)) (t : K) :
    ((ℑ f : C(K, ℂ)) t).re = (f t).im := by
  rw [imaginaryPart_apply_coe]
  simp [ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.star_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The lattice-valued modulus of a complex-valued continuous function is its
pointwise norm. -/
@[simp]
theorem modulus_apply (f : C(K, ℂ)) (t : K) :
    ((ComplexVectorLattice.modulus f : selfAdjoint C(K, ℂ)) : C(K, ℂ)) t =
      (‖f t‖ : ℂ) := by
  rw [ComplexVectorLattice.modulus_eq_of_isLUB
    (selfAdjoint_rotationRange_isLUB (ℜ f) (ℑ f))]
  change (Real.sqrt (((ℜ f : C(K, ℂ)) t).re ^ 2 +
    ((ℑ f : C(K, ℂ)) t).re ^ 2) : ℂ) = (‖f t‖ : ℂ)
  rw [realPart_apply_re, imaginaryPart_apply_re, ← Complex.norm_eq_sqrt_sq_add_sq]

variable [CompactSpace K]

/-- The self-adjoint part of `C(K, ℂ)` is linearly isometric equivalent
as normed space to `C(K, ℝ)`. -/
noncomputable def selfAdjointRealEquiv :
    selfAdjoint C(K, ℂ) ≃ₗᵢ[ℝ] C(K, ℝ) := by
  refine { toLinearEquiv := selfAdjointRealLinearEquiv, norm_map' := ?_ }
  intro f
  change ‖selfAdjointRealLinearEquiv f‖ = ‖(f.1 : C(K, ℂ))‖
  rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
  exact iSup_congr (fun t ↦ (Complex.norm_real _).symm.trans
    (congrArg norm (selfAdjoint_apply_re f t)))

/-- The equivalence from `selfAdjoint C(K, ℂ)` to `C(K, ℝ)` sends a
self-adjoint function to its pointwise real part. -/
@[simp]
theorem selfAdjointRealEquiv_apply_apply
    (f : selfAdjoint C(K, ℂ)) (t : K) :
    selfAdjointRealEquiv f t = (f.1 t).re := by
  rfl

/-- The inverse equivalence from `C(K, ℝ)` to `selfAdjoint C(K, ℂ)` sends a
real-valued function to its pointwise inclusion into the complex numbers. -/
@[simp]
theorem selfAdjointRealEquiv_symm_apply_apply
    (f : C(K, ℝ)) (t : K) :
    ((selfAdjointRealEquiv.symm f : selfAdjoint C(K, ℂ)) : C(K, ℂ)) t =
      (f t : ℂ) := by
  rfl

/-! ### `selfAdjoint C(K, ℂ)` as a real Banach lattice -/

private theorem selfAdjointRealEquiv_sup
    (x y : selfAdjoint C(K, ℂ)) :
    selfAdjointRealEquiv (x ⊔ y) =
      selfAdjointRealEquiv x ⊔ selfAdjointRealEquiv y := by
  exact selfAdjointRealEquiv.apply_symm_apply _

private theorem selfAdjointRealEquiv_inf
    (x y : selfAdjoint C(K, ℂ)) :
    selfAdjointRealEquiv (x ⊓ y) =
      selfAdjointRealEquiv x ⊓ selfAdjointRealEquiv y := by
  exact selfAdjointRealEquiv.apply_symm_apply _

/-- `selfAdjoint C(K, ℂ)` forms a Banach lattice. -/
noncomputable instance instBanachLatticeSelfAdjoint :
    BanachLattice (selfAdjoint C(K, ℂ)) := by
  refine
    { toVectorLattice := instVectorLatticeSelfAdjoint
      solid := by
        intro x y hxy
        rw [← selfAdjointRealEquiv.norm_map x, ← selfAdjointRealEquiv.norm_map y]
        apply norm_le_norm_of_abs_le_abs
        change selfAdjointRealEquiv |x| ≤ selfAdjointRealEquiv |y| at hxy
        simpa only [abs, selfAdjointRealEquiv_sup, map_neg] using hxy
      norm_smul := by
        intro r x
        rw [← selfAdjointRealEquiv.norm_map (r • x),
          ← selfAdjointRealEquiv.norm_map x, map_smul, norm_smul]
      toCompleteSpace := ?_ }
  exact
    (completeSpace_congr (e := (selfAdjointRealEquiv (K := K)).toEquiv)
      (AddMonoidHomClass.isometry_of_norm (selfAdjointRealEquiv (K := K))
        (selfAdjointRealEquiv (K := K)).norm_map).isUniformEmbedding).mpr inferInstance

/-- The canonical Banach lattice isometry between `selfAdjoint C(K, ℂ)` and `C(K, ℝ)`. -/
noncomputable def selfAdjointBanachLatEquiv :
    BanachLatEquiv (selfAdjoint C(K, ℂ)) C(K, ℝ) := by
  exact
    { toLinearIsometryEquiv := selfAdjointRealEquiv
      map_sup' := selfAdjointRealEquiv_sup
      map_inf' := selfAdjointRealEquiv_inf }

/-- The Banach lattice equivalence from `selfAdjoint C(K, ℂ)` to `C(K, ℝ)` sends
a self-adjoint function to its pointwise real part. -/
@[simp]
theorem selfAdjointBanachLatEquiv_apply_apply
    (f : selfAdjoint C(K, ℂ)) (t : K) :
    selfAdjointBanachLatEquiv f t = (f.1 t).re := by
  rfl

/-! ### Complex Banach lattice structures -/

/-- `C(K, ℂ)` is a **complex Banach lattice.** -/
noncomputable instance instComplexBanachLattice :
    ComplexBanachLattice C(K, ℂ) := by
  refine
    { instBanachLatticeSelfAdjoint (K := K), instComplexVectorLattice (K := K) with
      norm_modulus := ?_ }
  intro f
  change ‖((ComplexVectorLattice.modulus f : selfAdjoint C(K, ℂ)) : C(K, ℂ))‖ = ‖f‖
  rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
  apply iSup_congr
  intro t
  rw [modulus_apply, Complex.norm_real, norm_norm]

/-- The equivalence from `selfAdjoint C(K, ℂ)` to `C(K, ℝ)` sends the
lattice-valued modulus to the pointwise complex norm. -/
theorem selfAdjointRealEquiv_modulus_apply
    (f : C(K, ℂ)) (t : K) :
    selfAdjointRealEquiv (ComplexVectorLattice.modulus f) t = ‖f t‖ := by
  change (((ComplexVectorLattice.modulus f : selfAdjoint C(K, ℂ)) : C(K, ℂ)) t).re =
    ‖f t‖
  rw [modulus_apply, Complex.ofReal_re]

/-! ### `C(K, ℂ) ≅ Complexification C(K, ℝ)` -/

/-- The complexification of `C(K, ℝ)` is complex-Banach lattice
isometric to `C(K, ℂ)`. -/
noncomputable def complexificationEquiv :
    ComplexBanachLatEquiv
      (Complexification C(K, ℝ))
      C(K, ℂ) := by
  exact ComplexBanachLatEquiv.ofSelfAdjointBanachLatEquiv
    (Complexification.selfAdjointBanachLatEquiv.trans
      (selfAdjointBanachLatEquiv (K := K)).symm)

/-- If `z = (f, g) ∈ Complexification C(K, ℝ)`, then
`complexificationEquiv z= f + Complex.I * g`. -/
@[simp]
theorem complexificationEquiv_apply_apply
    (z : Complexification C(K, ℝ)) (t : K) :
    complexificationEquiv z t =
      (z.re t : ℂ) + Complex.I * z.im t := by
  rw [complexificationEquiv,
    ComplexBanachLatEquiv.ofSelfAdjointBanachLatEquiv_apply,
    ContinuousMap.add_apply, ContinuousMap.smul_apply]
  have hre :
      (Complexification.selfAdjointBanachLatEquiv.trans
        (selfAdjointBanachLatEquiv (K := K)).symm) (ℜ z) =
        (selfAdjointRealEquiv (K := K)).symm z.re := by
    apply (selfAdjointRealEquiv (K := K)).injective
    change Complexification.selfAdjointEquiv (ℜ z) = z.re
    exact Complexification.selfAdjointEquiv_realPart z
  have him :
      (Complexification.selfAdjointBanachLatEquiv.trans
        (selfAdjointBanachLatEquiv (K := K)).symm) (ℑ z) =
        (selfAdjointRealEquiv (K := K)).symm z.im := by
    apply (selfAdjointRealEquiv (K := K)).injective
    change Complexification.selfAdjointEquiv (ℑ z) = z.im
    exact Complexification.selfAdjointEquiv_imaginaryPart z
  rw [hre, him, selfAdjointRealEquiv_symm_apply_apply,
    selfAdjointRealEquiv_symm_apply_apply]
  simp

/-- If `f ∈ C(K, ℂ)`,
then `Re[complexificationEquiv⁻¹ f] = Re[f]`. -/
@[simp]
theorem complexificationEquiv_symm_re_apply
    (f : C(K, ℂ)) (t : K) :
    (complexificationEquiv.symm f).re t = (f t).re := by
  have h := complexificationEquiv_apply_apply (complexificationEquiv.symm f) t
  have hinv := congrArg (fun g : C(K, ℂ) => g t)
    (complexificationEquiv.apply_symm_apply f)
  have h' : f t =
      ((complexificationEquiv.symm f).re t : ℂ) +
        Complex.I * (complexificationEquiv.symm f).im t := by
    exact hinv.symm.trans h
  have hre := congrArg Complex.re h'
  simpa using hre.symm

/-- If `f ∈ C(K, ℂ)`,
then `Im[complexificationEquiv⁻¹ f] = Im[f]`. -/
@[simp]
theorem complexificationEquiv_symm_im_apply
    (f : C(K, ℂ)) (t : K) :
    (complexificationEquiv.symm f).im t = (f t).im := by
  have h := complexificationEquiv_apply_apply (complexificationEquiv.symm f) t
  have hinv := congrArg (fun g : C(K, ℂ) => g t)
    (complexificationEquiv.apply_symm_apply f)
  have h' : f t =
      ((complexificationEquiv.symm f).re t : ℂ) +
        Complex.I * (complexificationEquiv.symm f).im t := by
    exact hinv.symm.trans h
  have him := congrArg Complex.im h'
  simpa using him.symm

/-! ### Complex AM-space with unit structure -/

/-- The constant-one function is a strong order unit of `selfAdjoint C(K, ℂ)`. -/
private theorem one_strongOrderUnit :
    StrongOrderUnit (1 : selfAdjoint C(K, ℂ)) := by
  change StrongOrderUnit
    ((selfAdjointBanachLatEquiv (K := K)).toLinearIsometryEquiv.symm (1 : C(K, ℝ)))
  let e := selfAdjointBanachLatEquiv (K := K)
  have hone : StrongOrderUnit (1 : C(K, ℝ)) := by
    change StrongOrderUnit (AMSpaceWithUnit.unit : C(K, ℝ))
    exact AMSpaceWithUnit.strongOrderUnit_unit'
  refine ⟨?_, ?_⟩
  · apply (e.toOrderIso.le_iff_le).mpr
    change e.toLinearIsometryEquiv 0 ≤
      e.toLinearIsometryEquiv (e.toLinearIsometryEquiv.symm 1)
    rw [map_zero, e.toLinearIsometryEquiv.apply_symm_apply]
    exact hone.1
  · intro x
    obtain ⟨c, hc, hcx⟩ := hone.2 (e x)
    refine ⟨c, hc, (e.toOrderIso.le_iff_le).mpr ?_⟩
    have habs : e.toLinearIsometryEquiv |x| =
        |e.toLinearIsometryEquiv x| :=
      e.toVecLatEquiv.toVecLatHom.map_abs x
    have hsmul : e.toLinearIsometryEquiv
        (c • e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))) =
        c • (1 : C(K, ℝ)) := by
      rw [map_smul, e.toLinearIsometryEquiv.apply_symm_apply]
    change e.toLinearIsometryEquiv |x| ≤
      e.toLinearIsometryEquiv
        (c • e.toLinearIsometryEquiv.symm (1 : C(K, ℝ)))
    rwa [habs, hsmul]

/-- The gauge norm induced by `1` in `selfAdjoint C(K, ℂ)` is identified
 with the gauge norm induced by `1` in `C(K, ℝ)`. -/
private theorem gaugeNorm_one
    (x : selfAdjoint C(K, ℂ)) :
    OrderIdeal.gaugeNorm (1 : selfAdjoint C(K, ℂ)) x =
      OrderIdeal.gaugeNorm (1 : C(K, ℝ))
        ((selfAdjointBanachLatEquiv (K := K)) x) := by
  let e := selfAdjointBanachLatEquiv (K := K)
  change OrderIdeal.gaugeNorm (e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))) x =
    OrderIdeal.gaugeNorm (1 : C(K, ℝ)) (e x)
  unfold OrderIdeal.gaugeNorm
  apply congrArg sInf
  ext c
  simp only [Set.mem_setOf_eq]
  have habs : e.toLinearIsometryEquiv |x| =
      |e.toLinearIsometryEquiv x| :=
    e.toVecLatEquiv.toVecLatHom.map_abs x
  have hunit : e.toLinearIsometryEquiv
      |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))| = |(1 : C(K, ℝ))| := by
    calc
      e.toLinearIsometryEquiv |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))| =
          |e.toLinearIsometryEquiv
            (e.toLinearIsometryEquiv.symm (1 : C(K, ℝ)))| :=
        e.toVecLatEquiv.toVecLatHom.map_abs _
      _ = |(1 : C(K, ℝ))| := by rw [e.toLinearIsometryEquiv.apply_symm_apply]
  have hsmul : e.toLinearIsometryEquiv
      (c • |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))|) =
      c • |(1 : C(K, ℝ))| := by
    rw [map_smul, hunit]
  constructor
  · rintro ⟨hc, hx⟩
    refine ⟨hc, ?_⟩
    have hx' : e.toLinearIsometryEquiv |x| ≤ e.toLinearIsometryEquiv
        (c • |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))|) :=
      e.toOrderIso.monotone hx
    rwa [habs, hsmul] at hx'
  · rintro ⟨hc, hx⟩
    refine ⟨hc, (e.toOrderIso.le_iff_le).mpr ?_⟩
    change e.toLinearIsometryEquiv |x| ≤ e.toLinearIsometryEquiv
      (c • |e.toLinearIsometryEquiv.symm (1 : C(K, ℝ))|)
    rwa [habs, hsmul]

/-- With the constant-one function, `C(K, ℂ)` is a **complex AM-space with unit.** -/
noncomputable instance instComplexAMSpaceWithUnit :
    ComplexAMSpaceWithUnit C(K, ℂ) where
  norm_add_eq_max_of_inf_eq_zero {x y} hxy := by
    let e := selfAdjointBanachLatEquiv (K := K)
    rw [← e.norm_map (x + y), map_add, ← e.norm_map x, ← e.norm_map y]
    apply AMSpace.norm_add_eq_max_of_inf_eq_zero
    exact e.toVecLatEquiv.toVecLatHom.map_disjoint hxy
  unit := 1
  strongOrderUnit_unit := one_strongOrderUnit
  norm_eq_gaugeNorm x := by
    let e := selfAdjointBanachLatEquiv (K := K)
    calc
      ‖x‖ = ‖e x‖ := (e.norm_map x).symm
      _ = OrderIdeal.gaugeNorm (1 : C(K, ℝ)) (e x) := by
        change ‖e x‖ =
          OrderIdeal.gaugeNorm (AMSpaceWithUnit.unit : C(K, ℝ)) (e x)
        exact AMSpaceWithUnit.norm_eq_gaugeNorm (e x)
      _ = OrderIdeal.gaugeNorm (1 : selfAdjoint C(K, ℂ)) x :=
        (gaugeNorm_one x).symm

/-- The distinguished unit of `C(K, ℂ)` is the constant-one function. -/
@[simp]
theorem complexAMSpaceWithUnit_unit_apply (t : K) :
    ((ComplexAMSpaceWithUnit.unit : selfAdjoint C(K, ℂ)) : C(K, ℂ)) t = 1 := by
  rfl

end ContinuousMap
