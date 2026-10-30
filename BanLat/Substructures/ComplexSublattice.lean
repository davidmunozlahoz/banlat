/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Hom
import BanLat.Substructures.Sublattice

/-!
# Sublattices of complex vector lattices

This file develops complex vector sublattices, which are complex linear subspaces closed under
conjugation and the lattice-valued modulus, together with their induced structures and generated
sublattices.
-/

open scoped ComplexStarModule

/-- A complex vector sublattice is a complex submodule closed under conjugation
and the lattice-valued modulus. -/
structure ComplexVectorSublattice (Z : Type*)
    [AddCommGroup Z] [Module ℂ Z]
    [StarAddMonoid Z] [StarModule ℂ Z]
    [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
    [ComplexVectorLattice Z] extends Submodule ℂ Z where
  star_mem' : ∀ {z : Z}, z ∈ carrier → star z ∈ carrier
  modulus_mem' : ∀ {z : Z}, z ∈ carrier →
    (|z|_ℂ : Z) ∈ carrier

namespace ComplexVectorSublattice

variable {Z : Type*}
  [AddCommGroup Z] [Module ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexVectorLattice Z]

/-! ### Membership and algebraic structures -/

/-- The underlying set of a complex vector sublattice. -/
instance instSetLike : SetLike (ComplexVectorSublattice Z) Z := by
  exact
    { coe := fun W ↦ W.carrier
      coe_injective := fun W V h ↦ by
        cases W
        cases V
        congr
        exact SetLike.ext' h }

/-- Two complex vector sublattices are equal if they have the same elements. -/
@[ext]
theorem ext {W V : ComplexVectorSublattice Z}
    (h : ∀ z, z ∈ W ↔ z ∈ V) : W = V := by
  exact SetLike.ext h

/-- Complex vector sublattices are additive subgroups of their ambient space. -/
instance instAddSubgroupClass :
    AddSubgroupClass (ComplexVectorSublattice Z) Z := by
  exact
    { zero_mem := fun W ↦ W.toSubmodule.zero_mem
      add_mem := fun {W _ _} hx hy ↦ W.toSubmodule.add_mem hx hy
      neg_mem := fun {W _} hx ↦ W.toSubmodule.neg_mem hx }

/-- Complex vector sublattices are closed under complex scalar multiplication. -/
instance instSMulMemClass :
    SMulMemClass (ComplexVectorSublattice Z) ℂ Z := by
  exact { smul_mem := fun {W} c _ hz ↦ W.toSubmodule.smul_mem c hz }

/-- The underlying submodule has the same carrier as the complex vector sublattice. -/
@[simp]
theorem coe_toSubmodule (W : ComplexVectorSublattice Z) :
    (W.toSubmodule : Set Z) = (W : Set Z) := by
  rfl

/-- The underlying submodule determines a complex vector sublattice. -/
theorem toSubmodule_injective :
    Function.Injective
      (toSubmodule : ComplexVectorSublattice Z → Submodule ℂ Z) := by
  exact fun W V h ↦ ext (fun z ↦
    show z ∈ W.toSubmodule ↔ z ∈ V.toSubmodule from h ▸ Iff.rfl)

variable (W : ComplexVectorSublattice Z)

/-- A complex vector sublattice is closed under conjugation. -/
theorem star_mem {z : Z} (hz : z ∈ W) : star z ∈ W := by
  exact W.star_mem' hz

/-- A complex vector sublattice contains the modulus of each of its elements. -/
theorem modulus_mem {z : Z} (hz : z ∈ W) :
    (|z|_ℂ : Z) ∈ W := by
  exact W.modulus_mem' hz

/-- A complex vector sublattice contains the real part of each of its elements. -/
theorem realPart_mem {z : Z} (hz : z ∈ W) : (ℜ z : Z) ∈ W := by
  rw [realPart_apply_coe]
  exact (W.toSubmodule.restrictScalars ℝ).smul_mem _
    (W.toSubmodule.add_mem hz (W.star_mem hz))

/-- A complex vector sublattice contains the imaginary part of each of its elements. -/
theorem imaginaryPart_mem {z : Z} (hz : z ∈ W) : (ℑ z : Z) ∈ W := by
  rw [imaginaryPart_apply_coe]
  exact W.toSubmodule.smul_mem (-Complex.I)
    ((W.toSubmodule.restrictScalars ℝ).smul_mem (2 : ℝ)⁻¹
      (W.toSubmodule.sub_mem hz (W.star_mem hz)))

/-! ### The self-adjoint sublattice -/

/-- The self-adjoint elements of a complex vector sublattice form a real vector sublattice. -/
noncomputable def selfAdjointSublattice (W : ComplexVectorSublattice Z) :
    VectorSublattice (selfAdjoint Z) := by
  refine VectorSublattice.ofAbsClosed
    { carrier := {x : selfAdjoint Z | (x : Z) ∈ W}
      zero_mem' := W.toSubmodule.zero_mem
      add_mem' := fun hx hy ↦ W.toSubmodule.add_mem hx hy
      smul_mem' := ?_ } ?_
  · exact fun c x hx ↦ by
      change ((@SMul.smul ℝ (selfAdjoint Z)
        (ComplexVectorLattice.toVectorLattice (Z := Z)).toModule.toSMul c x) : Z) ∈ W
      exact (ComplexVectorLattice.coe_smul (Z := Z) c x).symm ▸
        (W.toSubmodule.restrictScalars ℝ).smul_mem c hx
  · exact fun x hx ↦ by
      have h := W.modulus_mem hx
      change ((|x| : selfAdjoint Z) : Z) ∈ W
      simpa only [ComplexVectorLattice.modulus_coe] using h

/-- Membership in the self-adjoint sublattice is membership after ambient coercion. -/
@[simp]
theorem mem_selfAdjointSublattice (x : selfAdjoint Z) :
    x ∈ W.selfAdjointSublattice ↔ (x : Z) ∈ W := by
  rfl

/-! ### Structures on the underlying subtype -/

/-- Conjugation restricts to an additive involution on a complex vector sublattice. -/
noncomputable instance instStarAddMonoidCoe : StarAddMonoid W := by
  exact
    { star := fun z ↦ ⟨star (z : Z), W.star_mem z.property⟩
      star_involutive := fun z ↦ Subtype.ext (star_star (z : Z))
      star_add := fun z w ↦ Subtype.ext (star_add (z : Z) (w : Z)) }

/-- Conjugation on a complex vector sublattice respects complex scalar multiplication. -/
instance instStarModuleCoe : StarModule ℂ W := by
  exact { star_smul := fun c z ↦ Subtype.ext (star_smul c (z : Z)) }

/-- Conjugation in a complex vector sublattice agrees with ambient conjugation. -/
@[simp, norm_cast]
theorem coe_star (z : W) : ((star z : W) : Z) = star (z : Z) := by
  rfl

/-- The self-adjoint part of the subtype identifies with the real self-adjoint sublattice. -/
noncomputable def selfAdjointEquiv :
    selfAdjoint W ≃ₗ[ℝ] ↥(W.selfAdjointSublattice) := by
  refine
    { toFun := fun x ↦ ⟨⟨((x : W) : Z), congrArg Subtype.val x.property⟩,
        (x : W).property⟩
      invFun := fun x ↦ ⟨⟨((x : selfAdjoint Z) : Z), x.property⟩,
        Subtype.ext (x : selfAdjoint Z).property⟩
      left_inv := fun x ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun x ↦ Subtype.ext (Subtype.ext rfl)
      map_add' := fun _ _ ↦ rfl
      map_smul' := ?_ }
  exact fun c x ↦ Subtype.ext (Subtype.ext
    (ComplexVectorLattice.coe_smul c
      ⟨((x : W) : Z), congrArg Subtype.val x.property⟩).symm)

/-- The self-adjoint identification preserves the underlying ambient element. -/
@[simp]
theorem coe_selfAdjointEquiv (x : selfAdjoint W) :
    ((W.selfAdjointEquiv x : selfAdjoint Z) : Z) = ((x : W) : Z) := by
  rfl

/-- The self-adjoint part inherits the lattice operations of the ambient space. -/
noncomputable instance instLatticeSelfAdjointCoe : Lattice (selfAdjoint W) := by
  exact W.selfAdjointEquiv.toEquiv.lattice

/-- The inherited order on self-adjoint elements respects addition. -/
instance instIsOrderedAddMonoidSelfAdjointCoe :
    IsOrderedAddMonoid (selfAdjoint W) := by
  exact Function.Injective.isOrderedAddMonoid W.selfAdjointEquiv
    W.selfAdjointEquiv.map_add Iff.rfl

/-- The self-adjoint identification preserves suprema. -/
@[simp]
theorem selfAdjointEquiv_sup (x y : selfAdjoint W) :
    W.selfAdjointEquiv (x ⊔ y) =
      W.selfAdjointEquiv x ⊔ W.selfAdjointEquiv y := by
  exact W.selfAdjointEquiv.apply_symm_apply _

/-- The self-adjoint identification preserves infima. -/
@[simp]
theorem selfAdjointEquiv_inf (x y : selfAdjoint W) :
    W.selfAdjointEquiv (x ⊓ y) =
      W.selfAdjointEquiv x ⊓ W.selfAdjointEquiv y := by
  exact W.selfAdjointEquiv.apply_symm_apply _

private theorem isLUB_rotationRange_selfAdjointSublattice
    (x y u : ↥(W.selfAdjointSublattice))
    (h : IsLUB (VectorLattice.rotationRange (x : selfAdjoint Z) (y : selfAdjoint Z))
      (u : selfAdjoint Z)) : IsLUB (VectorLattice.rotationRange x y) u := by
  constructor
  · rintro _ ⟨θ, rfl⟩
    exact h.1 ⟨θ, rfl⟩
  · exact fun v hv ↦ h.2 (by
      rintro _ ⟨θ, rfl⟩
      exact hv ⟨θ, rfl⟩)

private theorem exists_isLUB_rotationRange_selfAdjointSublattice
    (x y : ↥(W.selfAdjointSublattice)) :
    ∃ u, IsLUB (VectorLattice.rotationRange x y) u := by
  let z : Z := ((x : selfAdjoint Z) : Z) +
    Complex.I • ((y : selfAdjoint Z) : Z)
  have hz : z ∈ W := W.toSubmodule.add_mem x.property
    (W.toSubmodule.smul_mem Complex.I y.property)
  let m : ↥(W.selfAdjointSublattice) :=
    ⟨ComplexVectorLattice.modulus z, W.modulus_mem hz⟩
  have hm : IsLUB
      (VectorLattice.rotationRange (x : selfAdjoint Z) (y : selfAdjoint Z))
      (ComplexVectorLattice.modulus z) := by
    simpa only [z, map_add, realPart_I_smul, imaginaryPart_I_smul,
      selfAdjoint.realPart_coe, selfAdjoint.imaginaryPart_coe,
      neg_zero, add_zero, zero_add] using ComplexVectorLattice.modulus_isLUB z
  exact ⟨m, isLUB_rotationRange_selfAdjointSublattice W x y m hm⟩

/-- A complex vector sublattice inherits the ambient complex vector lattice structure. -/
noncomputable instance instComplexVectorLatticeCoe : ComplexVectorLattice W := by
  letI : VectorLattice (selfAdjoint W) :=
    { smul_le_smul_of_nonneg_left := fun c hc x y h ↦ by
        change W.selfAdjointEquiv (c • x) ≤ W.selfAdjointEquiv (c • y)
        simpa only [map_smul] using
          smul_le_smul_of_nonneg_left
            (show W.selfAdjointEquiv x ≤ W.selfAdjointEquiv y from h) hc }
  refine { coe_smul := fun _ _ ↦ rfl, exists_isLUB_rotationRange := ?_ }
  intro x y
  let e : selfAdjoint W ≃o ↥(W.selfAdjointSublattice) :=
    { W.selfAdjointEquiv.toEquiv with map_rel_iff' := Iff.rfl }
  obtain ⟨u, hu⟩ := exists_isLUB_rotationRange_selfAdjointSublattice W (e x) (e y)
  change IsLUB (VectorLattice.rotationRange
    (W.selfAdjointEquiv x) (W.selfAdjointEquiv y)) u at hu
  refine ⟨e.symm u, e.isLUB_image.mp ?_⟩
  change IsLUB (W.selfAdjointEquiv '' VectorLattice.rotationRange x y) u
  simpa only [VectorLattice.rotationRange, ← Set.range_comp, Function.comp_def,
    map_add, map_smul] using hu

/-- The modulus in a complex vector sublattice agrees with the ambient modulus. -/
@[simp, norm_cast]
theorem coe_modulus (z : W) :
    ((|z|_ℂ : W) : Z) = (|(z : Z)|_ℂ : Z) := by
  let m : ↥(W.selfAdjointSublattice) :=
    ⟨ComplexVectorLattice.modulus (z : Z), W.modulus_mem z.property⟩
  have h := ComplexVectorLattice.modulus_isLUB (z : Z)
  change IsLUB (VectorLattice.rotationRange
    (W.selfAdjointEquiv (ℜ z) : selfAdjoint Z)
    (W.selfAdjointEquiv (ℑ z) : selfAdjoint Z)) (m : selfAdjoint Z) at h
  have hsub := isLUB_rotationRange_selfAdjointSublattice W
    (W.selfAdjointEquiv (ℜ z)) (W.selfAdjointEquiv (ℑ z)) m h
  let e : selfAdjoint W ≃o ↥(W.selfAdjointSublattice) :=
    { W.selfAdjointEquiv.toEquiv with map_rel_iff' := Iff.rfl }
  have hm : IsLUB (VectorLattice.rotationRange (ℜ z) (ℑ z)) (e.symm m) := by
    apply e.isLUB_image.mp
    change IsLUB (W.selfAdjointEquiv '' VectorLattice.rotationRange (ℜ z) (ℑ z)) m
    simpa only [VectorLattice.rotationRange, ← Set.range_comp, Function.comp_def,
      map_add, map_smul] using hsub
  have heq := ComplexVectorLattice.modulus_eq_of_isLUB hm
  exact congrArg (fun x : selfAdjoint W ↦ ((x : W) : Z)) heq

/-- The self-adjoint part of a complex vector sublattice is vector lattice
isomorphic to its real self-adjoint sublattice. -/
noncomputable def selfAdjointVecLatEquiv (W : ComplexVectorSublattice Z) :
    VecLatEquiv (selfAdjoint W) ↥(W.selfAdjointSublattice) := by
  exact
    { toLinearEquiv := W.selfAdjointEquiv
      map_sup' := W.selfAdjointEquiv_sup
      map_inf' := W.selfAdjointEquiv_inf }

/-- The bundled vector lattice equivalence agrees with the linear equivalence. -/
@[simp]
theorem selfAdjointVecLatEquiv_apply (W : ComplexVectorSublattice Z)
    (x : selfAdjoint W) :
    W.selfAdjointVecLatEquiv x = W.selfAdjointEquiv x := by
  rfl

/-! ### Inclusion homomorphisms -/

/-- The inclusion of a complex vector sublattice is a complex vector lattice homomorphism. -/
noncomputable def subtype : ComplexVecLatHom W Z := by
  exact
    { toLinearMap := W.toSubmodule.subtype
      map_modulus' := W.coe_modulus }

/-- The inclusion homomorphism acts by subtype coercion. -/
@[simp]
theorem subtype_apply (z : W) : W.subtype z = (z : Z) := by
  rfl

/-- Complex vector sublattices are ordered by inclusion. -/
instance instPartialOrder : PartialOrder (ComplexVectorSublattice Z) := by
  exact .ofSetLike (ComplexVectorSublattice Z) Z

/-- An inclusion between complex vector sublattices is a complex lattice homomorphism. -/
noncomputable def inclusion {W V : ComplexVectorSublattice Z} (h : W ≤ V) :
    ComplexVecLatHom W V := by
  let L : W →ₗ[ℂ] V :=
    { toFun := Set.inclusion h
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact
    { toLinearMap := L
      map_modulus' := fun z ↦ Subtype.ext
        ((W.coe_modulus z).trans (V.coe_modulus (L z)).symm) }

/-- Inclusion between complex vector sublattices preserves the ambient element. -/
@[simp]
theorem inclusion_apply {W V : ComplexVectorSublattice Z} (h : W ≤ V) (z : W) :
    ((inclusion h z : V) : Z) = (z : Z) := by
  rfl

/-! ### Pullbacks of complex vector sublattices -/

section Comap

variable {Y : Type*}
  [AddCommGroup Y] [Module ℂ Y]
  [StarAddMonoid Y] [StarModule ℂ Y]
  [Lattice (selfAdjoint Y)] [IsOrderedAddMonoid (selfAdjoint Y)]
  [ComplexVectorLattice Y]

/-- The preimage of a complex vector sublattice under a complex lattice
homomorphism is a complex vector sublattice. -/
def comap (T : ComplexVecLatHom Z Y) (V : ComplexVectorSublattice Y) :
    ComplexVectorSublattice Z := by
  exact
    { toSubmodule := V.toSubmodule.comap T.toLinearMap
      star_mem' := fun {z} hz ↦ show T (star z) ∈ V from
        (T.map_star z).symm ▸ V.star_mem hz
      modulus_mem' := fun {z} hz ↦
        show T ((ComplexVectorLattice.modulus z : selfAdjoint Z) : Z) ∈ V from
          (T.map_modulus z).symm ▸ V.modulus_mem hz }

/-- Membership in a pulled-back sublattice is membership of the image. -/
@[simp]
theorem mem_comap (T : ComplexVecLatHom Z Y)
    (V : ComplexVectorSublattice Y) (z : Z) :
    z ∈ comap T V ↔ T z ∈ V := by
  rfl

end Comap

/-! ### Intersections and generated sublattices -/

/-- The whole ambient space is a complex vector sublattice. -/
instance instTop : Top (ComplexVectorSublattice Z) := by
  exact
    { top :=
        { toSubmodule := ⊤
          star_mem' := fun _ ↦ Submodule.mem_top
          modulus_mem' := fun _ ↦ Submodule.mem_top } }

/-- Every ambient element belongs to the whole complex vector sublattice. -/
@[simp]
theorem mem_top (z : Z) : z ∈ (⊤ : ComplexVectorSublattice Z) := by
  exact Submodule.mem_top

/-- Arbitrary intersections of complex vector sublattices are complex vector sublattices. -/
instance instInfSet : InfSet (ComplexVectorSublattice Z) := by
  exact
    { sInf := fun S ↦
        { toSubmodule := sInf (toSubmodule '' S)
          star_mem' := fun hz ↦ Submodule.mem_sInf.mpr (by
            rintro _ ⟨V, hV, rfl⟩
            exact V.star_mem (Submodule.mem_sInf.mp hz _ ⟨V, hV, rfl⟩))
          modulus_mem' := fun hz ↦ Submodule.mem_sInf.mpr (by
            rintro _ ⟨V, hV, rfl⟩
            exact V.modulus_mem (Submodule.mem_sInf.mp hz _ ⟨V, hV, rfl⟩)) } }

/-- Membership in an intersection means membership in each constituent sublattice. -/
@[simp]
theorem mem_sInf (S : Set (ComplexVectorSublattice Z)) (z : Z) :
    z ∈ sInf S ↔ ∀ W ∈ S, z ∈ W := by
  exact
    ⟨fun hz V hV ↦ Submodule.mem_sInf.mp hz _ ⟨V, hV, rfl⟩,
      fun hz ↦ Submodule.mem_sInf.mpr (by
        rintro _ ⟨V, hV, rfl⟩
        exact hz V hV)⟩

/-- The complex vector sublattice generated by a set is the intersection of all
complex vector sublattices containing that set. -/
noncomputable def generated (s : Set Z) : ComplexVectorSublattice Z := by
  exact sInf {W : ComplexVectorSublattice Z | s ⊆ W}

/-- A set is contained in the complex vector sublattice it generates. -/
theorem subset_generated (s : Set Z) : s ⊆ (generated s : Set Z) := by
  exact fun z hz ↦ (mem_sInf _ z).mpr (fun V hV ↦ hV hz)

/-- The generated complex vector sublattice lies in every sublattice containing its generators. -/
theorem generated_le {s : Set Z} {W : ComplexVectorSublattice Z} (h : s ⊆ W) :
    generated s ≤ W := by
  exact fun z hz ↦ (mem_sInf _ z).mp hz W h

/-- Containment of a generated complex vector sublattice is determined by its generators. -/
theorem generated_le_iff {s : Set Z} {W : ComplexVectorSublattice Z} :
    generated s ≤ W ↔ s ⊆ W := by
  exact ⟨fun h ↦ (subset_generated s).trans h, generated_le⟩

private theorem mem_of_mem_generators {s : Set Z}
    (W : ComplexVectorSublattice ↥(generated s))
    (hW : ∀ z (hz : z ∈ s), (⟨z, subset_generated s hz⟩ : generated s) ∈ W) :
    ∀ z : generated s, z ∈ W := by
  let V : ComplexVectorSublattice Z :=
    { toSubmodule := W.toSubmodule.map (generated s).subtype.toLinearMap
      star_mem' := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨star z, W.star_mem hz, (generated s).coe_star z⟩
      modulus_mem' := by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨((ComplexVectorLattice.modulus z : selfAdjoint (generated s)) :
          generated s), W.modulus_mem hz, (generated s).coe_modulus z⟩ }
  have hV : generated s ≤ V := generated_le (fun z hz ↦
    ⟨⟨z, subset_generated s hz⟩, hW z hz, rfl⟩)
  intro z
  obtain ⟨w, hw, heq⟩ := hV z.property
  exact (Subtype.ext heq) ▸ hw

end ComplexVectorSublattice

namespace ComplexVecLatHom

variable {Z Y : Type*}
  [AddCommGroup Z] [Module ℂ Z]
  [StarAddMonoid Z] [StarModule ℂ Z]
  [Lattice (selfAdjoint Z)] [IsOrderedAddMonoid (selfAdjoint Z)]
  [ComplexVectorLattice Z]
  [AddCommGroup Y] [Module ℂ Y]
  [StarAddMonoid Y] [StarModule ℂ Y]
  [Lattice (selfAdjoint Y)] [IsOrderedAddMonoid (selfAdjoint Y)]
  [ComplexVectorLattice Y]

/-- Complex lattice homomorphisms from a generated sublattice are equal
if they agree on its generators. -/
theorem ext_generated {s : Set Z}
    {T U : ComplexVecLatHom ↥(ComplexVectorSublattice.generated s) Y}
    (h : ∀ z (hz : z ∈ s),
      T ⟨z, ComplexVectorSublattice.subset_generated s hz⟩ =
        U ⟨z, ComplexVectorSublattice.subset_generated s hz⟩) : T = U := by
  let V : ComplexVectorSublattice ↥(ComplexVectorSublattice.generated s) :=
    { toSubmodule := LinearMap.eqLocus T.toLinearMap U.toLinearMap
      star_mem' := fun {z} hz ↦ by
        change T z = U z at hz
        change T (star z) = U (star z)
        rw [map_star, map_star, hz]
      modulus_mem' := fun {z} hz ↦ by
        change T z = U z at hz
        change T _ = U _
        rw [map_modulus, map_modulus, hz] }
  exact ext (ComplexVectorSublattice.mem_of_mem_generators V h)

end ComplexVecLatHom
