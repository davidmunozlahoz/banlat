/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.ComplexBanachLattice.Modulus.Basic
import BanLat.Examples.CofK.FunctionalCalculus

/-!
# Complex modulus and functional calculus

In a uniformly complete vector lattice, the complex modulus can be defined by
applying the functional calculus to the map `(x, y) ↦ √(x²+y²)`.

This file proves that this construction agrees with the complex modulus and uses
it to show that vector lattice homomorphisms between uniformly complete vector
lattices preserve the complex modulus.
-/

/-- The Euclidean norm as a positively homogeneous function on two coordinates. -/
private noncomputable def euclideanNorm : posHomFunctions 2 :=
  ⟨⟨fun r => Real.sqrt (r 0 ^ 2 + r 1 ^ 2),
      Real.continuous_sqrt.comp
        (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2))⟩, by
    intro c hc r
    change Real.sqrt ((c * r 0) ^ 2 + (c * r 1) ^ 2) =
      c * Real.sqrt (r 0 ^ 2 + r 1 ^ 2)
    rw [show (c * r 0) ^ 2 + (c * r 1) ^ 2 =
        c ^ 2 * (r 0 ^ 2 + r 1 ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]⟩

/-- The complex modulus agrees with the functional calculus of the Euclidean norm. -/
private theorem complexModulus_eq_functionalCalculus
    {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [VectorLattice E] [IsUniformlyCompleteVectorLattice E] (x y : E) :
    VectorLattice.complexModulus x y =
      PosHomFunction.functionalCalculus ![x, y] euclideanNorm := by
  let e := |x| + |y|
  have he : 0 ≤ e := add_nonneg (abs_nonneg x) (abs_nonneg y)
  by_cases hzero : e = 0
  · have hmod : VectorLattice.complexModulus x y = 0 :=
      le_antisymm
        ((VectorLattice.complexModulus_le_abs_add_abs x y).trans hzero.le)
        (VectorLattice.complexModulus_nonneg x y)
    obtain ⟨rfl, rfl⟩ :=
      (VectorLattice.complexModulus_eq_zero_iff x y).mp hmod
    rw [VectorLattice.complexModulus_zero_right, abs_zero]
    have htuple : ![(0 : E), 0] = (fun _ : Fin 2 => 0) := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, PosHomFunction.functionalCalculus_zero]
  · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hzero)
    letI : NormedAddCommGroup ↥(OrderIdeal.principal e) :=
      OrderIdeal.principalNormedAddCommGroup e
    letI : Lattice ↥(OrderIdeal.principal e) := OrderIdeal.instLatticePrincipal e
    letI : IsOrderedAddMonoid ↥(OrderIdeal.principal e) :=
      OrderIdeal.instIsOrderedAddMonoidPrincipal e
    letI : AMSpaceWithUnit ↥(OrderIdeal.principal e) :=
      OrderIdeal.principalAMSpaceWithUnit he
        (IsUniformlyCompleteVectorLattice.complete_principal e hepos)
    have hx : x ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he]
      exact le_add_of_nonneg_right (abs_nonneg y)
    have hy : y ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he]
      exact le_add_of_nonneg_left (abs_nonneg x)
    let x' : ↥(OrderIdeal.principal e) := ⟨x, hx⟩
    let y' : ↥(OrderIdeal.principal e) := ⟨y, hy⟩
    have hm : VectorLattice.complexModulus x y ∈ OrderIdeal.principal e := by
      rw [OrderIdeal.mem_principal]
      refine ⟨1, zero_le_one, ?_⟩
      rw [one_smul, abs_of_nonneg he,
        abs_of_nonneg (VectorLattice.complexModulus_nonneg x y)]
      exact VectorLattice.complexModulus_le_abs_add_abs x y
    let m : ↥(OrderIdeal.principal e) :=
      ⟨VectorLattice.complexModulus x y, hm⟩
    letI := isUniformlyCompleteVectorLattice_of_banachLattice
      ↥(OrderIdeal.principal e)
    have hm_eq : VectorLattice.complexModulus x' y' = m := by
      apply (VectorLattice.complexModulus_isLUB x' y').unique
      constructor
      · rintro _ ⟨θ, rfl⟩
        exact (VectorLattice.complexModulus_isLUB x y).1 ⟨θ, rfl⟩
      · intro u hu
        change VectorLattice.complexModulus x y ≤ u.1
        apply (VectorLattice.complexModulus_isLUB x y).2
        rintro _ ⟨θ, rfl⟩
        exact hu ⟨θ, rfl⟩
    let K := OrderIdeal.principalKakutaniEquiv hepos
    letI := isUniformlyCompleteVectorLattice_of_banachLattice
      C(AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principal e), ℝ)
    have hprincipal :
        VectorLattice.complexModulus x' y' =
          PosHomFunction.functionalCalculus ![x', y'] euclideanNorm := by
      apply K.injective
      calc
        K (VectorLattice.complexModulus x' y') =
            VectorLattice.complexModulus (K x') (K y') :=
          K.toVecLatEquiv.map_complexModulus x' y'
        _ = PosHomFunction.functionalCalculus ![K x', K y'] euclideanNorm := by
          ext t
          rw [VectorLattice.complexModulus_apply,
            PosHomFunction.functionalCalculus_continuousMap_apply]
          rfl
        _ = K (PosHomFunction.functionalCalculus ![x', y'] euclideanNorm) := by
          have htuple :
              (fun i => K.toVecLatEquiv.toVecLatHom (![x', y'] i)) =
                ![K x', K y'] := by
            funext i
            fin_cases i <;> rfl
          rw [← htuple]
          exact (PosHomFunction.functionalCalculus_map
            K.toVecLatEquiv.toVecLatHom ![x', y'] euclideanNorm).symm
    calc
      VectorLattice.complexModulus x y = (m : E) := rfl
      _ = ((VectorLattice.complexModulus x' y' :
          ↥(OrderIdeal.principal e)) : E) := congrArg Subtype.val hm_eq.symm
      _ = ((PosHomFunction.functionalCalculus ![x', y'] euclideanNorm :
          ↥(OrderIdeal.principal e)) : E) := congrArg Subtype.val hprincipal
      _ = PosHomFunction.functionalCalculus ![x, y] euclideanNorm := by
        have htuple :
            (fun i => (OrderIdeal.principal e).subtype (![x', y'] i)) =
              ![x, y] := by
          funext i
          fin_cases i <;> rfl
        rw [← htuple]
        exact PosHomFunction.functionalCalculus_map
          (OrderIdeal.principal e).subtype ![x', y'] euclideanNorm

namespace VecLatHom

variable {E F : Type*}
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [IsUniformlyCompleteVectorLattice E]
  [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F]
  [VectorLattice F] [IsUniformlyCompleteVectorLattice F]

/-- A vector lattice homomorphism between uniformly complete
vector lattices preserves the complex modulus. -/
@[simp]
theorem map_complexModulus (T : VecLatHom E F) (x y : E) :
    T (VectorLattice.complexModulus x y) =
      VectorLattice.complexModulus (T x) (T y) := by
  rw [complexModulus_eq_functionalCalculus]
  calc
    T (PosHomFunction.functionalCalculus ![x, y] euclideanNorm) =
        PosHomFunction.functionalCalculus (fun i => T (![x, y] i))
          euclideanNorm :=
      PosHomFunction.functionalCalculus_map T ![x, y] euclideanNorm
    _ = PosHomFunction.functionalCalculus ![T x, T y] euclideanNorm := by
      congr 2
      funext i
      fin_cases i <;> rfl
    _ = VectorLattice.complexModulus (T x) (T y) :=
      (complexModulus_eq_functionalCalculus (T x) (T y)).symm

end VecLatHom
