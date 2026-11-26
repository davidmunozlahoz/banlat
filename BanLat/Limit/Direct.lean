/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Operators.Hom
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Direct limits of vector lattices

The direct limit (as vector) of a directed system of vector lattices can be equipped with a
vector lattice structure in such a way that it satisfies
the universal property for vector lattice homomorphisms. If the vector lattices are Archimedean
and the connecting homomorphisms are injective, then their direct limit is also Archimedean.
-/

universe u

namespace VectorLattice

section DirectedUnions

variable {D : Type u} [Preorder D] [IsDirectedOrder D]
  {G : D → Type u} [∀ i, AddCommGroup (G i)] [∀ i, Lattice (G i)]
  [∀ i, IsOrderedAddMonoid (G i)] [∀ i, VectorLattice (G i)]
  (f : ∀ i j, i ≤ j → VecLatHom (G i) (G j)) [DirectedSystem G (f · · ·)]

/-- The supremum operation induced on the direct limit. -/
private noncomputable instance directLimitMax : Max (DirectLimit G f) :=
  ⟨DirectLimit.map₂ f f f (fun _ ↦ (· ⊔ ·)) (fun _ _ _ ↦ map_sup _)⟩

/-- The infimum operation induced on the direct limit. -/
private noncomputable instance directLimitMin : Min (DirectLimit G f) :=
  ⟨DirectLimit.map₂ f f f (fun _ ↦ (· ⊓ ·)) (fun _ _ _ ↦ map_inf _)⟩

/-- The canonical map into the direct limit preserves binary suprema. -/
private lemma directLimit_sup (i : D) (x y : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) ⊔ ⟦⟨i, y⟩⟧ = ⟦⟨i, x ⊔ y⟩⟧ :=
  DirectLimit.map₂_def ..

/-- The canonical map into the direct limit preserves binary infima. -/
private lemma directLimit_inf (i : D) (x y : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) ⊓ ⟦⟨i, y⟩⟧ = ⟦⟨i, x ⊓ y⟩⟧ :=
  DirectLimit.map₂_def ..

/-- The lattice structure induced on the direct limit. -/
private noncomputable instance directLimitLattice : Lattice (DirectLimit G f) :=
  Lattice.mk'
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_sup, sup_comm]))
    (DirectLimit.induction₃ f (fun _ _ _ _ ↦ by simp only [directLimit_sup, sup_assoc]))
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_inf, inf_comm]))
    (DirectLimit.induction₃ f (fun _ _ _ _ ↦ by simp only [directLimit_inf, inf_assoc]))
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_sup, directLimit_inf,
      sup_inf_self]))
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_sup, directLimit_inf,
      inf_sup_self]))

variable [Nonempty D]

/-- Addition is compatible with the order induced on the direct limit. -/
private noncomputable instance directLimitOrderedAddMonoid :
    IsOrderedAddMonoid (DirectLimit G f) where
  add_le_add_left a b hab c := by
    have h (a b c : DirectLimit G f) : (a + c) ⊔ (b + c) = (a ⊔ b) + c := by
      induction a, b, c using DirectLimit.induction₃ f with
      | ih i a b c => simp only [DirectLimit.add_def, directLimit_sup, sup_add]
    exact sup_eq_right.mp ((h a b c).trans (congrArg (· + c) (sup_eq_right.mpr hab)))

/-- The real vector lattice structure on the direct limit. -/
noncomputable instance directLimitVectorLattice : VectorLattice (DirectLimit G f) where
  smul_le_smul_of_nonneg_left := by
    intro r hr a b hab
    have h (a b : DirectLimit G f) : (r • a) ⊔ (r • b) = r • (a ⊔ b) := by
      induction a, b using DirectLimit.induction₂ f with
      | ih i a b => simp only [DirectLimit.smul_def, directLimit_sup, nonneg_smul_sup a b r hr]
    exact sup_eq_right.mp ((h a b).trans (congrArg (r • ·) (sup_eq_right.mpr hab)))

/-- The canonical vector lattice homomorphism from `G i` into the direct limit. -/
noncomputable def directLimitInclusion (i : D) : VecLatHom (G i) (DirectLimit G f) :=
  { DirectLimit.Module.of ℝ D G f i with
    map_sup' := fun x y ↦ (directLimit_sup f i x y).symm
    map_inf' := fun x y ↦ (directLimit_inf f i x y).symm }

/-- The direct limit of a directed system of Archimedean vector lattices with injective
connecting homomorphisms is Archimedean. -/
lemma directLimit_archimedean [∀ i, IsVLArchimedean (G i)]
    (hf : ∀ i j h, Function.Injective (f i j h)) : IsVLArchimedean (DirectLimit G f) := by
  constructor
  intro z w
  induction z, w using DirectLimit.induction₂ f with
  | ih i x y =>
    intro h
    have hi : Function.Injective (directLimitInclusion f i) := DirectLimit.mk_injective f hf i
    have hx : x ≤ 0 := IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦
      (directLimitInclusion f i).le_of_map_le hi
        (by rw [map_nsmul]; exact h n))
    have hxi := (directLimitInclusion f i).monotone hx
    rw [map_zero] at hxi
    exact hxi

/-- The vector lattice homomorphism on the direct limit induced by a compatible family
of vector lattice homomorphisms. -/
noncomputable def directLimitLift {Y : Type u} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (g : ∀ i, VecLatHom (G i) Y)
    (hg : ∀ i j h x, g j (f i j h x) = g i x) : VecLatHom (DirectLimit G f) Y :=
  { DirectLimit.Module.lift ℝ D G f (fun i ↦ (g i).toLinearMap) hg with
    map_sup' := DirectLimit.induction₂ f (fun i x y ↦ by
      rw [directLimit_sup]
      exact map_sup (g i) x y)
    map_inf' := DirectLimit.induction₂ f (fun i x y ↦ by
      rw [directLimit_inf]
      exact map_inf (g i) x y) }

/-- Composing the induced vector lattice homomorphism with the canonical map from `G i`
recovers `g i`. -/
@[simp]
lemma directLimitLift_inclusion {Y : Type u} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (g : ∀ i, VecLatHom (G i) Y)
    (hg : ∀ i j h x, g j (f i j h x) = g i x) (i : D) (x : G i) :
    directLimitLift f g hg (directLimitInclusion f i x) = g i x := rfl

/-- A vector lattice homomorphism on the direct limit is uniquely determined by its
compositions with the canonical maps. -/
@[ext]
lemma directLimit_hom_ext {Y : Type*} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    {g₁ g₂ : VecLatHom (DirectLimit G f) Y}
    (h : ∀ i x, g₁ (directLimitInclusion f i x) = g₂ (directLimitInclusion f i x)) :
    g₁ = g₂ := by
  exact DFunLike.ext _ _ fun x ↦ LinearMap.congr_fun
    (DirectLimit.Module.hom_ext (g₁ := g₁.toLinearMap) (g₂ := g₂.toLinearMap)
      (fun i ↦ LinearMap.ext (h i))) x

end DirectedUnions

end VectorLattice
