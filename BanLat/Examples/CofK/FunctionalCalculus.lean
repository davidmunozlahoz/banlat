/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.Examples.CofK.Basic
import BanLat.FunctionalCalculus

/-!
# Functional calculus in `C(K, ℝ)`

For a compact topological space `K`, the Banach lattice `C(K, ℝ)` is uniformly
complete, and its positively homogeneous functional calculus is computed
pointwise.
-/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- `C(K, ℝ)` is uniformly complete, being a Banach lattice. -/
instance instIsUniformlyCompleteVectorLatticeCofK :
    IsUniformlyCompleteVectorLattice C(K, ℝ) :=
  isUniformlyCompleteVectorLattice_of_banachLattice _

namespace PosHomFunction

variable {n : ℕ}

/-- The positively homogeneous functional calculus on `C(K, ℝ)` is
computed pointwise. -/
theorem functionalCalculus_continuousMap_apply
    (x : Fin n → C(K, ℝ)) (f : posHomFunctions n) (t : K) :
    functionalCalculus x f t = f (fun i => x i t) := by
  let V : VecLatHom (posHomFunctions n) C(K, ℝ) :=
    { toFun := fun g =>
        ⟨fun s => g (fun i => x i s),
          g.1.continuous.comp (continuous_pi fun i => (x i).continuous)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_sup' := fun _ _ => rfl
      map_inf' := fun _ _ => rfl }
  have hV : ∀ i, V (coordinate i) = x i := by
    intro i
    ext t
    rfl
  have heq := eq_functionalCalculus_of_map_coordinate x V hV
  rw [← heq]
  rfl

end PosHomFunction
