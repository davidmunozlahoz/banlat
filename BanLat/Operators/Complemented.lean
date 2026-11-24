/-
Authors: Alberto Salguero-Alarcón
-/

import BanLat.Operators.Positive
import BanLat.Substructures.Band.BandProjection.Basic
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Complemented Banach lattices

A positive isometric embedding witnesses positive `λ`-complementation if it admits
a positive left inverse of norm at most `λ`. Positive contractive retracts
correspond to the case `λ = 1`.
Lattice complementation requires both the embedding and its left inverse to be
vector lattice homomorphisms.
-/

/-! ## Positive complementation -/

namespace Positive

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- The map `J` witnesses that `X` is positively 1-complemented in `Y` if
it is a positive contraction with a positive contractive left inverse.
These conditions make `J` an isometric embedding. -/
def IsPositiveContractiveRetract (J : X →L[ℝ] Y) : Prop :=
  ∃ Q : Y →L[ℝ] X,
    Positive J.toLinearMap ∧ Positive Q.toLinearMap ∧ Function.LeftInverse Q J ∧
      ‖J‖ ≤ 1 ∧ ‖Q‖ ≤ 1

/-- A positive isometric embedding `J` witnesses positive `λ`-complementation
if it has a positive left inverse of norm at most `λ`. -/
def IsPositiveComplemented (J : X →L[ℝ] Y) (c : ℝ) : Prop :=
  Positive J.toLinearMap ∧ Isometry J ∧
    ∃ Q : Y →L[ℝ] X, Positive Q.toLinearMap ∧ Function.LeftInverse Q J ∧ ‖Q‖ ≤ c

/-- Positive contractive retracts are exactly the embeddings witnessing positive
`1`-complementation. -/
theorem isPositiveContractiveRetract_iff_isPositiveComplemented_one
    {J : X →L[ℝ] Y} :
    IsPositiveContractiveRetract J ↔ IsPositiveComplemented J 1 :=
  ⟨fun ⟨Q, hJ, hQ, hQJ, hJn, hQn⟩ =>
    ⟨hJ, (AddMonoidHomClass.isometry_iff_norm J).2 fun x =>
      le_antisymm
        ((J.le_of_opNorm_le hJn x).trans_eq (one_mul ‖x‖))
        (calc
          ‖x‖ = ‖Q (J x)‖ := congrArg norm (hQJ x).symm
          _ ≤ ‖J x‖ := (Q.le_of_opNorm_le hQn (J x)).trans_eq (one_mul ‖J x‖)),
      Q, hQ, hQJ, hQn⟩,
    fun ⟨hJ, hJi, Q, hQ, hQJ, hQn⟩ =>
      ⟨Q, hJ, hQ, hQJ, J.opNorm_le_bound zero_le_one fun x =>
        le_of_eq (((AddMonoidHomClass.isometry_iff_norm J).1 hJi x).trans
          (one_mul ‖x‖).symm), hQn⟩⟩

/-- Increasing the norm bound preserves positive complementation. -/
theorem IsPositiveComplemented.mono {J : X →L[ℝ] Y} {a b : ℝ}
    (h : IsPositiveComplemented J a) (hab : a ≤ b) : IsPositiveComplemented J b :=
  match h with
  | ⟨hJ, hJi, Q, hQ, hQJ, hQn⟩ => ⟨hJ, hJi, Q, hQ, hQJ, hQn.trans hab⟩

/-- A positively complemented embedding has complemented range as a Banach subspace. -/
theorem IsPositiveComplemented.closedComplemented_range {J : X →L[ℝ] Y} {c : ℝ}
    (h : IsPositiveComplemented J c) : J.range.ClosedComplemented :=
  match h with
  | ⟨_, _, Q, _, hQJ, _⟩ => J.closedComplemented_range_of_leftInverse Q hQJ

end Positive

/-! ## Lattice complementation -/

section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- An isometric vector lattice embedding `J` witnesses lattice complementation
with bound `c` if it admits a vector lattice homomorphism as a left inverse of norm at most `c`. -/
def IsLatticeComplemented (J : X →L[ℝ] Y) (c : ℝ) : Prop :=
  IsVecLatHom J ∧ Isometry J ∧
    ∃ Q : Y →L[ℝ] X, IsVecLatHom Q ∧ Function.LeftInverse Q J ∧ ‖Q‖ ≤ c

private theorem norm_bandProjection_le (B : ProjectionBand Y) (y : Y) :
    ‖B.bandProjection y‖ ≤ ‖y‖ :=
  norm_le_norm_of_abs_le_abs <|
    (Positive.abs_le_map_abs (Positive.zero_le_iff.mp B.bandProjection_nonneg) y).trans
      (Positive.le_iff.mp B.bandProjection_le_id |y| (abs_nonneg y))

/-- An isometric vector lattice embedding onto a projection band witnesses
lattice complementation with bound `1`. -/
theorem IsLatticeComplemented.of_projectionBand {J : X →L[ℝ] Y}
    (hJ : IsVecLatHom J) (hJi : Isometry J)
    (B : ProjectionBand Y) (hB : Set.range J = (B : Set Y)) :
    IsLatticeComplemented J 1 :=
  let e := LinearEquiv.ofInjective J.toLinearMap hJi.injective
  let T := e.symm.toLinearMap.comp (B.bandProjection.codRestrict J.toLinearMap.range
    fun y => show B.bandProjection y ∈ Set.range J from
      hB.symm ▸ (show B.bandProjection y ∈ (B : Set Y) from B.bandProjection_mem y))
  have hT (y : Y) : J (T y) = B.bandProjection y :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hnorm (y : Y) : ‖T y‖ ≤ 1 * ‖y‖ := calc
    ‖T y‖ = ‖J (T y)‖ := ((AddMonoidHomClass.isometry_iff_norm J).mp hJi (T y)).symm
    _ = ‖B.bandProjection y‖ := congrArg norm (hT y)
    _ ≤ 1 * ‖y‖ := (one_mul ‖y‖).symm ▸ norm_bandProjection_le B y
  have habs (y : Y) : T |y| = |T y| := hJi.injective <| calc
    J (T |y|) = B.bandProjection |y| := hT _
    _ = |B.bandProjection y| := (IsVecLatHom.mk' _ B.bandProjection_isVecLatHom).map_abs y
    _ = |J (T y)| := congrArg abs (hT y).symm
    _ = J |T y| := ((IsVecLatHom.mk' _ hJ).map_abs (T y)).symm
  ⟨hJ, hJi, T.mkContinuous 1 hnorm, IsVecLatHom.of_abs T.isLinear habs,
    fun x => hJi.injective ((hT (J x)).trans (B.bandProjection_eq_of_mem
      (show J x ∈ (B : Set Y) from hB ▸ Set.mem_range_self x))),
    T.mkContinuous_norm_le zero_le_one hnorm⟩

/-- A lattice-complemented embedding is positively complemented with the same bound. -/
theorem IsLatticeComplemented.isPositiveComplemented {J : X →L[ℝ] Y} {c : ℝ}
    (h : IsLatticeComplemented J c) : Positive.IsPositiveComplemented J c :=
  match h with
  | ⟨hJ, hJi, Q, hQ, hQJ, hQn⟩ =>
    ⟨fun _ hx => (IsVecLatHom.mk' _ hJ).map_nonneg hx, hJi,
      Q, fun _ hx => (IsVecLatHom.mk' _ hQ).map_nonneg hx, hQJ, hQn⟩

end
