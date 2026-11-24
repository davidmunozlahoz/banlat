/-
Authors: Alberto Salguero-Alarcón
-/

import BanLat.Operators.Positive
import BanLat.Substructures.Band.BandProjection.Basic
import Mathlib.Topology.Algebra.Module.Complement

/-!
# Complemented Banach lattices

We describe several notions of complementation in the context of Banach lattices.
Fix an isometric embedding `J : X →L[ℝ] Y`. Complementation of `X` in `Y` via `J`
requires a bounded projection `P : Y →L[ℝ] Y` onto the range of `J`, so `P ∘ J = J`.
In increasing order of generality, we consider

* lattice complementation, when `J` and `P` are lattice homomorphisms;
* positive complementation, when `J` and `P` are positive.

In both cases, the bound `C` is an upper bound on the norm of `P`.
An isometric lattice embedding onto a projection band gives lattice `1`-complementation.
Positive complementation implies complementation of the range of `J` as a Banach subspace.
-/

/-! ## Positive complementation -/

namespace PositiveComplemented

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- Given `J: X → Y` an isometric positive embedding, `X` is positively 1-complemented in `Y`
via `J` if `J` admits a positive contractive left inverse. -/
def IsPositiveContractiveRetract (J : X →L[ℝ] Y) : Prop :=
  ∃ Q : Y →L[ℝ] X,
    Positive J.toLinearMap ∧ Positive Q.toLinearMap ∧ Function.LeftInverse Q J ∧
      ‖J‖ ≤ 1 ∧ ‖Q‖ ≤ 1

/-- Given `J: X → Y` an isometric positive embedding, `X` is positively `C`-complemented in `Y`
via `J` if `J` admits a positive left inverse of norm at most `C`. -/
def IsPositiveComplemented (J : X →L[ℝ] Y) (C : ℝ) : Prop :=
  Positive J.toLinearMap ∧ Isometry J ∧
    ∃ Q : Y →L[ℝ] X, Positive Q.toLinearMap ∧ Function.LeftInverse Q J ∧ ‖Q‖ ≤ C

/-- `X` is positively `1`-complemented in `Y` via `J` exactly when `J` is a positive
contraction with a positive contractive left inverse. -/
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

/-- If `X` is positively `C`-complemented in `Y` via `J`, then it is positively
`C'`-complemented in `Y` via `J` for every `C' ≥ C`. -/
theorem IsPositiveComplemented.mono {J : X →L[ℝ] Y} {C C' : ℝ}
    (h : IsPositiveComplemented J C) (hCC' : C ≤ C') : IsPositiveComplemented J C' :=
  match h with
  | ⟨hJ, hJi, Q, hQ, hQJ, hQn⟩ => ⟨hJ, hJi, Q, hQ, hQJ, hQn.trans hCC'⟩

/-- If `X` is positively `C`-complemented in `Y` via `J`, then the range of `J` is
complemented in `Y` as a Banach subspace. -/
theorem IsPositiveComplemented.closedComplemented_range {J : X →L[ℝ] Y} {C : ℝ}
    (h : IsPositiveComplemented J C) : J.range.ClosedComplemented :=
  match h with
  | ⟨_, _, Q, _, hQJ, _⟩ => J.closedComplemented_range_of_leftInverse Q hQJ

end PositiveComplemented

/-! ## Lattice complementation -/

section

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- Given `J: X → Y` an isometric lattice embedding, `X` is lattice `C`-complemented
in `Y` via `J` if `J` admits a lattice homomorphism as a left inverse of norm at most `C`. -/
def IsLatticeComplemented (J : X →L[ℝ] Y) (C : ℝ) : Prop :=
  IsVecLatHom J ∧ Isometry J ∧
    ∃ Q : Y →L[ℝ] X, IsVecLatHom Q ∧ Function.LeftInverse Q J ∧ ‖Q‖ ≤ C

private theorem norm_bandProjection_le (B : ProjectionBand Y) (y : Y) :
    ‖B.bandProjection y‖ ≤ ‖y‖ :=
  norm_le_norm_of_abs_le_abs <|
    (Positive.abs_le_map_abs (Positive.zero_le_iff.mp B.bandProjection_nonneg) y).trans
      (Positive.le_iff.mp B.bandProjection_le_id |y| (abs_nonneg y))

/-- If `J` is an isometric lattice embedding onto a projection band, then `X`
is lattice `1`-complemented in `Y` via `J`. -/
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

/-- If `X` is lattice `C`-complemented in `Y` via `J`, then `X` is positively
`C`-complemented in `Y` via `J`. -/
theorem IsLatticeComplemented.isPositiveComplemented {J : X →L[ℝ] Y} {C : ℝ}
    (h : IsLatticeComplemented J C) : PositiveComplemented.IsPositiveComplemented J C :=
  match h with
  | ⟨hJ, hJi, Q, hQ, hQJ, hQn⟩ =>
    ⟨fun _ hx => (IsVecLatHom.mk' _ hJ).map_nonneg hx, hJi,
      Q, fun _ hx => (IsVecLatHom.mk' _ hQ).map_nonneg hx, hQJ, hQn⟩

end
