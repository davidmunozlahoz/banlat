import BanLat.Examples.Ellp.Basic
import BanLat.Atom
import BanLat.Examples.Lp.OrderContinuous
import BanLat.OrderContinuous.Decomposition

/-!
# Classification of discrete `L^p` spaces

For `1 ≤ p < ∞`, every atomic `L^p(α, μ)` space is lattice isometric to
`ℓ^p(A, ℝ)`, where `A` is the set of its normalized atoms.

If `L^p(α, μ)` is separable, then `A` is countable. Consequently, every
separable atomic `L^p(α, μ)` space is lattice isometric to either
`ℓ^p(Fin n, ℝ)` or `ℓ^p(ℕ, ℝ)`.
-/

open MeasureTheory
open scoped ENNReal NNReal lp

noncomputable section

namespace MeasureTheory.Lp

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0} [Fact (1 ≤ p)]

/-! ### The coordinate map -/

/-- Every element of an atomic `L^p(α, μ)` space is the unconditional sum
of its components along the normalized atoms. -/
private lemma hasSum_atomCoordinate_smul
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    (x : Lp ℝ (p : ENNReal) μ) :
    HasSum (fun a : normalizedAtoms (Lp ℝ (p : ENNReal) μ) ↦
      atomCoordinate a.property.1 x •
        (a : Lp ℝ (p : ENNReal) μ)) x := by
  apply (BanachLattice.hasSum_principalBandProjection
    (normalizedAtoms_isMaximalDisjoint (X := Lp ℝ (p : ENNReal) μ))
    (fun a ha ↦ (mem_normalizedAtoms.mp ha).1.pos) x).congr
  intro s
  apply Finset.sum_congr rfl
  intro a ha
  exact principalBandProjection_eq_atomCoordinate_smul a.property.1 x

private lemma norm_smul_normalizedAtom
    (a : normalizedAtoms (Lp ℝ (p : ENNReal) μ)) (c : ℝ) :
    ‖c • (a : Lp ℝ (p : ENNReal) μ)‖ = |c| := by
  have ha_norm : ‖(a : Lp ℝ (p : ENNReal) μ)‖ = 1 :=
    (mem_normalizedAtoms.mp a.property).2
  rw [norm_smul, ha_norm, mul_one, Real.norm_eq_abs]

/-- The `p`-th powers of the absolute atomic coordinates sum to the
`p`-th power of the `L^p(α, μ)` norm. -/
private lemma hasSum_rpow_atomCoordinate
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    (x : Lp ℝ (p : ENNReal) μ) :
    HasSum (fun a : normalizedAtoms (Lp ℝ (p : ENNReal) μ) ↦
      |atomCoordinate a.property.1 x| ^ (p : ℝ))
      (‖x‖ ^ (p : ℝ)) := by
  have hdisj : Pairwise fun a b : normalizedAtoms (Lp ℝ (p : ENNReal) μ) ↦
      IsVLDisjoint (atomCoordinate a.property.1 x • (a : Lp ℝ (p : ENNReal) μ))
        (atomCoordinate b.property.1 x • (b : Lp ℝ (p : ENNReal) μ)) := by
    intro a b hab
    have hd : IsVLDisjoint (a : Lp ℝ (p : ENNReal) μ) b :=
      normalizedAtoms_isDisjointSet.2 a.property b.property
        (fun h ↦ hab (Subtype.ext h))
    exact (hd.smul_left (atomCoordinate a.property.1 x)).smul_right
      (atomCoordinate b.property.1 x)
  have hnorm := ALpSpace.HasSum.norm_rpow_of_pairwise_isVLDisjoint
    (p := p) (hasSum_atomCoordinate_smul x) hdisj
  convert hnorm using 1
  funext a
  exact congrArg (fun r : ℝ ↦ r ^ (p : ℝ))
    (norm_smul_normalizedAtom a (atomCoordinate a.property.1 x)).symm

/-- The atomic coordinates of an element of `L^p(α, μ)` belong to
`ℓ^p(A, ℝ)`, where `A` is the set of normalized atoms. -/
private lemma atomCoordinate_memℓp
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    (x : Lp ℝ (p : ENNReal) μ) :
    Memℓp (fun a : normalizedAtoms (Lp ℝ (p : ENNReal) μ) ↦
      atomCoordinate a.property.1 x)
      (p : ENNReal) := by
  apply memℓp_gen
  simpa [Real.norm_eq_abs] using (hasSum_rpow_atomCoordinate x).summable

/-- The atomic coordinate map from `L^p(α, μ)` to `ℓ^p(A, ℝ)`, bundled as
a vector lattice homomorphism. -/
private noncomputable def coordinateMap
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)] :
    VecLatHom (Lp ℝ (p : ENNReal) μ)
      ℓ^(p : ENNReal)(normalizedAtoms (Lp ℝ (p : ENNReal) μ), ℝ) := by
  refine
    { toFun := fun x ↦ ⟨fun a ↦ atomCoordinate a.property.1 x,
        atomCoordinate_memℓp x⟩
      map_add' := ?_
      map_smul' := ?_
      map_sup' := ?_
      map_inf' := ?_ }
  · intro x y
    ext a
    change atomCoordinate a.property.1 (x + y) =
      atomCoordinate a.property.1 x + atomCoordinate a.property.1 y
    exact map_add (atomCoordinateLinearMap a.property.1) x y
  · intro c x
    ext a
    change atomCoordinate a.property.1 (c • x) = c • atomCoordinate a.property.1 x
    exact map_smul (atomCoordinateLinearMap a.property.1) c x
  · intro x y
    ext a
    change atomCoordinate a.property.1 (x ⊔ y) =
      atomCoordinate a.property.1 x ⊔ atomCoordinate a.property.1 y
    exact map_sup (atomCoordinateVecLatHom a.property.1) x y
  · intro x y
    ext a
    change atomCoordinate a.property.1 (x ⊓ y) =
      atomCoordinate a.property.1 x ⊓ atomCoordinate a.property.1 y
    exact map_inf (atomCoordinateVecLatHom a.property.1) x y

/-- Evaluation of the coordinate map at an atom `a` gives `λₐ(x)`. -/
@[simp]
private lemma coordinateMap_apply
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    (x : Lp ℝ (p : ENNReal) μ)
    (a : normalizedAtoms (Lp ℝ (p : ENNReal) μ)) :
    coordinateMap x a = atomCoordinate a.property.1 x := by
  rfl

/-- The atomic coordinate map preserves the `L^p(α, μ)` norm. -/
private lemma norm_coordinateMap
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    (x : Lp ℝ (p : ENNReal) μ) :
    ‖coordinateMap x‖ = ‖x‖ := by
  have hp_pos : 0 < (p : ℝ) := NNReal.coe_pos.mpr
    (lt_of_lt_of_le zero_lt_one Fact.out)
  rw [lp.norm_eq_tsum_rpow (by simpa using hp_pos)]
  have hsum := (hasSum_rpow_atomCoordinate x).tsum_eq
  have hsum' :
      (∑' i : normalizedAtoms (Lp ℝ (p : ENNReal) μ),
        ‖(coordinateMap x) i‖ ^ (p : ENNReal).toReal) = ‖x‖ ^ (p : ℝ) := by
    simpa [coordinateMap_apply, Real.norm_eq_abs] using hsum
  rw [hsum']
  simpa [one_div] using Real.rpow_rpow_inv (norm_nonneg x) hp_pos.ne'

/-- A scalar multiple of a normalized atom has the expected coordinate at
that atom and zero coordinates at all the other normalized atoms. -/
private lemma coordinateMap_smul_normalizedAtom
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    (a : normalizedAtoms (Lp ℝ (p : ENNReal) μ)) (c : ℝ) :
    coordinateMap (c • (a : Lp ℝ (p : ENNReal) μ)) a = c ∧
      ∀ b, b ≠ a →
        coordinateMap (c • (a : Lp ℝ (p : ENNReal) μ)) b = 0 := by
  constructor
  · rw [coordinateMap_apply]
    change atomCoordinateLinearMap a.property.1
      (c • (a : Lp ℝ (p : ENNReal) μ)) = c
    rw [map_smul, atomCoordinateLinearMap_apply, atomCoordinate_self]
    simp
  · intro b hba
    rw [coordinateMap_apply]
    change atomCoordinateLinearMap b.property.1 (c • (a : Lp ℝ (p : ENNReal) μ)) = 0
    rw [map_smul]
    have hdis : IsVLDisjoint (b : Lp ℝ (p : ENNReal) μ) a :=
      normalizedAtoms_isDisjointSet.2 b.property a.property
        (fun h ↦ hba (Subtype.ext h))
    rw [atomCoordinateLinearMap_apply,
      atomCoordinate_eq_zero_of_isVLDisjoint b.property.1 hdis, smul_zero]

private lemma coordinateMap_smul_normalizedAtom_eq_single
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    [DecidableEq (normalizedAtoms (Lp ℝ (p : ENNReal) μ))]
    (a : normalizedAtoms (Lp ℝ (p : ENNReal) μ)) (c : ℝ) :
    coordinateMap (c • (a : Lp ℝ (p : ENNReal) μ)) =
      lp.single (p : ENNReal) a c := by
  ext b
  by_cases hba : b = a
  · subst b
    rw [lp.single_apply_self]
    exact (coordinateMap_smul_normalizedAtom a c).1
  · rw [lp.single_apply_ne _ _ _ hba]
    exact (coordinateMap_smul_normalizedAtom a c).2 b hba

/-- The atomic coordinate map has closed range containing every
single-coordinate family and is therefore surjective. -/
private lemma coordinateMap_surjective
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)] :
    Function.Surjective (coordinateMap (μ := μ) (p := p)) := by
  classical
  intro f
  let T : Lp ℝ (p : ENNReal) μ →ₗᵢ[ℝ]
      ℓ^(p : ENNReal)(normalizedAtoms (Lp ℝ (p : ENNReal) μ), ℝ) :=
    { toLinearMap := (coordinateMap (μ := μ) (p := p)).toLinearMap
      norm_map' := norm_coordinateMap (μ := μ) (p := p) }
  have hclosed : IsClosed (Set.range (coordinateMap (μ := μ) (p := p))) := by
    change IsClosed (Set.range T)
    exact T.isometry.isClosedEmbedding.isClosed_range
  apply hclosed.mem_of_tendsto (lp.hasSum_single (by simp) f)
  exact Filter.Eventually.of_forall fun s ↦ by
    refine ⟨∑ a ∈ s, f a • (a : Lp ℝ (p : ENNReal) μ), ?_⟩
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact coordinateMap_smul_normalizedAtom_eq_single a (f a)

/-! ### Discrete classification -/

/-- The atomic coordinate map is a lattice isometry from an atomic
`L^p(α, μ)` space onto `ℓ^p(A, ℝ)`, where `A` is the set of normalized atoms. -/
private noncomputable def banachLatEquivNormalizedAtoms
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)] :
    BanachLatEquiv (Lp ℝ (p : ENNReal) μ)
      (ℓ^(p : ENNReal)(normalizedAtoms (Lp ℝ (p : ENNReal) μ), ℝ)) := by
  let T : Lp ℝ (p : ENNReal) μ →ₗᵢ[ℝ]
      ℓ^(p : ENNReal)(normalizedAtoms (Lp ℝ (p : ENNReal) μ), ℝ) :=
    { toLinearMap := (coordinateMap (μ := μ) (p := p)).toLinearMap
      norm_map' := norm_coordinateMap (μ := μ) (p := p) }
  exact
    { toLinearIsometryEquiv := LinearIsometryEquiv.ofSurjective T coordinateMap_surjective
      map_sup' := (coordinateMap (μ := μ) (p := p)).map_sup'
      map_inf' := (coordinateMap (μ := μ) (p := p)).map_inf' }

/-- Every atomic real `L^p(α, μ)` space is lattice isometric to
`ℓ^p(A, ℝ)` for some index type `A`. -/
theorem exists_banachLatEquiv_lp
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)] :
    ∃ A : Type u, Nonempty
      (BanachLatEquiv (Lp ℝ (p : ENNReal) μ) (ℓ^(p : ENNReal)(A, ℝ))) := by
  exact ⟨{a : Lp ℝ (p : ENNReal) μ // a ∈ normalizedAtoms (Lp ℝ (p : ENNReal) μ)},
    ⟨banachLatEquivNormalizedAtoms (μ := μ) (p := p)⟩⟩

/-! ### The separable case -/

/-- A separable atomic real `L^p(α, μ)` space is lattice isometric either
to `ℓ^p(Fin n, ℝ)` for some `n`, or to `ℓ^p(ℕ, ℝ)`. -/
theorem exists_banachLatEquiv_fin_or_nat
    [IsAtomicVectorLattice (Lp ℝ (p : ENNReal) μ)]
    [TopologicalSpace.SeparableSpace (Lp ℝ (p : ENNReal) μ)] :
    (∃ n : ℕ, Nonempty
      (BanachLatEquiv (Lp ℝ (p : ENNReal) μ) (ℓ^(p : ENNReal)(Fin n, ℝ)))) ∨
      Nonempty (BanachLatEquiv (Lp ℝ (p : ENNReal) μ)
        (ℓ^(p : ENNReal)(ℕ, ℝ))) := by
  classical
  let A := normalizedAtoms (Lp ℝ (p : ENNReal) μ)
  have hcount : Countable A := countable_normalizedAtoms
  letI : Countable A := hcount
  rcases finite_or_infinite A with hfin | hinf
  · left
    letI : Finite A := hfin
    refine ⟨Nat.card A, ?_⟩
    exact ⟨(banachLatEquivNormalizedAtoms (μ := μ) (p := p)).trans
      (lpCongr (p := (p : ENNReal)) (Finite.equivFin A).symm)⟩
  · right
    letI : Infinite A := hinf
    let he : Nonempty (A ≃ ℕ) := inferInstance
    obtain ⟨e⟩ := he
    exact ⟨(banachLatEquivNormalizedAtoms (μ := μ) (p := p)).trans
      (lpCongr (p := (p : ENNReal)) e.symm)⟩

end MeasureTheory.Lp
