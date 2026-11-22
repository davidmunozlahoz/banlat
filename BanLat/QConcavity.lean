/-
Authors: Pedro Tradacete
-/

import BanLat.PConvexity

/-!
# q-concave operators and Banach lattices

For `1 ≤ q ≤ ∞`, an operator `T` from a Banach lattice is q-concave when `(∑_n ∣∣T x_n∣∣^q)^{1/q}`
is bounded by a fixed multiple of `∣∣ (∑_n |x_n|^q)^{1/q}∣∣`. A Banach lattice is q-concave when
its identity is q-concave. Closed vector sublattices inherit q-concavity, and every bounded linear
operator from a Banach lattice is ∞-concave with optimal constant equal to its norm.
-/

open scoped ENNReal Topology

noncomputable section

variable (q : ℝ≥0∞) [Fact (1 ≤ q)]
variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An operator `T` satisfies the q-concavity estimate with constant `C ≥ 0` when
`(∑_n ∣∣T x_n∣∣^q)^{1/q} ≤ C * ∣∣ (∑_n |x_n|^q)^{1/q}∣∣` for any finite family `(x i)_{i < n}`. -/
def ConcaveWith (C : ℝ) (T : X →L[ℝ] E) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → X),
    ‖WithLp.toLp q (fun i ↦ ‖T (x i)‖)‖ ≤ C * ‖latticePSum q x‖

/-- An operator from a Banach lattice is q-concave if its q-concavity estimate holds
with some nonnegative constant. -/
def IsQConcaveOp (T : X →L[ℝ] E) : Prop :=
  ∃ C, ConcaveWith q C T

/-- The infimum of the q-concavity constants of an operator. -/
def concavityConstant (T : X →L[ℝ] E) : ℝ :=
  sInf {C | ConcaveWith q C T}

/-- A Banach lattice is q-concave when its identity operator is q-concave. -/
def IsQConcave (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] : Prop :=
  IsQConcaveOp q (ContinuousLinearMap.id ℝ X)

/-- A Banach lattice is q-concave with constant `C ≥ 0` when
`(∑_n ∣∣x_n∣∣^q)^{1/q} ≤ C * ∣∣ (∑_n |x_n|^q)^{1/q}∣∣` for any finite family `(x i)_{i < n}`. -/
abbrev IsQConcaveWith (C : ℝ) (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] : Prop :=
  ConcaveWith q C (ContinuousLinearMap.id ℝ X)

/-- For a q-concave Banach lattice, its q-concavity constant is the least constant
satisfying the q-concavity estimate. -/
abbrev qConcavityConstant (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] : ℝ :=
  concavityConstant q (ContinuousLinearMap.id ℝ X)

/-- A Banach lattice is q-concave iff `(∑_n ∣∣x_n∣∣^q)^{1/q} ≤ C * ∣∣ (∑_n |x_n|^q)^{1/q}∣∣`
for some `C ≥ 0` and any finite family `(x i)_{i < n}`. -/
theorem isQConcave_iff :
    IsQConcave q X ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → X),
      ‖WithLp.toLp q (fun i ↦ ‖x i‖)‖ ≤ C * ‖latticePSum q x‖ :=
  Iff.rfl

variable {q} {T : X →L[ℝ] E}

/-- If an operator is q-concave with constant `C`, then it is also q-concave with any larger
constant `D`. -/
theorem ConcaveWith.mono {C D : ℝ} (hC : ConcaveWith q C T) (hCD : C ≤ D) :
    ConcaveWith q D T :=
  ⟨hC.1.trans hCD, fun n x ↦ (hC.2 n x).trans
    (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))⟩

/-- Every q-concavity constant is larger than or equal to the operator norm. -/
theorem ConcaveWith.norm_le {C : ℝ} (hC : ConcaveWith q C T) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC.1 fun x ↦ ?_
  have h := hC.2 1 (fun _ ↦ x)
  rw [latticePSum_fin_one, norm_abs_eq_norm] at h
  simpa only [PiLp.toLp_apply, norm_norm] using
    (PiLp.norm_apply_le (WithLp.toLp q (fun _ : Fin 1 ↦ ‖T x‖)) 0).trans h

private lemma bddBelow_concaveWith :
    BddBelow {C | ConcaveWith q C T} :=
  ⟨0, fun _ hC ↦ hC.1⟩

/-- The optimal operator q-concavity constant is less than or equal to every admissible constant. -/
theorem ConcaveWith.concavityConstant_le {C : ℝ} (hC : ConcaveWith q C T) :
    concavityConstant q T ≤ C :=
  csInf_le bddBelow_concaveWith hC

/-- The optimal constant of a q-concave operator is nonnegative. -/
theorem IsQConcaveOp.concavityConstant_nonneg (hT : IsQConcaveOp q T) :
    0 ≤ concavityConstant q T :=
  le_csInf hT (fun _ hC ↦ hC.1)

/-- The set of admissible q-concavity constants of an operator is closed. -/
private lemma isClosed_concaveWith :
    IsClosed {C | ConcaveWith q C T} := by
  simp only [ConcaveWith, Set.ofPred_and, Set.ofPred_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (continuous_id.mul continuous_const))

/-- A q-concave operator is q-concave with the optimal constant. -/
theorem IsQConcaveOp.concavityConstant_spec (hT : IsQConcaveOp q T) :
    ConcaveWith q (concavityConstant q T) T :=
  isClosed_concaveWith.csInf_mem hT bddBelow_concaveWith

/-- The optimal q-concavity constant is larger than or equal to the operator norm. -/
theorem IsQConcaveOp.norm_le_concavityConstant (hT : IsQConcaveOp q T) :
    ‖T‖ ≤ concavityConstant q T :=
  hT.concavityConstant_spec.norm_le

/-- The admissible q-concavity constants of a q-concave operator are exactly those greater
than or equal to its optimal constant. -/
theorem IsQConcaveOp.concaveWith_iff (hT : IsQConcaveOp q T) {C : ℝ} :
    ConcaveWith q C T ↔ concavityConstant q T ≤ C :=
  ⟨ConcaveWith.concavityConstant_le, hT.concavityConstant_spec.mono⟩

/-- The zero operator satisfies every q-concavity estimate with constant zero. -/
theorem concaveWith_zero :
    ConcaveWith q 0 (0 : X →L[ℝ] E) := by
  simp [ConcaveWith, Pi.zero_def]

/-- The zero operator is q-concave for every q. -/
@[simp]
theorem isQConcaveOp_zero : IsQConcaveOp q (0 : X →L[ℝ] E) :=
  ⟨0, concaveWith_zero⟩

/-- The zero operator has optimal q-concavity constant zero. -/
@[simp]
theorem concavityConstant_zero : concavityConstant q (0 : X →L[ℝ] E) = 0 :=
  le_antisymm concaveWith_zero.concavityConstant_le
    isQConcaveOp_zero.concavityConstant_nonneg

/-- Every bounded linear operator from a Banach lattice is ∞-concave with its norm
as an admissible constant. -/
theorem concaveWith_top (T : X →L[ℝ] E) : ConcaveWith ∞ ‖T‖ T := by
  refine ⟨norm_nonneg _, fun n x ↦ ?_⟩
  rw [PiLp.norm_toLp, pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  intro i
  simpa only [norm_norm] using (T.le_opNorm (x i)).trans
    (mul_le_mul_of_nonneg_left (norm_le_norm_of_abs_le_abs
      ((abs_le_latticePSum ∞ x i).trans (le_abs_self _))) (norm_nonneg T))

/-- Every bounded linear operator from a Banach lattice into a real normed space
is ∞-concave. -/
theorem isQConcaveOp_top (T : X →L[ℝ] E) : IsQConcaveOp ∞ T :=
  ⟨‖T‖, concaveWith_top T⟩

/-- The optimal ∞-concavity constant of an operator is exactly its operator norm. -/
@[simp]
theorem concavityConstant_top (T : X →L[ℝ] E) : concavityConstant ∞ T = ‖T‖ :=
  le_antisymm (concaveWith_top T).concavityConstant_le
    (isQConcaveOp_top T).norm_le_concavityConstant

/-- Every Banach lattice is ∞-concave with constant one. -/
theorem concaveWith_top_id : IsQConcaveWith ∞ 1 X :=
  (concaveWith_top _).mono ContinuousLinearMap.norm_id_le

/-- Every Banach lattice is ∞-concave. -/
theorem isQConcave_top : IsQConcave ∞ X :=
  ⟨1, concaveWith_top_id⟩

/-- The optimal q-concavity constant of a nontrivial q-concave Banach lattice
is at least one. -/
theorem IsQConcave.one_le_concavityConstant [Nontrivial X] (hX : IsQConcave q X) :
    1 ≤ qConcavityConstant q X := by
  simpa only [ContinuousLinearMap.norm_id] using
    IsQConcaveOp.norm_le_concavityConstant hX

/-- An isometric vector lattice embedding pulls back every q-concavity constant
of its codomain to its domain. -/
theorem ConcaveWith.of_isometry {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] {C : ℝ} (hC : IsQConcaveWith q C Y)
    (S : VecLatHom X Y) (hS : Isometry S) : IsQConcaveWith q C X := by
  refine ⟨hC.1, fun n x ↦ ?_⟩
  simpa only [ContinuousLinearMap.id_apply, ← latticePSum_map,
    hS.norm_map_of_map_zero (map_zero S)] using hC.2 n (fun i ↦ S (x i))

/-- A Banach lattice admitting an isometric vector lattice embedding into a q-concave
Banach lattice is itself q-concave. -/
theorem IsQConcave.of_isometry {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] (hY : IsQConcave q Y)
    (S : VecLatHom X Y) (hS : Isometry S) : IsQConcave q X :=
  hY.elim fun C hC ↦ ⟨C, hC.of_isometry S hS⟩

/-- A closed vector sublattice inherits every q-concavity constant
of the ambient Banach lattice. -/
theorem ConcaveWith.id_sublattice {C : ℝ}
    (hC : IsQConcaveWith q C X)
    (Y : VectorSublattice X) (hY : IsClosed (Y : Set X)) :
    letI := Y.banachLatticeCoe hY
    IsQConcaveWith q C Y :=
  letI := Y.banachLatticeCoe hY
  hC.of_isometry Y.subtype isometry_subtype_coe

/-- Every closed vector sublattice of a q-concave Banach lattice is q-concave. -/
theorem IsQConcave.sublattice (hX : IsQConcave q X)
    (Y : VectorSublattice X) (hY : IsClosed (Y : Set X)) :
    letI := Y.banachLatticeCoe hY
    IsQConcave q Y :=
  letI := Y.banachLatticeCoe hY
  hX.elim fun C hC ↦ ⟨C, hC.id_sublattice Y hY⟩
