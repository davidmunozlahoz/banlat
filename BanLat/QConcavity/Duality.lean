/-
Authors: Pedro Tradacete
-/

import BanLat.QConcavity
import BanLat.PConvexity.Dual
import BanLat.Bidual.Basic
import BanLat.Preliminaries.PiLpDualPairing

/-!
# Duality between convexity and concavity

For conjugate exponents p and q, an operator is p-convex exactly when its adjoint is q-concave,
and an operator is q-concave exactly when its adjoint is p-convex. The admissible and
optimal constants coincide. Applying these equivalences to identity operators relates
convexity and concavity of a Banach lattice to those of its dual, including the endpoint exponents.
-/

open scoped ENNReal

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fact (1 ≤ q)] in
private lemma exists_norming_dual_family {n : ℕ} (x : Fin n → E) :
    ∃ φ : Fin n → StrongDual ℝ E,
      ‖WithLp.toLp p (fun i ↦ ‖φ i‖)‖ ≤ 1 ∧
        ∑ i, φ i (x i) = ‖WithLp.toLp q (fun i ↦ ‖x i‖)‖ := by
  choose ψ hψnorm hψx using fun i ↦ exists_dual_vector'' ℝ (x i)
  obtain ⟨a, ha, hanorm, hax⟩ :=
    PiLp.exists_nonneg_norming (p := q) (q := p) (fun i ↦ ‖x i‖) (fun i ↦ norm_nonneg _)
  refine ⟨fun i ↦ a i • ψ i, ?_, ?_⟩
  · refine (norm_le_norm_of_abs_le_abs (b := WithLp.toLp p a) ?_).trans hanorm
    intro i
    change |‖a i • ψ i‖| ≤ |a i|
    rw [abs_of_nonneg (norm_nonneg _), norm_smul, Real.norm_of_nonneg (ha i),
      abs_of_nonneg (ha i)]
    exact (mul_le_mul_of_nonneg_left (hψnorm i) (ha i)).trans_eq (mul_one _)
  · simpa [hψx, mul_comm] using hax

private lemma concaveWith_of_convexWith_precomp {T : X →L[ℝ] E} {C : ℝ}
    (hT : ConvexWith p C (T.precomp ℝ : StrongDual ℝ E →L[ℝ] StrongDual ℝ X)) :
    ConcaveWith q C T := by
  refine ⟨hT.1, fun n x ↦ ?_⟩
  obtain ⟨φ, hφnorm, hφx⟩ := exists_norming_dual_family (p := p) (q := q) (fun i ↦ T (x i))
  rw [← hφx]
  have hbound : ‖latticePSum p (fun i ↦ (T.precomp ℝ) (φ i))‖ ≤ C :=
    (hT.2 n φ).trans ((mul_le_mul_of_nonneg_left hφnorm hT.1).trans_eq (mul_one _))
  exact (le_abs_self _).trans
    ((abs_sum_apply_le_norm_latticePSum_mul_norm_latticePSum (p := q) (q := p)
      x (fun i ↦ (φ i).comp T)).trans
        ((mul_le_mul_of_nonneg_left hbound (norm_nonneg _)).trans_eq (mul_comm _ _)))

private lemma pairing_le_of_concaveWith {T : X →L[ℝ] E} {C : ℝ}
    (hT : ConcaveWith q C T) {n : ℕ} (φ : Fin n → StrongDual ℝ E) (x : Fin n → X) :
    ∑ i, φ i (T (x i)) ≤
      (C * ‖WithLp.toLp p (fun i ↦ ‖φ i‖)‖) * ‖latticePSum q x‖ := by
  calc
    ∑ i, φ i (T (x i)) ≤ ∑ i, ‖φ i‖ * ‖T (x i)‖ :=
      Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans ((φ i).le_opNorm _)
    _ ≤ ‖WithLp.toLp p (fun i ↦ ‖φ i‖)‖ *
        ‖WithLp.toLp q (fun i ↦ ‖T (x i)‖)‖ := PiLp.sum_mul_le_norm_mul _ _
    _ ≤ ‖WithLp.toLp p (fun i ↦ ‖φ i‖)‖ * (C * ‖latticePSum q x‖) :=
      mul_le_mul_of_nonneg_left (hT.2 n x) (norm_nonneg _)
    _ = _ := by ring

private lemma convexWith_of_convexWith_precomp_precomp {T : E →L[ℝ] X} {C : ℝ}
    (hT : ConvexWith p C
      (((T.precomp ℝ : StrongDual ℝ X →L[ℝ] StrongDual ℝ E)).precomp ℝ :
        StrongDual ℝ (StrongDual ℝ E) →L[ℝ] StrongDual ℝ (StrongDual ℝ X))) :
    ConvexWith p C T := by
  refine ⟨hT.1, fun n x ↦ ?_⟩
  have h := hT.2 n (fun i ↦ NormedSpace.inclusionInDoubleDualLi ℝ (x i))
  change ‖latticePSum p (fun i ↦ BidualSpace.inclusionVecLatHom (T (x i)))‖ ≤
    C * ‖WithLp.toLp p (fun i ↦ ‖NormedSpace.inclusionInDoubleDualLi ℝ (x i)‖)‖ at h
  rw [← latticePSum_map] at h
  change ‖BidualSpace.inclusionLi (latticePSum p (fun i ↦ T (x i)))‖ ≤ _ at h
  simpa only [LinearIsometry.norm_map] using h

private lemma concaveWith_precomp_of_convexWith {T : E →L[ℝ] X} {C : ℝ}
    (hT : ConvexWith p C T) :
    ConcaveWith q C (T.precomp ℝ : StrongDual ℝ X →L[ℝ] StrongDual ℝ E) := by
  refine ⟨hT.1, fun n φ ↦ ?_⟩
  apply PiLp.norm_dual_family_le_of_sum_apply_le (p := p)
    (fun i ↦ (φ i).comp T) (mul_nonneg hT.1 (norm_nonneg _))
  intro x
  calc
    ∑ i, φ i (T (x i)) ≤ |∑ i, φ i (T (x i))| := le_abs_self _
    _ ≤ ‖latticePSum p (fun i ↦ T (x i))‖ * ‖latticePSum q φ‖ :=
      abs_sum_apply_le_norm_latticePSum_mul_norm_latticePSum _ _
    _ ≤ (C * ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖) * ‖latticePSum q φ‖ :=
      mul_le_mul_of_nonneg_right (hT.2 n x) (norm_nonneg _)
    _ = _ := by ring

/-- An operator from a Banach lattice is q-concave with constant `C` exactly when
its adjoint is p-convex with the same constant, for conjugate exponents `p` and `q`. -/
theorem concaveWith_iff_convexWith_precomp {T : X →L[ℝ] E} {C : ℝ} :
    ConcaveWith q C T ↔
      ConvexWith p C (T.precomp ℝ : StrongDual ℝ E →L[ℝ] StrongDual ℝ X) := by
  constructor
  · intro hT
    refine ⟨hT.1, fun n φ ↦ ?_⟩
    exact norm_latticePSum_dual_le (p := q) (q := p) (fun i ↦ (φ i).comp T)
      (mul_nonneg hT.1 (norm_nonneg _)) (pairing_le_of_concaveWith hT φ)
  · exact concaveWith_of_convexWith_precomp

/-- An operator into a Banach lattice is p-convex with constant `C` exactly when
its adjoint is q-concave with the same constant, for conjugate exponents `p` and `q`. -/
theorem convexWith_iff_concaveWith_precomp {T : E →L[ℝ] X} {C : ℝ} :
    ConvexWith p C T ↔
      ConcaveWith q C (T.precomp ℝ : StrongDual ℝ X →L[ℝ] StrongDual ℝ E) := by
  constructor
  · exact concaveWith_precomp_of_convexWith
  · intro hT
    exact convexWith_of_convexWith_precomp_precomp
      ((concaveWith_iff_convexWith_precomp (p := p) (q := q)).mp hT)

/-- An operator from a Banach lattice is q-concave exactly when its adjoint is
p-convex, for conjugate exponents `p` and `q`. -/
theorem isQConcaveOp_iff_isPConvexOp_precomp {T : X →L[ℝ] E} :
    IsQConcaveOp q T ↔
      IsPConvexOp p (T.precomp ℝ : StrongDual ℝ E →L[ℝ] StrongDual ℝ X) :=
  exists_congr fun _ ↦ concaveWith_iff_convexWith_precomp

/-- An operator into a Banach lattice is p-convex exactly when its adjoint is
q-concave, for conjugate exponents `p` and `q`. -/
theorem isPConvexOp_iff_isQConcaveOp_precomp {T : E →L[ℝ] X} :
    IsPConvexOp p T ↔
      IsQConcaveOp q (T.precomp ℝ : StrongDual ℝ X →L[ℝ] StrongDual ℝ E) :=
  exists_congr fun _ ↦ convexWith_iff_concaveWith_precomp

/-- The optimal q-concavity constant of an operator equals the optimal p-convexity
constant of its adjoint. -/
theorem concavityConstant_eq_convexityConstant_precomp (T : X →L[ℝ] E) :
    concavityConstant q T =
      convexityConstant p (T.precomp ℝ : StrongDual ℝ E →L[ℝ] StrongDual ℝ X) := by
  unfold concavityConstant convexityConstant
  congr 1
  exact Set.ext fun _ ↦ concaveWith_iff_convexWith_precomp

/-- The optimal p-convexity constant of an operator equals the optimal q-concavity
constant of its adjoint. -/
theorem convexityConstant_eq_concavityConstant_precomp (T : E →L[ℝ] X) :
    convexityConstant p T =
      concavityConstant q (T.precomp ℝ : StrongDual ℝ X →L[ℝ] StrongDual ℝ E) := by
  unfold convexityConstant concavityConstant
  congr 1
  exact Set.ext fun _ ↦ convexWith_iff_concaveWith_precomp

/-- A Banach lattice is q-concave with constant `C` exactly when its dual is
p-convex with the same constant, for conjugate exponents `p` and `q`. -/
theorem isQConcaveWith_iff_isPConvexWith_dual {C : ℝ} :
    IsQConcaveWith q C X ↔ IsPConvexWith p C (StrongDual ℝ X) :=
  concaveWith_iff_convexWith_precomp (T := ContinuousLinearMap.id ℝ X)

/-- A Banach lattice is p-convex with constant `C` exactly when its dual is
q-concave with the same constant, for conjugate exponents `p` and `q`. -/
theorem isPConvexWith_iff_isQConcaveWith_dual {C : ℝ} :
    IsPConvexWith p C X ↔ IsQConcaveWith q C (StrongDual ℝ X) :=
  convexWith_iff_concaveWith_precomp (T := ContinuousLinearMap.id ℝ X)

/-- A Banach lattice is q-concave exactly when its dual is p-convex,
for conjugate exponents `p` and `q`. -/
theorem isQConcave_iff_isPConvex_dual :
    IsQConcave q X ↔ IsPConvex p (StrongDual ℝ X) :=
  exists_congr fun _ ↦ isQConcaveWith_iff_isPConvexWith_dual

/-- A Banach lattice is p-convex exactly when its dual is q-concave,
for conjugate exponents `p` and `q`. -/
theorem isPConvex_iff_isQConcave_dual :
    IsPConvex p X ↔ IsQConcave q (StrongDual ℝ X) :=
  exists_congr fun _ ↦ isPConvexWith_iff_isQConcaveWith_dual

/-- The q-concavity constant of a Banach lattice equals the p-convexity constant
of its dual, for conjugate exponents `p` and `q`. -/
theorem qConcavityConstant_eq_pConvexityConstant_dual :
    qConcavityConstant q X = pConvexityConstant p (StrongDual ℝ X) :=
  concavityConstant_eq_convexityConstant_precomp (ContinuousLinearMap.id ℝ X)

/-- The p-convexity constant of a Banach lattice equals the q-concavity constant
of its dual, for conjugate exponents `p` and `q`. -/
theorem pConvexityConstant_eq_qConcavityConstant_dual :
    pConvexityConstant p X = qConcavityConstant q (StrongDual ℝ X) :=
  convexityConstant_eq_concavityConstant_precomp (ContinuousLinearMap.id ℝ X)
