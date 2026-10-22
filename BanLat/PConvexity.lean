/-
Authors: Pedro Tradacete
-/

import BanLat.FunctionalCalculus
import BanLat.Pi
import BanLat.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# p-convex operators and Banach lattices

For `1 ≤ p ≤ ∞`, a bounded linear operator into a Banach lattice is p-convex when
finite lattice p-sums of its images are norm bounded by the ℓᵖ norms of the inputs.
Admissible constants are nonnegative, and their infimum is attained for p-convex
operators. A Banach lattice is p-convex when its identity operator is p-convex.
Quotients by closed order ideals preserve the operator and lattice estimates.
Closed vector sublattices inherit lattice p-convexity, and decreasing the exponent
preserves every admissible operator constant. Every bounded linear operator is
1-convex, with optimal constant equal to its operator norm.
-/

open scoped ENNReal Topology

noncomputable section

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The finite ℓᵖ norm as a continuous positively homogeneous function.
At `p = ∞` this is the maximum of the absolute values, with empty value zero. -/
def pSumFunction (n : ℕ) : posHomFunctions n :=
  ⟨⟨fun a ↦ ‖WithLp.toLp p a‖,
    continuous_norm.comp (PiLp.continuous_toLp p (fun _ : Fin n ↦ ℝ))⟩,
    fun c hc a ↦ (norm_smul c (WithLp.toLp p a)).trans
      (congrArg (· * ‖WithLp.toLp p a‖) (Real.norm_of_nonneg hc))⟩

/-- Evaluation of the homogeneous p-sum function is the finite ℓᵖ norm. -/
@[simp]
theorem pSumFunction_apply {n : ℕ} (a : Fin n → ℝ) :
    pSumFunction p n a = ‖WithLp.toLp p a‖ := rfl

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

/-- The lattice p-sum of a finite family, defined by homogeneous functional calculus.
For finite `p` it represents `(∑ i, |x i| ^ p) ^ (1 / p)`. -/
def latticePSum {n : ℕ} (x : Fin n → X) : X :=
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  PosHomFunction.functionalCalculus x (pSumFunction p n)

/-- Every finite lattice p-sum is nonnegative. -/
theorem latticePSum_nonneg {n : ℕ} (x : Fin n → X) :
    0 ≤ latticePSum p x :=
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  (PosHomFunction.functionalCalculus x).map_nonneg (fun a ↦ norm_nonneg (WithLp.toLp p a))

/-- The lattice p-sum of a zero family is zero. -/
@[simp]
theorem latticePSum_zero {n : ℕ} :
    latticePSum p (fun _ : Fin n ↦ (0 : X)) = 0 :=
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  PosHomFunction.functionalCalculus_zero (pSumFunction p n)

/-- The lattice p-sum of the empty family is zero. -/
@[simp]
theorem latticePSum_fin_zero (x : Fin 0 → X) :
    latticePSum p x = 0 :=
  (congrArg (latticePSum p) (Subsingleton.elim x (fun _ ↦ 0))).trans (latticePSum_zero p)

/-- Each absolute value in a finite family is bounded by its lattice p-sum. -/
theorem abs_le_latticePSum {n : ℕ} (x : Fin n → X) (i : Fin n) :
    |x i| ≤ latticePSum p x := by
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  have h : |PosHomFunction.coordinate i| ≤ pSumFunction p n :=
    fun a ↦ PiLp.norm_apply_le (WithLp.toLp p a) i
  simpa only [latticePSum, VecLatHom.map_abs, PosHomFunction.functionalCalculus_coordinate]
    using (PosHomFunction.functionalCalculus x).monotone h

/-- The lattice p-sum of a singleton is its absolute value. -/
@[simp]
theorem latticePSum_fin_one (x : Fin 1 → X) :
    latticePSum p x = |x 0| := by
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  have h : pSumFunction p 1 = |PosHomFunction.coordinate 0| := by
    ext a
    change ‖WithLp.toLp p a‖ = |a 0|
    have ha : a = Function.const (Fin 1) (a 0) :=
      funext fun i ↦ congrArg a (Subsingleton.elim i 0)
    rw [ha, PiLp.norm_toLp_const']
    simp [Real.norm_eq_abs]
  simp only [latticePSum, h, VecLatHom.map_abs,
    PosHomFunction.functionalCalculus_coordinate]

/-- At exponent one, the lattice p-sum is the sum of the absolute values. -/
@[simp]
theorem latticePSum_one {n : ℕ} (x : Fin n → X) :
    latticePSum 1 x = ∑ i, |x i| := by
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  have h : pSumFunction 1 n = ∑ i, |PosHomFunction.coordinate i| := by
    ext a
    simp [pSumFunction, PiLp.norm_eq_of_L1, Real.norm_eq_abs]
    rfl
  simp only [latticePSum, h, map_sum, VecLatHom.map_abs,
    PosHomFunction.functionalCalculus_coordinate]

/-- Vector lattice homomorphisms between Banach lattices preserve finite lattice p-sums. -/
theorem latticePSum_map {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] (T : VecLatHom X Y)
    {n : ℕ} (x : Fin n → X) :
    T (latticePSum p x) = latticePSum p (fun i ↦ T (x i)) :=
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  letI := isUniformlyCompleteVectorLattice_of_banachLattice Y
  PosHomFunction.functionalCalculus_map T x (pSumFunction p n)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded linear operator satisfies the p-convexity estimate with constant `C ≥ 0`
when lattice p-sums of its images are bounded in norm by `C` times the ℓᵖ sums of the
norms of the inputs. -/
def ConvexWith (C : ℝ) (T : E →L[ℝ] X) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
    ‖latticePSum p (fun i ↦ T (x i))‖ ≤ C * ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖

/-- A bounded linear operator into a Banach lattice is p-convex if it satisfies
a p-convexity estimate with some nonnegative constant. -/
def IsPConvexOp (T : E →L[ℝ] X) : Prop :=
  ∃ C, ConvexWith p C T

/-- p-convexity constant of an operator.
The infimum of the admissible p-convexity constants of an operator.
It is admissible whenever `IsPConvexOp p T` holds. -/
def convexityConstant (T : E →L[ℝ] X) : ℝ :=
  sInf {C | ConvexWith p C T}

/-- A Banach lattice is p-convex when its identity operator is p-convex. -/
def IsPConvex (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] : Prop :=
  IsPConvexOp p (ContinuousLinearMap.id ℝ X)

variable {p} {T : E →L[ℝ] X}

/-- Increasing an admissible constant preserves the operator p-convexity estimate. -/
theorem ConvexWith.mono {C D : ℝ} (hC : ConvexWith p C T) (hCD : C ≤ D) :
    ConvexWith p D T :=
  ⟨hC.1.trans hCD, fun n x ↦ (hC.2 n x).trans
    (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))⟩

/-- Every admissible p-convexity constant bounds the operator norm. -/
theorem ConvexWith.norm_le {C : ℝ} (hC : ConvexWith p C T) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC.1 fun x ↦ ?_
  simpa [latticePSum_fin_one, norm_abs_eq_norm, PiLp.norm_toLp_const', Function.const_def]
    using hC.2 1 (fun _ ↦ x)

private lemma bddBelow_convexWith :
    BddBelow {C | ConvexWith p C T} :=
  ⟨0, fun _ hC ↦ hC.1⟩

/-- The optimal operator p-convexity constant is at most every admissible constant. -/
theorem ConvexWith.convexityConstant_le {C : ℝ} (hC : ConvexWith p C T) :
    convexityConstant p T ≤ C :=
  csInf_le bddBelow_convexWith hC

/-- The optimal constant of a p-convex operator is nonnegative. -/
theorem IsPConvexOp.convexityConstant_nonneg (hT : IsPConvexOp p T) :
    0 ≤ convexityConstant p T :=
  le_csInf hT (fun _ hC ↦ hC.1)

private lemma isClosed_convexWith :
    IsClosed {C | ConvexWith p C T} := by
  simp only [ConvexWith, Set.setOf_and, Set.setOf_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (continuous_id.mul continuous_const))

/-- A p-convex operator satisfies its estimate with the optimal constant. -/
theorem IsPConvexOp.convexityConstant_spec (hT : IsPConvexOp p T) :
    ConvexWith p (convexityConstant p T) T :=
  isClosed_convexWith.csInf_mem hT bddBelow_convexWith

/-- The optimal p-convexity constant bounds the operator norm. -/
theorem IsPConvexOp.norm_le_convexityConstant (hT : IsPConvexOp p T) :
    ‖T‖ ≤ convexityConstant p T :=
  hT.convexityConstant_spec.norm_le

/-- Admissible constants of a p-convex operator are exactly those greater than
or equal to its optimal constant. -/
theorem IsPConvexOp.convexWith_iff (hT : IsPConvexOp p T) {C : ℝ} :
    ConvexWith p C T ↔ convexityConstant p T ≤ C :=
  ⟨ConvexWith.convexityConstant_le, hT.convexityConstant_spec.mono⟩

/-- The zero operator satisfies every p-convexity estimate with constant zero. -/
theorem convexWith_zero :
    ConvexWith p 0 (0 : E →L[ℝ] X) := by
  simp [ConvexWith, latticePSum_zero]

/-- The zero operator is p-convex for every exponent. -/
@[simp]
theorem isPConvexOp_zero : IsPConvexOp p (0 : E →L[ℝ] X) :=
  ⟨0, convexWith_zero⟩

/-- The optimal p-convexity constant of the zero operator is zero. -/
@[simp]
theorem convexityConstant_zero : convexityConstant p (0 : E →L[ℝ] X) = 0 :=
  le_antisymm convexWith_zero.convexityConstant_le
    isPConvexOp_zero.convexityConstant_nonneg

/-- Composing a p-convex operator with the quotient map by a closed order ideal
preserves its admissible constant. -/
theorem ConvexWith.quotient {C : ℝ} (hC : ConvexWith p C T)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ConvexWith p C (J.toSubmodule.mkQL.comp T) := by
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  refine ⟨hC.1, fun n x ↦ ?_⟩
  have hmap := latticePSum_map p J.mkQVecLatHom (fun i ↦ T (x i))
  calc
    ‖latticePSum p (fun i ↦ (J.toSubmodule.mkQL.comp T) (x i))‖ =
        ‖J.mkQ (latticePSum p (fun i ↦ T (x i)))‖ := congrArg norm hmap.symm
    _ ≤ ‖latticePSum p (fun i ↦ T (x i))‖ :=
      Submodule.Quotient.norm_mk_le J.toSubmodule _
    _ ≤ C * ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ := hC.2 n x

/-- Passing to a quotient of the target by a closed order ideal preserves
p-convexity of an operator. -/
theorem IsPConvexOp.quotient (hT : IsPConvexOp p T)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    IsPConvexOp p (J.toSubmodule.mkQL.comp T) :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  hT.elim fun C hC ↦ ⟨C, hC.quotient J hJ⟩

/-- Passing to a quotient of the target cannot increase an operator's optimal
p-convexity constant. -/
theorem IsPConvexOp.convexityConstant_quotient_le (hT : IsPConvexOp p T)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    convexityConstant p (J.toSubmodule.mkQL.comp T) ≤ convexityConstant p T :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  (hT.convexityConstant_spec.quotient J hJ).convexityConstant_le

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma norm_latticePSum_le_of_lifts {C δ : ℝ}
    (S : F →L[ℝ] X) (q : E →L[ℝ] F) (hC : ConvexWith p C (S.comp q))
    {n : ℕ} (x : Fin n → F) (y : Fin n → E) (hy : ∀ i, q (y i) = x i)
    (hδ : 0 ≤ δ) (hbound : ∀ i, ‖y i‖ ≤ ‖x i‖ + δ) :
    ‖latticePSum p (fun i ↦ S (x i))‖ ≤
      C * ‖WithLp.toLp p (fun i ↦ ‖x i‖ + δ)‖ := by
  have hsum : ‖WithLp.toLp p (fun i ↦ ‖y i‖)‖ ≤
      ‖WithLp.toLp p (fun i ↦ ‖x i‖ + δ)‖ := by
    apply norm_le_norm_of_abs_le_abs
    change ∀ i, |‖y i‖| ≤ |‖x i‖ + δ|
    simpa only [abs_norm, abs_of_nonneg (add_nonneg (norm_nonneg _) hδ)] using hbound
  have h := (hC.2 n y).trans (mul_le_mul_of_nonneg_left hsum hC.1)
  simpa only [ContinuousLinearMap.comp_apply, hy] using h

private lemma convexWith_of_quotient {C : ℝ}
    (S : F →L[ℝ] X) (q : E →L[ℝ] F) (hC : ConvexWith p C (S.comp q))
    (hlift : ∀ x : F, ∀ δ > 0, ∃ y, q y = x ∧ ‖y‖ < ‖x‖ + δ) :
    ConvexWith p C S := by
  refine ⟨hC.1, fun n x ↦ ?_⟩
  have hcont : Continuous (fun δ : ℝ ↦ C *
      ‖WithLp.toLp p (fun i ↦ ‖x i‖ + δ)‖) :=
    continuous_const.mul (continuous_norm.comp ((PiLp.continuous_toLp p _).comp
      (continuous_pi fun _ ↦ continuous_const.add continuous_id)))
  have hlim := (hcont.tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  choose y hy hbound using fun i ↦ hlift (x i) δ hδ
  exact norm_latticePSum_le_of_lifts S q hC x y hy hδ.le (fun i ↦ (hbound i).le)

/-- The identity on a quotient by a closed order ideal retains each p-convexity
constant of the original identity operator. -/
theorem ConvexWith.id_quotient {C : ℝ}
    (hC : ConvexWith p C (ContinuousLinearMap.id ℝ X))
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ConvexWith p C (ContinuousLinearMap.id ℝ (X ⧸ J.toSubmodule)) :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  convexWith_of_quotient (ContinuousLinearMap.id ℝ (X ⧸ J.toSubmodule))
    J.toSubmodule.mkQL (hC.quotient J hJ)
    (fun x _ hδ ↦ Submodule.Quotient.norm_mk_lt x hδ)

/-- Quotients by closed order ideals of p-convex Banach lattices are p-convex. -/
theorem IsPConvex.quotient (hX : IsPConvex p X)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    IsPConvex p (X ⧸ J.toSubmodule) :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  hX.elim fun C hC ↦ ⟨C, hC.id_quotient J hJ⟩

/-- The optimal p-convexity constant of the identity on a nontrivial
p-convex Banach lattice is at least one. -/
theorem IsPConvex.one_le_convexityConstant [Nontrivial X] (hX : IsPConvex p X) :
    1 ≤ convexityConstant p (ContinuousLinearMap.id ℝ X) := by
  simpa only [ContinuousLinearMap.norm_id] using
    IsPConvexOp.norm_le_convexityConstant hX

/-- Taking a quotient by a closed order ideal cannot increase the optimal
p-convexity constant of a Banach lattice's identity operator. -/
theorem IsPConvex.convexityConstant_quotient_le (hX : IsPConvex p X)
    (J : OrderIdeal X) (hJ : IsClosed (J : Set X)) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    convexityConstant p (ContinuousLinearMap.id ℝ (X ⧸ J.toSubmodule)) ≤
      convexityConstant p (ContinuousLinearMap.id ℝ X) :=
  letI := J.quotientNormedAddCommGroup hJ
  letI := J.quotientBanachLattice hJ
  ((IsPConvexOp.convexityConstant_spec hX).id_quotient J hJ).convexityConstant_le

private lemma latticePSum_le_of_scalar_bound {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {n : ℕ} (x : Fin n → X) (w : Fin n → ℝ) (K : ℝ)
    (h : ∀ a : Fin n → ℝ,
      ‖WithLp.toLp q a‖ ≤ K * ‖WithLp.toLp p (fun i ↦ w i * a i)‖) :
    latticePSum q x ≤ K • latticePSum p (fun i ↦ w i • x i) := by
  letI := isUniformlyCompleteVectorLattice_of_banachLattice X
  have hfun : pSumFunction q n ≤ K • PosHomFunction.comp (pSumFunction p n)
      (fun i ↦ w i • PosHomFunction.coordinate i) := h
  have hcalc := (PosHomFunction.functionalCalculus x).monotone hfun
  simpa only [latticePSum, map_smul, ← PosHomFunction.functionalCalculus_comp,
    PosHomFunction.functionalCalculus_coordinate] using hcalc

omit [Fact (1 ≤ p)] in
private lemma norm_toLp_rpow {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hp : 0 < p.toReal) (t : ℝ) :
    ‖WithLp.toLp p (fun i ↦ a i ^ t)‖ =
      (∑ i, a i ^ (t * p.toReal)) ^ (1 / p.toReal) := by
  simp only [PiLp.norm_eq_sum hp,
    Real.norm_of_nonneg (Real.rpow_nonneg (ha _) _), ← Real.rpow_mul (ha _)]

omit [Fact (1 ≤ p)] in
private lemma scalar_holder_bound {q : ℝ≥0∞} {r : ℝ}
    (hpqr : p.toReal.HolderTriple r q.toReal) {n : ℕ} (a b : Fin n → ℝ) :
    ‖WithLp.toLp q (fun i ↦ a i * b i)‖ ≤
      ‖WithLp.toLp p a‖ * (∑ i, |b i| ^ r) ^ (1 / r) := by
  have h := NNReal.coe_le_coe.mpr (NNReal.Lr_le_Lp_mul_Lq Finset.univ
    (fun i ↦ ⟨|a i|, abs_nonneg _⟩) (fun i ↦ ⟨|b i|, abs_nonneg _⟩) hpqr)
  simpa only [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_sum, NNReal.coe_mk,
    PiLp.norm_eq_sum hpqr.pos, PiLp.norm_eq_sum hpqr.pos', Real.norm_eq_abs,
    abs_mul] using! h

omit [Fact (1 ≤ p)] in
private lemma rescaling_mul {q r : ℝ} (hpqr : p.toReal.HolderTriple r q)
    {a : ℝ} (ha : 0 < a) :
    a ^ (-(q / r)) * a = a ^ (q / p.toReal) := by
  rw [← Real.rpow_add_one ha.ne']
  congr 1
  linear_combination -q * hpqr.inv_add_inv_eq_inv - mul_inv_cancel₀ hpqr.ne_zero'

omit [Fact (1 ≤ p)] in
private lemma scalar_rescaling_bound {q : ℝ≥0∞} {r : ℝ}
    (hpqr : p.toReal.HolderTriple r q.toReal) {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (y : Fin n → ℝ) :
    ‖WithLp.toLp q y‖ ≤ (∑ i, a i ^ q.toReal) ^ (1 / r) *
      ‖WithLp.toLp p (fun i ↦ a i ^ (-(q.toReal / r)) * y i)‖ := by
  have h := scalar_holder_bound hpqr
    (fun i ↦ a i ^ (-(q.toReal / r)) * y i) (fun i ↦ a i ^ (q.toReal / r))
  have hcancel (i) : a i ^ (-(q.toReal / r)) * y i * a i ^ (q.toReal / r) =
      y i := by
    rw [Real.rpow_neg (ha i).le, mul_right_comm,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos (ha i) (q.toReal / r)).ne', one_mul]
  simpa only [hcancel, abs_of_pos (Real.rpow_pos_of_pos (ha _) _),
    ← Real.rpow_mul (ha _).le, div_mul_cancel₀ _ hpqr.symm.ne_zero]
    using h.trans_eq (mul_comm _ _)

omit [Fact (1 ≤ p)] in
private lemma scalar_rescaling_norm {q : ℝ≥0∞} {r : ℝ}
    (hpqr : p.toReal.HolderTriple r q.toReal) {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (∑ i, a i ^ q.toReal) ^ (1 / r) *
      ‖WithLp.toLp p (fun i ↦ a i ^ (-(q.toReal / r)) * a i)‖ =
        ‖WithLp.toLp q a‖ := by
  simp_rw [rescaling_mul hpqr (ha _)]
  rw [norm_toLp_rpow a (fun i ↦ (ha i).le) hpqr.pos,
    div_mul_cancel₀ _ hpqr.ne_zero]
  rw [← Real.rpow_add_of_nonneg
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i).le _) hpqr.symm.one_div_nonneg
      hpqr.one_div_nonneg, hpqr.symm.one_div_add_one_div]
  simp only [PiLp.norm_eq_sum hpqr.pos', Real.norm_of_nonneg (ha _).le]

private lemma scalar_rescaling_top_bound {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (y : Fin n → ℝ) :
    ‖WithLp.toLp q y‖ ≤ ‖WithLp.toLp q a‖ *
      ‖WithLp.toLp ∞ (fun i ↦ (a i)⁻¹ * y i)‖ := by
  let M := ‖WithLp.toLp ∞ (fun i ↦ (a i)⁻¹ * y i)‖
  have hpoint (i) : |y i| ≤ M * a i := by
    have h := mul_le_mul_of_nonneg_left
      (PiLp.norm_apply_le (WithLp.toLp ∞ (fun i ↦ (a i)⁻¹ * y i)) i) (ha i).le
    simpa only [PiLp.toLp_apply, Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos (ha i), ← mul_assoc, mul_inv_cancel₀ (ha i).ne', one_mul]
      using h.trans_eq (mul_comm _ _)
  have hnorm : ‖WithLp.toLp q y‖ ≤ ‖M • WithLp.toLp q a‖ := by
    apply norm_le_norm_of_abs_le_abs
    exact fun i ↦ (hpoint i).trans_eq
      (abs_of_nonneg (mul_nonneg (norm_nonneg _) (ha i).le)).symm
  simpa only [norm_smul, M, norm_norm, mul_comm] using hnorm

private lemma exists_scalar_rescaling {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hqp : q < p) {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ (w : Fin n → ℝ) (K : ℝ), (∀ i, 0 ≤ w i) ∧ 0 ≤ K ∧
      (∀ y : Fin n → ℝ,
        ‖WithLp.toLp q y‖ ≤ K * ‖WithLp.toLp p (fun i ↦ w i * y i)‖) ∧
      K * ‖WithLp.toLp p (fun i ↦ w i * a i)‖ ≤ ‖WithLp.toLp q a‖ := by
  by_cases hp : p = ∞
  · subst p
    refine ⟨fun i ↦ (a i)⁻¹, ‖WithLp.toLp q a‖,
      fun i ↦ inv_nonneg.mpr (ha i).le, norm_nonneg _,
      scalar_rescaling_top_bound a ha, ?_⟩
    apply (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)).trans_eq (mul_one _)
    simp [PiLp.norm_toLp, inv_mul_cancel₀ (ha _).ne',
      pi_norm_le_iff_of_nonneg zero_le_one]
  have hq : q ≠ ∞ := ne_of_lt (hqp.trans_le le_top)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le Fact.out)) hq
  have hlt := (ENNReal.toReal_lt_toReal hq hp).mpr hqp
  let r := q.toReal * p.toReal / (p.toReal - q.toReal)
  have hr : 0 < r := div_pos (mul_pos hq0 hp0) (sub_pos.mpr hlt)
  have hh : p.toReal.HolderTriple r q.toReal := ⟨by
    dsimp [r]
    field_simp
    ring, hp0, hr⟩
  exact ⟨fun i ↦ a i ^ (-(q.toReal / r)), (∑ i, a i ^ q.toReal) ^ (1 / r),
    fun i ↦ Real.rpow_nonneg (ha i).le _,
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i).le _) _,
    scalar_rescaling_bound hh a ha, (scalar_rescaling_norm hh a ha).le⟩

private lemma norm_latticePSum_le_of_rescaling {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {C : ℝ} (hC : ConvexWith p C T) (hqp : q < p) {n : ℕ}
    (x : Fin n → E) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hxa : ∀ i, ‖x i‖ ≤ a i) :
    ‖latticePSum q (fun i ↦ T (x i))‖ ≤ C * ‖WithLp.toLp q a‖ := by
  obtain ⟨w, K, hw, hK, hscalar, hnorm⟩ := exists_scalar_rescaling hqp a ha
  have hinput : ‖WithLp.toLp p (fun i ↦ ‖w i • x i‖)‖ ≤
      ‖WithLp.toLp p (fun i ↦ w i * a i)‖ := by
    apply norm_le_norm_of_abs_le_abs
    change ∀ i, |‖w i • x i‖| ≤ |w i * a i|
    simpa only [norm_smul, Real.norm_of_nonneg (hw _), abs_mul,
      abs_of_nonneg (hw _), abs_norm, abs_of_pos (ha _)] using
      fun i ↦ mul_le_mul_of_nonneg_left (hxa i) (hw i)
  have hout : ‖latticePSum p (fun i ↦ w i • T (x i))‖ ≤
      C * ‖WithLp.toLp p (fun i ↦ w i * a i)‖ := by
    simpa only [map_smul] using (hC.2 n (fun i ↦ w i • x i)).trans
      (mul_le_mul_of_nonneg_left hinput hC.1)
  have hlattice := latticePSum_le_of_scalar_bound (fun i ↦ T (x i)) w K hscalar
  calc
    ‖latticePSum q (fun i ↦ T (x i))‖ ≤
        ‖K • latticePSum p (fun i ↦ w i • T (x i))‖ :=
      norm_le_norm_of_abs_le_abs ((abs_of_nonneg (latticePSum_nonneg q _)).trans_le
        (hlattice.trans (le_abs_self _)))
    _ = K * ‖latticePSum p (fun i ↦ w i • T (x i))‖ :=
      norm_smul_of_nonneg hK _
    _ ≤ K * (C * ‖WithLp.toLp p (fun i ↦ w i * a i)‖) :=
      mul_le_mul_of_nonneg_left hout hK
    _ = C * (K * ‖WithLp.toLp p (fun i ↦ w i * a i)‖) := mul_left_comm _ _ _
    _ ≤ C * ‖WithLp.toLp q a‖ := mul_le_mul_of_nonneg_left hnorm hC.1

/-- Decreasing the exponent preserves every admissible operator convexity constant.
The exponents may include infinity and satisfy `1 ≤ q ≤ p`. -/
theorem ConvexWith.of_le {q : ℝ≥0∞} [Fact (1 ≤ q)] {C : ℝ}
    (hC : ConvexWith p C T) (hqp : q ≤ p) : ConvexWith q C T := by
  rcases hqp.eq_or_lt with hqp | hqp
  · subst q
    exact hC
  refine ⟨hC.1, fun n x ↦ ?_⟩
  have hcont : Continuous (fun δ : ℝ ↦ C *
      ‖WithLp.toLp q (fun i ↦ ‖x i‖ + δ)‖) :=
    continuous_const.mul (continuous_norm.comp ((PiLp.continuous_toLp q _).comp
      (continuous_pi fun _ ↦ continuous_const.add continuous_id)))
  have hlim := (hcont.tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact norm_latticePSum_le_of_rescaling hC hqp x (fun i ↦ ‖x i‖ + δ)
    (fun i ↦ add_pos_of_nonneg_of_pos (norm_nonneg _) hδ)
    (fun _ ↦ le_add_of_nonneg_right hδ.le)

/-- A p-convex operator is q-convex whenever `1 ≤ q ≤ p`.
This also applies when the original exponent is infinity. -/
theorem IsPConvexOp.of_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hT : IsPConvexOp p T) (hqp : q ≤ p) : IsPConvexOp q T :=
  hT.elim fun C hC ↦ ⟨C, hC.of_le hqp⟩

/-- A p-convex Banach lattice is q-convex whenever `1 ≤ q ≤ p`.
The result follows by applying exponent monotonicity to the identity operator. -/
theorem IsPConvex.of_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hX : IsPConvex p X) (hqp : q ≤ p) : IsPConvex q X :=
  IsPConvexOp.of_le hX hqp

/-- Every bounded linear operator into a Banach lattice is 1-convex
with its operator norm as an admissible constant. -/
theorem convexWith_one (T : E →L[ℝ] X) : ConvexWith 1 ‖T‖ T := by
  refine ⟨norm_nonneg _, fun n x ↦ ?_⟩
  simp only [latticePSum_one, PiLp.norm_eq_of_L1, norm_norm]
  calc
    ‖∑ i, |T (x i)|‖ ≤ ∑ i, ‖T (x i)‖ := by
      simpa only [norm_abs_eq_norm] using
        norm_sum_le (Finset.univ : Finset (Fin n)) (fun i ↦ |T (x i)|)
    _ ≤ ∑ i, ‖T‖ * ‖x i‖ := Finset.sum_le_sum fun i _ ↦ T.le_opNorm (x i)
    _ = ‖T‖ * ∑ i, ‖x i‖ := (Finset.mul_sum ..).symm

/-- Every bounded linear operator from a real normed space into a Banach lattice
is 1-convex. Completeness of the domain is not required. -/
theorem isPConvexOp_one (T : E →L[ℝ] X) : IsPConvexOp 1 T :=
  ⟨‖T‖, convexWith_one T⟩

/-- At exponent one, the optimal convexity constant of an operator
is exactly its operator norm. -/
@[simp]
theorem convexityConstant_one (T : E →L[ℝ] X) : convexityConstant 1 T = ‖T‖ :=
  le_antisymm (convexWith_one T).convexityConstant_le
    (isPConvexOp_one T).norm_le_convexityConstant

/-- The identity on any Banach lattice satisfies the 1-convexity estimate
with constant one, by the triangle inequality and the lattice norm identity. -/
theorem convexWith_one_id : ConvexWith 1 1 (ContinuousLinearMap.id ℝ X) :=
  (convexWith_one _).mono ContinuousLinearMap.norm_id_le

/-- Every Banach lattice is 1-convex.
The identity operator admits the constant one. -/
theorem isPConvex_one : IsPConvex 1 X :=
  ⟨1, convexWith_one_id⟩

/-- A closed vector sublattice inherits every p-convexity constant
of the identity on the ambient Banach lattice. -/
theorem ConvexWith.id_sublattice {C : ℝ}
    (hC : ConvexWith p C (ContinuousLinearMap.id ℝ X))
    (Y : VectorSublattice X) (hY : IsClosed (Y : Set X)) :
    letI := Y.banachLatticeCoe hY
    ConvexWith p C (ContinuousLinearMap.id ℝ Y) := by
  letI := Y.banachLatticeCoe hY
  refine ⟨hC.1, fun n x ↦ ?_⟩
  have hmap := latticePSum_map p Y.subtype x
  change ‖((latticePSum p x : Y) : X)‖ ≤
    C * ‖WithLp.toLp p (fun i ↦ ‖(x i : X)‖)‖
  rw [show ((latticePSum p x : Y) : X) = latticePSum p (fun i ↦ (x i : X)) from hmap]
  exact hC.2 n (fun i ↦ (x i : X))

/-- Every closed vector sublattice of a p-convex Banach lattice is p-convex.
It carries the norm and lattice operations induced by the ambient space. -/
theorem IsPConvex.sublattice (hX : IsPConvex p X)
    (Y : VectorSublattice X) (hY : IsClosed (Y : Set X)) :
    letI := Y.banachLatticeCoe hY
    IsPConvex p Y :=
  letI := Y.banachLatticeCoe hY
  hX.elim fun C hC ↦ ⟨C, hC.id_sublattice Y hY⟩
