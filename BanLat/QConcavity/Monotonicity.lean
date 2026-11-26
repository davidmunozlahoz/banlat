/-
Authors: Pedro Tradacete
-/

import BanLat.QConcavity.Duality

/-!
# Monotonicity of concavity exponents

Increasing the exponent preserves operator concavity and every admissible constant.
The proof uses duality and the corresponding monotonicity theorem for convexity.
-/

open scoped ENNReal

/-- Ordered exponents at least one have conjugate exponents in the reverse order.
The inverse formula includes the conjugate pair consisting of one and infinity. -/
private lemma exists_holderConjugate_antitone {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r) :
    ∃ p s : ℝ≥0∞, q.HolderConjugate p ∧ r.HolderConjugate s ∧ s ≤ p := by
  let p := (1 - q⁻¹)⁻¹
  let s := (1 - r⁻¹)⁻¹
  have hp : q.HolderConjugate p := ENNReal.holderConjugate_iff.mpr (by
    dsimp [p]
    rw [inv_inv, add_tsub_cancel_of_le]
    exact ENNReal.inv_le_one.mpr hq)
  have hs : r.HolderConjugate s := ENNReal.holderConjugate_iff.mpr (by
    dsimp [s]
    rw [inv_inv, add_tsub_cancel_of_le]
    exact ENNReal.inv_le_one.mpr (hq.trans hqr))
  exact ⟨p, s, hp, hs,
    ENNReal.inv_le_inv.mpr (tsub_le_tsub_left (ENNReal.inv_le_inv.mpr hqr) 1)⟩

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] {T : X →L[ℝ] E}

/-- If an operator is q-concave with constant `C`, and `1 ≤ q ≤ r`, then it is also r-concave with
constant `C`. -/
theorem ConcaveWith.of_le {C : ℝ} (hC : ConcaveWith q C T) (hqr : q ≤ r) :
    ConcaveWith r C T := by
  obtain ⟨p, s, hp, hs, hsp⟩ := exists_holderConjugate_antitone (Fact.out : 1 ≤ q) hqr
  let := hp
  let := hs
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ s) := ⟨ENNReal.HolderConjugate.one_le s r⟩
  have hdual :=
    (concaveWith_iff_convexWith_precomp (p := p) (q := q) (T := T) (C := C)).mp hC
  exact (concaveWith_iff_convexWith_precomp (p := s) (q := r) (T := T) (C := C)).mpr
    (hdual.of_le hsp)

/-- A q-concave operator is r-concave whenever `1 ≤ q ≤ r`. -/
theorem IsQConcaveOp.of_le (hT : IsQConcaveOp q T) (hqr : q ≤ r) : IsQConcaveOp r T :=
  hT.elim fun C hC ↦ ⟨C, hC.of_le hqr⟩

/-- A q-concave Banach lattice is r-concave whenever `1 ≤ q ≤ r`. -/
theorem IsQConcave.of_le (hX : IsQConcave q X) (hqr : q ≤ r) : IsQConcave r X :=
  IsQConcaveOp.of_le hX hqr

/-- If an operator is q-concave, then its optimal r-concavity constant is less than or equal to
the q-concavity constant whenever `1 ≤ q ≤ r`. -/
theorem IsQConcaveOp.concavityConstant_le_of_le (hT : IsQConcaveOp q T) (hqr : q ≤ r) :
    concavityConstant r T ≤ concavityConstant q T :=
  (hT.concavityConstant_spec.of_le hqr).concavityConstant_le
