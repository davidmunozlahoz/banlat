/-
Authors: Pedro Tradacete
-/

import BanLat.Convergences.Order

/-!
# σ-order convergence

A net σ-order converges when its tails are controlled by a decreasing sequence
with greatest lower bound zero. This implies order convergence and is preserved
by the vector lattice operations. Monotone sequences σ-order converge to their
least upper bounds or greatest lower bounds when these exist.
-/

universe u v

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- A net `u` σ-order converges to `x` if its tails are eventually controlled by
a decreasing sequence of nonnegative bounds with greatest lower bound zero. -/
def SigmaOrderConvergesTo {ι : Type v} [Preorder ι] (u : ι → X) (x : X) : Prop :=
  ∃ r : ℕ → X, Antitone r ∧ (∀ n, 0 ≤ r n) ∧ IsGLB (Set.range r) 0 ∧
    ∀ n, ∀ᶠ i in Filter.atTop, |u i - x| ≤ r n

/-- A constant net σ-order converges to its constant value. -/
theorem sigmaOrderConvergesTo_const {ι : Type v} [Preorder ι] (x : X) :
    SigmaOrderConvergesTo (fun _ : ι ↦ x) x := by
  refine ⟨fun _ ↦ 0, fun _ _ _ ↦ le_rfl, fun _ ↦ le_rfl, ?_,
    fun _ ↦ Filter.Eventually.of_forall fun _ ↦ ?_⟩
  all_goals simp

private lemma isGLB_zero_range_add {r s : ℕ → X} (hr : Antitone r) (hs : Antitone s)
    (hrglb : IsGLB (Set.range r) 0) (hsglb : IsGLB (Set.range s) 0) :
    IsGLB (Set.range fun n ↦ r n + s n) 0 := by
  refine ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ add_nonneg (hrglb.1 ⟨n, rfl⟩)
    (hsglb.1 ⟨n, rfl⟩), ?_⟩
  exact fun _ hb ↦ by simpa only [add_zero] using
    ((orderConvergesTo_of_antitone_isGLB hr hrglb).add
      (orderConvergesTo_of_antitone_isGLB hs hsglb)).forall_le (fun n ↦ hb ⟨n, rfl⟩)

namespace SigmaOrderConvergesTo

omit [IsOrderedAddMonoid X] in
/-- σ-order convergence implies order convergence. -/
theorem orderConvergesTo {ι : Type v} [Preorder ι] {u : ι → X} {x : X}
    (hu : SigmaOrderConvergesTo u x) : OrderConvergesTo u x := by
  rcases hu with ⟨r, hr, hrnn, hrglb, hrevent⟩
  exact ⟨ULift.{u} ℕ, inferInstance, inferInstance, inferInstance, fun n ↦ r n.down,
    fun _ _ h ↦ hr h, fun n ↦ hrnn n.down,
    (ULift.down_surjective.range_comp r).symm ▸ hrglb, fun n ↦ hrevent n.down⟩

/-- Addition preserves σ-order convergence. -/
theorem add {ι : Type v} [Preorder ι] {u v : ι → X} {x y : X}
    (hu : SigmaOrderConvergesTo u x) (hv : SigmaOrderConvergesTo v y) :
    SigmaOrderConvergesTo (fun i ↦ u i + v i) (x + y) := by
  rcases hu with ⟨r, hr, hrnn, hrglb, hrevent⟩
  rcases hv with ⟨s, hs, hsnn, hsglb, hsevent⟩
  refine ⟨fun n ↦ r n + s n, fun _ _ h ↦ add_le_add (hr h) (hs h),
    fun n ↦ add_nonneg (hrnn n) (hsnn n), isGLB_zero_range_add hr hs hrglb hsglb,
    fun n ↦ ((hrevent n).and (hsevent n)).mono fun i hi ↦ ?_⟩
  simpa only [add_sub_add_comm] using
    (abs_add_le (u i - x) (v i - y)).trans (add_le_add hi.1 hi.2)

omit [IsOrderedAddMonoid X] in
/-- Negation preserves σ-order convergence. -/
theorem neg {ι : Type v} [Preorder ι] {u : ι → X} {x : X}
    (hu : SigmaOrderConvergesTo u x) : SigmaOrderConvergesTo (fun i ↦ -u i) (-x) := by
  rcases hu with ⟨r, hr, hrnn, hrglb, hrevent⟩
  exact ⟨r, hr, hrnn, hrglb, fun n ↦ by
    simpa only [neg_sub_neg, abs_sub_comm] using hrevent n⟩

/-- Subtraction preserves σ-order convergence. -/
theorem sub {ι : Type v} [Preorder ι] {u v : ι → X} {x y : X}
    (hu : SigmaOrderConvergesTo u x) (hv : SigmaOrderConvergesTo v y) :
    SigmaOrderConvergesTo (fun i ↦ u i - v i) (x - y) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

/-- Multiplication by a fixed real scalar preserves σ-order convergence. -/
theorem smul [VectorLattice X] (a : ℝ) {ι : Type v} [Preorder ι]
    {u : ι → X} {x : X} (hu : SigmaOrderConvergesTo u x) :
    SigmaOrderConvergesTo (fun i ↦ a • u i) (a • x) := by
  rcases hu with ⟨r, hr, hrnn, hrglb, hrevent⟩
  refine ⟨fun n ↦ |a| • r n,
    fun _ _ h ↦ smul_le_smul_of_nonneg_left (hr h) (abs_nonneg a),
    fun n ↦ smul_nonneg (abs_nonneg a) (hrnn n), ?_,
    fun n ↦ (hrevent n).mono fun i hi ↦ ?_⟩
  · simpa only [← Set.range_comp, Function.comp_def, smul_zero] using
      isGLB_smul_of_nonneg (abs_nonneg a) hrglb
  · simpa only [← smul_sub, abs_smul'] using
      smul_le_smul_of_nonneg_left hi (abs_nonneg a)

/-- Supremum preserves σ-order convergence. -/
theorem sup {ι : Type v} [Preorder ι] {u v : ι → X} {x y : X}
    (hu : SigmaOrderConvergesTo u x) (hv : SigmaOrderConvergesTo v y) :
    SigmaOrderConvergesTo (fun i ↦ u i ⊔ v i) (x ⊔ y) := by
  rcases hu with ⟨r, hr, hrnn, hrglb, hrevent⟩
  rcases hv with ⟨s, hs, hsnn, hsglb, hsevent⟩
  exact ⟨fun n ↦ r n + s n, fun _ _ h ↦ add_le_add (hr h) (hs h),
    fun n ↦ add_nonneg (hrnn n) (hsnn n), isGLB_zero_range_add hr hs hrglb hsglb,
    fun n ↦ ((hrevent n).and (hsevent n)).mono fun i hi ↦
      (abs_sup_sub_sup_le_add (u i) (v i) x y).trans (add_le_add hi.1 hi.2)⟩

/-- Infimum preserves σ-order convergence. -/
theorem inf {ι : Type v} [Preorder ι] {u v : ι → X} {x y : X}
    (hu : SigmaOrderConvergesTo u x) (hv : SigmaOrderConvergesTo v y) :
    SigmaOrderConvergesTo (fun i ↦ u i ⊓ v i) (x ⊓ y) := by
  simpa only [neg_sup, neg_neg] using (hu.neg.sup hv.neg).neg

/-- Absolute value preserves σ-order convergence. -/
theorem abs {ι : Type v} [Preorder ι] {u : ι → X} {x : X}
    (hu : SigmaOrderConvergesTo u x) : SigmaOrderConvergesTo (fun i ↦ |u i|) |x| :=
  hu.sup hu.neg

/-- A pointwise nonnegative σ-order-convergent net has a nonnegative limit. -/
theorem nonneg {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hu : SigmaOrderConvergesTo u x) (hnn : ∀ i, 0 ≤ u i) :
    0 ≤ x :=
  hu.orderConvergesTo.nonneg hnn

/-- σ-order limits respect pointwise order between nets with the same index set. -/
theorem le {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u v : ι → X} {x y : X} (hu : SigmaOrderConvergesTo u x)
    (hv : SigmaOrderConvergesTo v y) (hle : ∀ i, u i ≤ v i) : x ≤ y :=
  hu.orderConvergesTo.le hv.orderConvergesTo hle

/-- A pointwise upper bound of a σ-order-convergent net also bounds its limit. -/
theorem le_of_forall_le {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x b : X} (hu : SigmaOrderConvergesTo u x) (hub : ∀ i, u i ≤ b) :
    x ≤ b :=
  hu.orderConvergesTo.le_of_forall_le hub

/-- A pointwise lower bound of a σ-order-convergent net also bounds its limit. -/
theorem forall_le {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {a x : X} (hu : SigmaOrderConvergesTo u x) (hau : ∀ i, a ≤ u i) :
    a ≤ x :=
  hu.orderConvergesTo.forall_le hau

end SigmaOrderConvergesTo

/-- A decreasing sequence σ-order converges to its greatest lower bound (if it exists). -/
theorem sigmaOrderConvergesTo_of_antitone_isGLB {u : ℕ → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) : SigmaOrderConvergesTo u x := by
  have hnn : ∀ n, 0 ≤ u n - x := fun n ↦ sub_nonneg.mpr (hglb.1 ⟨n, rfl⟩)
  refine ⟨fun n ↦ u n - x, fun _ _ h ↦ sub_le_sub_right (hanti h) x, hnn,
    ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ hnn n, fun b hb ↦ ?_⟩, fun n ↦ ?_⟩
  · exact add_le_iff_nonpos_left.mp (hglb.2 fun _ ⟨n, hn⟩ ↦
      hn ▸ le_sub_iff_add_le.mp (hb ⟨n, rfl⟩))
  · exact Filter.eventually_atTop.mpr ⟨n, fun m hnm ↦ by
      simpa only [abs_of_nonneg (hnn m)] using sub_le_sub_right (hanti hnm) x⟩

/-- An increasing sequence σ-order converges to its least upper bound (if it exists). -/
theorem sigmaOrderConvergesTo_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) : SigmaOrderConvergesTo u x := by
  have hglb : IsGLB (Set.range fun n ↦ -u n) (-x) := by
    simpa only [Set.neg_range] using hlub.neg
  simpa only [neg_neg] using
    (sigmaOrderConvergesTo_of_antitone_isGLB (fun _ _ h ↦ neg_le_neg (hmono h)) hglb).neg
