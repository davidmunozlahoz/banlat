import BanLat.Basic

/-!
# Order convergence

This file introduces order convergence of nets in a vector lattice. The definition uses a
separate directed regulator net decreasing to zero, so the regulator need not have the same
index set as the net being controlled.
-/

universe u v

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-- A net `u` **order converges** to `x` if its tails are eventually controlled
by a separate decreasing regulator net with greatest lower bound zero. -/
def OrderConvergesTo {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (u : ι → X) (x : X) : Prop :=
  ∃ (κ : Type u) (_ : Preorder κ) (_ : IsDirected κ (· ≤ ·)) (_ : Nonempty κ),
    ∃ r : κ → X,
      Antitone r ∧
        (∀ k, 0 ≤ r k) ∧
        IsGLB (Set.range r) 0 ∧
        ∀ k, ∀ᶠ i in Filter.atTop, |u i - x| ≤ r k

omit [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] in
private theorem isDirected_prod {κ τ : Type u} [Preorder κ] [Preorder τ]
    [IsDirected κ (· ≤ ·)] [IsDirected τ (· ≤ ·)] :
    IsDirected (κ × τ) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
  obtain ⟨l, hal, hbl⟩ := directed_of (· ≤ ·) a.2 b.2
  exact ⟨(k, l), ⟨hak, hal⟩, ⟨hbk, hbl⟩⟩

private theorem isGLB_range_add {κ τ : Type u} (r : κ → X) (s : τ → X)
    (hr : IsGLB (Set.range r) 0) (hs : IsGLB (Set.range s) 0) :
    IsGLB (Set.range (fun p : κ × τ => r p.1 + s p.2)) 0 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨k, l⟩, rfl⟩
    exact add_nonneg (hr.1 ⟨k, rfl⟩) (hs.1 ⟨l, rfl⟩)
  · intro w hw
    have hw_s : w ∈ lowerBounds (Set.range s) := by
      rintro _ ⟨l, rfl⟩
      have hw_r : w - s l ∈ lowerBounds (Set.range r) := by
        rintro _ ⟨k, rfl⟩
        exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hw ⟨(k, l), rfl⟩)
      exact sub_nonpos.mp (hr.2 hw_r)
    exact hs.2 hw_s

private theorem abs_sup_sub_sup_le_add (a b c d : X) :
    |(a ⊔ b) - (c ⊔ d)| ≤ |a - c| + |b - d| := by
  calc
    |(a ⊔ b) - (c ⊔ d)|
        = |((a ⊔ b) - (c ⊔ b)) + ((c ⊔ b) - (c ⊔ d))| := by
          congr 1
          abel
    _ ≤ |(a ⊔ b) - (c ⊔ b)| + |(c ⊔ b) - (c ⊔ d)| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      exact add_le_add (abs_sup_sub_sup_le_abs a c b) (by
        rw [sup_comm c b, sup_comm c d]
        exact abs_sup_sub_sup_le_abs b d c)

private theorem abs_inf_sub_inf_le_add (a b c d : X) :
    |(a ⊓ b) - (c ⊓ d)| ≤ |a - c| + |b - d| := by
  calc
    |(a ⊓ b) - (c ⊓ d)|
        = |((a ⊓ b) - (c ⊓ b)) + ((c ⊓ b) - (c ⊓ d))| := by
          congr 1
          abel
    _ ≤ |(a ⊓ b) - (c ⊓ b)| + |(c ⊓ b) - (c ⊓ d)| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      exact add_le_add (abs_inf_sub_inf_le_abs a c b) (by
        rw [inf_comm c b, inf_comm c d]
        exact abs_inf_sub_inf_le_abs b d c)

omit [AddCommGroup X] [IsOrderedAddMonoid X] in
private theorem isDirected_range_monotone {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {u : ι → X} (hmono : Monotone u) :
    IsDirected (Set.range u) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  rcases a.2 with ⟨i, hi⟩
  rcases b.2 with ⟨j, hj⟩
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  exact ⟨⟨u k, ⟨k, rfl⟩⟩, by
    change (a : X) ≤ u k
    simpa [← hi] using hmono hik, by
    change (b : X) ≤ u k
    simpa [← hj] using hmono hjk⟩

/-- An increasing net order converges to its least upper bound. -/
theorem orderConvergesTo_of_monotone_isLUB {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x : X}
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) :
    OrderConvergesTo u x := by
  letI : Nonempty (Set.range u) := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨⟨u i, ⟨i, rfl⟩⟩⟩
  refine ⟨Set.range u, inferInstance, isDirected_range_monotone hmono, inferInstance,
    fun y => x - y.1, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact sub_le_sub_left (show (a : X) ≤ (b : X) from h) x
  · rintro ⟨_, i, rfl⟩
    exact sub_nonneg.mpr (hlub.1 ⟨i, rfl⟩)
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨⟨_, i, rfl⟩, rfl⟩
      exact sub_nonneg.mpr (hlub.1 ⟨i, rfl⟩)
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, y ≤ x - w := by
        rintro _ ⟨i, rfl⟩
        exact le_sub_comm.mp (hw ⟨⟨u i, ⟨i, rfl⟩⟩, rfl⟩)
      have h := hlub.2 hlb
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  · intro k
    rcases k.2 with ⟨j, hj⟩
    refine Filter.eventually_atTop.mpr ⟨j, fun i hij => ?_⟩
    have hix : u i ≤ x := hlub.1 ⟨i, rfl⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hix), neg_sub]
    simpa [hj] using sub_le_sub_left (hmono hij) x

namespace OrderConvergesTo

/-- Addition is order continuous. -/
theorem add {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i + v i) (x + y) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  rcases hv with ⟨τ, hτpre, hτdir, hτnon, s, hsanti, hsnn, hsglb, hsevent⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκnon
  letI : Preorder τ := hτpre
  letI : IsDirected τ (· ≤ ·) := hτdir
  letI : Nonempty τ := hτnon
  letI : IsDirected (κ × τ) (· ≤ ·) := isDirected_prod
  refine ⟨κ × τ, inferInstance, inferInstance, inferInstance,
    fun p => r p.1 + s p.2, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    exact add_le_add (hranti hpq.1) (hsanti hpq.2)
  · exact fun p => add_nonneg (hrnn p.1) (hsnn p.2)
  · exact isGLB_range_add r s hrglb hsglb
  · intro p
    exact ((hrevent p.1).and (hsevent p.2)).mono fun i hi => by
      calc
        |u i + v i - (x + y)| = |(u i - x) + (v i - y)| := by
          congr 1
          abel
        _ ≤ |u i - x| + |v i - y| := abs_add_le _ _
        _ ≤ r p.1 + s p.2 := add_le_add hi.1 hi.2

omit [IsOrderedAddMonoid X] in
/-- Negation is order continuous. -/
theorem neg {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => -u i) (-x) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, r, hranti, hrnn, hrglb, ?_⟩
  intro k
  exact (hrevent k).mono fun i hi => by
    calc
      |-u i - -x| = |-(u i - x)| := by
        congr 1
        abel
      _ = |u i - x| := abs_neg _
      _ ≤ r k := hi

/-- Subtraction is order continuous. -/
theorem sub {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i - v i) (x - y) := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

/-- Scalar multiplication is order continuous. -/
theorem smul [VectorLattice X] (a : ℝ) {ι : Type v} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → X} {x : X}
    (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => a • u i) (a • x) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκnon
  refine ⟨κ, inferInstance, inferInstance, inferInstance, fun k => |a| • r k, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    exact smul_le_smul_of_nonneg_left (hranti hkl) (abs_nonneg a)
  · exact fun k => smul_nonneg (abs_nonneg a) (hrnn k)
  · have h := isGLB_smul_of_nonneg (X := X) (lam := |a|) (abs_nonneg a) hrglb
    have hset :
        Set.range (fun k => |a| • r k) = (fun z => |a| • z) '' Set.range r := by
      ext z
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨r k, ⟨k, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, rfl⟩
    simpa [hset] using h
  · intro k
    exact (hrevent k).mono fun i hi => by
      calc
        |a • u i - a • x| = |a • (u i - x)| := by
          rw [smul_sub]
        _ = |a| • |u i - x| := abs_smul' (X := X) (x := u i - x) a
        _ ≤ |a| • r k := smul_le_smul_of_nonneg_left hi (abs_nonneg a)

/-- Supremum is order continuous. -/
theorem sup {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i ⊔ v i) (x ⊔ y) := by
  rcases hu with ⟨κ, hκpre, hκdir, hκnon, r, hranti, hrnn, hrglb, hrevent⟩
  rcases hv with ⟨τ, hτpre, hτdir, hτnon, s, hsanti, hsnn, hsglb, hsevent⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκnon
  letI : Preorder τ := hτpre
  letI : IsDirected τ (· ≤ ·) := hτdir
  letI : Nonempty τ := hτnon
  letI : IsDirected (κ × τ) (· ≤ ·) := isDirected_prod
  refine ⟨κ × τ, inferInstance, inferInstance, inferInstance,
    fun p => r p.1 + s p.2, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    exact add_le_add (hranti hpq.1) (hsanti hpq.2)
  · exact fun p => add_nonneg (hrnn p.1) (hsnn p.2)
  · exact isGLB_range_add r s hrglb hsglb
  · intro p
    exact ((hrevent p.1).and (hsevent p.2)).mono fun i hi => by
      exact (abs_sup_sub_sup_le_add (u i) (v i) x y).trans (add_le_add hi.1 hi.2)

/-- Infimum is order continuous. -/
theorem inf {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i ⊓ v i) (x ⊓ y) := by
  simpa [neg_sup] using (hu.neg.sup hv.neg).neg

/-- Absolute value is order continuous. -/
theorem abs {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => |u i|) |x| := by
  simpa [abs] using hu.sup hu.neg

end OrderConvergesTo
