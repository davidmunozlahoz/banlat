import BanLat.Operators.OrderContinuous

/-!
# Carriers of order bounded operators

This file defines the null ideal and carrier band of an order bounded operator between vector
lattices. It proves that the null ideal of an order-continuous operator is a band, and
characterizes disjointness of order-continuous real-valued order bounded operators in terms of
their carriers and null ideals.
-/

universe u v

namespace OrderBoundedHom

variable {X : Type u} {Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [ConditionallyCompleteLattice Y] [IsOrderedAddMonoid X]
  [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

private noncomputable def nullSet (T : OrderBoundedHom X Y) : Set X :=
  {x | (|T| : OrderBoundedHom X Y) |x| = 0}

private lemma modulus_positive (T : OrderBoundedHom X Y) :
    Positive (|T| : OrderBoundedHom X Y).toLinearMap := fun x hx => by
  convert OrderBoundedHom.le_iff.mp (abs_nonneg T) x hx using 1

private lemma modulus_monotone (T : OrderBoundedHom X Y) :
    Monotone (|T| : OrderBoundedHom X Y).toLinearMap :=
  Positive.monotone_iff.mpr (modulus_positive T)

private lemma nullSet_zero (T : OrderBoundedHom X Y) :
    (0 : X) ∈ nullSet T := by
  change (|T| : OrderBoundedHom X Y).toLinearMap |(0 : X)| = 0
  rw [abs_zero, map_zero]

private lemma nullSet_add (T : OrderBoundedHom X Y) {x y : X}
    (hx : x ∈ nullSet T) (hy : y ∈ nullSet T) :
    x + y ∈ nullSet T := by
  rw [nullSet] at hx hy ⊢
  change (|T| : OrderBoundedHom X Y).toLinearMap |x| = 0 at hx
  change (|T| : OrderBoundedHom X Y).toLinearMap |y| = 0 at hy
  apply le_antisymm
  · calc
      (|T| : OrderBoundedHom X Y) |x + y|
          ≤ (|T| : OrderBoundedHom X Y) (|x| + |y|) :=
            modulus_monotone T (abs_add_le x y)
      _ = 0 := by
        change (|T| : OrderBoundedHom X Y).toLinearMap (|x| + |y|) = 0
        rw [map_add, hx, hy, add_zero]
  · exact modulus_positive T _ (abs_nonneg _)

private lemma nullSet_smul (T : OrderBoundedHom X Y) (c : ℝ) {x : X}
    (hx : x ∈ nullSet T) :
    c • x ∈ nullSet T := by
  change (|T| : OrderBoundedHom X Y).toLinearMap |x| = 0 at hx
  change (|T| : OrderBoundedHom X Y).toLinearMap |c • x| = 0
  rw [abs_smul']
  rw [map_smul, hx, smul_zero]

private lemma nullSet_solid (T : OrderBoundedHom X Y) {x y : X}
    (hx : x ∈ nullSet T) (hxy : |y| ≤ |x|) :
    y ∈ nullSet T := by
  rw [nullSet] at hx ⊢
  apply le_antisymm
  · exact (modulus_monotone T hxy).trans_eq hx
  · exact modulus_positive T _ (abs_nonneg _)

/-- The **null ideal** of an order bounded operator `T` consists of vectors whose
absolute value is annihilated by the modulus of `T`. -/
noncomputable def null (T : OrderBoundedHom X Y) : OrderIdeal X :=
  OrderIdeal.ofSolid
    { carrier := nullSet T
      add_mem' := by
        exact fun {x y} hx hy => nullSet_add T hx hy
      zero_mem' := by
        exact nullSet_zero T
      smul_mem' := by
        exact fun c {x} hx => nullSet_smul T c hx }
    (by
      exact fun x y hx hxy => nullSet_solid T hx hxy)

/-- Membership in the null ideal. -/
theorem mem_null {T : OrderBoundedHom X Y} {x : X} :
    x ∈ null T ↔ (|T| : OrderBoundedHom X Y) |x| = 0 := by
  rfl

/-- The **carrier** of an order bounded operator is the disjoint complement of
its null ideal. -/
noncomputable def carrier (T : OrderBoundedHom X Y) : Band X :=
  Band.disjointComplement (null T : Set X)

/-- Membership in the carrier. -/
theorem mem_carrier {T : OrderBoundedHom X Y} {x : X} :
    x ∈ carrier T ↔ ∀ y : X, y ∈ null T → IsVLDisjoint x y := by
  rfl

private lemma eq_zero_of_orderConvergesTo_const_zero
    {Z : Type v} [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {a : Z}
    (ha : OrderConvergesTo (fun _ : ι => (0 : Z)) a) :
    a = 0 := by
  rcases ha with ⟨κ, hκpre, hκdir, hκnon, r, _hranti, _hrnn, hrglb, hrevent⟩
  letI : Preorder κ := hκpre
  letI : IsDirected κ (· ≤ ·) := hκdir
  letI : Nonempty κ := hκnon
  have hle : |a| ≤ 0 := by
    apply hrglb.2
    rintro _ ⟨k, rfl⟩
    rcases (hrevent k).exists with ⟨i, hi⟩
    calc
      |a| = |(0 : Z) - a| := by rw [zero_sub, abs_neg]
      _ ≤ r k := hi
  exact (abs_eq_zero_iff_zero a).mp (le_antisymm hle (abs_nonneg a))

private theorem modulus_orderContinuous_of_orderContinuous {T : OrderBoundedHom X Y}
    (hT : IsOrderContinuousOp T.toLinearMap) :
    IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap := by
  obtain ⟨B, hB⟩ := OrderContinuousOp.ogasawara_theorem (X := X) (Y := Y)
  have hTmem : T ∈ (B : Set (OrderBoundedHom X Y)) := by
    rw [hB, OrderContinuousOp.mem_OrderContinuousOperator]
    exact hT
  have hAbsT : |T| ∈ (B : Set (OrderBoundedHom X Y)) :=
    B.toBand.abs_mem hTmem
  rw [hB] at hAbsT
  change IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap at hAbsT
  intro ι _ _ _ x a hx
  exact hAbsT (ι := ι) hx

private lemma null_sSup_mem_of_modulus_orderContinuous (T : OrderBoundedHom X Y)
    (hT : IsOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap)
    {S : Set X} (hS : S ⊆ (null T : Set X)) (hSpos : ∀ x ∈ S, 0 ≤ x)
    (hSdir : DirectedOn (· ≤ ·) S) (hSne : S.Nonempty) {x : X}
    (hx : IsLUB S x) :
    x ∈ null T := by
  let U : OrderBoundedHom X Y := |T|
  let ι : Type u := {y : X // y ∈ S}
  letI : Preorder ι := inferInstance
  haveI : IsDirected ι (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hcS, hac, hbc⟩ := hSdir (a : X) a.2 (b : X) b.2
    exact ⟨⟨c, hcS⟩, hac, hbc⟩⟩
  haveI : Nonempty ι := by
    obtain ⟨s, hs⟩ := hSne
    exact ⟨⟨s, hs⟩⟩
  let u : ι → X := fun s => s
  have hu_mono : Monotone u := fun _ _ h => h
  have hRange : Set.range u = S := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hxRange : IsLUB (Set.range u) x := by
    simpa [u, hRange] using hx
  have hxu : OrderConvergesTo u x :=
    orderConvergesTo_of_monotone_isLUB hu_mono hxRange
  have hUxu : OrderConvergesTo (fun s : ι => U.toLinearMap (u s)) (U.toLinearMap x) :=
    hT hxu
  have hU_zero : (fun s : ι => U.toLinearMap (u s)) = fun _ : ι => (0 : Y) := by
    funext s
    have hsnull : (s : X) ∈ null T := hS s.2
    have hspos : 0 ≤ (s : X) := hSpos s s.2
    have h := mem_null.mp hsnull
    simpa [U, u, abs_of_nonneg hspos] using h
  rw [hU_zero] at hUxu
  have hUx : U.toLinearMap x = 0 :=
    eq_zero_of_orderConvergesTo_const_zero hUxu
  have hx_nonneg : 0 ≤ x := by
    obtain ⟨s, hs⟩ := hSne
    exact (hSpos s hs).trans (hx.1 hs)
  rw [mem_null]
  simpa [U, abs_of_nonneg hx_nonneg] using hUx

/-- If an order bounded operator is order continuous, there is a band whose carrier is its
null ideal. -/
theorem exists_band_coe_eq_null_of_orderContinuous (T : OrderBoundedHom X Y)
    (hT : IsOrderContinuousOp T.toLinearMap) :
    ∃ B : Band X, (B : Set X) = (null T : Set X) := by
  refine ⟨Band.ofPosDirectedSSupMem (null T) ?_, rfl⟩
  intro S hS hSpos hSdir hSne x hx
  exact null_sSup_mem_of_modulus_orderContinuous T
    (modulus_orderContinuous_of_orderContinuous hT) hS hSpos hSdir hSne hx

section Nakano

variable [IsVLArchimedean X]

private lemma real_eq_zero_of_nonneg_of_forall_pos_le {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ε) :
    a = 0 := by
  refine le_antisymm ?_ ha
  by_contra hle
  have hpos : 0 < a := lt_of_not_ge hle
  have ha_half := h (a / 2) (by positivity)
  linarith

private lemma real_eq_zero_of_nonneg_of_le_geometric {a ε : ℝ} (ha : 0 ≤ a)
    (h : ∀ n : ℕ, a ≤ ε / 2 / (2 : ℝ) ^ n) :
    a = 0 := by
  refine le_antisymm ?_ ha
  by_contra hle
  have hpos : 0 < a := lt_of_not_ge hle
  have htend : Filter.Tendsto (fun n : ℕ => ε / 2 / (2 : ℝ) ^ n)
      Filter.atTop (nhds 0) := by
    simpa using (summable_geometric_two' ε).tendsto_atTop_zero
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, ε / 2 / (2 : ℝ) ^ n < a :=
    htend (isOpen_Iio.mem_nhds hpos)
  rcases hevent.exists with ⟨n, hn⟩
  linarith [h n]

private lemma sum_geometric_halves_le (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (∑ i ∈ Finset.range n, ε / 2 / (2 : ℝ) ^ i) ≤ ε := by
  calc
    (∑ i ∈ Finset.range n, ε / 2 / (2 : ℝ) ^ i)
        ≤ ∑' i : ℕ, ε / 2 / (2 : ℝ) ^ i := by
          exact Summable.sum_le_tsum _ (fun i _ => by positivity)
            (summable_geometric_two' ε)
    _ = ε := tsum_geometric_two' ε

private def prefixInf (y : ℕ → X) : ℕ → X
  | 0 => y 0
  | n + 1 => prefixInf y n ⊓ y (n + 1)

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] in
@[simp] private lemma prefixInf_zero (y : ℕ → X) :
    prefixInf y 0 = y 0 := rfl

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] in
@[simp] private lemma prefixInf_succ (y : ℕ → X) (n : ℕ) :
    prefixInf y (n + 1) = prefixInf y n ⊓ y (n + 1) := rfl

omit [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] in
private lemma prefixInf_nonneg {y : ℕ → X} (hy : ∀ n, 0 ≤ y n) :
    ∀ n, 0 ≤ prefixInf y n
  | 0 => by simpa using hy 0
  | n + 1 => by
      rw [prefixInf_succ]
      exact le_inf (prefixInf_nonneg hy n) (hy (n + 1))

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] in
private lemma prefixInf_le_of_le {y : ℕ → X} {k n : ℕ} (hkn : k ≤ n) :
    prefixInf y n ≤ y k := by
  induction n with
  | zero =>
      have hk : k = 0 := Nat.eq_zero_of_le_zero hkn
      subst hk
      simp
  | succ n ih =>
      by_cases hk : k = n + 1
      · subst hk
        rw [prefixInf_succ]
        exact inf_le_right
      · have hkle : k ≤ n := Nat.le_of_lt_succ (lt_of_le_of_ne hkn hk)
        rw [prefixInf_succ]
        exact inf_le_left.trans (ih hkle)

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] in
private lemma prefixInf_le_bound {y : ℕ → X} {x : X} (hyx : ∀ n, y n ≤ x) :
    ∀ n, prefixInf y n ≤ x
  | 0 => by simpa using hyx 0
  | n + 1 => by
      rw [prefixInf_succ]
      exact inf_le_left.trans (prefixInf_le_bound hyx n)

omit [AddCommGroup X] [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] in
private lemma prefixInf_antitone (y : ℕ → X) :
    Antitone (prefixInf y) := by
  intro n m hnm
  exact Nat.le_induction (le_refl _) (fun m _ hm => by
    rw [prefixInf_succ]
    exact inf_le_left.trans hm) m hnm

omit [VectorLattice X] [IsVLArchimedean X] in
private lemma sub_prefixInf_le_sum {x : X} {y : ℕ → X} (hyx : ∀ n, y n ≤ x) :
    ∀ n, x - prefixInf y n ≤ ∑ i ∈ Finset.range (n + 1), (x - y i)
  | 0 => by simp
  | n + 1 => by
      have hleft : 0 ≤ x - prefixInf y n :=
        sub_nonneg.mpr (prefixInf_le_bound hyx n)
      have hright : 0 ≤ x - y (n + 1) := sub_nonneg.mpr (hyx (n + 1))
      calc
        x - prefixInf y (n + 1)
            = (x - prefixInf y n) ⊔ (x - y (n + 1)) := by
              rw [prefixInf_succ, sub_inf]
        _ ≤ (x - prefixInf y n) + (x - y (n + 1)) :=
              sup_le (le_add_of_nonneg_right hright) (le_add_of_nonneg_left hleft)
        _ ≤ (∑ i ∈ Finset.range (n + 1), (x - y i)) + (x - y (n + 1)) := by
              exact add_le_add (sub_prefixInf_le_sum hyx n) le_rfl
        _ = ∑ i ∈ Finset.range (n + 2), (x - y i) := by
              simpa [Nat.add_assoc] using
                (Finset.sum_range_succ (fun i => x - y i) (n + 1)).symm

omit [IsVLArchimedean X] in
private lemma exists_decomposition_lt_of_disjoint_positive {f g : OrderBoundedHom X ℝ}
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hfg : IsVLDisjoint f g)
    {x : X} (hx : 0 ≤ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : X, 0 ≤ y ∧ y ≤ x ∧ f y + g (x - y) < ε := by
  have hfg_inf : f ⊓ g = 0 := inf_eq_zero_of_isVLDisjoint hf0 hg0 hfg
  let S : Set ℝ :=
    {w | ∃ y z : X, 0 ≤ y ∧ 0 ≤ z ∧ y + z = x ∧ w = f y + g z}
  have hglb : IsGLB S 0 := by
    simpa [S, hfg_inf] using (isGLB_inf_apply (f := f) (g := g) hx)
  have hex : ∃ w ∈ S, w < ε := by
    by_contra hnone
    push Not at hnone
    have hε_lb : ε ∈ lowerBounds S := fun w hw => hnone w hw
    exact (not_le_of_gt hε) (hglb.2 hε_lb)
  rcases hex with ⟨_, ⟨y, z, hy, hz, hyz, rfl⟩, hlt⟩
  refine ⟨y, hy, hyz ▸ le_add_of_nonneg_right hz, ?_⟩
  simpa [eq_sub_of_add_eq' hyz] using hlt

omit [IsVLArchimedean X] in
private lemma apply_eq_zero_of_mem_carrier_of_disjoint_positive
    {f g : OrderBoundedHom X ℝ} (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hgoc : IsOrderContinuousOp g.toLinearMap) (hfg : IsVLDisjoint f g)
    {x : X} (hx0 : 0 ≤ x) (hxC : x ∈ carrier f) :
    g x = 0 := by
  have hf_pos : Positive f.toLinearMap := le_iff.mp hf0
  have hg_pos : Positive g.toLinearMap := le_iff.mp hg0
  have hf_mono : Monotone f.toLinearMap := Positive.monotone_iff.mpr hf_pos
  have hg_mono : Monotone g.toLinearMap := Positive.monotone_iff.mpr hg_pos
  refine real_eq_zero_of_nonneg_of_forall_pos_le (hg_pos x hx0) ?_
  intro ε hε
  have hdecomp : ∀ n : ℕ, ∃ y : X, 0 ≤ y ∧ y ≤ x ∧
      f y + g (x - y) < ε / 2 / (2 : ℝ) ^ n := fun n =>
    exists_decomposition_lt_of_disjoint_positive hf0 hg0 hfg hx0 (by positivity)
  choose y hy0 hyx hy_small using hdecomp
  let z : ℕ → X := prefixInf y
  have hz_nn : ∀ n, 0 ≤ z n := prefixInf_nonneg hy0
  have hz_le_x : ∀ n, z n ≤ x := prefixInf_le_bound hyx
  have hz_glb : IsGLB (Set.range z) 0 := by
    refine ⟨?_, fun w hw => ?_⟩
    · rintro a ⟨n, ha⟩
      rw [← ha]
      exact hz_nn n
    set v : X := w⁺ with hv_def
    have hv_nn : 0 ≤ v := by simpa [v] using posPart_nonneg w
    have hv_le_z : ∀ n, v ≤ z n := fun n => by
      rw [hv_def]
      exact sup_le (hw ⟨n, rfl⟩) (hz_nn n)
    have hv_le_y : ∀ n, v ≤ y n := fun n =>
      (hv_le_z n).trans (prefixInf_le_of_le (le_refl n))
    have hv_le_x : v ≤ x := (hv_le_z 0).trans (hz_le_x 0)
    have hf_v_zero : f v = 0 := by
      refine real_eq_zero_of_nonneg_of_le_geometric (ε := ε) (hf_pos v hv_nn) ?_
      intro n
      calc
        f v ≤ f (y n) := hf_mono (hv_le_y n)
        _ ≤ f (y n) + g (x - y n) :=
            le_add_of_nonneg_right (hg_pos _ (sub_nonneg.mpr (hyx n)))
        _ ≤ ε / 2 / (2 : ℝ) ^ n := le_of_lt (hy_small n)
    have hv_null : v ∈ null f := by
      rw [mem_null, abs_of_nonneg hf0, abs_of_nonneg hv_nn, hf_v_zero]
    have hv_carrier : v ∈ carrier f :=
      (carrier f).solid hxC hv_nn hv_le_x
    have hdisj : IsVLDisjoint x v := mem_carrier.mp hxC v hv_null
    have hv_zero : v = 0 := by
      have hxv : x ⊓ v = 0 := by
        unfold IsVLDisjoint at hdisj
        rwa [abs_of_nonneg hx0, abs_of_nonneg hv_nn] at hdisj
      have hvx : v ⊓ x = 0 := by simpa [inf_comm] using hxv
      exact (inf_eq_left.mpr hv_le_x).symm.trans hvx
    exact (le_posPart w).trans_eq hv_zero
  have hz_anti_lift : Antitone (fun n : ULift.{u} ℕ => z n.down) := fun a b hab =>
    prefixInf_antitone y (show a.down ≤ b.down from hab)
  have hz_glb_lift : IsGLB (Set.range (fun n : ULift.{u} ℕ => z n.down)) 0 := by
    have hRange : Set.range (fun n : ULift.{u} ℕ => z n.down) = Set.range z := by
      ext w
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n.down, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨ULift.up n, rfl⟩
    simpa [hRange] using hz_glb
  have hz_order : OrderConvergesTo (fun n : ULift.{u} ℕ => z n.down) 0 :=
    orderConvergesTo_of_antitone_isGLB hz_anti_lift hz_glb_lift
  have hx_sub_order : OrderConvergesTo (fun n : ULift.{u} ℕ => x - z n.down) x := by
    simpa [sub_zero] using
      (orderConvergesTo_const (ι := ULift.{u} ℕ) x).sub hz_order
  have hg_order : OrderConvergesTo (fun n : ULift.{u} ℕ => g (x - z n.down)) (g x) :=
    hgoc hx_sub_order
  apply le_of_orderConvergesTo_of_forall_le hg_order
  intro n
  have hsum_bound :
      (∑ i ∈ Finset.range (n.down + 1), (f (y i) + g (x - y i))) ≤ ε := by
    calc
      (∑ i ∈ Finset.range (n.down + 1), (f (y i) + g (x - y i)))
          ≤ ∑ i ∈ Finset.range (n.down + 1), ε / 2 / (2 : ℝ) ^ i := by
            exact Finset.sum_le_sum fun i _ => le_of_lt (hy_small i)
      _ ≤ ε := sum_geometric_halves_le ε hε.le (n.down + 1)
  calc
    g (x - z n.down) ≤ g (∑ i ∈ Finset.range (n.down + 1), (x - y i)) :=
      hg_mono (sub_prefixInf_le_sum hyx n.down)
    _ = ∑ i ∈ Finset.range (n.down + 1), g (x - y i) := by
      exact map_sum g.toLinearMap (fun i => x - y i) (Finset.range (n.down + 1))
    _ ≤ ∑ i ∈ Finset.range (n.down + 1), (f (y i) + g (x - y i)) := by
      exact Finset.sum_le_sum fun i _ =>
        le_add_of_nonneg_left (hf_pos _ (hy0 i))
    _ ≤ ε := hsum_bound

omit [IsVLArchimedean X] in
private lemma carrier_subset_null_of_disjoint_positive {f g : OrderBoundedHom X ℝ}
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hgoc : IsOrderContinuousOp g.toLinearMap)
    (hfg : IsVLDisjoint f g) :
    (carrier f : Set X) ⊆ (null g : Set X) := by
  intro x hx
  have hx_abs : |x| ∈ carrier f := (carrier f).abs_mem hx
  have hzero := apply_eq_zero_of_mem_carrier_of_disjoint_positive
    hf0 hg0 hgoc hfg (abs_nonneg x) hx_abs
  change (|g| : OrderBoundedHom X ℝ) |x| = 0
  rw [abs_of_nonneg hg0]
  exact hzero

omit [IsVLArchimedean X] in
private lemma inf_orderContinuous_of_orderContinuous {f g : OrderBoundedHom X ℝ}
    (hf : IsOrderContinuousOp f.toLinearMap) (hg : IsOrderContinuousOp g.toLinearMap) :
    IsOrderContinuousOp (f ⊓ g).toLinearMap := by
  obtain ⟨B, hB⟩ := OrderContinuousOp.ogasawara_theorem (X := X) (Y := ℝ)
  have hfB : f ∈ (B : Set (OrderBoundedHom X ℝ)) := by
    rw [hB, OrderContinuousOp.mem_OrderContinuousOperator]
    exact hf
  have hgB : g ∈ (B : Set (OrderBoundedHom X ℝ)) := by
    rw [hB, OrderContinuousOp.mem_OrderContinuousOperator]
    exact hg
  have hfgB : f ⊓ g ∈ (B : Set (OrderBoundedHom X ℝ)) :=
    B.toBand.inf_mem hfB hgB
  rw [hB] at hfgB
  change IsOrderContinuousOp (f ⊓ g).toLinearMap at hfgB
  intro ι _ _ _ x a hx
  exact hfgB (ι := ι) hx

private lemma disjoint_of_carrier_subset_null_positive {f g : OrderBoundedHom X ℝ}
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf : IsOrderContinuousOp f.toLinearMap) (hg : IsOrderContinuousOp g.toLinearMap)
    (hsub : (carrier f : Set X) ⊆ (null g : Set X)) :
    IsVLDisjoint f g := by
  let h : OrderBoundedHom X ℝ := f ⊓ g
  have hh0 : 0 ≤ h := le_inf hf0 hg0
  have hhf : h ≤ f := inf_le_left
  have hhg : h ≤ g := inf_le_right
  have hh : IsOrderContinuousOp h.toLinearMap :=
    inf_orderContinuous_of_orderContinuous hf hg
  have hvanish : (null f : Set X) ∪ (carrier f : Set X) ⊆ (null h : Set X) := by
    rintro x (hx | hx)
    · change (|h| : OrderBoundedHom X ℝ) |x| = 0
      rw [abs_of_nonneg hh0]
      apply le_antisymm
      · have hx0 := mem_null.mp hx
        have hfx : f |x| = 0 := by
          simpa [abs_of_nonneg hf0] using hx0
        exact (le_iff.mp hhf |x| (abs_nonneg x)).trans_eq hfx
      · exact le_iff.mp hh0 |x| (abs_nonneg x)
    · change (|h| : OrderBoundedHom X ℝ) |x| = 0
      rw [abs_of_nonneg hh0]
      apply le_antisymm
      · have hx0 := mem_null.mp (hsub hx)
        have hgx : g |x| = 0 := by
          simpa [abs_of_nonneg hg0] using hx0
        exact (le_iff.mp hhg |x| (abs_nonneg x)).trans_eq hgx
      · exact le_iff.mp hh0 |x| (abs_nonneg x)
  obtain ⟨Bh, hBh⟩ := exists_band_coe_eq_null_of_orderContinuous h hh
  have hgen_le : Band.generated ((null f : Set X) ∪ (carrier f : Set X)) ≤ Bh := by
    apply Band.generated_le
    intro x hx
    rw [hBh]
    exact hvanish hx
  have hgen_top : Band.generated ((null f : Set X) ∪ (carrier f : Set X)) = ⊤ := by
    change Band.generated ((null f : Set X) ∪ (null f : Set X)ᵈ) = ⊤
    exact Band.generated_union_disjointComplement_eq_top (null f : Set X)
  have htop_le : (⊤ : Band X) ≤ Bh := by
    rw [← hgen_top]
    exact hgen_le
  have h_all_null : ∀ x : X, x ∈ null h := by
    intro x
    change x ∈ (null h : Set X)
    rw [← hBh]
    exact htop_le Band.mem_top
  have h_eq_zero : h = 0 := by
    ext x
    have hxnull := mem_null.mp (h_all_null x)
    have hh_abs : h |x| = 0 := by
      simpa [abs_of_nonneg hh0] using hxnull
    have hle : |h x| ≤ 0 := by
      exact (Positive.abs_le_map_abs (le_iff.mp hh0) x).trans_eq hh_abs
    exact (abs_eq_zero_iff_zero (h x)).mp (le_antisymm hle (abs_nonneg _))
  unfold IsVLDisjoint
  rw [abs_of_nonneg hf0, abs_of_nonneg hg0]
  exact h_eq_zero

omit [IsVLArchimedean X] in
private lemma null_abs_coe (T : OrderBoundedHom X ℝ) :
    (null (|T| : OrderBoundedHom X ℝ) : Set X) = (null T : Set X) := by
  ext x
  change (|(|T| : OrderBoundedHom X ℝ)| : OrderBoundedHom X ℝ) |x| = 0 ↔
    (|T| : OrderBoundedHom X ℝ) |x| = 0
  rw [abs_abs]

omit [IsVLArchimedean X] in
private lemma carrier_abs_coe (T : OrderBoundedHom X ℝ) :
    (carrier (|T| : OrderBoundedHom X ℝ) : Set X) = (carrier T : Set X) := by
  change ((null (|T| : OrderBoundedHom X ℝ) : Set X)ᵈ) = (null T : Set X)ᵈ
  rw [null_abs_coe T]

omit [IsVLArchimedean X] in
private lemma carrier_subset_null_of_disjoint {f g : OrderBoundedHom X ℝ}
    (_hf : IsOrderContinuousOp f.toLinearMap) (hg : IsOrderContinuousOp g.toLinearMap)
    (hfg : IsVLDisjoint f g) :
    (carrier f : Set X) ⊆ (null g : Set X) := by
  have hg_abs : IsOrderContinuousOp (|g| : OrderBoundedHom X ℝ).toLinearMap :=
    modulus_orderContinuous_of_orderContinuous (T := g) hg
  have hfg_abs : IsVLDisjoint (|f| : OrderBoundedHom X ℝ) (|g| : OrderBoundedHom X ℝ) := by
    unfold IsVLDisjoint at hfg ⊢
    simpa [abs_abs] using hfg
  have h := carrier_subset_null_of_disjoint_positive
    (abs_nonneg f) (abs_nonneg g) hg_abs hfg_abs
  intro x hx
  rw [← null_abs_coe g]
  apply h
  rwa [carrier_abs_coe f]

private lemma disjoint_of_carrier_subset_null {f g : OrderBoundedHom X ℝ}
    (hf : IsOrderContinuousOp f.toLinearMap) (hg : IsOrderContinuousOp g.toLinearMap)
    (hsub : (carrier f : Set X) ⊆ (null g : Set X)) :
    IsVLDisjoint f g := by
  have hf_abs : IsOrderContinuousOp (|f| : OrderBoundedHom X ℝ).toLinearMap :=
    modulus_orderContinuous_of_orderContinuous (T := f) hf
  have hg_abs : IsOrderContinuousOp (|g| : OrderBoundedHom X ℝ).toLinearMap :=
    modulus_orderContinuous_of_orderContinuous (T := g) hg
  have hsub_abs :
      (carrier (|f| : OrderBoundedHom X ℝ) : Set X) ⊆
        (null (|g| : OrderBoundedHom X ℝ) : Set X) := by
    intro x hx
    rw [null_abs_coe g]
    exact hsub (by rwa [carrier_abs_coe f] at hx)
  have hdisj_abs := disjoint_of_carrier_subset_null_positive
    (abs_nonneg f) (abs_nonneg g) hf_abs hg_abs hsub_abs
  unfold IsVLDisjoint at hdisj_abs ⊢
  simpa [abs_abs] using hdisj_abs

private lemma null_disjointComplement_disjointComplement_eq {T : OrderBoundedHom X ℝ}
    (hT : IsOrderContinuousOp T.toLinearMap) :
    (((null T : Set X)ᵈ)ᵈ) = (null T : Set X) := by
  obtain ⟨B, hB⟩ := exists_band_coe_eq_null_of_orderContinuous T hT
  rw [← hB]
  exact Band.eq_disjointComplement_disjointComplement B

private lemma disjointComplement_carrier_eq_null {T : OrderBoundedHom X ℝ}
    (hT : IsOrderContinuousOp T.toLinearMap) :
    (carrier T : Set X)ᵈ = (null T : Set X) := by
  change (((null T : Set X)ᵈ)ᵈ) = (null T : Set X)
  exact null_disjointComplement_disjointComplement_eq hT

private lemma carrier_subset_null_symm_of_carrier_subset_null
    {f g : OrderBoundedHom X ℝ}
    (hf : IsOrderContinuousOp f.toLinearMap) (_hg : IsOrderContinuousOp g.toLinearMap)
    (hsub : (carrier f : Set X) ⊆ (null g : Set X)) :
    (carrier g : Set X) ⊆ (null f : Set X) := by
  intro x hx
  have hxdd : x ∈ ((null f : Set X)ᵈ)ᵈ := by
    exact disjointComplement_anti hsub hx
  rwa [null_disjointComplement_disjointComplement_eq hf] at hxdd

omit [IsVLArchimedean X] in
private lemma carrier_subset_disjointComplement_carrier_of_carrier_subset_null
    {f g : OrderBoundedHom X ℝ}
    (hsub : (carrier g : Set X) ⊆ (null f : Set X)) :
    (carrier f : Set X) ⊆ (carrier g : Set X)ᵈ := by
  intro x hx y hy
  exact mem_carrier.mp hx y (hsub hy)

private lemma carrier_subset_null_of_subset_disjointComplement_carrier
    {f g : OrderBoundedHom X ℝ} (hg : IsOrderContinuousOp g.toLinearMap)
    (hsub : (carrier f : Set X) ⊆ (carrier g : Set X)ᵈ) :
    (carrier f : Set X) ⊆ (null g : Set X) := by
  intro x hx
  have hx' := hsub hx
  rwa [disjointComplement_carrier_eq_null hg] at hx'

/-- Two order-continuous functionals are disjoint exactly when their carriers are disjoint,
equivalently each carrier is contained in the other's null ideal. -/
theorem nakano_theorem (f g : OrderBoundedHom X ℝ)
    (hf : IsOrderContinuousOp f.toLinearMap) (hg : IsOrderContinuousOp g.toLinearMap) :
    List.TFAE [
      IsVLDisjoint f g,
      (carrier f : Set X) ⊆ (null g : Set X),
      (carrier g : Set X) ⊆ (null f : Set X),
      (carrier f : Set X) ⊆ (carrier g : Set X)ᵈ] := by
  refine List.tfae_of_cycle ?_ ?_
  · simp only [List.isChain_cons_cons]
    exact ⟨carrier_subset_null_of_disjoint hf hg,
      carrier_subset_null_symm_of_carrier_subset_null hf hg,
      carrier_subset_disjointComplement_carrier_of_carrier_subset_null,
      List.IsChain.singleton _⟩
  · intro h
    exact disjoint_of_carrier_subset_null hf hg
      (carrier_subset_null_of_subset_disjointComplement_carrier hg h)

end Nakano

end OrderBoundedHom
