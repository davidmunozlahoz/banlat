/-
Authors: Pedro Tradacete
-/

import BanLat.Operators.OrderContinuous
import BanLat.Substructures.Band.Generated
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Finsupp.Order

/-!
# The countable supremum property

An ordered space has the countable supremum property if every set with a supremum has a
countable subset with the same supremum. For positive linear maps on a vector lattice with
this property, order continuity is equivalent to σ-order continuity.
For Archimedean vector lattices, the countable chain condition implies the countable supremum
property; the converse holds in the presence of a weak order unit.
Separable normed vector lattices have the countable supremum property.
Finitely supported real-valued functions on `ℝ` give an example of an Archimedean vector lattice
with the countable supremum property but without the countable chain condition or a weak order unit.
-/

universe u v w

/-- Every set with a least upper bound has a countable subset with the same least upper bound. -/
def HasCountableSupProperty (E : Type*) [Preorder E] : Prop :=
  ∀ (s : Set E) (a : E), IsLUB s a → ∃ t ⊆ s, t.Countable ∧ IsLUB t a

/-- Every set of pairwise disjoint nonzero vectors is countable. -/
def HasCountableChainCondition (E : Type*) [AddCommGroup E] [Lattice E] : Prop :=
  ∀ s : Set E, IsDisjointSet s → s.Countable

/-- Every sequence in a directed preorder admits a monotone sequence whose next term
dominates the corresponding original term. -/
private lemma exists_monotone_dominating {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] (a : ℕ → ι) :
    ∃ b : ℕ → ι, Monotone b ∧ ∀ n, a n ≤ b (n + 1) := by
  choose upper hleft hright using fun i j : ι ↦ directed_of (· ≤ ·) i j
  let b : ℕ → ι := Nat.rec (a 0) (fun n i ↦ upper i (a n))
  exact ⟨b, monotone_nat_of_le_succ (fun n ↦ hleft (b n) (a n)),
    fun n ↦ hright (b n) (a n)⟩

variable {E : Type u} {F : Type v} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E] [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [VectorLattice F]

omit [VectorLattice E] in
/-- Under the countable supremum property, a decreasing net with greatest lower bound zero
admits a monotone sequence of indices along which the greatest lower bound is still zero. -/
private lemma exists_seq_isGLB_zero (hE : HasCountableSupProperty E)
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {x : ι → E} (hx : Antitone x) (hglb : IsGLB (Set.range x) 0) :
    ∃ b : ℕ → ι, Monotone b ∧ IsGLB (Set.range fun n ↦ x (b n)) 0 := by
  obtain ⟨s, hs, hsc, hlub⟩ := hE (-(Set.range x)) 0 (by simpa using hglb.neg)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨f, hf⟩ := (hsc.insert (-x i₀)).exists_eq_range (Set.insert_nonempty _ _)
  have hsub : insert (-x i₀) s ⊆ -(Set.range x) :=
    Set.insert_subset_iff.mpr ⟨by simp, hs⟩
  choose a ha using fun n ↦ Set.mem_neg.mp (hsub (hf.symm ▸ Set.mem_range_self n))
  obtain ⟨b, hb, hab⟩ := exists_monotone_dominating a
  refine ⟨b, hb, ⟨fun y ⟨n, hn⟩ ↦ hn ▸ hglb.1 ⟨b n, rfl⟩,
    fun z hz ↦ neg_nonneg.mp (hlub.2 ?_)⟩⟩
  intro y hy
  obtain ⟨n, rfl⟩ := hf ▸ Set.mem_insert_of_mem (-x i₀) hy
  exact le_neg.mpr ((hz ⟨n + 1, rfl⟩).trans ((hx (hab n)).trans_eq (ha n)))

/-- A linear operator is σ-order continuous if it preserves decreasing sequences with
greatest lower bound zero. -/
def IsSigmaOrderContinuousOp (T : E →ₗ[ℝ] F) : Prop :=
  ∀ {x : ℕ → E}, Antitone x → IsGLB (Set.range x) 0 →
    Antitone (fun n ↦ T (x n)) ∧ IsGLB (Set.range fun n ↦ T (x n)) 0

private lemma positive_of_isGLB_zero {T : E →ₗ[ℝ] F}
    (h : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {x : ι → E}, Antitone x → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun i ↦ T (x i)) 0) : Positive T := by
  intro a ha
  let x : ℕ → E := fun n ↦ if n = 0 then a else 0
  have hx : Antitone x := antitone_nat_of_succ_le (fun n ↦ by
    simpa [x] using (ite_nonneg (p := n = 0) ha le_rfl))
  have hglb : IsGLB (Set.range fun n : ULift.{u} ℕ ↦ x n.down) 0 :=
    ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ ite_nonneg ha le_rfl, fun _ hb ↦ hb ⟨⟨1⟩, rfl⟩⟩
  exact (h (x := fun n : ULift.{u} ℕ ↦ x n.down) (fun _ _ hij ↦ hx hij) hglb).1
    ⟨⟨0⟩, rfl⟩

/-- A linear operator is order continuous if it preserves greatest lower bounds
of decreasing nets with greatest lower bound zero. -/
private lemma orderContinuous_of_isGLB_zero {T : E →ₗ[ℝ] F}
    (h : ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {x : ι → E}, Antitone x → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun i ↦ T (x i)) 0) : IsOrderContinuousOp T := by
  have hT : Positive T := positive_of_isGLB_zero h
  rintro ι _ _ _ x a ⟨κ, hκ, hdκ, hnκ, r, hr, hrpos, hrglb, hevent⟩
  letI := hκ
  letI := hdκ
  letI := hnκ
  obtain ⟨τ, hτ, hdτ, hnτ, s, hs, hspos, hsglb, hsevent⟩ :=
    orderConvergesTo_of_antitone_isGLB ((Positive.monotone_iff.mpr hT).comp_antitone hr)
      (h hr hrglb)
  refine ⟨τ, hτ, hdτ, hnτ, s, hs, hspos, hsglb, fun k ↦ ?_⟩
  obtain ⟨j, hj⟩ := (hsevent k).exists
  refine (hevent j).mono fun i hi ↦ ?_
  calc
    |T (x i) - T a| = |T (x i - a)| := by rw [map_sub]
    _ ≤ T |x i - a| := hT.abs_le_map_abs _
    _ ≤ T (r j) := (Positive.monotone_iff.mpr hT) hi
    _ ≤ s k := by simpa only [Function.comp_apply, sub_zero,
      abs_of_nonneg (hT _ (hrpos j))] using hj

namespace Positive

variable {T : E →ₗ[ℝ] F}

/-- A positive linear operator is order continuous exactly when it preserves greatest
lower bounds of decreasing nets with greatest lower bound zero. -/
theorem isOrderContinuousOp_iff_isGLB_zero (hT : Positive T) :
    IsOrderContinuousOp T ↔
      ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        {x : ι → E}, Antitone x → IsGLB (Set.range x) 0 →
          IsGLB (Set.range fun i ↦ T (x i)) 0 := by
  refine ⟨?_, orderContinuous_of_isGLB_zero⟩
  intro h ι _ _ _ x hx hglb
  have hc := h (orderConvergesTo_of_antitone_isGLB hx hglb)
  exact ⟨fun y ⟨i, hi⟩ ↦ hi ▸ hT _ (hglb.1 ⟨i, rfl⟩),
    fun z hz ↦ by simpa only [map_zero] using hc.forall_le (fun i ↦ hz ⟨i, rfl⟩)⟩

/-- An order-continuous positive linear operator is σ-order continuous. -/
theorem isSigmaOrderContinuousOp (hT : Positive T) (h : IsOrderContinuousOp T) :
    IsSigmaOrderContinuousOp T := by
  intro x hx hglb
  have hrange : Set.range (fun n : ULift.{u} ℕ ↦ x n.down) = Set.range x :=
    ULift.down_surjective.range_comp x
  have hc := (hT.isOrderContinuousOp_iff_isGLB_zero.mp h)
    (show Antitone (fun n : ULift.{u} ℕ ↦ x n.down) from fun _ _ h ↦ hx h)
    (hrange.symm ▸ hglb)
  exact ⟨(monotone_iff.mpr hT).comp_antitone hx,
    (ULift.down_surjective.range_comp (fun n ↦ T (x n))) ▸ hc⟩

/-- On a vector lattice with the countable supremum property, a positive linear operator
is order continuous exactly when it is σ-order continuous. -/
theorem isOrderContinuousOp_iff_isSigmaOrderContinuousOp (hT : Positive T)
    (hE : HasCountableSupProperty E) : IsOrderContinuousOp T ↔ IsSigmaOrderContinuousOp T := by
  refine ⟨hT.isSigmaOrderContinuousOp, fun h ↦ hT.isOrderContinuousOp_iff_isGLB_zero.mpr ?_⟩
  intro ι _ _ _ x hx hglb
  obtain ⟨b, hb, hbglb⟩ := exists_seq_isGLB_zero hE hx hglb
  exact ⟨fun y ⟨i, hi⟩ ↦ hi ▸ hT _ (hglb.1 ⟨i, rfl⟩),
    fun z hz ↦ (h (hx.comp_monotone hb) hbglb).2.2
      (fun y ⟨n, hn⟩ ↦ hn ▸ hz ⟨b n, rfl⟩)⟩

end Positive

namespace HasCountableChainCondition

omit [IsOrderedAddMonoid E] [VectorLattice E] in
/-- Every set contains a maximal pairwise disjoint subset. -/
private lemma exists_maximal_disjoint_subset (s : Set E) :
    ∃ d : Set E, Maximal (fun d ↦ d ⊆ s ∧ d.Pairwise IsVLDisjoint) d := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ⟨Set.sUnion_subset (fun t ht ↦ (hc ht).1), ?_⟩,
    fun t ht ↦ Set.subset_sUnion_of_mem ht⟩
  rintro x ⟨s, hs, hxs⟩ y ⟨t, ht, hyt⟩ hxy
  exact (hchain.total hs ht).elim
    (fun hst ↦ (hc ht).2 (hst hxs) hyt hxy)
    (fun hts ↦ (hc hs).2 hxs (hts hyt) hxy)

omit [VectorLattice E] in
/-- Under the countable chain condition, every set of nonnegative vectors has a countable
subset such that any nonnegative vector disjoint from it is disjoint from the whole set. -/
private lemma countable_disjoint_detection (hE : HasCountableChainCondition E)
    (s : Set E) (hs : ∀ x ∈ s, 0 ≤ x) :
    ∃ t ⊆ s, t.Countable ∧ ∀ x, 0 ≤ x →
      (∀ y ∈ t, IsVLDisjoint x y) → ∀ y ∈ s, IsVLDisjoint x y := by
  obtain ⟨d, hd, hmax⟩ := exists_maximal_disjoint_subset {x : E | 0 < x ∧ ∃ y ∈ s, x ≤ y}
  have hdc := hE d ⟨fun h ↦ (lt_irrefl 0) (hd.1 h).1, hd.2⟩
  letI := hdc.to_subtype
  choose f hf hle using fun a : d ↦ (hd.1 a.2).2
  refine ⟨Set.range f, Set.range_subset_iff.mpr hf, Set.countable_range f, ?_⟩
  intro x hx hxt y hy
  have hxd (a : E) (ha : a ∈ d) : IsVLDisjoint (x ⊓ y) a :=
    ((hxt _ (Set.mem_range_self ⟨a, ha⟩)).mono_left
      (by simpa only [abs_of_nonneg (le_inf hx (hs y hy)), abs_of_nonneg hx]
        using (inf_le_left : x ⊓ y ≤ x))).mono_right
      (by simpa only [abs_of_nonneg (hd.1 ha).1.le, abs_of_nonneg (hs _ (hf ⟨a, ha⟩))]
        using hle ⟨a, ha⟩)
  apply isVLDisjoint_of_inf_eq_zero
  by_contra hne
  have hpos : 0 < x ⊓ y := lt_of_le_of_ne (le_inf hx (hs y hy)) (Ne.symm hne)
  have hins : insert (x ⊓ y) d ⊆ {z : E | 0 < z ∧ ∃ a ∈ s, z ≤ a} :=
    Set.insert_subset_iff.mpr ⟨⟨hpos, y, hy, inf_le_right⟩, hd.1⟩
  have hpair : (insert (x ⊓ y) d).Pairwise IsVLDisjoint :=
    Set.pairwise_insert.mpr ⟨hd.2, fun a ha _ ↦ ⟨hxd a ha, isVLDisjoint_comm.mp (hxd a ha)⟩⟩
  have hmem := hmax ⟨hins, hpair⟩ (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact hne (by simpa only [IsVLDisjoint, abs_of_nonneg hpos.le, inf_idem] using hxd _ hmem)

omit [VectorLattice E] in
/-- If `s` has supremum `a` and `v ≤ a`, the positive parts of `x - v` for `x ∈ s`
have supremum `a - v`. -/
private lemma isLUB_posPart_sub {s : Set E} {a v : E} (h : IsLUB s a) (hv : v ≤ a) :
    IsLUB ((fun x ↦ (x - v)⁺) '' s) (a - v) := by
  refine ⟨?_, fun b hb ↦ sub_le_iff_le_add.mpr (h.2 ?_)⟩
  · exact fun y ⟨x, hx, heq⟩ ↦ heq ▸
      sup_le (sub_le_sub_right (h.1 hx) v) (sub_nonneg.mpr hv)
  · exact fun x hx ↦ sub_le_iff_le_add.mp
      ((le_sup_left : x - v ≤ (x - v)⁺).trans (hb ⟨x, hx, rfl⟩))

/-- For nonnegative `a` and `b` and `0 ≤ r < 1`, disjointness of `(r • a - b)⁺` and
`a - r • a` implies `r • a ≤ b`. -/
private lemma le_of_disjoint_posPart_sub {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hdis : IsVLDisjoint (r • a - b)⁺ (a - r • a)) : r • a ≤ b := by
  have hbase : a - r • a = (1 - r) • a := by rw [sub_smul, one_smul]
  have hscale : (r / (1 - r)) • (a - r • a) = r • a := by
    rw [hbase, smul_smul, div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hr1))]
  have hdisRa : IsVLDisjoint (r • a - b)⁺ (r • a) := by
    simpa only [hscale] using hdis.smul_right (r / (1 - r))
  have hself := hdisRa.mono_right (show |(r • a - b)⁺| ≤ |r • a| by
    rw [abs_of_nonneg (posPart_nonneg _), abs_of_nonneg (smul_nonneg hr ha), posPart_def]
    exact sup_le (sub_le_self (r • a) hb) (smul_nonneg hr ha))
  exact sub_nonpos.mp (posPart_eq_zero.mp
    (by simpa only [IsVLDisjoint, inf_idem, abs_of_nonneg (posPart_nonneg _)] using hself))

/-- Under the countable chain condition, a nonempty set with nonnegative supremum `a`
has, for each `0 ≤ r < 1`, a countable subset whose nonnegative upper bounds dominate `r • a`. -/
private lemma countable_lower_approximation (hE : HasCountableChainCondition E)
    {s : Set E} {a : E} (ha : 0 ≤ a) (hs : s.Nonempty) (hlub : IsLUB s a)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ t ⊆ s, t.Countable ∧ ∀ b, 0 ≤ b → b ∈ upperBounds t → r • a ≤ b := by
  obtain ⟨d, hd, hdc, hdet⟩ := countable_disjoint_detection hE
    ((fun x ↦ (x - r • a)⁺) '' s) (by rintro _ ⟨x, _, rfl⟩; exact posPart_nonneg _)
  letI := hdc.to_subtype
  choose f hf hfeq using fun x : d ↦ hd x.2
  refine ⟨Set.range f, Set.range_subset_iff.mpr hf, Set.countable_range f, ?_⟩
  intro b hb hbt
  have hdis : IsVLDisjoint (r • a - b)⁺ (b - r • a)⁺ := by
    simpa only [negPart_def, posPart_def, neg_sub] using isVLDisjoint_posPart_negPart (r • a - b)
  have hdisd (x : d) : IsVLDisjoint (r • a - b)⁺ x.1 :=
    hfeq x ▸ hdis.mono_right (by
      simpa only [abs_of_nonneg (posPart_nonneg _)] using
        posPart_mono (sub_le_sub_right (hbt (Set.mem_range_self x)) (r • a)))
  have hc := isLUB_posPart_sub hlub
    (show r • a ≤ a by simpa only [one_smul] using smul_le_smul_of_nonneg_right hr1.le ha)
  have hdet' := hdet _ (posPart_nonneg (r • a - b)) (fun x hx ↦ hdisd ⟨x, hx⟩)
  have hmem : a - r • a ∈ Band.disjointComplement {(r • a - b)⁺} :=
    (Band.disjointComplement {(r • a - b)⁺}).sSup_mem
      (fun z hz y hy ↦ (Set.mem_singleton_iff.mp hy) ▸ isVLDisjoint_comm.mp (hdet' z hz))
      (hs.image _) hc
  exact le_of_disjoint_posPart_sub ha hb hr hr1
    (isVLDisjoint_comm.mp (hmem _ (Set.mem_singleton _)))

/-- In an Archimedean vector lattice, an upper bound for `(1 - (n + 1)⁻¹) • a` for every
natural number `n`, with `a` nonnegative, is also an upper bound for `a`. -/
private lemma le_of_forall_approx_le [IsVLArchimedean E] {a b : E} (ha : 0 ≤ a)
    (h : ∀ n : ℕ, (1 - ((n + 1 : ℕ) : ℝ)⁻¹) • a ≤ b) : a ≤ b := by
  apply sub_nonpos.mp
  apply (isVLArchimedean_iff_isGLB_inv_smul.mp inferInstance a ha).2
  rintro _ ⟨n, hn, rfl⟩
  apply sub_le_comm.mp
  simpa only [Nat.sub_add_cancel (Nat.one_le_of_lt hn), sub_smul, one_smul] using h (n - 1)

/-- In an Archimedean vector lattice satisfying the countable chain condition, every nonempty
set of nonnegative vectors with a supremum has a countable subset with the same supremum. -/
private lemma countable_lub_nonneg [IsVLArchimedean E] (hE : HasCountableChainCondition E)
    {s : Set E} {a : E} (hs : s.Nonempty) (hpos : ∀ x ∈ s, 0 ≤ x) (hlub : IsLUB s a) :
    ∃ t ⊆ s, t.Countable ∧ IsLUB t a := by
  obtain ⟨a₀, ha₀⟩ := hs
  have ha : 0 ≤ a := (hpos a₀ ha₀).trans (hlub.1 ha₀)
  have hr (n : ℕ) : 0 ≤ 1 - ((n + 1 : ℕ) : ℝ)⁻¹ ∧
      1 - ((n + 1 : ℕ) : ℝ)⁻¹ < 1 :=
    ⟨sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))),
      sub_lt_self _ (inv_pos.mpr (by exact_mod_cast Nat.zero_lt_succ n))⟩
  choose t hts htc ht using fun n ↦
    countable_lower_approximation hE ha ⟨a₀, ha₀⟩ hlub (hr n).1 (hr n).2
  have hsub : insert a₀ (⋃ n, t n) ⊆ s :=
    Set.insert_subset_iff.mpr ⟨ha₀, Set.iUnion_subset hts⟩
  refine ⟨insert a₀ (⋃ n, t n), hsub, (Set.countable_iUnion htc).insert a₀,
    ⟨fun _ hx ↦ hlub.1 (hsub hx), fun b hb ↦ le_of_forall_approx_le ha ?_⟩⟩
  exact fun n ↦ ht n b ((hpos a₀ ha₀).trans (hb (Set.mem_insert _ _)))
    (fun x hx ↦ hb (Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, hx⟩)))

/-- In an Archimedean vector lattice satisfying the countable chain condition, every nonempty
set with a supremum has a countable subset with the same supremum. -/
private lemma countable_lub_nonempty [IsVLArchimedean E] (hE : HasCountableChainCondition E)
    {s : Set E} {a : E} (hs : s.Nonempty) (hlub : IsLUB s a) :
    ∃ t ⊆ s, t.Countable ∧ IsLUB t a := by
  obtain ⟨a₀, ha₀⟩ := hs
  obtain ⟨d, hd, hdc, hd_lub⟩ := countable_lub_nonneg hE
    (Set.Nonempty.image _ ⟨a₀, ha₀⟩)
    (show ∀ x ∈ (fun x ↦ (x - a₀)⁺) '' s, 0 ≤ x from
      fun _ ⟨x, _, hx⟩ ↦ hx ▸ posPart_nonneg _)
    (isLUB_posPart_sub hlub (hlub.1 ha₀))
  letI := hdc.to_subtype
  choose f hf hfeq using fun x : d ↦ hd x.2
  have hsub : insert a₀ (Set.range f) ⊆ s :=
    Set.insert_subset_iff.mpr ⟨ha₀, Set.range_subset_iff.mpr hf⟩
  refine ⟨insert a₀ (Set.range f), hsub, (Set.countable_range f).insert a₀,
    ⟨fun _ hx ↦ hlub.1 (hsub hx), fun b hb ↦ ?_⟩⟩
  apply (sub_le_sub_iff_right a₀).mp
  apply hd_lub.2
  have hbound (x : d) : (x : E) ≤ b - a₀ := hfeq x ▸
    sup_le (sub_le_sub_right (hb (Set.mem_insert_of_mem _ (Set.mem_range_self x))) a₀)
      (sub_nonneg.mpr (hb (Set.mem_insert _ _)))
  exact fun x hx ↦ hbound ⟨x, hx⟩

/-- An Archimedean vector lattice satisfying the countable chain condition has the countable
supremum property. -/
theorem hasCountableSupProperty [IsVLArchimedean E] (hE : HasCountableChainCondition E) :
    HasCountableSupProperty E := by
  intro s a ha
  by_cases hs : s.Nonempty
  · exact countable_lub_nonempty hE hs ha
  · exact ⟨s, Set.Subset.rfl,
      (Set.not_nonempty_iff_eq_empty.mp hs) ▸ Set.countable_empty, ha⟩

end HasCountableChainCondition

namespace HasCountableSupProperty

/-- Every element of the order ideal generated by `s` belongs to the order ideal generated
by some finite subset of `s`. -/
private lemma finite_support_mem_generated {s : Set E} {x : E}
    (hx : x ∈ OrderIdeal.generated s) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧ x ∈ OrderIdeal.generated (t : Set E) := by
  obtain ⟨t, c, ht, hc, hx⟩ := OrderIdeal.mem_generated_iff.mp hx
  exact ⟨t, ht, OrderIdeal.mem_generated_iff.mpr ⟨t, c, fun _ hy ↦ hy, hc, hx⟩⟩

/-- Every countable subset of the order ideal generated by `s` is contained in the band
generated by some countable subset of `s`. -/
private lemma countable_support_of_subset_generated {s d : Set E} (hd : d.Countable)
    (hds : d ⊆ OrderIdeal.generated s) :
    ∃ t ⊆ s, t.Countable ∧ d ⊆ Band.generated t := by
  letI := hd.to_subtype
  choose f hf hmem using fun x : d ↦ finite_support_mem_generated (hds x.2)
  refine ⟨⋃ x, (f x : Set E), Set.iUnion_subset hf,
    Set.countable_iUnion (fun x ↦ (f x).countable_toSet), ?_⟩
  intro x hx
  exact OrderIdeal.generated_le (J := (Band.generated (⋃ y, (f y : Set E))).toOrderIdeal)
    (fun y hy ↦ Band.subset_generated _ (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩))
    (hmem ⟨x, hx⟩)

/-- In an Archimedean vector lattice with the countable supremum property, every nonnegative
element of the band generated by `s` belongs to the band generated by a countable subset of `s`. -/
private lemma countable_band_support [IsVLArchimedean E] (hE : HasCountableSupProperty E)
    {s : Set E} {x : E} (hx : 0 ≤ x) (hxs : x ∈ Band.generated s) :
    ∃ t ⊆ s, t.Countable ∧ x ∈ Band.generated t := by
  have hxJ : x ∈ Band.generated (OrderIdeal.generated s : Set E) :=
    Band.generated_le (fun y hy ↦ Band.subset_generated _ (OrderIdeal.subset_generated s hy))
      hxs
  obtain ⟨d, hd, hdc, hd_lub⟩ := hE _ x
    ((Band.mem_generated_orderIdeal_iff_isLUB_inter (OrderIdeal.generated s) hx).mp hxJ)
  obtain ⟨t, ht, htc, hdt⟩ := countable_support_of_subset_generated hdc (fun y hy ↦ (hd hy).1)
  refine ⟨t, ht, htc, (Band.generated t).sSup_mem
    (Set.insert_subset_iff.mpr ⟨(Band.generated t).toSubmodule.zero_mem, hdt⟩)
    (Set.insert_nonempty 0 d) ?_⟩
  simpa only [sup_of_le_right hx] using hd_lub.insert 0

/-- In an Archimedean vector lattice with a weak order unit, the countable supremum property
implies the countable chain condition. -/
theorem hasCountableChainCondition_of_weakOrderUnit [IsVLArchimedean E]
    (hE : HasCountableSupProperty E) {e : E} (he : WeakOrderUnit e) :
    HasCountableChainCondition E := by
  intro s hs
  have heG : e ∈ Band.generated (s ∪ sᵈ) := by
    simp only [Band.generated_union_disjointComplement_eq_top, Band.mem_top]
  obtain ⟨t, ht, htc, het⟩ := countable_band_support hE he.1 heG
  apply htc.mono
  intro x hx
  by_contra hxt
  have htd : t ⊆ Band.disjointComplement {x} := by
    intro y hy z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    rcases ht hy with hyS | hyd
    · exact hs.2 hyS hx (fun h ↦ hxt (h ▸ hy))
    · exact hyd _ hx
  have hed := (Band.generated_le htd het) x (Set.mem_singleton _)
  exact hs.1 ((he.2 x (isVLDisjoint_comm.mp hed)) ▸ hx)

end HasCountableSupProperty

/-- For an Archimedean vector lattice with a weak order unit, the countable supremum property
and the countable chain condition are equivalent. -/
theorem WeakOrderUnit.hasCountableSupProperty_iff_hasCountableChainCondition
    [IsVLArchimedean E] {e : E} (he : WeakOrderUnit e) :
    HasCountableSupProperty E ↔ HasCountableChainCondition E := by
  constructor
  · exact fun hE ↦ hE.hasCountableChainCondition_of_weakOrderUnit he
  · exact HasCountableChainCondition.hasCountableSupProperty

/-- Every separable normed vector lattice, in particular every separable Banach lattice,
has the countable supremum property. -/
theorem hasCountableSupProperty_of_separableSpace {E : Type*}
    [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [NormedVectorLattice E]
    [TopologicalSpace.SeparableSpace E] : HasCountableSupProperty E := by
  intro s a ha
  obtain ⟨t, ht, htc, hcl⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace s).exists_countable_dense_subset
  exact ⟨t, ht, htc, (isLUB_iff_of_subset_of_subset_closure ht hcl).mpr ha⟩


namespace Finsupp

variable {ι : Type*}

/-- Finitely supported real-valued functions form a vector lattice with pointwise order. -/
noncomputable instance instVectorLatticeReal : VectorLattice (ι →₀ ℝ) := ⟨⟩

/-- Finitely supported real-valued functions are Archimedean. -/
instance instIsVLArchimedeanReal : IsVLArchimedean (ι →₀ ℝ) where
  le_zero_of_forall_nsmul_le h i :=
    IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦ h n i)

/-- Evaluation at any coordinate preserves existing suprema of finitely supported functions. -/
private lemma isLUB_eval {s : Set (ι →₀ ℝ)} {a : ι →₀ ℝ} (ha : IsLUB s a) (i : ι) :
    IsLUB ((fun f ↦ f i) '' s) (a i) := by
  classical
  refine ⟨fun _ ⟨f, hf, hfi⟩ ↦ hfi ▸ ha.1 hf i, fun b hb ↦ ?_⟩
  have hub : a.update i b ∈ upperBounds s := by
    intro f hf j
    by_cases hji : j = i
    · simpa [update_apply, hji] using hb ⟨f, hf, rfl⟩
    · simpa only [update_apply, if_neg hji] using ha.1 hf j
  simpa [update_apply] using ha.2 hub i

/-- A countable subset suffices to determine a given coordinate of an existing supremum. -/
private lemma countable_eval_upperBounds {s : Set (ι →₀ ℝ)} {a : ι →₀ ℝ}
    (ha : IsLUB s a) (i : ι) :
    ∃ t ⊆ s, t.Countable ∧ ∀ b ∈ upperBounds t, a i ≤ b i := by
  obtain ⟨d, hd, hdc, hd_lub⟩ :=
    hasCountableSupProperty_of_separableSpace _ _ (isLUB_eval ha i)
  letI := hdc.to_subtype
  choose f hf hfeq using fun x : d ↦ hd x.2
  refine ⟨Set.range f, Set.range_subset_iff.mpr hf, Set.countable_range f, fun b hb ↦ ?_⟩
  apply hd_lub.2
  have hbound (x : d) : (x : ℝ) ≤ b i := hfeq x ▸ hb (Set.mem_range_self x) i
  exact fun x hx ↦ hbound ⟨x, hx⟩

/-- A nonempty set of finitely supported real-valued functions with a supremum has a
countable subset with the same supremum. -/
private lemma countable_lub_nonempty {s : Set (ι →₀ ℝ)} {a : ι →₀ ℝ}
    (hs : s.Nonempty) (ha : IsLUB s a) : ∃ t ⊆ s, t.Countable ∧ IsLUB t a := by
  classical
  obtain ⟨f₀, hf₀⟩ := hs
  let k := a.support ∪ f₀.support
  choose t hts htc ht using fun i : k ↦ countable_eval_upperBounds ha i.1
  have hsub : insert f₀ (⋃ i, t i) ⊆ s :=
    Set.insert_subset_iff.mpr ⟨hf₀, Set.iUnion_subset hts⟩
  refine ⟨insert f₀ (⋃ i, t i), hsub, (Set.countable_iUnion htc).insert f₀,
    ⟨fun _ hf ↦ ha.1 (hsub hf), fun b hb i ↦ ?_⟩⟩
  by_cases hi : i ∈ k
  · exact ht ⟨i, hi⟩ b
      (fun f hf ↦ hb (Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hf⟩)))
  · have hk : i ∉ a.support ∧ i ∉ f₀.support := by
      simpa only [k, Finset.mem_union, not_or] using hi
    simpa only [notMem_support_iff.mp hk.1, notMem_support_iff.mp hk.2]
      using hb (Set.mem_insert _ _) i

/-- Finitely supported real-valued functions have the countable supremum property,
regardless of the cardinality of the index set. -/
theorem hasCountableSupProperty : HasCountableSupProperty (ι →₀ ℝ) := by
  intro s a ha
  by_cases hs : s.Nonempty
  · exact countable_lub_nonempty hs ha
  · exact ⟨s, Set.Subset.rfl,
      (Set.not_nonempty_iff_eq_empty.mp hs) ▸ Set.countable_empty, ha⟩

/-- A coordinate vector is disjoint from every finitely supported function vanishing
at that coordinate. -/
private lemma isVLDisjoint_single_of_eq_zero {f : ι →₀ ℝ} {i : ι} (hf : f i = 0) :
    IsVLDisjoint (single i 1) f := by
  classical
  change |single i 1| ⊓ |f| = 0
  ext j
  change |(single i 1 : ι →₀ ℝ) j| ⊓ |f j| = 0
  by_cases hji : j = i
  · simp [hji, hf]
  · simp [single_eq_of_ne hji]

/-- The coordinate vectors form a set of pairwise disjoint nonzero vectors. -/
private lemma isDisjointSet_range_single_one :
    IsDisjointSet (Set.range fun i : ι ↦ single i (1 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    exact one_ne_zero (single_eq_zero.mp hi)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact isVLDisjoint_single_of_eq_zero
      (single_eq_of_ne (fun h ↦ hij (congrArg (fun k ↦ single k (1 : ℝ)) h)))

/-- Finitely supported real-valued functions on an uncountable index set do not satisfy
the countable chain condition. -/
theorem not_hasCountableChainCondition [Uncountable ι] :
    ¬ HasCountableChainCondition (ι →₀ ℝ) := by
  intro h
  have hc := h _ isDisjointSet_range_single_one
  apply Set.not_countable_univ (α := ι)
  apply Set.countable_of_injective_of_countable_image
    (single_left_injective (one_ne_zero : (1 : ℝ) ≠ 0)).injOn
  simpa only [Set.image_univ] using hc

/-- No finitely supported real-valued function on an infinite index set is a weak order unit. -/
theorem not_weakOrderUnit [Infinite ι] (e : ι →₀ ℝ) : ¬ WeakOrderUnit e := by
  intro he
  obtain ⟨i, hi⟩ := e.support.exists_notMem
  have hd := isVLDisjoint_single_of_eq_zero (notMem_support_iff.mp hi)
  exact one_ne_zero (single_eq_zero.mp (he.2 _ hd))

/-- The Archimedean vector lattice of finitely supported functions on `ℝ` has the countable
supremum property, fails the countable chain condition, and has no weak order unit. -/
theorem countableSupProperty_counterexample :
    IsVLArchimedean (ℝ →₀ ℝ) ∧ HasCountableSupProperty (ℝ →₀ ℝ) ∧
      ¬ HasCountableChainCondition (ℝ →₀ ℝ) ∧ ¬ ∃ e : ℝ →₀ ℝ, WeakOrderUnit e :=
  ⟨inferInstance, hasCountableSupProperty, not_hasCountableChainCondition,
    fun ⟨e, he⟩ ↦ not_weakOrderUnit e he⟩

end Finsupp
