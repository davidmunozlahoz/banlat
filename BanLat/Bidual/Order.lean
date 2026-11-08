/-
Authors: Pedro Tradacete
-/

import BanLat.Bidual
import BanLat.OrderContinuous.Basic
import BanLat.Substructures.Ideal
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Order properties of the canonical bidual embedding

The canonical embedding of a Banach lattice in its bidual is order continuous
exactly when the norm is order continuous. Its range is an order ideal exactly when
positive order intervals are weakly compact.
-/

noncomputable section

open Set Filter Topology

universe u

namespace BidualSpace

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

omit [NormedAddCommGroup X] [IsOrderedAddMonoid X] [BanachLattice X] in
/-- Finite suprema of elements of a set, each including a fixed member, have the same
supremum as the original set. -/
private lemma isLUB_range_sup_insert {A : Set X} [DecidableEq A] {a : X}
    (a₀ : A) (ha : IsLUB A a) :
    IsLUB (range (fun F : Finset A ↦
      (insert a₀ F).sup' (Finset.insert_nonempty _ _) Subtype.val)) a := by
  refine ⟨fun _ ⟨F, hF⟩ ↦ hF ▸
    (Finset.sup'_le_iff _ _).mpr (fun b _ ↦ ha.1 b.property), ?_⟩
  intro b hb
  exact ha.2 fun x hx ↦
    (Finset.le_sup' Subtype.val (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self (⟨x, hx⟩ : A)))).trans (hb ⟨{⟨x, hx⟩}, rfl⟩)

/-- The canonical embedding preserves nonempty suprema when the norm is order continuous. -/
theorem isLUB_image_inclusion [IsOrderContinuousNorm X]
    {A : Set X} {a : X} (hA : A.Nonempty) (ha : IsLUB A a) :
    IsLUB (inclusion '' A) (inclusion a) := by
  change IsLUB (inclusionVecLatHom '' A) (inclusionVecLatHom a)
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  let f : Finset A → X := fun F ↦
    (insert ⟨a₀, ha₀⟩ F).sup' (Finset.insert_nonempty _ _) Subtype.val
  have hf : Monotone f := fun F G hFG ↦
    Finset.sup'_mono Subtype.val (Finset.insert_subset_insert _ hFG) (Finset.insert_nonempty _ _)
  have hfaLub : IsLUB (range f) a := isLUB_range_sup_insert ⟨a₀, ha₀⟩ ha
  have hnet := isLUB_of_tendsto_atTop ((inclusionVecLatHom (X := X)).monotone.comp hf)
    ((inclusion (X := X)).continuous.tendsto a |>.comp
      (tendsto_of_orderConvergesTo_of_isOrderContinuousNorm
        (orderConvergesTo_of_monotone_isLUB hf hfaLub)))
  refine ⟨?_, ?_⟩
  · exact fun _ ⟨x, hx, h⟩ ↦ h ▸ inclusionVecLatHom.monotone (ha.1 hx)
  · intro b hb
    apply hnet.2
    rintro _ ⟨F, rfl⟩
    simpa only [Function.comp_apply, f, map_finset_sup'] using
      (Finset.sup'_le (Finset.insert_nonempty ⟨a₀, ha₀⟩ F)
        (fun z : A ↦ inclusionVecLatHom z.val) (fun z _ ↦ hb ⟨z.val, z.property, rfl⟩))

/-- At a positive vector `x`, the positive part of a functional equals the supremum
of its values on the order interval `[0, x]`. -/
private lemma isLUB_posPart_apply (φ : StrongDual ℝ X)
    (x : X) (hx : 0 ≤ x) : IsLUB (φ '' Icc 0 x) (φ⁺ x) := by
  convert OrderDualSpace.isLUB_posPart_apply (φ := StrongDual.toOrderDualSpace φ) hx using 1
  · ext r
    simp only [mem_image, mem_Icc, mem_ofPred_eq, StrongDual.toOrderDualSpace_apply]
    aesop
  · rfl

/-- Every bidual vector between zero and `inclusion x` lies in the weak-star closure
of the canonical image of `[0, x]`. -/
private lemma mem_closure_inclusion_Icc (x : X) (hx : 0 ≤ x)
    (F : BidualSpace X) (hF0 : 0 ≤ F) (hFx : F ≤ inclusion x) :
    StrongDual.toWeakDual F ∈ closure
      ((fun y : X ↦ StrongDual.toWeakDual (inclusion y)) '' Icc 0 x) := by
  let j : X →ₗ[ℝ] WeakDual ℝ (StrongDual ℝ X) :=
    StrongDual.toWeakDual.toLinearMap.comp (inclusion (X := X)).toLinearMap
  have hconv : Convex ℝ (j '' Icc 0 x) := (convex_Icc 0 x).linear_image j
  by_contra hn
  let : LocallyConvexSpace ℝ (WeakDual ℝ (StrongDual ℝ X)) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing ℝ (StrongDual ℝ X))
  obtain ⟨g, c, hgc, hcF⟩ :=
    geometric_hahn_banach_closed_point hconv.closure isClosed_closure hn
  obtain ⟨φ, hφ⟩ := LinearMap.dualEmbedding_surjective
    (topDualPairing ℝ (StrongDual ℝ X)) g
  have hφupper : φ⁺ x ≤ c :=
    (isLUB_posPart_apply φ x hx).2
      (fun _ ⟨y, hy, heq⟩ ↦ heq ▸ (show φ y < c from by
        change (WeakBilin.eval (topDualPairing ℝ (StrongDual ℝ X)) φ) (j y) < c
        exact (congrArg (fun l ↦ l (j y)) hφ).le.trans_lt
          (hgc (j y) (subset_closure ⟨y, hy, rfl⟩))).le)
  have hFφ : (show StrongDual ℝ (StrongDual ℝ X) from F) φ ≤ φ⁺ x :=
    (StrongDual.apply_le_apply_of_nonneg hF0 le_sup_left).trans
      (StrongDual.le_iff.mp hFx φ⁺ (posPart_nonneg φ))
  exact (not_lt_of_ge (hFφ.trans hφupper))
    (hcF.trans_le (congrArg (fun l ↦ l (StrongDual.toWeakDual F)) hφ).symm.le)

/-- Weak compactness of positive order intervals makes the canonical embedding
interval preserving. -/
theorem image_inclusion_Icc_of_isCompact
    (h : ∀ x : X, 0 ≤ x → IsCompact ((toWeakSpace ℝ X) '' Icc 0 x)) :
    ∀ x : X, 0 ≤ x → inclusion '' Icc 0 x = Icc 0 (inclusion x) := by
  intro x hx
  have hc : IsCompact
      ((fun y : X ↦ StrongDual.toWeakDual (inclusion y)) '' Icc 0 x) := by
    have hc := (h x hx).image (NormedSpace.inclusionInDoubleDualWeak ℝ X).continuous
    rw [Set.image_image] at hc
    exact hc
  ext F
  constructor
  · exact fun ⟨y, hy, heq⟩ ↦ heq ▸
      ⟨inclusion_nonneg hy.1, inclusion_le_inclusion_iff.mpr hy.2⟩
  · intro hF
    have hmem := mem_closure_inclusion_Icc x hx F hF.1 hF.2
    rw [hc.isClosed.closure_eq] at hmem
    exact hmem.imp (fun y hy ↦ ⟨hy.1, StrongDual.toWeakDual.injective hy.2⟩)

/-- If the canonical embedding preserves positive intervals, the weak-star closure
of each such interval's image remains in the canonical bidual range. -/
private lemma closure_inclusion_Icc_subset_range
    (hi : ∀ x : X, 0 ≤ x → inclusion '' Icc 0 x = Icc 0 (inclusion x))
    (x : X) (hx : 0 ≤ x) :
    closure (NormedSpace.inclusionInDoubleDualWeak ℝ X '' (toWeakSpace ℝ X '' Icc 0 x)) ⊆
      range (NormedSpace.inclusionInDoubleDualWeak ℝ X) := by
  let W := (toWeakSpace ℝ X) '' Icc 0 x
  let j := NormedSpace.inclusionInDoubleDualWeak ℝ X
  let K : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    {z | ∀ φ : StrongDual ℝ X, 0 ≤ φ → z φ ∈ Icc 0 (φ x)}
  have hclosed : IsClosed K := by
    simpa only [K, ofPred_forall, Set.preimage] using isClosed_iInter (fun φ : StrongDual ℝ X ↦
      isClosed_iInter (fun _ : 0 ≤ φ ↦ isClosed_Icc.preimage (WeakDual.eval_continuous φ)))
  have hsub : j '' W ⊆ K := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ φ hφ
    exact ⟨StrongDual.apply_nonneg_of_nonneg hφ hy.1,
      StrongDual.apply_le_apply_of_nonneg hφ hy.2⟩
  have hclosure : closure (j '' W) ⊆ K := closure_minimal hsub hclosed
  intro z hz
  have hinterval : WeakDual.toStrongDual z ∈ Icc 0 (inclusion x) :=
    ⟨StrongDual.nonneg_iff.mpr (fun φ hφ ↦ (hclosure hz φ hφ).1),
      StrongDual.le_iff.mpr (fun φ hφ ↦ (hclosure hz φ hφ).2)⟩
  obtain ⟨y, _, hy⟩ := (hi x hx).symm ▸ hinterval
  exact ⟨toWeakSpace ℝ X y, congrArg StrongDual.toWeakDual hy⟩

/-- Interval preservation by the canonical embedding implies weak compactness of order intervals. -/
theorem isCompact_Icc_of_image_inclusion_Icc
    (hi : ∀ x : X, 0 ≤ x → inclusion '' Icc 0 x = Icc 0 (inclusion x)) (x : X) (hx : 0 ≤ x) :
    IsCompact ((toWeakSpace ℝ X) '' Icc 0 x) := by
  let W := (toWeakSpace ℝ X) '' Icc 0 x
  have hb : Bornology.IsBounded ((toWeakSpace ℝ X) ⁻¹' W) := by
    rw [show W = (toWeakSpace ℝ X) '' Icc 0 x from rfl,
      Set.preimage_image_eq _ (toWeakSpace ℝ X).injective]
    exact NormedVectorLattice.isBounded_of_bddBelow_bddAbove bddBelow_Icc bddAbove_Icc
  have hc := NormedSpace.isCompact_closure_of_isBounded ℝ X W hb
    (closure_inclusion_Icc_subset_range hi x hx)
  have hW : closure W = W := by
    simpa only [isClosed_Icc.closure_eq] using
      ((convex_Icc (0 : X) x).toWeakSpace_closure ℝ).symm
  simpa only [hW] using hc

/-- Interval preservation makes the canonical bidual range solid: a vector whose
modulus is bounded by that of an image vector also belongs to the range. -/
private lemma mem_range_inclusion_of_abs_le
    (h : ∀ x : X, 0 ≤ x → inclusion '' Icc 0 x = Icc 0 (inclusion x))
    {x : X} {y : BidualSpace X} (hy : |y| ≤ |inclusion x|) :
    y ∈ range (inclusion (X := X)) := by
  have hb : |y| ≤ inclusion |x| := (inclusion_abs x).symm ▸ hy
  have hp : y⁺ ∈ inclusion '' Icc 0 |x| :=
    (h |x| (abs_nonneg x)).symm ▸
      ⟨posPart_nonneg y, (sup_le (le_abs_self y) (abs_nonneg y)).trans hb⟩
  have hn : y⁻ ∈ inclusion '' Icc 0 |x| :=
    (h |x| (abs_nonneg x)).symm ▸
      ⟨negPart_nonneg y, (sup_le (neg_le_abs y) (abs_nonneg y)).trans hb⟩
  obtain ⟨a, _, ha⟩ := hp
  obtain ⟨b, _, hb⟩ := hn
  exact ⟨a - b, by rw [map_sub, ha, hb, posPart_sub_negPart]⟩

/-- The canonical embedding preserves positive intervals exactly when
its range is an order ideal. -/
theorem image_inclusion_Icc_iff_range_eq_orderIdeal :
    (∀ x : X, 0 ≤ x → inclusion '' Icc 0 x = Icc 0 (inclusion x)) ↔
      ∃ J : OrderIdeal (BidualSpace X), range inclusion = (J : Set (BidualSpace X)) := by
  constructor
  · intro h
    refine ⟨OrderIdeal.ofSolid (inclusion (X := X)).range ?_, rfl⟩
    rintro _ y ⟨x, rfl⟩ hy
    exact mem_range_inclusion_of_abs_le h hy
  · rintro ⟨J, hJ⟩ x hx
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨inclusion_nonneg hz.1, inclusion_le_inclusion_iff.mpr hz.2⟩
    · intro hy
      have hxJ : inclusion x ∈ (J : Set (BidualSpace X)) := hJ ▸ mem_range_self x
      obtain ⟨z, rfl⟩ := hJ.symm ▸ (show y ∈ (J : Set (BidualSpace X)) from J.solid hxJ hy.1 hy.2)
      exact ⟨z, ⟨inclusion_le_inclusion_iff.mp (by simpa using hy.1),
        inclusion_le_inclusion_iff.mp hy.2⟩, rfl⟩

/-- Existing suprema of nonempty upward directed sets of continuous functionals are
computed pointwise on positive vectors. -/
private lemma isLUB_apply_of_directedOn (A : Set (StrongDual ℝ X))
    (hne : A.Nonempty) (hdir : DirectedOn (· ≤ ·) A)
    (F : StrongDual ℝ X) (hF : IsLUB A F) (x : X) (hx : 0 ≤ x) :
    IsLUB ((fun φ : StrongDual ℝ X ↦ φ x) '' A) (F x) := by
  let e : StrongDual ℝ X ≃o OrderDualSpace X := {
    toEquiv := StrongDual.equivOrderDualSpace.toEquiv
    map_rel_iff' := by rfl }
  have hE : IsLUB (e '' A) (e F) :=
    e.isLUB_image.mpr (by simpa only [OrderIso.symm_apply_apply] using hF)
  have hdir' : DirectedOn (· ≤ ·) (e '' A) := by
    rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    obtain ⟨η, hη, hφη, hψη⟩ := hdir φ hφ ψ hψ
    exact ⟨e η, ⟨η, hη, rfl⟩, e.monotone hφη, e.monotone hψη⟩
  obtain ⟨G, hG, hpoint⟩ := OrderBoundedHom.isLUB_of_directedOn
    (hne.image e) hdir' ⟨e F, hE.1⟩
  have heq : G = e F := hG.unique hE
  have hp := hpoint hx
  rw [heq, Set.image_image] at hp
  exact hp

/-- If the canonical embedding preserves nonempty suprema, every decreasing net
with infimum zero converges weakly to zero. -/
private lemma weak_tendsto_zero_of_isLUB_image_inclusion
    (hr : ∀ (A : Set X) (a : X), A.Nonempty → IsLUB A a →
      IsLUB (inclusion '' A) (inclusion a))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {f : I → X} (hf : Antitone f) (hglb : IsGLB (range f) 0) :
    Tendsto (fun i ↦ toWeakSpace ℝ X (f i)) atTop (𝓝 (toWeakSpace ℝ X 0)) := by
  have hn : IsLUB (range (fun i ↦ -f i)) (0 : X) := by
    simpa only [← Set.image_neg_eq_neg, ← Set.range_comp, Function.comp_def, neg_zero]
      using hglb.neg
  have hjn : IsLUB (range (fun i ↦ inclusion (-f i))) 0 := by
    simpa only [← Set.range_comp, Function.comp_def, map_zero] using
      hr (range (fun i ↦ -f i)) 0 (range_nonempty _) hn
  have hm : Monotone (fun i ↦ inclusion (-f i)) :=
    fun i j hij ↦ (inclusionVecLatHom (X := X)).monotone (neg_le_neg (hf hij))
  have hdir : DirectedOn (· ≤ ·) (range (fun i ↦ inclusion (X := X) (-f i))) :=
    directedOn_range.mpr (fun i j ↦ (exists_ge_ge i j).imp
      (fun k hk ↦ ⟨hm hk.1, hm hk.2⟩))
  have hposTend (φ : StrongDual ℝ X) (hφ : 0 ≤ φ) :
      Tendsto (fun i ↦ φ (f i)) atTop (nhds 0) := by
    have hp := isLUB_apply_of_directedOn (X := StrongDual ℝ X) _ (range_nonempty _) hdir 0 hjn φ hφ
    change IsLUB ((fun F : StrongDual ℝ (StrongDual ℝ X) ↦ F φ) ''
      range (fun i ↦ inclusion (-f i))) (0 : ℝ) at hp
    rw [← Set.range_comp' (fun F : StrongDual ℝ (StrongDual ℝ X) ↦ F φ)
      (fun i ↦ inclusion (-f i))] at hp
    change IsLUB (range (fun i ↦ φ (-f i))) 0 at hp
    simpa only [map_neg, neg_neg, neg_zero] using
      (tendsto_atTop_isLUB (fun i j hij ↦
        StrongDual.apply_le_apply_of_nonneg hφ (neg_le_neg (hf hij))) hp).neg
  have hall (φ : StrongDual ℝ X) : Tendsto (fun i ↦ φ (f i)) atTop (nhds 0) := by
    simpa only [← sub_apply, posPart_sub_negPart, sub_zero] using
      (hposTend φ⁺ (posPart_nonneg φ)).sub (hposTend φ⁻ (negPart_nonneg φ))
  have hb : Function.Injective ((topDualPairing ℝ X).flip) :=
    fun x y hxy ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
      (fun φ ↦ DFunLike.congr_fun hxy φ)
  have hw : Tendsto (fun i ↦ toWeakSpace ℝ X (f i)) atTop
      (nhds (toWeakSpace ℝ X 0)) :=
    (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ X).flip hb).2
      (fun φ ↦ show Tendsto (fun i ↦ φ (f i)) atTop (nhds (φ 0)) from
        by simpa only [map_zero] using hall φ)
  exact hw

/-- Preservation of nonempty suprema by the canonical embedding forces order continuity. -/
theorem isOrderContinuousNorm_of_isLUB_image_inclusion
    (h : ∀ (A : Set X) (a : X), A.Nonempty → IsLUB A a →
      IsLUB (inclusion '' A) (inclusion a)) : IsOrderContinuousNorm X :=
  ⟨fun hf _ hglb ↦ StrongDual.tendsto_of_monotone_weak_tendsto (Or.inr hf)
    (weak_tendsto_zero_of_isLUB_image_inclusion h hf hglb)⟩

/-- The norm is order continuous exactly when the canonical embedding
preserves nonempty suprema. -/
theorem isOrderContinuousNorm_iff_isLUB_image_inclusion :
    IsOrderContinuousNorm X ↔
      ∀ (A : Set X) (a : X), A.Nonempty → IsLUB A a →
        IsLUB (inclusion '' A) (inclusion a) :=
  ⟨fun _ _ _ hA ha ↦ isLUB_image_inclusion hA ha,
    isOrderContinuousNorm_of_isLUB_image_inclusion⟩

/-- The canonical bidual image is an order ideal exactly when
positive intervals are weakly compact. -/
theorem range_inclusion_eq_orderIdeal_iff_isCompact_Icc :
    (∃ J : OrderIdeal (BidualSpace X), range inclusion = (J : Set (BidualSpace X))) ↔
      ∀ x : X, 0 ≤ x → IsCompact (toWeakSpace ℝ X '' Icc 0 x) :=
  image_inclusion_Icc_iff_range_eq_orderIdeal.symm.trans
    ⟨isCompact_Icc_of_image_inclusion_Icc, image_inclusion_Icc_of_isCompact⟩

/-- An order ideal canonical bidual image ensures that the embedding preserves
all existing nonempty suprema. -/
private lemma isLUB_image_inclusion_of_range_eq_orderIdeal
    (J : OrderIdeal (BidualSpace X)) (hJ : range inclusion = (J : Set (BidualSpace X)))
    {A : Set X} {a : X} (hA : A.Nonempty) (ha : IsLUB A a) :
    IsLUB (inclusion '' A) (inclusion a) := by
  obtain ⟨a₀, ha₀⟩ := hA
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact inclusion_le_inclusion_iff.mpr (ha.1 hx)
  · intro b hb
    have h₀ : inclusion a₀ ≤ b ⊓ inclusion a :=
      le_inf (hb ⟨a₀, ha₀, rfl⟩) (inclusion_le_inclusion_iff.mpr (ha.1 ha₀))
    have hmem : inclusion (a - a₀) ∈ (J : Set (BidualSpace X)) :=
      hJ ▸ mem_range_self _
    have hz : b ⊓ inclusion a - inclusion a₀ ∈ (J : Set (BidualSpace X)) :=
      J.solid hmem (sub_nonneg.mpr h₀)
        (by rw [map_sub]; exact sub_le_sub_right inf_le_right _)
    obtain ⟨z, hz⟩ := hJ.symm ▸ hz
    have heq : inclusion (z + a₀) = b ⊓ inclusion a := by
      rw [map_add, hz, sub_add_cancel]
    have hub : a ≤ z + a₀ := ha.2 fun x hx ↦
      inclusion_le_inclusion_iff.mp (heq.symm ▸
        le_inf (hb ⟨x, hx, rfl⟩) (inclusion_le_inclusion_iff.mpr (ha.1 hx)))
    exact (inclusion_le_inclusion_iff.mpr hub).trans (heq ▸ inf_le_left)

/-- An ideal canonical bidual image forces order continuity of the norm. -/
theorem isOrderContinuousNorm_of_range_inclusion_eq_orderIdeal
    (h : ∃ J : OrderIdeal (BidualSpace X), range inclusion = (J : Set (BidualSpace X))) :
    IsOrderContinuousNorm X :=
  isOrderContinuousNorm_of_isLUB_image_inclusion fun _ _ hA ha ↦
    isLUB_image_inclusion_of_range_eq_orderIdeal h.choose h.choose_spec hA ha

end BidualSpace
