/-
Authors: Pedro Tradacete
-/

import BanLat.Convergences.SigmaOrder
import BanLat.Operators.OrderContinuous

/-!
# σ-order continuous operators

σ-order continuous linear maps preserve σ-order convergence. For positive maps,
this is equivalent to preserving zero infima of decreasing sequences. The
order bounded σ-order continuous operators into an order complete vector lattice
form a projection band in the lattice of order bounded operators.
-/

universe u v w

variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]

/-- A linear map is σ-order continuous if it preserves σ-order convergence of nets. -/
def IsSigmaOrderContinuousOp (T : X →ₗ[ℝ] Y) : Prop :=
  ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {x : ι → X} {a : X},
    SigmaOrderConvergesTo x a → SigmaOrderConvergesTo (fun i ↦ T (x i)) (T a)

namespace IsSigmaOrderContinuousOp

/-- The zero linear map is σ-order continuous. -/
theorem zero : IsSigmaOrderContinuousOp (0 : X →ₗ[ℝ] Y) :=
  fun {_} _ _ _ {_} {_} _ ↦ sigmaOrderConvergesTo_const 0

/-- The identity linear map is σ-order continuous. -/
theorem id : IsSigmaOrderContinuousOp (LinearMap.id : X →ₗ[ℝ] X) :=
  fun {_} _ _ _ {_} {_} hx ↦ hx

/-- Sums of σ-order continuous linear maps are σ-order continuous. -/
theorem add {S T : X →ₗ[ℝ] Y} (hS : IsSigmaOrderContinuousOp S)
    (hT : IsSigmaOrderContinuousOp T) : IsSigmaOrderContinuousOp (S + T) :=
  fun {_} _ _ _ {_} {_} hx ↦ (hS hx).add (hT hx)

/-- Negatives of σ-order continuous linear maps are σ-order continuous. -/
theorem neg {T : X →ₗ[ℝ] Y} (hT : IsSigmaOrderContinuousOp T) :
    IsSigmaOrderContinuousOp (-T) :=
  fun {_} _ _ _ {_} {_} hx ↦ (hT hx).neg

/-- Differences of σ-order continuous linear maps are σ-order continuous. -/
theorem sub {S T : X →ₗ[ℝ] Y} (hS : IsSigmaOrderContinuousOp S)
    (hT : IsSigmaOrderContinuousOp T) : IsSigmaOrderContinuousOp (S - T) :=
  fun {_} _ _ _ {_} {_} hx ↦ (hS hx).sub (hT hx)

/-- Scalar multiples of σ-order continuous linear maps are σ-order continuous. -/
theorem smul {T : X →ₗ[ℝ] Y} (hT : IsSigmaOrderContinuousOp T) (c : ℝ) :
    IsSigmaOrderContinuousOp (c • T) :=
  fun {_} _ _ _ {_} {_} hx ↦ (hT hx).smul c

end IsSigmaOrderContinuousOp

private lemma decreasing_abs_glb_zero {T : X →ₗ[ℝ] Y}
    (hT : IsSigmaOrderContinuousOp T) {x : ℕ → X} (hx : Antitone x)
    (hglb : IsGLB (Set.range x) 0) : IsGLB (Set.range fun n ↦ |T (x n)|) 0 := by
  refine ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ abs_nonneg _, fun z hz ↦ ?_⟩
  have hxlift : SigmaOrderConvergesTo (fun n : ULift.{u} ℕ ↦ x n.down) 0 :=
    ⟨x, hx, fun n ↦ hglb.1 ⟨n, rfl⟩, hglb, fun n ↦
      Filter.eventually_atTop.mpr ⟨⟨n⟩, fun m hnm ↦ by
        simpa only [sub_zero, abs_of_nonneg (hglb.1 ⟨m.down, rfl⟩)] using hx hnm⟩⟩
  simpa only [map_zero, abs_zero] using
    (hT hxlift).abs.forall_le (fun n ↦ hz ⟨n.down, rfl⟩)

private lemma positive_sigmaOrderContinuous_of_isGLB_zero {T : X →ₗ[ℝ] Y}
    (hT : Positive T)
    (h : ∀ {x : ℕ → X}, Antitone x → IsGLB (Set.range x) 0 →
      IsGLB (Set.range fun n ↦ T (x n)) 0) : IsSigmaOrderContinuousOp T := by
  rintro ι _ _ _ x a ⟨r, hr, hrnn, hrglb, hrevent⟩
  exact ⟨fun n ↦ T (r n), (Positive.monotone_iff.mpr hT).comp_antitone hr,
    fun n ↦ hT _ (hrnn n), h hr hrglb, fun n ↦ (hrevent n).mono fun i hi ↦ by
      simpa only [map_sub] using (Positive.abs_le_map_abs hT (x i - a)).trans
        (Positive.monotone_iff.mpr hT hi)⟩

/-- A positive linear map is σ-order continuous exactly when it sends decreasing sequences with
infimum zero to decreasing sequences with infimum zero. -/
theorem Positive.isSigmaOrderContinuousOp_iff_isGLB_zero {T : X →ₗ[ℝ] Y}
    (hT : Positive T) :
    IsSigmaOrderContinuousOp T ↔
      ∀ {x : ℕ → X}, Antitone x → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun n ↦ T (x n)) 0 := by
  refine ⟨fun h x hx hglb ↦ ?_, positive_sigmaOrderContinuous_of_isGLB_zero hT⟩
  simpa only [abs_of_nonneg (hT _ (hglb.1 ⟨_, rfl⟩))] using
    decreasing_abs_glb_zero h hx hglb

private lemma decreasing_abs_glb_zero_of_orderContinuous {T : X →ₗ[ℝ] Y}
    (hT : IsOrderContinuousOp T) {x : ℕ → X} (hx : Antitone x)
    (hglb : IsGLB (Set.range x) 0) : IsGLB (Set.range fun n ↦ |T (x n)|) 0 := by
  refine ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ abs_nonneg _, fun z hz ↦ ?_⟩
  have hc := hT (orderConvergesTo_of_antitone_isGLB
    (show Antitone (fun n : ULift.{u} ℕ ↦ x n.down) from fun _ _ h ↦ hx h)
    ((ULift.down_surjective.range_comp x).symm ▸ hglb))
  simpa only [map_zero, abs_zero] using hc.abs.forall_le (fun n ↦ hz ⟨n.down, rfl⟩)

/-- An order continuous positive linear map is σ-order continuous. -/
theorem Positive.isSigmaOrderContinuousOp {T : X →ₗ[ℝ] Y}
    (hT : Positive T) (h : IsOrderContinuousOp T) : IsSigmaOrderContinuousOp T :=
  hT.isSigmaOrderContinuousOp_iff_isGLB_zero.mpr fun hx hglb ↦ by
    simpa only [abs_of_nonneg (hT _ (hglb.1 ⟨_, rfl⟩))] using
      decreasing_abs_glb_zero_of_orderContinuous h hx hglb

namespace SigmaOrderContinuousOp

/-- The set of order bounded σ-order continuous operators. -/
def SigmaOrderContinuousOperator : Set (OrderBoundedHom X Y) :=
  {T | IsSigmaOrderContinuousOp T.toLinearMap}

/-- Membership means that the underlying linear map is σ-order continuous. -/
@[simp]
theorem mem_SigmaOrderContinuousOperator (T : OrderBoundedHom X Y) :
    T ∈ SigmaOrderContinuousOperator ↔ IsSigmaOrderContinuousOp T.toLinearMap :=
  Iff.rfl

variable {Y : Type v} [AddCommGroup Y] [ConditionallyCompleteLattice Y]
  [IsOrderedAddMonoid Y] [VectorLattice Y]

private lemma posPart_sub_le_abs_inf (T : OrderBoundedHom X Y) {a b c : X}
    (hba : b ≤ a) (hca : c ≤ a) :
    T⁺ b - (T⁺ a - T c) ≤ |T (c ⊓ b)| := by
  have hdiff : c - c ⊓ b ≤ a - b := by
    simpa only [sub_inf_eq_posPart, posPart_of_nonneg (sub_nonneg.mpr hba)] using
      posPart_mono (sub_le_sub_right hca b)
  have hlin : T c - T (c ⊓ b) ≤ T⁺ a - T⁺ b := by
    simpa only [← OrderBoundedHom.toLinearMap_apply, map_sub] using
      (OrderBoundedHom.le_iff.mp (le_posPart T) _ (sub_nonneg.mpr inf_le_left)).trans
        (Positive.monotone_iff.mpr
          (show Positive T⁺.toLinearMap from OrderBoundedHom.le_iff.mp (posPart_nonneg T))
          hdiff)
  calc
    T⁺ b - (T⁺ a - T c) = (T c + T⁺ b) - T⁺ a := by abel
    _ ≤ (T⁺ a + T (c ⊓ b)) - T⁺ a :=
      sub_le_sub_right (sub_le_sub_iff.mp hlin) _
    _ = T (c ⊓ b) := by abel
    _ ≤ |T (c ⊓ b)| := le_abs_self _

private lemma posPart_decreasing_glb_zero (T : OrderBoundedHom X Y)
    (h : ∀ {x : ℕ → X}, Antitone x → IsGLB (Set.range x) 0 →
      IsGLB (Set.range fun n ↦ |T (x n)|) 0)
    {x : ℕ → X} (hx : Antitone x) (hglb : IsGLB (Set.range x) 0) :
    IsGLB (Set.range fun n ↦ T⁺ (x n)) 0 := by
  refine ⟨fun _ ⟨n, hn⟩ ↦ hn ▸
    OrderBoundedHom.le_iff.mp (posPart_nonneg T) _ (hglb.1 ⟨n, rfl⟩), fun z hz ↦ ?_⟩
  have hzsub (c : X) (hc : 0 ≤ c) (hcx : c ≤ x 0) : z ≤ T⁺ (x 0) - T c :=
    sub_nonpos.mp ((h (fun _ _ hnm ↦ inf_le_inf_left c (hx hnm))
      ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ le_inf hc (hglb.1 ⟨n, rfl⟩),
        fun _ hb ↦ hglb.2 fun _ ⟨n, hn⟩ ↦ hn ▸ (hb ⟨n, rfl⟩).trans inf_le_right⟩).2
      (fun _ ⟨n, hn⟩ ↦ hn ▸ (sub_le_sub_right (hz ⟨n, rfl⟩) _).trans
        (posPart_sub_le_abs_inf T (hx (Nat.zero_le n)) hcx)))
  exact add_le_iff_nonpos_left.mp (le_sub_iff_add_le'.mp
    ((OrderBoundedHom.isLUB_posPart_apply (f := T) (hglb.1 ⟨0, rfl⟩)).2
      (fun _ ⟨c, hc, hcx, heq⟩ ↦ heq ▸ le_sub_comm.mp (hzsub c hc hcx))))

private lemma parts_sigmaOrderContinuous_of_decreasing_abs_glb_zero
    (T : OrderBoundedHom X Y)
    (h : ∀ {x : ℕ → X}, Antitone x → IsGLB (Set.range x) 0 →
      IsGLB (Set.range fun n ↦ |T (x n)|) 0) :
    IsSigmaOrderContinuousOp T⁺.toLinearMap ∧ IsSigmaOrderContinuousOp T⁻.toLinearMap := by
  refine ⟨positive_sigmaOrderContinuous_of_isGLB_zero
    (OrderBoundedHom.le_iff.mp (posPart_nonneg T)) (posPart_decreasing_glb_zero T h), ?_⟩
  have hneg : IsSigmaOrderContinuousOp (-T)⁺.toLinearMap :=
    positive_sigmaOrderContinuous_of_isGLB_zero
      (OrderBoundedHom.le_iff.mp (posPart_nonneg (-T)))
      (posPart_decreasing_glb_zero (-T) fun {x} hx hglb ↦ by
        simpa only [show ∀ y, (-T : OrderBoundedHom X Y) y = -T y from fun _ ↦ rfl,
          abs_neg] using h hx hglb)
  exact (posPart_neg T) ▸ @hneg

private lemma modulus_sigmaOrderContinuous_of_parts (T : OrderBoundedHom X Y)
    (h : IsSigmaOrderContinuousOp T⁺.toLinearMap ∧
      IsSigmaOrderContinuousOp T⁻.toLinearMap) :
    IsSigmaOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap := by
  rw [← posPart_add_negPart]
  exact IsSigmaOrderContinuousOp.add h.1 h.2

private lemma sigmaOrderContinuous_of_abs_le {S T : OrderBoundedHom X Y}
    (hT : IsSigmaOrderContinuousOp T.toLinearMap) (hST : ∀ x, |S x| ≤ T |x|) :
    IsSigmaOrderContinuousOp S.toLinearMap := by
  intro ι _ _ _ x a hx
  have habs : SigmaOrderConvergesTo (fun i ↦ |x i - a|) 0 := by
    simpa only [sub_self, abs_zero] using (hx.sub (sigmaOrderConvergesTo_const a)).abs
  obtain ⟨r, hr, hrnn, hrglb, hrevent⟩ := hT habs
  exact ⟨r, hr, hrnn, hrglb, fun n ↦ (hrevent n).mono fun i hi ↦
    (show |S.toLinearMap (x i) - S.toLinearMap a| ≤ T |x i - a| by
      simpa only [← OrderBoundedHom.toLinearMap_apply, map_sub] using hST (x i - a)).trans
        ((le_abs_self _).trans (by
          simpa only [map_zero, sub_zero, OrderBoundedHom.toLinearMap_apply] using hi))⟩

/-- For order bounded maps into an order complete vector lattice, σ-order continuity
is characterized by decreasing zero sequences, by both parts, and by the modulus. -/
theorem characterization (T : OrderBoundedHom X Y) :
    List.TFAE [
      IsSigmaOrderContinuousOp T.toLinearMap,
      (∀ {x : ℕ → X}, Antitone x → IsGLB (Set.range x) 0 →
        IsGLB (Set.range fun n ↦ |T (x n)|) 0),
      IsSigmaOrderContinuousOp T⁺.toLinearMap ∧ IsSigmaOrderContinuousOp T⁻.toLinearMap,
      IsSigmaOrderContinuousOp (|T| : OrderBoundedHom X Y).toLinearMap] := by
  refine List.tfae_of_cycle ?_ (fun h ↦ sigmaOrderContinuous_of_abs_le h fun x ↦
    (OrderBoundedHom.isLUB_abs_apply (f := T) (abs_nonneg x)).1 ⟨x, le_rfl, rfl⟩)
  simp only [List.isChain_cons_cons]
  exact ⟨fun h _ hx hglb ↦ decreasing_abs_glb_zero h hx hglb,
    parts_sigmaOrderContinuous_of_decreasing_abs_glb_zero T,
    modulus_sigmaOrderContinuous_of_parts T, List.IsChain.singleton _⟩

/-- An order continuous order bounded map into an order complete vector lattice
is σ-order continuous. -/
theorem of_isOrderContinuousOp {T : OrderBoundedHom X Y}
    (hT : IsOrderContinuousOp T.toLinearMap) : IsSigmaOrderContinuousOp T.toLinearMap :=
  ((characterization T).out 0 1 rfl rfl).mpr fun hx hglb ↦
    decreasing_abs_glb_zero_of_orderContinuous hT hx hglb

/-- An order bounded map dominated in modulus by a σ-order continuous map is
σ-order continuous. -/
theorem of_abs_le_abs {S T : OrderBoundedHom X Y}
    (hT : IsSigmaOrderContinuousOp T.toLinearMap) (hST : |S| ≤ |T|) :
    IsSigmaOrderContinuousOp S.toLinearMap :=
  sigmaOrderContinuous_of_abs_le (((characterization T).out 0 3 rfl rfl).mp @hT) fun x ↦
    ((OrderBoundedHom.isLUB_abs_apply (f := S) (abs_nonneg x)).1 ⟨x, le_rfl, rfl⟩).trans
      (OrderBoundedHom.le_iff.mp hST _ (abs_nonneg x))

private noncomputable def operatorOrderIdeal : OrderIdeal (OrderBoundedHom X Y) :=
  OrderIdeal.ofSolid
    { carrier := SigmaOrderContinuousOperator
      zero_mem' := IsSigmaOrderContinuousOp.zero
      add_mem' := fun hS hT ↦ IsSigmaOrderContinuousOp.add hS hT
      smul_mem' := fun c _ hT ↦ IsSigmaOrderContinuousOp.smul hT c }
    (fun _ _ hT hST ↦ of_abs_le_abs hT hST)

private lemma lowerBound_le_sub {A T : OrderBoundedHom X Y}
    (hApos : Positive A.toLinearMap) (hA : IsSigmaOrderContinuousOp A.toLinearMap)
    (hAT : A ≤ T) {x : ℕ → X} (hx : Antitone x) (hglb : IsGLB (Set.range x) 0)
    {z : Y} (hz : ∀ n, z ≤ T (x n)) : z ≤ T (x 0) - A (x 0) := by
  apply sub_nonpos.mp
    (((hApos.isSigmaOrderContinuousOp_iff_isGLB_zero.mp hA) hx hglb).2 ?_)
  rintro _ ⟨n, rfl⟩
  have hdiff : T (x n) - A (x n) ≤ T (x 0) - A (x 0) :=
    Positive.monotone_iff.mpr
      (show Positive (T - A).toLinearMap from
        OrderBoundedHom.le_iff.mp (sub_nonneg.mpr hAT)) (hx (Nat.zero_le n))
  exact sub_le_iff_le_add'.mpr ((hz n).trans (sub_le_iff_le_add.mp hdiff))

private lemma positive_directed_isLUB_mem
    {S : Set (OrderBoundedHom X Y)} (hS : S ⊆ SigmaOrderContinuousOperator)
    (hpos : ∀ A ∈ S, 0 ≤ A) (hdir : DirectedOn (· ≤ ·) S) (hne : S.Nonempty)
    {T : OrderBoundedHom X Y} (hT : IsLUB S T) : T ∈ SigmaOrderContinuousOperator := by
  have hTpos : Positive T.toLinearMap := OrderBoundedHom.le_iff.mp
    ((hpos hne.choose hne.choose_spec).trans (hT.1 hne.choose_spec))
  change IsSigmaOrderContinuousOp T.toLinearMap
  refine positive_sigmaOrderContinuous_of_isGLB_zero hTpos fun {x} hx hglb ↦
    ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ hTpos _ (hglb.1 ⟨n, rfl⟩), fun z hz ↦ ?_⟩
  obtain ⟨U, hU, hpoint⟩ := OrderBoundedHom.isLUB_of_directedOn hne hdir ⟨T, hT.1⟩
  have hpointT : IsLUB ((fun A : OrderBoundedHom X Y ↦ A (x 0)) '' S) (T (x 0)) :=
    hU.unique hT ▸ hpoint (hglb.1 ⟨0, rfl⟩)
  exact add_le_iff_nonpos_left.mp (le_sub_iff_add_le'.mp
    (hpointT.2 fun _ ⟨A, hA, heq⟩ ↦ heq ▸ le_sub_comm.mp
      (lowerBound_le_sub (OrderBoundedHom.le_iff.mp (hpos A hA)) (hS hA)
        (hT.1 hA) hx hglb (fun n ↦ hz ⟨n, rfl⟩))))

private noncomputable def operatorBand : Band (OrderBoundedHom X Y) :=
  Band.ofPosDirectedSSupMem operatorOrderIdeal
    (fun _ hS hpos hdir hne _ hT ↦ positive_directed_isLUB_mem hS hpos hdir hne hT)

/-- The order bounded σ-order continuous operators into an order complete vector
lattice form a projection band. -/
theorem exists_projectionBand :
    ∃ B : ProjectionBand (OrderBoundedHom X Y),
      (B : Set (OrderBoundedHom X Y)) = SigmaOrderContinuousOperator := by
  letI : ConditionallyCompleteLattice (OrderBoundedHom X Y) :=
    @conditionallyCompleteLatticeOfPosSet (OrderBoundedHom X Y) _ _ _
      (fun {S} _ hne hbdd ↦ OrderBoundedHom.exists_isLUB (S := S) hne hbdd)
  haveI : HasProjectionProperty (OrderBoundedHom X Y) :=
    HasProjectionProperty.of_isOrderComplete
  exact HasProjectionProperty.exists_projectionBand (operatorBand (X := X) (Y := Y))

section Functional

variable {X : Type u} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X] [CompleteSpace X] [IsSigmaOrderContinuousNorm X]

/-- On a Banach lattice with σ-order continuous norm, every order bounded
real-valued functional is σ-order continuous. -/
theorem functional_sigmaOrderContinuous_of_sigmaOrderContinuousNorm
    (f : OrderBoundedHom X ℝ) : IsSigmaOrderContinuousOp f.toLinearMap := by
  apply ((characterization f).out 0 1 rfl rfl).mpr
  intro x hx hglb
  letI : BanachLattice X := {}
  have ht : Filter.Tendsto (fun n ↦ |f (x n)|) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, map_zero, abs_zero, OrderBoundedHom.toLinearMap_apply]
      using (((IsOrderBounded.continuous f.isOrderBounded').tendsto 0).comp
        (IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB hx hglb)).abs
  exact ⟨fun _ ⟨n, hn⟩ ↦ hn ▸ abs_nonneg _,
    fun _ hb ↦ ge_of_tendsto' ht (fun n ↦ hb ⟨n, rfl⟩)⟩

end Functional

end SigmaOrderContinuousOp
