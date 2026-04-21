import BanLat.Normed
import BanLat.Band
import BanLat.OrderComplete

/-!
# Order continuous norms

A normed vector lattice has an **order continuous norm** when every decreasing
sequence of non-negative elements with infimum zero converges to zero in norm.
Equivalently, every increasing positive sequence whose supremum exists converges
in norm to that supremum.

The main results stated here are:
- Equivalent characterisations of an order continuous norm for sequences.
- Nakano's theorem: a Banach lattice has an order continuous norm and is
  σ-order complete iff every increasing order-bounded sequence converges in
  norm.
- The Meyer-Nieberg theorem: a Banach lattice is order continuous iff every
  order-bounded pairwise disjoint sequence converges to zero in norm.
- Ando's theorem: a Banach lattice is order continuous iff every norm-closed
  ideal is a band.
-/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

/-! ### Definitions -/

/-- A normed vector lattice has a **σ-order continuous norm** if every antitone
sequence of non-negative elements with greatest lower bound zero converges to
zero in norm. -/
class IsSigmaOrderContinuousNorm (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {u : ℕ → X}, Antitone u → (∀ n, 0 ≤ u n) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- A normed vector lattice has an **order continuous norm** if every antitone
net of non-negative elements (over a non-empty directed index set) with
greatest lower bound zero converges to zero in norm.

The index set `ι` is constrained to live in the same universe as `X`; in
applications (e.g. indexing by a subset of `X`) this is the case. -/
class IsOrderContinuousNorm.{u} (X : Type u) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → X}, Antitone u → (∀ i, 0 ≤ u i) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- An order continuous norm is in particular σ-order continuous. -/
instance (priority := 100)
    IsOrderContinuousNorm.toIsSigmaOrderContinuousNorm.{u} {X : Type u}
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] [h : IsOrderContinuousNorm X] :
    IsSigmaOrderContinuousNorm X := by
  refine ⟨fun {u} hanti hnn hglb => ?_⟩
  -- Transfer the ℕ-indexed sequence to the universe of `X` via `ULift`.
  let u' : ULift.{u, 0} ℕ → X := fun n => u n.down
  have hu'_anti : Antitone u' := fun a b h => hanti (by exact h)
  have hu'_nn : ∀ i, 0 ≤ u' i := fun i => hnn i.down
  have hu'_glb : IsGLB (Set.range u') 0 := by
    have hrange : Set.range u' = Set.range u := by
      ext z; constructor
      · rintro ⟨⟨n⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨⟨n⟩, rfl⟩
    rw [hrange]; exact hglb
  have htend := h.tendsto_of_antitone_isGLB_zero hu'_anti hu'_nn hu'_glb
  -- Pull back to ℕ: the map `n ↦ ⟨n⟩ : ℕ → ULift ℕ` is order isomorphic.
  have : Filter.Tendsto (fun n : ℕ => u' ⟨n⟩) Filter.atTop (nhds 0) := by
    refine htend.comp ?_
    refine Filter.tendsto_atTop.mpr fun ⟨b⟩ => ?_
    exact Filter.eventually_atTop.mpr ⟨b, fun n hn => hn⟩
  exact this

namespace IsSigmaOrderContinuousNorm

variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]

/-! ### Equivalent sequential characterisations -/

/-- An increasing sequence with a least upper bound converges in norm to
that bound. -/
theorem tendsto_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u) (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  -- Define v n = x - u n, which is antitone, nonneg, with GLB 0
  have hv_anti : Antitone (fun n => x - u n) :=
    fun _ _ h => sub_le_sub_left (hmono h) x
  have hv_nn : ∀ n, 0 ≤ x - u n :=
    fun n => sub_nonneg.mpr (hlub.1 ⟨n, rfl⟩)
  have hv_glb : IsGLB (Set.range (fun n => x - u n)) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩; exact hv_nn n
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, y ≤ x - w := by
        rintro _ ⟨n, rfl⟩
        exact le_sub_comm.mp (hw ⟨n, rfl⟩)
      have h := hlub.2 hlb
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  have htv := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  convert htv.const_sub x using 1
  · ext n; abel
  · abel

/-- An antitone sequence with a greatest lower bound converges in norm to
that bound. -/
theorem tendsto_of_antitone_isGLB {u : ℕ → X} {x : X}
    (hanti : Antitone u) (hglb : IsGLB (Set.range u) x) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  have hv_anti : Antitone (fun n => u n - x) :=
    fun _ _ h => sub_le_sub_right (hanti h) x
  have hv_nn : ∀ n, 0 ≤ u n - x :=
    fun n => sub_nonneg.mpr (hglb.1 ⟨n, rfl⟩)
  have hv_glb : IsGLB (Set.range (fun n => u n - x)) 0 := by
    constructor
    · rintro _ ⟨n, rfl⟩; exact hv_nn n
    · intro w hw
      have hlb : ∀ y ∈ Set.range u, w + x ≤ y := by
        rintro _ ⟨n, rfl⟩
        exact add_le_of_le_sub_right (hw ⟨n, rfl⟩)
      have h := hglb.2 hlb
      rwa [add_le_iff_nonpos_left] at h
  have htv := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  convert htv.add tendsto_const_nhds using 1
  · ext n; abel
  · abel

/-- The norm is σ-order continuous: if `|u n - x| ≤ v n` for an antitone
sequence `v` with `inf v = 0`, then `u n → x` in norm. -/
theorem tendsto_of_abs_sub_le_antitone {u : ℕ → X} {v : ℕ → X} {x : X}
    (hv_anti : Antitone v) (hv_nn : ∀ n, 0 ≤ v n)
    (hv_glb : IsGLB (Set.range v) 0)
    (hle : ∀ n, |u n - x| ≤ v n) :
    Filter.Tendsto u Filter.atTop (nhds x) := by
  have hv_tend := tendsto_of_antitone_isGLB_zero hv_anti hv_nn hv_glb
  have hnorm_le : ∀ n, ‖u n - x‖ ≤ ‖v n‖ := fun n =>
    norm_le_norm_of_abs_le_abs ((hle n).trans (le_abs_self _))
  have hv_norm := hv_tend.norm
  rw [norm_zero] at hv_norm
  have h0 := squeeze_zero_norm hnorm_le hv_norm
  exact tendsto_sub_nhds_zero_iff.mp h0

/-- The norm itself is an order continuous function on positive elements:
if `u n` converges in order to `x`, then `‖u n‖ → ‖x‖`. -/
theorem tendsto_norm_of_monotone_isLUB {u : ℕ → X} {x : X}
    (hmono : Monotone u)
    (hlub : IsLUB (Set.range u) x) :
    Filter.Tendsto (fun n => ‖u n‖) Filter.atTop (nhds ‖x‖) :=
  (tendsto_of_monotone_isLUB hmono hlub).norm

end IsSigmaOrderContinuousNorm

/-! ### Order continuity in Banach lattices -/

namespace BanachLattice

variable [BanachLattice X]

/-! #### Order continuity implies order completeness -/

/-- Archimedean "gap" lemma (Troitsky Proposition 1.2.10). In an Archimedean
vector lattice, any common lower bound of all differences `w - a` with `w` an
upper bound of a nonempty bounded-above set `A` and `a ∈ A` must be `≤ 0`. -/
private lemma le_zero_of_lb_upperBounds_sub [IsVLArchimedean X]
    {A : Set X} (hne : A.Nonempty) (hbd : BddAbove A) {ε : X}
    (hε : ∀ w ∈ upperBounds A, ∀ a ∈ A, ε ≤ w - a) : ε ≤ 0 := by
  have key : ∀ n : ℕ, ∀ w ∈ upperBounds A, ∀ a ∈ A, n • ε ≤ w - a := by
    intro n
    induction n with
    | zero =>
        intro w hw a ha
        simpa using sub_nonneg.mpr (hw ha)
    | succ k ih =>
        intro w hw a ha
        have hub : w - k • ε ∈ upperBounds A := fun s hs =>
          le_sub_comm.mp (ih w hw s hs)
        have hstep : ε ≤ (w - k • ε) - a := hε _ hub a ha
        have h : k • ε + ε ≤ k • ε + ((w - k • ε) - a) :=
          add_le_add (le_refl (k • ε)) hstep
        have h3 : k • ε + ((w - k • ε) - a) = w - a := by abel
        rw [h3] at h
        simpa [succ_nsmul] using h
  obtain ⟨w₀, hw₀⟩ := hbd
  obtain ⟨a₀, ha₀⟩ := hne
  exact isVLArchimedean_iff_le_zero_of_forall_nsmul_le.mp inferInstance
    (fun n => key n w₀ hw₀ a₀ ha₀)

/-- An order continuous Banach lattice is order complete. -/
instance isOrderComplete_of_isOrderContinuousNorm [IsOrderContinuousNorm X] :
    IsOrderComplete X := by
  refine ⟨fun {S} hSbdd hSne => ?_⟩
  obtain ⟨w₀, hw₀⟩ := hSbdd
  obtain ⟨s₀, hs₀⟩ := hSne
  classical
  -- Index: (upper bound of S) ×ᵒᵈ (nonempty finite subset of S), ordered so
  -- that upper bounds decrease and finite subsets increase.
  let Ub : Type _ := {w : X // w ∈ upperBounds S}
  let Fn : Type _ := {F : Finset X // (↑F : Set X) ⊆ S ∧ F.Nonempty}
  let I : Type _ := Ubᵒᵈ × Fn
  haveI : Nonempty Ub := ⟨⟨w₀, hw₀⟩⟩
  haveI : Nonempty Fn := ⟨⟨{s₀}, by
    refine ⟨?_, Finset.singleton_nonempty s₀⟩
    intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact hs₀⟩⟩
  haveI : Nonempty I := instNonemptyProd
  haveI : IsDirected Fn (· ≤ ·) := by
    refine ⟨fun F G => ?_⟩
    refine ⟨⟨F.val ∪ G.val, ?_, F.prop.2.mono Finset.subset_union_left⟩,
            Finset.subset_union_left, Finset.subset_union_right⟩
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact F.prop.1 h
    · exact G.prop.1 h
  haveI : IsDirected Ubᵒᵈ (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    refine ⟨OrderDual.toDual ⟨(OrderDual.ofDual a).val ⊓ (OrderDual.ofDual b).val,
      fun s hs => le_inf ((OrderDual.ofDual a).prop hs) ((OrderDual.ofDual b).prop hs)⟩,
      ?_, ?_⟩
    · change (_ : Ub) ≤ OrderDual.ofDual a
      exact inf_le_left
    · change (_ : Ub) ≤ OrderDual.ofDual b
      exact inf_le_right
  haveI : IsDirected I (· ≤ ·) := by
    refine ⟨fun p q => ?_⟩
    obtain ⟨c, hac, hbc⟩ := (‹IsDirected Ubᵒᵈ (· ≤ ·)›).directed p.1 q.1
    obtain ⟨d, had, hbd⟩ := (‹IsDirected Fn (· ≤ ·)›).directed p.2 q.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩
  -- The antitone net `z` on `I`: `z (w, F) = w - sup' F`.
  let z : I → X := fun p =>
    (OrderDual.ofDual p.1).val - p.2.val.sup' p.2.prop.2 id
  have hFle : ∀ p : I, p.2.val.sup' p.2.prop.2 id ≤ (OrderDual.ofDual p.1).val :=
    fun p => Finset.sup'_le _ _ fun x hx =>
      (OrderDual.ofDual p.1).prop (p.2.prop.1 hx)
  have hz_nn : ∀ p : I, 0 ≤ z p := fun p => sub_nonneg.mpr (hFle p)
  have hz_anti : Antitone z := by
    intro p q hpq
    have h1 : (OrderDual.ofDual q.1).val ≤ (OrderDual.ofDual p.1).val := hpq.1
    have h2 : p.2.val ⊆ q.2.val := hpq.2
    have hsup : p.2.val.sup' p.2.prop.2 id ≤ q.2.val.sup' q.2.prop.2 id :=
      Finset.sup'_mono _ h2 p.2.prop.2
    exact sub_le_sub h1 hsup
  have hz_glb : IsGLB (Set.range z) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, rfl⟩; exact hz_nn p
    · intro ε hε
      -- `ε` is a lower bound of range `z`; apply the Archimedean helper.
      refine le_zero_of_lb_upperBounds_sub ⟨s₀, hs₀⟩ ⟨w₀, hw₀⟩ ?_
      intro w hw a ha
      -- Form the element `(w, {a})` of `I` and evaluate `z`.
      let p : I := (OrderDual.toDual ⟨w, hw⟩,
        ⟨{a}, by
          refine ⟨?_, Finset.singleton_nonempty a⟩
          intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact ha⟩)
      have hzp : z p = w - a := by
        simp [z, p, Finset.sup'_singleton]
      have := hε ⟨p, rfl⟩
      rw [hzp] at this
      exact this
  -- Apply OCN to get `z → 0` in norm.
  have htend : Filter.Tendsto z Filter.atTop (nhds 0) :=
    IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hz_anti hz_nn hz_glb
  -- Extract from `htend` that the monotone net `u_F = sup' F` is norm-Cauchy.
  let u : Fn → X := fun F => F.val.sup' F.prop.2 id
  have hu_mono : Monotone u := fun F G h => Finset.sup'_mono _ h F.prop.2
  have hu_cauchy : Cauchy (Filter.map u Filter.atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    rw [Metric.tendsto_nhds] at htend
    have hev := htend (ε/2) (by linarith)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨p₀, hp₀⟩ := hev
    refine ⟨u '' {F | p₀.2 ≤ F}, ?_, ?_⟩
    · exact Filter.image_mem_map (Filter.mem_atTop p₀.2)
    · rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
      have hpF : p₀ ≤ (p₀.1, F) := ⟨le_refl _, hF⟩
      have hpG : p₀ ≤ (p₀.1, G) := ⟨le_refl _, hG⟩
      have h1 : dist (z (p₀.1, F)) 0 < ε/2 := hp₀ _ hpF
      have h2 : dist (z (p₀.1, G)) 0 < ε/2 := hp₀ _ hpG
      rw [dist_zero_right] at h1 h2
      have hzF : z (p₀.1, F) = (OrderDual.ofDual p₀.1).val - u F := rfl
      have hzG : z (p₀.1, G) = (OrderDual.ofDual p₀.1).val - u G := rfl
      rw [dist_eq_norm]
      have heq : u F - u G = z (p₀.1, G) - z (p₀.1, F) := by
        rw [hzF, hzG]; abel
      rw [heq]
      have : ‖z (p₀.1, G) - z (p₀.1, F)‖ ≤ ‖z (p₀.1, G)‖ + ‖z (p₀.1, F)‖ := by
        rw [sub_eq_add_neg]
        exact (norm_add_le _ _).trans_eq (by rw [norm_neg])
      linarith
  -- By Banach completeness, `u` has a limit `x`.
  obtain ⟨x, hx_tend⟩ := CompleteSpace.complete hu_cauchy
  -- `x` is the LUB of range of `u`, which equals LUB of `S`.
  have hx_lub : IsLUB (Set.range u) x :=
    isLUB_of_tendsto_atTop hu_mono hx_tend
  refine ⟨x, ?_, ?_⟩
  · -- `x` is an upper bound of `S`
    intro s hs
    have hprop : (↑({s} : Finset X) : Set X) ⊆ S ∧ ({s} : Finset X).Nonempty := by
      refine ⟨?_, Finset.singleton_nonempty s⟩
      intro y hy; rcases Finset.mem_singleton.mp hy with rfl; exact hs
    have huFs : u ⟨{s}, hprop⟩ = s := by
      change ({s} : Finset X).sup' (Finset.singleton_nonempty s) id = s
      rw [Finset.sup'_singleton]; rfl
    rw [← huFs]
    exact hx_lub.1 ⟨⟨{s}, hprop⟩, rfl⟩
  · -- `x` is the least upper bound
    intro y hy
    refine hx_lub.2 ?_
    rintro _ ⟨F, rfl⟩
    exact Finset.sup'_le _ _ (fun s hs => hy (F.prop.1 hs))

/-! #### Nakano's theorem -/

/-- In an order continuous Banach lattice, every increasing order-bounded
sequence converges in norm to its supremum. -/
theorem tendsto_of_monotone_bddAbove [IsOrderContinuousNorm X]
    {u : ℕ → X} (hmono : Monotone u) (hbd : BddAbove (Set.range u)) :
    ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) := by
  -- Order continuity implies order completeness, hence σ-order completeness;
  -- σ-OC gives the LUB and σ-order continuity of the norm gives convergence.
  haveI : IsOrderComplete X := isOrderComplete_of_isOrderContinuousNorm
  obtain ⟨x, hx⟩ := isSigmaOrderComplete_iff_mono_bddAbove_isLUB.mp inferInstance hmono hbd
  exact ⟨x, hx, IsSigmaOrderContinuousNorm.tendsto_of_monotone_isLUB hmono hx⟩

omit [IsOrderedAddMonoid X] [BanachLattice X] in
/-- A Banach lattice in which every increasing order-bounded sequence
converges in norm is σ-order complete. -/
theorem isSigmaOrderComplete_of_mono_bddAbove_tendsto
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    IsSigmaOrderComplete X :=
  isSigmaOrderComplete_iff_mono_bddAbove_isLUB.mpr fun hmono hbd =>
    let ⟨x, hx, _⟩ := h hmono hbd
    ⟨x, hx⟩

/-- A Banach lattice in which every increasing order-bounded sequence
converges in norm has a σ-order continuous norm. -/
theorem isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto
    (h : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x)) :
    IsSigmaOrderContinuousNorm X := by
  refine ⟨fun {u} hanti hnn hglb => ?_⟩
  -- Set v n = u 0 - u n; this is monotone, ≥ 0, bounded above by u 0.
  have hv_mono : Monotone (fun n => u 0 - u n) :=
    fun n m hnm => sub_le_sub_left (hanti hnm) _
  have hv_bdd : BddAbove (Set.range fun n => u 0 - u n) :=
    ⟨u 0, by
      rintro _ ⟨n, rfl⟩
      simpa using sub_nonneg.mpr (hnn n)⟩
  obtain ⟨x, hx_lub, hx_tend⟩ := h hv_mono hv_bdd
  -- u 0 - x is a lower bound of range u, hence ≤ 0 since IsGLB (range u) 0.
  have hub_le : u 0 - x ∈ lowerBounds (Set.range u) := by
    rintro _ ⟨n, rfl⟩
    have h1 : u 0 - u n ≤ x := hx_lub.1 ⟨n, rfl⟩
    exact sub_le_comm.mp h1
  have h_le_zero : u 0 - x ≤ 0 := hglb.2 hub_le
  -- u 0 - x ≥ 0 since x ≤ u 0.
  have hxle : x ≤ u 0 := hx_lub.2 (by
    rintro _ ⟨n, rfl⟩
    exact sub_le_self _ (hnn n))
  have h_ge_zero : (0 : X) ≤ u 0 - x := sub_nonneg.mpr hxle
  have hux_eq : u 0 - x = 0 := le_antisymm h_le_zero h_ge_zero
  -- Now u n = u 0 - (u 0 - u n) → u 0 - x = 0.
  have htend : Filter.Tendsto (fun n => u 0 - (u 0 - u n)) Filter.atTop (nhds (u 0 - x)) :=
    tendsto_const_nhds.sub hx_tend
  have hux : Filter.Tendsto u Filter.atTop (nhds (u 0 - x)) := by
    convert htend using 1
    ext n; abel
  rw [hux_eq] at hux
  exact hux

/-- Auxiliary: in a σ-order complete Banach lattice with σ-order continuous norm,
every antitone sequence bounded below converges in norm to its greatest lower
bound. -/
private lemma tendsto_antitone_seq_of_bddBelow [IsSigmaOrderComplete X]
    [IsSigmaOrderContinuousNorm X]
    {z : ℕ → X} (hanti : Antitone z) (hbdd : BddBelow (Set.range z)) :
    ∃ v, IsGLB (Set.range z) v ∧ Filter.Tendsto z Filter.atTop (nhds v) := by
  obtain ⟨v, hv⟩ := isSigmaOrderComplete_iff_anti_bddBelow_isGLB.mp ‹_› hanti hbdd
  exact ⟨v, hv, IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB hanti hv⟩

omit [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X] in
/-- A function on a directed nonempty preorder satisfying the directed Cauchy
condition is a `CauchySeq`. -/
private lemma cauchySeq_of_directed_dist {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (y : ι → X)
    (h : ∀ ε > 0, ∃ α₀, ∀ α ≥ α₀, ∀ β ≥ α₀, dist (y α) (y β) < ε) :
    CauchySeq y := by
  rw [CauchySeq, Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
  obtain ⟨α₀, hα₀⟩ := h ε hε
  refine ⟨y '' {α | α₀ ≤ α}, ?_, ?_⟩
  · exact Filter.image_mem_map (Filter.mem_atTop α₀)
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    exact hα₀ α hα β hβ

/-- A Banach lattice that is σ-order complete and has σ-order continuous
norm has an order continuous norm. -/
theorem isOrderContinuousNorm_of_isSigmaOrderComplete
    [IsSigmaOrderComplete X] [IsSigmaOrderContinuousNorm X] :
    IsOrderContinuousNorm X := by
  classical
  refine ⟨fun {ι} _ _ _ {y} hanti hnn hglb => ?_⟩
  -- Strategy: show y is a Cauchy net, hence converges by completeness; the
  -- limit equals the order GLB 0 by the Monotone Convergence Lemma for nets.
  suffices hcauchy : CauchySeq y by
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hwglb : IsGLB (Set.range y) w := isGLB_of_tendsto_atTop hanti hw
    have hw_eq : w = 0 := hwglb.unique hglb
    rw [hw_eq] at hw
    exact hw
  -- For Cauchy: assume not, derive a "bad gap" for every starting point.
  refine cauchySeq_of_directed_dist y (fun ε hε => ?_)
  by_contra hcon
  push_neg at hcon
  -- For every α₀, ∃ α₀ ≤ α ≤ γ with ‖y α - y γ‖ ≥ ε/2.
  have hbad : ∀ α₀ : ι, ∃ p : ι × ι, α₀ ≤ p.1 ∧ p.1 ≤ p.2 ∧ ε / 2 ≤ ‖y p.1 - y p.2‖ := by
    intro α₀
    obtain ⟨α, hα, β, hβ, hdist⟩ := hcon α₀
    obtain ⟨γ, hγα, hγβ⟩ := exists_ge_ge α β
    have h1 : ‖y α - y γ‖ + ‖y β - y γ‖ ≥ ε := by
      have htr := dist_triangle (y α) (y γ) (y β)
      rw [dist_comm (y γ) (y β)] at htr
      simp only [dist_eq_norm] at htr hdist
      linarith
    by_cases hαbad : ε / 2 ≤ ‖y α - y γ‖
    · exact ⟨(α, γ), hα, hγα, hαbad⟩
    · push_neg at hαbad
      exact ⟨(β, γ), hβ, hγβ, by linarith⟩
  -- Define the recursive choice function and the resulting subsequence.
  let step : ι → ι × ι := fun α₀ => (hbad α₀).choose
  have hstep : ∀ α₀ : ι, α₀ ≤ (step α₀).1 ∧ (step α₀).1 ≤ (step α₀).2 ∧
      ε / 2 ≤ ‖y (step α₀).1 - y (step α₀).2‖ := fun α₀ => (hbad α₀).choose_spec
  -- Build the recursive pair-valued sequence g : ℕ → ι × ι.
  let g : ℕ → ι × ι := fun n => Nat.rec (step Classical.ofNonempty)
    (fun _ p => step p.2) n
  have hg_succ : ∀ n, g (n + 1) = step (g n).2 := fun _ => rfl
  have hg_le : ∀ n, (g n).1 ≤ (g n).2 := fun n => by
    induction n with
    | zero => exact (hstep _).2.1
    | succ k _ => rw [hg_succ]; exact (hstep _).2.1
  have hg_step : ∀ n, (g n).2 ≤ (g (n + 1)).1 := fun n => by
    rw [hg_succ]; exact (hstep _).1
  have hg_dist : ∀ n, ε / 2 ≤ ‖y (g n).1 - y (g n).2‖ := fun n => by
    induction n with
    | zero => exact (hstep _).2.2
    | succ k _ => rw [hg_succ]; exact (hstep _).2.2
  -- The interleaved sequence z : ℕ → X.
  let z : ℕ → X := fun k => if k % 2 = 0 then y (g (k / 2)).1 else y (g (k / 2)).2
  have hz_anti : Antitone z := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have e1 : (m + m) % 2 = 0 := by omega
      have e2 : (m + m + 1) % 2 = 1 := by omega
      have e3 : (m + m) / 2 = m := by omega
      have e4 : (m + m + 1) / 2 = m := by omega
      simp only [z, e1, e2, e3, e4, ↓reduceIte]
      exact hanti (hg_le m)
    · subst hm
      have e1 : (2 * m + 1) % 2 = 1 := by omega
      have e2 : (2 * m + 1 + 1) % 2 = 0 := by omega
      have e3 : (2 * m + 1) / 2 = m := by omega
      have e4 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      simp only [z, e1, e2, e3, e4, ↓reduceIte]
      exact hanti (hg_step m)
  have hz_nn : ∀ k, 0 ≤ z k := by
    intro k; simp only [z]; split <;> exact hnn _
  have hz_bdd : BddBelow (Set.range z) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hz_nn k⟩
  -- By σ-OC + σ-OCN, z is Cauchy.
  obtain ⟨_, _, hzv⟩ := tendsto_antitone_seq_of_bddBelow hz_anti hz_bdd
  have hzcauchy : CauchySeq z := hzv.cauchySeq
  rw [Metric.cauchySeq_iff] at hzcauchy
  obtain ⟨N, hN⟩ := hzcauchy (ε / 2) (by linarith)
  -- The pair (2N, 2N+1) violates Cauchy by hg_dist.
  have hN1 : 2 * N ≥ N := by omega
  have hN2 : 2 * N + 1 ≥ N := by omega
  have hdN := hN (2 * N) hN1 (2 * N + 1) hN2
  have hh1 : (2 * N) % 2 = 0 := by omega
  have hh2 : (2 * N + 1) % 2 = 1 := by omega
  have hh3 : (2 * N) / 2 = N := by omega
  have hh4 : (2 * N + 1) / 2 = N := by omega
  simp only [z, hh1, hh2, hh3, hh4, ↓reduceIte, one_ne_zero] at hdN
  rw [dist_eq_norm] at hdN
  linarith [hg_dist N]

/-- **Nakano's theorem** (Troitsky 2.5.13). For a Banach lattice `X`, the
following are equivalent:

* `X` has an order continuous norm;
* `X` is σ-order complete and has a σ-order continuous norm;
* every increasing order-bounded sequence in `X` converges in norm. -/
theorem isOrderContinuousNorm_tfae :
    List.TFAE
      [ Nonempty (IsOrderContinuousNorm X),
        Nonempty (IsSigmaOrderComplete X) ∧ Nonempty (IsSigmaOrderContinuousNorm X),
        ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
          ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) ] := by
  tfae_have h13 : 1 → 3 := by
    rintro ⟨_⟩ u hmono hbd
    exact tendsto_of_monotone_bddAbove hmono hbd
  tfae_have h32 : 3 → 2 := fun h =>
    ⟨⟨isSigmaOrderComplete_of_mono_bddAbove_tendsto h⟩,
     ⟨isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto h⟩⟩
  tfae_have h21 : 2 → 1 := by
    rintro ⟨⟨_⟩, ⟨_⟩⟩
    exact ⟨isOrderContinuousNorm_of_isSigmaOrderComplete⟩
  tfae_finish

/-! #### Meyer-Nieberg theorem -/

/-- In an order continuous Banach lattice, every order-bounded pairwise
disjoint sequence converges to zero in norm.

Proof: partial sums of `|u_k|` are monotone and, by disjointness, equal the
corresponding suprema, hence bounded by any bound of `|u n|`. Nakano's theorem
gives convergence of the partial sums; the difference `v_{m+1} - v_m = |u_{m+1}|`
then has vanishing norm. -/
theorem disjoint_bddAbove_tendsto_zero [IsOrderContinuousNorm X]
    {u : ℕ → X} (hd : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  classical
  obtain ⟨w, hw⟩ := hbd
  -- Partial sums of `|u_k|`.
  let v : ℕ → X := fun m => ∑ k ∈ Finset.range m, |u k|
  have hv_nn : ∀ m, 0 ≤ v m := fun m =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hv_mono : Monotone v := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [v, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (abs_nonneg _)
  -- Partial sums are disjoint from later terms (by induction).
  have key : ∀ m k, m ≤ k → v m ⊓ |u k| = 0 := by
    intro m
    induction m with
    | zero =>
        intro k _
        simp [v]
    | succ n ih =>
        intro k hk
        have h1 : v n ⊓ |u k| = 0 := ih k (by omega)
        have h2 : |u n| ⊓ |u k| = 0 := hd (by omega)
        have heq : v (n + 1) = v n + |u n| := by
          simp [v, Finset.sum_range_succ]
        refine le_antisymm ?_
          (le_inf (by rw [heq]; exact add_nonneg (hv_nn n) (abs_nonneg _))
            (abs_nonneg _))
        rw [heq, inf_comm]
        calc |u k| ⊓ (v n + |u n|)
            ≤ |u k| ⊓ v n + |u k| ⊓ |u n| :=
              inf_le_inf_add_inf_of_nonneg (x := |u k|) (v n) (|u n|)
                (abs_nonneg _) (hv_nn n) (abs_nonneg _)
          _ = 0 := by rw [inf_comm, h1, inf_comm, h2, add_zero]
  -- Partial sums are bounded by `w`.
  have hv_le : ∀ m, v m ≤ w := by
    intro m
    induction m with
    | zero => simpa [v] using (abs_nonneg (u 0)).trans (hw ⟨0, rfl⟩)
    | succ n ih =>
        have hdisj : v n ⊓ |u n| = 0 := key n n (le_refl n)
        have heq : v (n + 1) = v n + |u n| := by
          simp [v, Finset.sum_range_succ]
        have hsup : v n + |u n| = v n ⊔ |u n| := by
          have := inf_add_sup (v n) (|u n|)
          rw [hdisj, zero_add] at this
          exact this.symm
        rw [heq, hsup]
        exact sup_le ih (hw ⟨n, rfl⟩)
  -- Use Nakano to get `v` converges in norm.
  obtain ⟨_, _, hv_tend⟩ :=
    tendsto_of_monotone_bddAbove hv_mono ⟨w, by rintro _ ⟨m, rfl⟩; exact hv_le m⟩
  have hv_cauchy : CauchySeq v := hv_tend.cauchySeq
  rw [Metric.cauchySeq_iff] at hv_cauchy
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hv_cauchy ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun m hm => ?_⟩
  have hdist : dist (v (m + 1)) (v m) < ε := hN (m + 1) (by omega) m hm
  have heq : v (m + 1) - v m = |u m| := by
    simp [v, Finset.sum_range_succ]
  rw [dist_zero_right, ← norm_abs_eq_norm]
  rw [dist_eq_norm, heq] at hdist
  exact hdist

/-- A Banach lattice whose order-bounded pairwise disjoint sequences all
converge to zero in norm has an order continuous norm.

**Proof strategy (Aliprantis–Burkinshaw Theorem 4.12 + Fremlin 4.13).** By
Nakano's TFAE it suffices to show that every monotone bounded sequence in `X`
is norm-Cauchy. Given `0 ≤ x_n ↑ ≤ x` not Cauchy, extract a subsequence with
`‖x_{n+1} - x_n‖ > 2ε`. The Aliprantis–Burkinshaw disjointification lemma then
produces, for each `k`, `k` disjoint sequences `(y_n^1), …, (y_n^k) ⊆ [0, x]`
with `y_n^1 + … + y_n^k ≤ x_{n+1} - x_n ≤ y_n^1 + … + y_n^k + (2/(k+3))·x`.
Choosing `k` large enough that `(2/(k+3))·‖x‖ < ε` and applying the hypothesis
to each disjoint sequence gives a contradiction. The disjointification lemma
(AB Theorem 4.12) is not yet in this library and would need to be formalised
first. -/
theorem isOrderContinuousNorm_of_disjoint_tendsto_zero
    (h : ∀ {u : ℕ → X},
      Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
      BddAbove (Set.range fun n => |u n|) →
      Filter.Tendsto u Filter.atTop (nhds 0)) :
    IsOrderContinuousNorm X := sorry

/-- **Meyer-Nieberg theorem**: a Banach lattice has an order continuous norm
iff every order-bounded pairwise disjoint sequence converges to zero. -/
theorem isOrderContinuousNorm_iff_disjoint_tendsto_zero :
    IsOrderContinuousNorm X ↔
      (∀ {u : ℕ → X},
        Pairwise (fun i j => IsVLDisjoint (u i) (u j)) →
        BddAbove (Set.range fun n => |u n|) →
        Filter.Tendsto u Filter.atTop (nhds 0)) :=
  ⟨fun _ => disjoint_bddAbove_tendsto_zero,
   fun h => isOrderContinuousNorm_of_disjoint_tendsto_zero (fun hd hbd => h hd hbd)⟩

/-- In an order continuous Banach lattice, any order-bounded set of pairwise
disjoint non-zero elements is at most countable. -/
theorem countable_of_pairwise_disjoint_bddAbove [IsOrderContinuousNorm X]
    {S : Set X} (h0 : ∀ x ∈ S, x ≠ 0)
    (hd : S.Pairwise (fun x y => IsVLDisjoint x y))
    (hbd : BddAbove ((fun x => |x|) '' S)) :
    S.Countable := by
  -- Stratify by norm: `S_n = {x ∈ S | ‖x‖ ≥ 1/(n+1)}`.
  classical
  set T : ℕ → Set X := fun n => {x ∈ S | 1 / (n + 1 : ℝ) ≤ ‖x‖} with hT
  -- Each stratum is finite.
  have hTfin : ∀ n, (T n).Finite := by
    intro n
    by_contra hinf
    rw [Set.not_finite] at hinf
    let φ : ℕ ↪ ↥(T n) := hinf.natEmbedding
    let y : ℕ → X := fun k => ((φ k : ↥(T n)) : X)
    have hy_mem : ∀ k, y k ∈ S := fun k => (φ k).prop.1
    have hy_norm : ∀ k, 1 / (n + 1 : ℝ) ≤ ‖y k‖ := fun k => (φ k).prop.2
    have hy_inj : Function.Injective y := by
      intro a b hab
      have : φ a = φ b := Subtype.ext hab
      exact φ.injective this
    have hy_disj : Pairwise fun i j => IsVLDisjoint (y i) (y j) := by
      intro i j hij
      exact hd (hy_mem i) (hy_mem j) (fun h => hij (hy_inj h))
    have hy_bd : BddAbove (Set.range fun k => |y k|) := by
      obtain ⟨u, hu⟩ := hbd
      exact ⟨u, by rintro _ ⟨k, rfl⟩; exact hu ⟨y k, hy_mem k, rfl⟩⟩
    have htend : Filter.Tendsto y Filter.atTop (nhds 0) :=
      disjoint_bddAbove_tendsto_zero hy_disj hy_bd
    rw [Metric.tendsto_nhds] at htend
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hev := htend (1 / (n + 1 : ℝ)) hpos
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K, hK⟩ := hev
    have := hK K (le_refl K)
    rw [dist_zero_right] at this
    exact absurd (hy_norm K) (not_le.mpr this)
  -- `S = ⋃ n, T n` because every nonzero element has positive norm.
  have hcover : S ⊆ ⋃ n, T n := by
    intro x hx
    have hne : x ≠ 0 := h0 x hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hnorm
    exact Set.mem_iUnion.mpr ⟨n, hx, le_of_lt hn⟩
  refine (Set.Countable.mono hcover ?_)
  exact Set.countable_iUnion (fun n => (hTfin n).countable)

/-! #### Decomposition Lemma -/

private lemma principalBand_subset_disjointComplement
    {a b : X} (hab : IsVLDisjoint a b) :
    (Band.principalBand a : Set X) ⊆ disjointComplement (Band.principalBand b : Set X) := by
  have h₁ : (Band.principalBand b : Set X) ⊆ ({a} : Set X)ᵈ :=
    Band.bandGenerated_le (B := Band.disjointComplementBand ({a} : Set X)) (by
      intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
      intro c hc; rw [Set.mem_singleton_iff] at hc; subst hc
      exact isVLDisjoint_comm.mp hab)
  have ha_mem : a ∈ disjointComplement (Band.principalBand b : Set X) :=
    fun y hy => isVLDisjoint_comm.mp (h₁ hy a (Set.mem_singleton _))
  exact Band.bandGenerated_le (B := Band.disjointComplementBand (Band.principalBand b : Set X))
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact ha_mem)

private lemma principalBandProjection_isVLDisjoint
    [HasPrincipalProjectionProperty X]
    {a b : X} (hab : IsVLDisjoint a b) (x : X) :
    IsVLDisjoint (Band.principalBandProjection a x) (Band.principalBandProjection b x) := by
  have hPa : Band.principalBandProjection a x ∈ (Band.principalBand a : Set X) := by
    have := (Band.principalProjectionBand a).bandProjection_mem x
    change _ ∈ (Band.principalProjectionBand a : Set X) at this
    rw [Band.principalProjectionBand_coe] at this; exact this
  have hPb : Band.principalBandProjection b x ∈ (Band.principalBand b : Set X) := by
    have := (Band.principalProjectionBand b).bandProjection_mem x
    change _ ∈ (Band.principalProjectionBand b : Set X) at this
    rw [Band.principalProjectionBand_coe] at this; exact this
  exact principalBand_subset_disjointComplement hab hPa _ hPb

omit [BanachLattice X] in
private lemma inf_finset_sum_eq_zero {ι : Type*}
    {f : ι → X} {y : X} (F : Finset ι)
    (hy : 0 ≤ y) (hf : ∀ i ∈ F, 0 ≤ f i)
    (hdis : ∀ i ∈ F, y ⊓ f i = 0) :
    y ⊓ ∑ i ∈ F, f i = 0 := by
  induction F using Finset.cons_induction with
  | empty => simp [inf_of_le_right hy]
  | cons a F haF ih =>
    rw [Finset.sum_cons]
    apply le_antisymm _ (le_inf hy (add_nonneg (hf a (Finset.mem_cons_self a F))
      (Finset.sum_nonneg fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))))
    calc y ⊓ (f a + ∑ i ∈ F, f i)
        ≤ y ⊓ f a + y ⊓ ∑ i ∈ F, f i :=
          inf_le_inf_add_inf_of_nonneg y _ _ hy (hf a (Finset.mem_cons_self a F))
            (Finset.sum_nonneg fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))
      _ = 0 := by rw [hdis a (Finset.mem_cons_self a F),
          ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))
            (fun i hi => hdis i (Finset.mem_cons.mpr (Or.inr hi))), add_zero]

private lemma finset_sum_principalBandProjection_le
    [HasPrincipalProjectionProperty X]
    {Λ : Set X} (hΛ : IsMaximalDisjoint Λ)
    {x : X} (hx : 0 ≤ x) (F : Finset Λ) :
    ∑ a ∈ F, Band.principalBandProjection (a : X) x ≤ x := by
  induction F using Finset.cons_induction with
  | empty => simpa
  | cons a F haF ih =>
    rw [Finset.sum_cons]
    have ha_nn := (Band.principalProjectionBand (a : X)).bandProjection_nonneg hx
    have ha_le := (Band.principalProjectionBand (a : X)).bandProjection_le hx
    have hsum_nn := Finset.sum_nonneg fun i (_ : i ∈ F) =>
      (Band.principalProjectionBand (i : X)).bandProjection_nonneg hx
    have hdisj : Band.principalBandProjection (a : X) x ⊓
        ∑ i ∈ F, Band.principalBandProjection (i : X) x = 0 := by
      refine inf_finset_sum_eq_zero F ha_nn
        (fun i _ => (Band.principalProjectionBand (i : X)).bandProjection_nonneg hx)
        (fun i hi => ?_)
      have hab : IsVLDisjoint (a : X) (i : X) :=
        hΛ.prop.2 a.prop i.prop (fun h => haF (Subtype.val_injective h ▸ hi))
      have hdisij := principalBandProjection_isVLDisjoint hab x
      unfold IsVLDisjoint at hdisij
      have hPa_nn := ha_nn
      have hPi_nn := (Band.principalProjectionBand (i : X)).bandProjection_nonneg hx
      change 0 ≤ (Band.principalBandProjection (a : X)) x at hPa_nn
      change 0 ≤ (Band.principalBandProjection (i : X)) x at hPi_nn
      rwa [abs_of_nonneg hPa_nn, abs_of_nonneg hPi_nn] at hdisij
    have := inf_add_sup (Band.principalBandProjection (a : X) x)
      (∑ i ∈ F, Band.principalBandProjection (i : X) x)
    rw [hdisj, zero_add] at this
    rw [this.symm]
    exact sup_le ha_le ih

/-- **Decomposition Lemma.** In an order continuous Banach lattice, for any
maximal disjoint family `Λ` of positive elements and any `x : X`, the
family `(Pₐ x)_{a ∈ Λ}` is unconditionally summable with sum `x`. -/
private lemma hasSum_principalBandProjection_of_nonneg
    [IsOrderContinuousNorm X]
    {Λ : Set X} (hΛ : IsMaximalDisjoint Λ) {y : X} (hy : 0 ≤ y) :
    HasSum (fun a : Λ => Band.principalBandProjection (a : X) y) y := by
  -- HasSum is Tendsto of partial sums over Finset Λ
  -- The antitone net: F ↦ y - ∑_{a∈F} Pa y
  set g : Finset Λ → X := fun F =>
    y - ∑ a ∈ F, Band.principalBandProjection (a : X) y with hg_def
  suffices htend : Filter.Tendsto g Filter.atTop (nhds 0) by
    have : Filter.Tendsto (fun F => y - g F) Filter.atTop (nhds (y - 0)) :=
      tendsto_const_nhds.sub htend
    simp only [hg_def, sub_sub_cancel, sub_zero] at this
    exact this
  -- g is antitone
  have hg_anti : Antitone g := fun F G hFG => sub_le_sub_left
    (Finset.sum_le_sum_of_subset_of_nonneg hFG fun a _ _ =>
      (Band.principalProjectionBand (a : X)).bandProjection_nonneg hy) y
  -- g is nonneg
  have hg_nn : ∀ F, 0 ≤ g F := fun F =>
    sub_nonneg.mpr (finset_sum_principalBandProjection_le hΛ hy F)
  -- IsGLB (range g) 0
  have hg_glb : IsGLB (Set.range g) 0 := by
    refine ⟨fun _ ⟨F, hF⟩ => hF ▸ hg_nn F, fun w hw => ?_⟩
    -- For singleton F = {a}: w ≤ y - Pa y, hence Pa y ≤ y - w
    have hub : y - w ∈ upperBounds (Set.range fun a : Λ =>
        Band.principalBandProjection (a : X) y) := by
      rintro _ ⟨a, rfl⟩
      have := hw ⟨{a}, rfl⟩
      simp only [hg_def, Finset.sum_singleton] at this
      exact le_sub_comm.mp this
    -- y = LUB of {Pa y}, so y ≤ y - w, hence w ≤ 0
    have hlub := isLUB_principalBandProjection_of_isMaximalDisjoint hΛ hy
    have hyw := hlub.2 hub
    rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at hyw
  -- Apply order continuity of the norm
  exact IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hg_anti hg_nn hg_glb

/-- **Decomposition Lemma.** In an order continuous Banach lattice, for any
maximal disjoint family `Λ` of positive elements and any `x : X`, the
family `(Pₐ x)_{a ∈ Λ}` is unconditionally summable with sum `x`. -/
theorem hasSum_principalBandProjection
    [IsOrderContinuousNorm X]
    {Λ : Set X} (hΛ : IsMaximalDisjoint Λ) (x : X) :
    HasSum (fun a : Λ =>
      Band.principalBandProjection (a : X) x) x := by
  -- Decompose x = x⁺ - x⁻ and use linearity
  set xp : X := x ⊔ 0
  set xn : X := (-x) ⊔ 0
  have hxeq : x = xp - xn := by
    simp only [xp, xn]
    rw [show (-x) ⊔ 0 = -(x ⊓ 0) from by rw [neg_inf, neg_zero], sub_neg_eq_add, add_comm]
    rw [show x ⊓ 0 + (x ⊔ 0) = x from by rw [inf_add_sup, add_zero]]
  have hfun : (fun a : Λ => Band.principalBandProjection (a : X) x) =
      (fun a : Λ => Band.principalBandProjection (a : X) xp -
        Band.principalBandProjection (a : X) xn) := by
    funext ⟨a, _⟩
    change (Band.principalBandProjection a) x =
      (Band.principalBandProjection a) xp - (Band.principalBandProjection a) xn
    rw [← LinearMap.map_sub, ← hxeq]
  rw [hfun, hxeq]
  exact (hasSum_principalBandProjection_of_nonneg hΛ le_sup_right).sub
    (hasSum_principalBandProjection_of_nonneg hΛ le_sup_right)

/-! #### Ando's theorem -/

/-- In an order continuous Banach lattice, every norm-closed order ideal is
a band. -/
theorem band_of_isClosed_orderIdeal [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ B : Band X, (B : Set X) = (J : Set X) := by
  refine ⟨{ toOrderIdeal := J, directed_sSup_mem' := ?_ }, rfl⟩
  intro S hS hpos hdir hne x hx
  -- Index by `↥S` as a directed nonempty preorder.
  haveI : Nonempty ↥S := hne.to_subtype
  haveI : IsDirected ↥S (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.2 b.val b.2
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  -- Antitone net `u s = x - s`, nonneg, with `IsGLB 0` since `x = sup S`.
  let u : ↥S → X := fun s => x - s.val
  have hu_anti : Antitone u := fun a b h =>
    sub_le_sub_left (show a.val ≤ b.val from h) x
  have hu_nn : ∀ s, 0 ≤ u s := fun s => sub_nonneg.mpr (hx.1 s.2)
  have hu_glb : IsGLB (Set.range u) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨s, rfl⟩; exact hu_nn s
    · intro w hw
      have hub : ∀ y ∈ S, y ≤ x - w := fun y hy =>
        le_sub_comm.mp (hw ⟨⟨y, hy⟩, rfl⟩)
      have h := hx.2 hub
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  -- Order continuity gives `u → 0`, hence the inclusion `s ↦ s.val → x`.
  have htend := IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero
    hu_anti hu_nn hu_glb
  have hval_tend : Filter.Tendsto (fun s : ↥S => s.val) Filter.atTop (nhds x) := by
    have h1 : Filter.Tendsto (fun s : ↥S => x - u s) Filter.atTop (nhds (x - 0)) :=
      tendsto_const_nhds.sub htend
    simpa [u, sub_sub_cancel] using h1
  -- `J` is closed and contains each `s.val`, so `x ∈ J`.
  exact hcl.mem_of_tendsto hval_tend (Filter.Eventually.of_forall (fun s => hS s.2))

/-- A Banach lattice in which every norm-closed ideal is a band has an order
continuous norm.

**Proof sketch (Troitsky 11.1.10, (ii)⇒(iv)⇒(i)).** By Meyer-Nieberg's
characterisation, it suffices to show that every order-bounded disjoint
sequence converges to zero in norm. Given such a sequence `(uₙ) ⊆ [0, w]`,
let `J` be the closed ideal generated by `{uₙ}`. By hypothesis `J` is a band;
`OrderIdeal.isClosed_sum` (Troitsky 3.3.13) makes `J + Jᵈ` closed, hence a
band, hence `(J + Jᵈ)ᵈᵈ = J + Jᵈ`; combined with `(J + Jᵈ)ᵈ ⊆ Jᵈ ∩ Jᵈᵈ = {0}`
one gets `J + Jᵈ = X`, so `J` is a projection band. Denoting by `P` the band
projection, `Pw ∈ J` is norm-approximated by `v` with `|v| ≤ ∑_{k ≤ N} λ_k uₖ`;
for `n > N`, disjointness gives `v ⊥ uₙ` and `uₙ ≤ |Pw − v|`, whence `‖uₙ‖ < ε`.

The remaining `sorry` is this inner argument; it requires a "closed ideal
generated by a set" construction together with a density/approximation lemma
for principal-style generating elements, neither of which is yet in the
library. -/
theorem isOrderContinuousNorm_of_isClosed_ideal_isBand
    (h : ∀ J : OrderIdeal X, IsClosed (J : Set X) →
      ∃ B : Band X, (B : Set X) = (J : Set X)) :
    IsOrderContinuousNorm X := by
  -- Reduce to Meyer-Nieberg: every order-bounded disjoint sequence in a
  -- Banach lattice must converge to zero in norm.
  refine isOrderContinuousNorm_of_disjoint_tendsto_zero (fun {u} hd hbd => ?_)
  sorry

/-- **Ando's theorem**: a Banach lattice has an order continuous norm iff
every norm-closed ideal is a band. -/
theorem isOrderContinuousNorm_iff_isClosed_ideal_isBand :
    IsOrderContinuousNorm X ↔
      (∀ J : OrderIdeal X, IsClosed (J : Set X) →
        ∃ B : Band X, (B : Set X) = (J : Set X)) :=
  ⟨fun _ => band_of_isClosed_orderIdeal,
   fun h => isOrderContinuousNorm_of_isClosed_ideal_isBand h⟩

/-- In an order continuous Banach lattice, every norm-closed ideal is a
projection band. -/
theorem projectionBand_of_isClosed_orderIdeal
    [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ P : ProjectionBand X, (P : Set X) = (J : Set X) := by
  -- `Jᵈ` as an order ideal.
  let Jd : OrderIdeal X := Band.disjointComplementOrderIdeal ((J : Set X))
  have hJd_set : ((Jd : Set X)) = ((J : Set X))ᵈ := rfl
  -- `Jᵈ` is closed.
  have hJd_cl : IsClosed ((Jd : Set X)) := by
    rw [hJd_set]; exact Band.isClosed_disjointComplement ((J : Set X))
  -- `J + Jᵈ` is a closed order ideal.
  have hSum_cl : IsClosed ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) :=
    OrderIdeal.isClosed_sum hcl hJd_cl
  -- ...hence a band (under OCN).
  obtain ⟨BSum, hBSum⟩ :=
    band_of_isClosed_orderIdeal (OrderIdeal.sum J Jd) hSum_cl
  -- Show `J + Jᵈ = X` by chasing disjoint complements.
  -- Inclusions: `J ⊆ J + Jᵈ` and `Jᵈ ⊆ J + Jᵈ` (at the set level).
  have hJ_sub : ((J : Set X)) ⊆ ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) := by
    intro a ha
    exact Submodule.mem_sup.mpr ⟨a, ha, 0, Submodule.zero_mem _, by simp⟩
  have hJd_sub : ((Jd : Set X)) ⊆ ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) := by
    intro a ha
    exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, a, ha, by simp⟩
  -- `(J + Jᵈ)ᵈ ⊆ {0}`.
  have hSumd_zero : (((OrderIdeal.sum J Jd : OrderIdeal X) : Set X))ᵈ ⊆ ({0} : Set X) := by
    intro x hx
    have hxJ : x ∈ ((J : Set X))ᵈ := disjointComplement_anti hJ_sub hx
    have hxJd : x ∈ ((Jd : Set X))ᵈ := disjointComplement_anti hJd_sub hx
    rw [hJd_set] at hxJd
    exact disjointComplement_inter_eq_zero ((J : Set X))ᵈ ⟨hxJ, hxJd⟩
  -- Since `BSum = J + Jᵈ` as sets, and `BSum` is a band, `BSumᵈᵈ = BSum`.
  have hBSum_dd : (((BSum : Set X))ᵈ)ᵈ = ((BSum : Set X)) :=
    Band.eq_disjointComplement_disjointComplement BSum
  -- `{0}ᵈ = X`.
  have hzero_d : (({0} : Set X))ᵈ = (Set.univ : Set X) := by
    ext x
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    unfold IsVLDisjoint
    simp
  -- Chain: `BSum = BSumᵈᵈ ⊇ ({0})ᵈ = X` (using `BSumᵈ ⊆ {0}`).
  have hBSum_top : ((BSum : Set X)) = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← hBSum_dd]
    have : (((BSum : Set X))ᵈ) ⊆ ({0} : Set X) := by
      rw [hBSum]; exact hSumd_zero
    calc (Set.univ : Set X)
        = (({0} : Set X))ᵈ := hzero_d.symm
      _ ⊆ (((BSum : Set X))ᵈ)ᵈ := disjointComplement_anti this
  -- Transfer: `J + Jᵈ = X` as sets.
  have hSum_top : ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) = Set.univ := by
    rw [← hBSum]; exact hBSum_top
  -- Apply the decomposition characterisation.
  refine (ProjectionBand.projectionBand_iff_add_disjointComplement J).mpr (fun x => ?_)
  have hxmem : x ∈ ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) := by
    rw [hSum_top]; exact Set.mem_univ _
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxmem
  refine ⟨a, b, ha, ?_, hab.symm⟩
  exact (show b ∈ ((J : Set X))ᵈ by rw [← hJd_set]; exact hb)

end BanachLattice
