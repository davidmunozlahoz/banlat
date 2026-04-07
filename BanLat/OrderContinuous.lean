import BanLat.Banach
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
greatest lower bound zero converges to zero in norm. -/
class IsOrderContinuousNorm (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → X}, Antitone u → (∀ i, 0 ≤ u i) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)

/-- An order continuous norm is in particular σ-order continuous. -/
instance (priority := 100)
    IsOrderContinuousNorm.toIsSigmaOrderContinuousNorm
    [NormedVectorLattice X] [IsOrderContinuousNorm X] :
    IsSigmaOrderContinuousNorm X :=
  ⟨fun hanti hnn hglb =>
    IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hanti hnn hglb⟩

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

/-- An order continuous Banach lattice is order complete. -/
theorem isOrderComplete_of_isOrderContinuousNorm [IsOrderContinuousNorm X] :
    IsOrderComplete X := sorry

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
disjoint sequence converges to zero in norm. -/
theorem disjoint_bddAbove_tendsto_zero [IsOrderContinuousNorm X]
    {u : ℕ → X} (hd : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hbd : BddAbove (Set.range fun n => |u n|)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := sorry

/-- A Banach lattice whose order-bounded pairwise disjoint sequences all
converge to zero in norm has an order continuous norm. -/
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
    S.Countable := sorry

/-! #### Ando's theorem -/

/-- In an order continuous Banach lattice, every norm-closed order ideal is
a band. -/
theorem band_of_isClosed_orderIdeal [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ B : Band X, (B : Set X) = (J : Set X) := sorry

/-- A Banach lattice in which every norm-closed ideal is a band has an order
continuous norm. -/
theorem isOrderContinuousNorm_of_isClosed_ideal_isBand
    (h : ∀ J : OrderIdeal X, IsClosed (J : Set X) →
      ∃ B : Band X, (B : Set X) = (J : Set X)) :
    IsOrderContinuousNorm X := sorry

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
    ∃ P : ProjectionBand X, (P : Set X) = (J : Set X) := sorry

end BanachLattice
