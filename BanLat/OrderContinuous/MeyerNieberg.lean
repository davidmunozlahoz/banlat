import BanLat.OrderContinuous.Nakano
import BanLat.Disjoint

/-!
# Meyer-Nieberg theorem

A Banach lattice has an order continuous norm iff every order-bounded
pairwise disjoint sequence converges to zero in norm. As a corollary, in
an order continuous Banach lattice every order-bounded set of pairwise
disjoint non-zero elements is at most countable.
-/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

namespace BanachLattice

variable [BanachLattice X]

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

**Proof strategy.** By Nakano's TFAE it suffices to show that every monotone
bounded sequence in `X` is norm-Cauchy. Given `0 ≤ x_n ↑ ≤ x` not Cauchy,
extract a subsequence with `‖x_{n+1} - x_n‖ > 2ε`. The disjointification lemma
then produces, for each `k`, `k` disjoint sequences `(y_n^1), …, (y_n^k) ⊆ [0,
x]` with `y_n^1 + … + y_n^k ≤ x_{n+1} - x_n ≤ y_n^1 + … + y_n^k + (2/(k+3))·x`.
Choosing `k` large enough that `(2/(k+3))·‖x‖ < ε` and applying the hypothesis
to each disjoint sequence gives a contradiction. The disjointification lemma
is not yet in this library and would need to be formalised first. -/
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

end BanachLattice
