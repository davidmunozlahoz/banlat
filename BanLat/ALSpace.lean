import BanLat.AMSpace
import BanLat.Banach
import BanLat.Dual
import BanLat.Ideal
import BanLat.OrderContinuous

/-!
# AL-spaces

An **AL-space** is a Banach lattice whose norm satisfies the AL-axiom:
`‖x + y‖ = ‖x‖ + ‖y‖` for all non-negative `x` and `y`. Equivalently, the
norm is additive on positive disjoint elements. Every AL-space is order
continuous and σ-order complete. Closed sublattices of AL-spaces are again
AL-spaces.
-/

/-! ### AL-spaces -/

/-- An **AL-space** is a Banach lattice whose norm is additive on the positive
cone: for all non-negative elements `x` and `y`,
`‖x + y‖ = ‖x‖ + ‖y‖`. -/
class ALSpace (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends BanachLattice X where
  norm_add_eq_of_nonneg {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x + y‖ = ‖x‖ + ‖y‖

namespace ALSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [ALSpace X]

/-! #### Disjointness characterization -/

/-- For positive disjoint elements in an AL-space, the norm is additive.
This is the original AL-axiom formulation; it follows immediately from the
stronger `norm_add_eq_of_nonneg`. -/
theorem norm_add_eq_of_disjoint_nonneg {x y : X}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (_h : x ⊓ y = 0) :
    ‖x + y‖ = ‖x‖ + ‖y‖ :=
  norm_add_eq_of_nonneg hx hy

/-! #### Basic norm identities -/

/-- In an AL-space, `‖|x|‖ = ‖x‖` for all `x`. This follows from the
lattice norm (solidity), but we record it for convenience. -/
theorem norm_abs_eq (x : X) : ‖|x|‖ = ‖x‖ := norm_abs_eq_norm x

/-- The norm of the positive part plus the norm of the negative part
equals the norm: `‖x⁺‖ + ‖x⁻‖ = ‖x‖`. -/
theorem norm_posPart_add_norm_negPart (x : X) :
    ‖x⁺‖ + ‖x⁻‖ = ‖x‖ := by
  rw [← norm_add_eq_of_nonneg (posPart_nonneg x) (negPart_nonneg x),
    posPart_add_negPart, norm_abs_eq]

/-! #### Closed sublattices -/

private noncomputable def instLatticeClosedSublattice
    (Y : VectorSublattice X) : Lattice Y.toSubmodule where
  sup x y := ⟨x.1 ⊔ y.1, Y.sup_mem x.2 y.2⟩
  inf x y := ⟨x.1 ⊓ y.1, Y.inf_mem x.2 y.2⟩
  le_sup_left := fun x y => show x.1 ≤ x.1 ⊔ y.1 from le_sup_left
  le_sup_right := fun x y => show y.1 ≤ x.1 ⊔ y.1 from le_sup_right
  sup_le := fun x y z h1 h2 => show x.1 ⊔ y.1 ≤ z.1 from sup_le h1 h2
  inf_le_left := fun x y => show x.1 ⊓ y.1 ≤ x.1 from inf_le_left
  inf_le_right := fun x y => show x.1 ⊓ y.1 ≤ y.1 from inf_le_right
  le_inf := fun x y z h1 h2 =>
    show x.1 ≤ y.1 ⊓ z.1 from le_inf h1 h2

private instance instIsOrderedAddMonoidClosedSublattice
    (Y : VectorSublattice X) :
    @IsOrderedAddMonoid Y.toSubmodule inferInstance
      (instLatticeClosedSublattice Y).toPartialOrder where
  add_le_add_left := by
    intro a b (h : a.1 ≤ b.1) c
    exact add_le_add_left h c.1
  add_le_add_right := by
    intro a b (h : a.1 ≤ b.1) c
    exact add_le_add_right h c.1

/-- A closed vector sublattice of an AL-space, equipped with the subspace
norm and induced lattice operations, is an AL-space. -/
instance instALSpace_closedSublattice (Y : VectorSublattice X)
    (hclosed : IsClosed (Y : Set X)) :
    @ALSpace Y.toSubmodule Y.toSubmodule.normedAddCommGroup
      (instLatticeClosedSublattice Y)
      (instIsOrderedAddMonoidClosedSublattice Y) := by
  letI : NormedAddCommGroup Y.toSubmodule :=
    Y.toSubmodule.normedAddCommGroup
  letI : Lattice Y.toSubmodule := instLatticeClosedSublattice Y
  letI : IsOrderedAddMonoid Y.toSubmodule :=
    instIsOrderedAddMonoidClosedSublattice Y
  exact {
    toNormedVectorLattice := {
      toVectorLattice := {
        toModule := Y.toSubmodule.module
        smul_le_smul_of_nonneg_left := by
          intro c hc x y hxy
          change c • x.1 ≤ c • y.1
          exact smul_le_smul_of_nonneg_left hxy hc
      }
      solid := by
        intro x y h
        change ‖x.1‖ ≤ ‖y.1‖
        exact norm_le_norm_of_abs_le_abs h
      norm_smul := by
        intro r x
        change ‖r • x.1‖ = ‖r‖ * ‖x.1‖
        exact norm_smul r x.1
    }
    toCompleteSpace := by
      haveI : IsClosed (Y.toSubmodule : Set X) := hclosed
      infer_instance
    norm_add_eq_of_nonneg := by
      intro x y hx hy
      change ‖x.1 + y.1‖ = ‖x.1‖ + ‖y.1‖
      exact ALSpace.norm_add_eq_of_nonneg hx hy
  }

/-! ### Order continuity -/

/-- In an AL-space, every monotone non-negative bounded-above sequence is
Cauchy in norm. The argument uses the AL-axiom to convert convergence of the
norms (in `ℝ`) into a Cauchy condition on the original sequence: for `n ≤ m`,
`‖u m - u n‖ = ‖u m‖ - ‖u n‖`. -/
private lemma cauchySeq_monotone_nonneg_bddAbove {u : ℕ → X} (hmono : Monotone u)
    (hnn : ∀ n, 0 ≤ u n) (hbdd : BddAbove (Set.range u)) : CauchySeq u := by
  have hnorm_mono : Monotone (fun n => ‖u n‖) := fun n m hnm =>
    norm_le_norm_of_abs_le_abs <| by
      rw [abs_of_nonneg (hnn n), abs_of_nonneg (hnn m)]; exact hmono hnm
  have hnorm_bdd : BddAbove (Set.range fun n => ‖u n‖) := by
    obtain ⟨b, hb⟩ := hbdd
    have hb_nn : 0 ≤ b := le_trans (hnn 0) (hb ⟨0, rfl⟩)
    refine ⟨‖b‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply norm_le_norm_of_abs_le_abs
    rw [abs_of_nonneg (hnn n), abs_of_nonneg hb_nn]
    exact hb ⟨n, rfl⟩
  have hnorm_cauchy : CauchySeq (fun n => ‖u n‖) :=
    (tendsto_atTop_ciSup hnorm_mono hnorm_bdd).cauchySeq
  have hAL : ∀ {n m : ℕ}, n ≤ m → ‖u m - u n‖ = ‖u m‖ - ‖u n‖ := by
    intro n m hnm
    have h2 : 0 ≤ u m - u n := sub_nonneg.mpr (hmono hnm)
    have h3 := ALSpace.norm_add_eq_of_nonneg (hnn n) h2
    rw [show u n + (u m - u n) = u m from by abel] at h3
    linarith
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rw [Metric.cauchySeq_iff] at hnorm_cauchy
  obtain ⟨N, hN⟩ := hnorm_cauchy ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  rcases lt_or_ge n m with hnm | hnm
  · rw [dist_eq_norm, hAL hnm.le]
    have h := hN m hm n hn
    rwa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hnorm_mono hnm.le))] at h
  · rw [dist_comm, dist_eq_norm, hAL hnm]
    have h := hN n hn m hm
    rwa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hnorm_mono hnm))] at h

/-- Every AL-space has an order continuous norm. By Nakano's theorem
(`isOrderContinuousNorm_tfae`), it suffices to prove that every monotone
order-bounded sequence converges in norm to its supremum. The translated
sequence `n ↦ u n - u 0` is monotone, non-negative, and bounded above; the
private lemma `cauchySeq_monotone_nonneg_bddAbove` shows it is Cauchy, and the
limit is the supremum by monotone convergence. -/
instance instIsOrderContinuousNorm : IsOrderContinuousNorm X := by
  suffices hseq : ∀ {u : ℕ → X}, Monotone u → BddAbove (Set.range u) →
      ∃ x, IsLUB (Set.range u) x ∧ Filter.Tendsto u Filter.atTop (nhds x) by
    haveI : IsSigmaOrderComplete X :=
      BanachLattice.isSigmaOrderComplete_of_mono_bddAbove_tendsto hseq
    haveI : IsSigmaOrderContinuousNorm X :=
      BanachLattice.isSigmaOrderContinuousNorm_of_mono_bddAbove_tendsto hseq
    exact BanachLattice.isOrderContinuousNorm_of_isSigmaOrderComplete
  intro u hmono hbdd
  set v : ℕ → X := fun n => u n - u 0 with hv_def
  have hv_mono : Monotone v := fun n m hnm => sub_le_sub_right (hmono hnm) _
  have hv_nn : ∀ n, 0 ≤ v n := fun n => sub_nonneg.mpr (hmono (Nat.zero_le n))
  have hv_bdd : BddAbove (Set.range v) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨b - u 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sub_le_sub_right (hb ⟨n, rfl⟩) _
  have hv_cauchy : CauchySeq v :=
    cauchySeq_monotone_nonneg_bddAbove hv_mono hv_nn hv_bdd
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hv_cauchy
  have hx_lub : IsLUB (Set.range v) x :=
    NormedVectorLattice.isLUB_of_monotone_tendsto hv_mono hx
  refine ⟨x + u 0, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      have h := hx_lub.1 ⟨n, rfl⟩
      have h2 : v n + u 0 ≤ x + u 0 := add_le_add_left h (u 0)
      rwa [show v n + u 0 = u n from by change (u n - u 0) + u 0 = u n; abel] at h2
    · intro y hy
      have hub : y - u 0 ∈ upperBounds (Set.range v) := by
        rintro _ ⟨n, rfl⟩
        exact sub_le_sub_right (hy ⟨n, rfl⟩) _
      have h : x ≤ y - u 0 := hx_lub.2 hub
      calc x + u 0 ≤ (y - u 0) + u 0 := add_le_add_left h _
        _ = y := by abel
  · have htend : Filter.Tendsto (fun n => v n + u 0) Filter.atTop (nhds (x + u 0)) :=
      hx.add_const (u 0)
    have heq : (fun n => v n + u 0) = u := by
      funext n; change (u n - u 0) + u 0 = u n; abel
    rwa [heq] at htend

end ALSpace

/-! ### Duality between AL- and AM-spaces -/

/-- The norm dual of an AM-space is an AL-space: for positive `φ, ψ` in the
dual, the dual norm satisfies `‖φ + ψ‖ = ‖φ‖ + ‖ψ‖`. The proof characterizes
the dual norm as a supremum over the positive unit ball, and uses the
AM-property `x ⊔ y ∈ S` (with `‖x ⊔ y‖ ≤ 1`) to show that for any
`x, y ∈ S` we have `(φ + ψ)(x ⊔ y) ≥ φ(x) + ψ(y)`. -/
noncomputable instance NormDualSpace.instALSpace_of_amSpace
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [AMSpace X] : ALSpace (NormDualSpace X) := by
  refine { norm_add_eq_of_nonneg := ?_ }
  intro φ ψ hφ hψ
  apply le_antisymm
  · exact norm_add_le φ ψ
  -- ≥ direction via AM property and dual-norm characterization
  have hsum_nn : 0 ≤ φ + ψ := add_nonneg hφ hψ
  rw [NormDualSpace.norm_of_nonneg hφ, NormDualSpace.norm_of_nonneg hψ,
      NormDualSpace.norm_of_nonneg hsum_nn]
  set S : Set X := {x | ‖x‖ ≤ 1} ∩ {x | 0 ≤ x} with hS_def
  have hS_zero : (0 : X) ∈ S := ⟨by simp, le_refl _⟩
  have hpos_apply : ∀ {ρ : NormDualSpace X}, 0 ≤ ρ →
      ∀ {x : X}, 0 ≤ x → 0 ≤ (ρ : X → ℝ) x := by
    intro ρ hρ x hx
    change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace ρ at hρ
    have := hρ x hx; simpa using this
  have hbdd_above : ∀ {ρ : NormDualSpace X}, 0 ≤ ρ →
      BddAbove ((ρ : X → ℝ) '' S) := by
    intro ρ hρ
    refine ⟨‖ρ‖, ?_⟩
    rintro _ ⟨x, ⟨hx1, hx0⟩, rfl⟩
    have hx1' : ‖x‖ ≤ 1 := hx1
    have h_pos : 0 ≤ (ρ : X → ℝ) x := hpos_apply hρ hx0
    calc (ρ : X → ℝ) x = ‖ρ x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
      _ ≤ ‖ρ‖ * ‖x‖ := ρ.le_opNorm x
      _ ≤ ‖ρ‖ * 1 := by gcongr
      _ = ‖ρ‖ := mul_one _
  have hbdd_φ := hbdd_above hφ
  have hbdd_ψ := hbdd_above hψ
  have hbdd_sum := hbdd_above hsum_nn
  have hne_φ : ((φ : X → ℝ) '' S).Nonempty := ⟨(φ : X → ℝ) 0, 0, hS_zero, rfl⟩
  have hne_ψ : ((ψ : X → ℝ) '' S).Nonempty := ⟨(ψ : X → ℝ) 0, 0, hS_zero, rfl⟩
  have hS_sup : ∀ {x y : X}, x ∈ S → y ∈ S → x ⊔ y ∈ S := by
    intro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    have hx1' : ‖x‖ ≤ 1 := hx1
    have hy1' : ‖y‖ ≤ 1 := hy1
    refine ⟨?_, le_sup_of_le_left hx2⟩
    change ‖x ⊔ y‖ ≤ 1
    rw [AMSpace.norm_sup_eq_max_of_nonneg hx2 hy2]
    exact max_le hx1' hy1'
  have hmono : ∀ {ρ : NormDualSpace X}, 0 ≤ ρ →
      ∀ {w z : X}, w ≤ z → (ρ : X → ℝ) w ≤ (ρ : X → ℝ) z := by
    intro ρ hρ w z hwz
    have hpos : 0 ≤ z - w := sub_nonneg.mpr hwz
    have := hpos_apply hρ hpos
    rw [map_sub] at this
    linarith
  -- For x, y ∈ S, φ x + ψ y ≤ (φ + ψ)(x ⊔ y) ≤ sSup ((φ + ψ) '' S).
  have hsum_le : ∀ x y : X, x ∈ S → y ∈ S →
      (φ : X → ℝ) x + (ψ : X → ℝ) y ≤
        sSup (((φ + ψ : NormDualSpace X) : X → ℝ) '' S) := by
    intro x y hx hy
    have hxy : x ⊔ y ∈ S := hS_sup hx hy
    have h1 := hmono hφ (le_sup_left : x ≤ x ⊔ y)
    have h2 := hmono hψ (le_sup_right : y ≤ x ⊔ y)
    have h4 : ((φ + ψ : NormDualSpace X) : X → ℝ) (x ⊔ y) ≤
        sSup (((φ + ψ : NormDualSpace X) : X → ℝ) '' S) :=
      le_csSup hbdd_sum ⟨x ⊔ y, hxy, rfl⟩
    have h3 : ((φ + ψ : NormDualSpace X) : X → ℝ) (x ⊔ y) =
        (φ : X → ℝ) (x ⊔ y) + (ψ : X → ℝ) (x ⊔ y) := rfl
    linarith
  -- Take the sup first over y, then over x.
  have hstep : ∀ x ∈ S, (φ : X → ℝ) x + sSup ((ψ : X → ℝ) '' S) ≤
      sSup (((φ + ψ : NormDualSpace X) : X → ℝ) '' S) := by
    intro x hx
    have h_inner : sSup ((ψ : X → ℝ) '' S) ≤
        sSup (((φ + ψ : NormDualSpace X) : X → ℝ) '' S) - (φ : X → ℝ) x := by
      apply csSup_le hne_ψ
      rintro _ ⟨y, hy, rfl⟩
      linarith [hsum_le x y hx hy]
    linarith
  have h_outer : sSup ((φ : X → ℝ) '' S) ≤
      sSup (((φ + ψ : NormDualSpace X) : X → ℝ) '' S) - sSup ((ψ : X → ℝ) '' S) := by
    apply csSup_le hne_φ
    rintro _ ⟨x, hx, rfl⟩
    linarith [hstep x hx]
  linarith

/-- The norm dual of an AL-space is an AM-space: for positive `φ, ψ` in the
dual, the dual norm satisfies `‖φ ⊔ ψ‖ = max ‖φ‖ ‖ψ‖`. The proof combines the
Riesz–Kantorovich formula with the AL-axiom: any positive `x` with `‖x‖ ≤ 1`
splits as `x = y + z` with `‖y‖ + ‖z‖ = ‖x‖ ≤ 1`, so the operator norm bounds
on `φ y` and `ψ z` give the bound by `max ‖φ‖ ‖ψ‖`. -/
noncomputable instance NormDualSpace.instAMSpace_of_alSpace
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] : AMSpace (NormDualSpace X) := by
  refine { norm_sup_eq_max_of_nonneg := ?_ }
  intro φ ψ hφ hψ
  have hsup_nn : 0 ≤ φ ⊔ ψ := le_sup_of_le_left hφ
  apply le_antisymm
  · -- ≤: Riesz–Kantorovich + AL
    rw [NormDualSpace.norm_of_nonneg hsup_nn]
    apply csSup_le
    · refine ⟨((φ ⊔ ψ : NormDualSpace X) : X → ℝ) 0, 0, ⟨by simp, le_refl _⟩, rfl⟩
    rintro _ ⟨x, ⟨hx1, hx0⟩, rfl⟩
    have hx1' : ‖x‖ ≤ 1 := hx1
    have hsup_eq : ((φ ⊔ ψ : NormDualSpace X) : X → ℝ) x =
        (NormDualSpace.toOrderDualSpace φ ⊔ NormDualSpace.toOrderDualSpace ψ) x := rfl
    rw [hsup_eq]
    have hRK := OrderDualSpace.isLUB_sup_apply
      (φ := NormDualSpace.toOrderDualSpace φ)
      (ψ := NormDualSpace.toOrderDualSpace ψ) hx0
    apply hRK.2
    rintro _ ⟨y, z, hy, hz, hyz, rfl⟩
    have hyz_norm : ‖y‖ + ‖z‖ = ‖x‖ := by
      rw [← hyz, ALSpace.norm_add_eq_of_nonneg hy hz]
    have hbound : ∀ {ρ : NormDualSpace X} {w : X}, 0 ≤ ρ → 0 ≤ w →
        (NormDualSpace.toOrderDualSpace ρ) w ≤ ‖ρ‖ * ‖w‖ := by
      intro ρ w hρ hw
      simp only [NormDualSpace.toOrderDualSpace_apply]
      have h_pos : 0 ≤ (ρ : X → ℝ) w := by
        change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace ρ at hρ
        have := hρ w hw; simpa using this
      calc (ρ : X → ℝ) w = ‖ρ w‖ := by rw [Real.norm_eq_abs, abs_of_nonneg h_pos]
        _ ≤ ‖ρ‖ * ‖w‖ := ρ.le_opNorm w
    have hφ_y := hbound hφ hy
    have hψ_z := hbound hψ hz
    have hmax_nn : 0 ≤ max ‖φ‖ ‖ψ‖ := le_max_of_le_left (norm_nonneg _)
    calc (NormDualSpace.toOrderDualSpace φ) y + (NormDualSpace.toOrderDualSpace ψ) z
        ≤ ‖φ‖ * ‖y‖ + ‖ψ‖ * ‖z‖ := add_le_add hφ_y hψ_z
      _ ≤ max ‖φ‖ ‖ψ‖ * ‖y‖ + max ‖φ‖ ‖ψ‖ * ‖z‖ := by gcongr <;> simp
      _ = max ‖φ‖ ‖ψ‖ * (‖y‖ + ‖z‖) := by ring
      _ = max ‖φ‖ ‖ψ‖ * ‖x‖ := by rw [hyz_norm]
      _ ≤ max ‖φ‖ ‖ψ‖ * 1 := by gcongr
      _ = max ‖φ‖ ‖ψ‖ := mul_one _
  · -- ≥: solidness, since `φ ≤ φ ⊔ ψ` and `ψ ≤ φ ⊔ ψ`
    apply max_le
    · apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg hφ, abs_of_nonneg hsup_nn]
      exact le_sup_left
    · apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg hψ, abs_of_nonneg hsup_nn]
      exact le_sup_right

/-! ### The unit functional on the dual of an AL-space -/

/-- The underlying additive monoid hom of the canonical unit functional
`e(x) = ‖x⁺‖ - ‖x⁻‖` on the dual of an AL-space. Additivity follows from the
AL-axiom applied to the identity `(x + y)⁺ + x⁻ + y⁻ = x⁺ + y⁺ + (x + y)⁻`. -/
private noncomputable def alSpaceDualUnitHom
    (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] : X →+ ℝ where
  toFun x := ‖x⁺‖ - ‖x⁻‖
  map_zero' := by simp
  map_add' x y := by
    change ‖(x + y)⁺‖ - ‖(x + y)⁻‖ = (‖x⁺‖ - ‖x⁻‖) + (‖y⁺‖ - ‖y⁻‖)
    have key : (x + y)⁺ + x⁻ + y⁻ = x⁺ + y⁺ + (x + y)⁻ := by
      have h : (x + y)⁺ - (x + y)⁻ = (x⁺ - x⁻) + (y⁺ - y⁻) := by
        rw [posPart_sub_negPart, posPart_sub_negPart, posPart_sub_negPart]
      have h' : (x + y)⁺ = (x⁺ - x⁻) + (y⁺ - y⁻) + (x + y)⁻ := by
        rw [← h]; abel
      rw [h']; abel
    have hLHS : ‖(x + y)⁺ + x⁻ + y⁻‖ = ‖(x + y)⁺‖ + ‖x⁻‖ + ‖y⁻‖ := by
      rw [ALSpace.norm_add_eq_of_nonneg
            (add_nonneg (posPart_nonneg _) (negPart_nonneg _))
            (negPart_nonneg _),
          ALSpace.norm_add_eq_of_nonneg (posPart_nonneg _) (negPart_nonneg _)]
    have hRHS : ‖x⁺ + y⁺ + (x + y)⁻‖ = ‖x⁺‖ + ‖y⁺‖ + ‖(x + y)⁻‖ := by
      rw [ALSpace.norm_add_eq_of_nonneg
            (add_nonneg (posPart_nonneg _) (posPart_nonneg _))
            (negPart_nonneg _),
          ALSpace.norm_add_eq_of_nonneg (posPart_nonneg _) (posPart_nonneg _)]
    have hsame : ‖(x + y)⁺ + x⁻ + y⁻‖ = ‖x⁺ + y⁺ + (x + y)⁻‖ := by rw [key]
    rw [hLHS, hRHS] at hsame
    linarith

/-- The canonical unit functional on the dual of an AL-space, defined via
`e(x) = ‖x⁺‖ - ‖x⁻‖`. On the positive cone it agrees with the AL-norm.
A continuous additive map between topological `ℝ`-vector spaces is
automatically `ℝ`-linear, so the additive monoid hom `alSpaceDualUnitHom`
together with continuity yields a continuous linear functional. -/
private noncomputable def alSpaceDualUnit
    (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] : NormDualSpace X :=
  (alSpaceDualUnitHom X).toRealLinearMap <| by
    apply Continuous.sub
    · exact continuous_norm.comp continuous_posPart
    · exact continuous_norm.comp continuous_negPart

private theorem alSpaceDualUnit_apply_of_nonneg
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] {x : X} (hx : 0 ≤ x) :
    (alSpaceDualUnit X : X → ℝ) x = ‖x‖ := by
  change ‖x⁺‖ - ‖x⁻‖ = ‖x‖
  rw [posPart_of_nonneg hx, negPart_of_nonneg hx, norm_zero, sub_zero]

private theorem alSpaceDualUnit_nonneg
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] : (0 : NormDualSpace X) ≤ alSpaceDualUnit X := by
  change NormDualSpace.toOrderDualSpace 0
    ≤ NormDualSpace.toOrderDualSpace (alSpaceDualUnit X)
  intro x hx
  change (0 : ℝ) ≤ alSpaceDualUnit X x
  rw [alSpaceDualUnit_apply_of_nonneg hx]
  exact norm_nonneg _

private theorem alSpaceDual_abs_le_norm_smul_unit
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] (φ : NormDualSpace X) :
    (|φ| : NormDualSpace X) ≤ ‖φ‖ • alSpaceDualUnit X := by
  change NormDualSpace.toOrderDualSpace _
    ≤ NormDualSpace.toOrderDualSpace (‖φ‖ • alSpaceDualUnit X)
  intro x hx
  change (|φ| : NormDualSpace X) x ≤ (‖φ‖ • alSpaceDualUnit X) x
  have h1 : (‖φ‖ • alSpaceDualUnit X) x = ‖φ‖ * alSpaceDualUnit X x := rfl
  rw [h1, alSpaceDualUnit_apply_of_nonneg hx]
  have h_pos : 0 ≤ (|φ| : NormDualSpace X) x := by
    have h_abs_nn : (0 : NormDualSpace X) ≤ |φ| := abs_nonneg φ
    change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace _ at h_abs_nn
    have := h_abs_nn x hx; simpa using this
  have h_op := (|φ| : NormDualSpace X).le_opNorm x
  rw [Real.norm_eq_abs, abs_of_nonneg h_pos, NormDualSpace.norm_abs] at h_op
  exact h_op

private theorem alSpaceDualUnit_norm_eq_gaugeNorm
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [ALSpace X] (φ : NormDualSpace X) :
    ‖φ‖ = OrderIdeal.gaugeNorm (alSpaceDualUnit X) φ := by
  apply le_antisymm
  · -- `‖φ‖ ≤ gaugeNorm e φ`: bound `‖φ x‖` via `|φ| ≤ gaugeNorm e φ • e`
    apply ContinuousLinearMap.opNorm_le_bound _ (OrderIdeal.gaugeNorm_nonneg _ _)
    intro x
    have habs_unit : (|alSpaceDualUnit X| : NormDualSpace X) = alSpaceDualUnit X :=
      abs_of_nonneg alSpaceDualUnit_nonneg
    have hφ_principal : φ ∈ OrderIdeal.principal (alSpaceDualUnit X) := by
      refine ⟨‖φ‖, norm_nonneg _, ?_⟩
      rw [habs_unit]
      exact alSpaceDual_abs_le_norm_smul_unit φ
    have h_gauge :=
      OrderIdeal.abs_le_gaugeNorm_smul_abs (alSpaceDualUnit X) hφ_principal
    rw [habs_unit] at h_gauge
    have h_apply : (|φ| : NormDualSpace X) (|x|) ≤
        OrderIdeal.gaugeNorm (alSpaceDualUnit X) φ * ‖x‖ := by
      change NormDualSpace.toOrderDualSpace _ ≤ NormDualSpace.toOrderDualSpace _ at h_gauge
      have h := h_gauge (|x|) (abs_nonneg x)
      simp only [NormDualSpace.toOrderDualSpace_apply] at h
      have h2 : (OrderIdeal.gaugeNorm (alSpaceDualUnit X) φ • alSpaceDualUnit X) (|x|) =
          OrderIdeal.gaugeNorm (alSpaceDualUnit X) φ * (alSpaceDualUnit X (|x|)) := rfl
      rw [h2, alSpaceDualUnit_apply_of_nonneg (abs_nonneg x), norm_abs_eq_norm] at h
      exact h
    have h_abs : |φ x| ≤ (|φ| : NormDualSpace X) (|x|) := by
      have heq : (|φ| : NormDualSpace X) (|x|) =
          (|NormDualSpace.toOrderDualSpace φ|) (|x|) := rfl
      rw [heq]
      exact (OrderBoundedHom.isLUB_abs_apply
        (f := NormDualSpace.toOrderDualSpace φ) (abs_nonneg x)).1 ⟨x, le_refl _, rfl⟩
    rw [Real.norm_eq_abs]
    exact h_abs.trans h_apply
  · -- `gaugeNorm e φ ≤ ‖φ‖`: from `|φ| ≤ ‖φ‖ • e` and `gaugeNorm_le_of_abs_le`
    apply OrderIdeal.gaugeNorm_le_of_abs_le (alSpaceDualUnit X) (norm_nonneg _)
    have habs_unit : (|alSpaceDualUnit X| : NormDualSpace X) = alSpaceDualUnit X :=
      abs_of_nonneg alSpaceDualUnit_nonneg
    rw [habs_unit]
    exact alSpaceDual_abs_le_norm_smul_unit φ

/-- The norm dual of a non-trivial AL-space is an AM-space with unit. The
strong unit is the positive functional `e : x ↦ ‖x⁺‖ - ‖x⁻‖`, which on the
positive cone agrees with the AL-norm. The hypothesis `Nontrivial X` is
needed to ensure that `e ≠ 0` in the dual ordering: for the trivial AL-space,
the dual is also trivial and admits no strict unit. -/
noncomputable instance NormDualSpace.instAMSpaceWithUnit_of_alSpace
    {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [Nontrivial X] [ALSpace X] : AMSpaceWithUnit (NormDualSpace X) where
  unit := alSpaceDualUnit X
  unit_pos := by
    refine ⟨alSpaceDualUnit_nonneg, ?_⟩
    intro h_le_zero
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    have h1 : alSpaceDualUnit X (|x|) = ‖x‖ := by
      rw [alSpaceDualUnit_apply_of_nonneg (abs_nonneg x), norm_abs_eq_norm]
    have h2 : alSpaceDualUnit X (|x|) ≤ 0 := by
      change NormDualSpace.toOrderDualSpace _ ≤ NormDualSpace.toOrderDualSpace _ at h_le_zero
      have := h_le_zero (|x|) (abs_nonneg x)
      simpa using this
    rw [h1] at h2
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    linarith
  norm_eq_gaugeNorm := alSpaceDualUnit_norm_eq_gaugeNorm
