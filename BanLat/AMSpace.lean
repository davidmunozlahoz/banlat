import BanLat.Normed
import BanLat.Substructures.Ideal
import Mathlib.Order.Zorn

/-!
# AM-spaces and AM-spaces with unit

An **AM-space** is a Banach lattice whose norm satisfies the AM-axiom:
`‖x ⊔ y‖ = max ‖x‖ ‖y‖` for all non-negative `x` and `y`. Equivalently, the
norm of the supremum of two disjoint elements equals the maximum of their norms.
An **AM-space with unit** is an AM-space possessing a strong unit `e` whose
gauge norm (see `OrderIdeal.gaugeNorm`) agrees with the original norm. This
makes the closed unit ball exactly the order interval `[-e, e]`.
-/

/-! ### Strong units -/

/-- An element `e > 0` of a vector lattice is a **strong unit** if every element
is dominated by a positive real multiple of `e`. -/
class IsStrongUnit (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [Module ℝ X] (e : X) : Prop where
  pos : (0 : X) < e
  dominates : ∀ x : X, ∃ r : ℝ, 0 < r ∧ |x| ≤ r • e

namespace IsStrongUnit

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] {e : X} [IsStrongUnit X e]

/-- A strong unit is non-negative. -/
theorem nonneg : (0 : X) ≤ e := le_of_lt pos

/-- If `e` is a strong unit, the principal ideal of `e` is the whole space. -/
theorem principal_eq_top (x : X) : x ∈ OrderIdeal.principal e := by
  rw [OrderIdeal.mem_principal]
  obtain ⟨r, hr, hle⟩ := @dominates X _ _ _ _ e _ x
  exact ⟨r, le_of_lt hr,
    hle.trans (smul_le_smul_of_nonneg_left (le_abs_self e) (le_of_lt hr))⟩

end IsStrongUnit

/-! ### AM-spaces -/

/-- An **AM-space** is a Banach lattice whose norm satisfies the AM-axiom: for
all non-negative elements `x` and `y`, `‖x ⊔ y‖ = max ‖x‖ ‖y‖`. -/
class AMSpace (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends BanachLattice X where
  norm_sup_eq_max_of_nonneg {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x ⊔ y‖ = max ‖x‖ ‖y‖

namespace AMSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [AMSpace X]

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
  le_inf := fun x y z h1 h2 => show x.1 ≤ y.1 ⊓ z.1 from le_inf h1 h2

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

/-- A closed vector sublattice of an AM-space, equipped with the subspace norm
and induced lattice operations, is an AM-space. -/
instance instAMSpace_closedSublattice (Y : VectorSublattice X)
    (hclosed : IsClosed (Y : Set X)) :
    @AMSpace Y.toSubmodule Y.toSubmodule.normedAddCommGroup
      (instLatticeClosedSublattice Y)
      (instIsOrderedAddMonoidClosedSublattice Y) := by
  letI : NormedAddCommGroup Y.toSubmodule := Y.toSubmodule.normedAddCommGroup
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
    norm_sup_eq_max_of_nonneg := by
      intro x y hx hy
      change ‖x.1 ⊔ y.1‖ = max ‖x.1‖ ‖y.1‖
      exact AMSpace.norm_sup_eq_max_of_nonneg hx hy
  }

end AMSpace

/-! ### AM-spaces with unit -/

/-- An **AM-space with unit** is an AM-space equipped with a strong unit `e`
whose gauge norm agrees with the original norm. The gauge norm theory from
`OrderIdeal` then gives a complete description of the norm. -/
class AMSpaceWithUnit (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] extends AMSpace X where
  unit : X
  unit_pos : 0 < unit
  norm_eq_gaugeNorm : ∀ x : X, ‖x‖ = OrderIdeal.gaugeNorm unit x

namespace AMSpaceWithUnit

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [AMSpaceWithUnit X]

/-- The unit element of an AM-space with unit. -/
noncomputable def e : X := AMSpaceWithUnit.unit

/-- The norm of the unit is one. -/
theorem norm_unit : ‖(e : X)‖ = 1 := by
  unfold e
  apply le_antisymm
  · -- ‖unit‖ ≤ 1: gauge norm of unit ≤ 1
    rw [norm_eq_gaugeNorm]
    exact OrderIdeal.gaugeNorm_le_of_abs_le _ one_pos.le (one_smul ℝ _).ge
  · -- 1 ≤ ‖unit‖: from |unit| ≤ ‖unit‖ • |unit|, take norms
    have hmem := OrderIdeal.self_mem_principal (X := X) unit
    have h := OrderIdeal.abs_le_gaugeNorm_smul_abs unit hmem
    rw [← norm_eq_gaugeNorm] at h
    have hnpos : (0 : ℝ) < ‖(unit : X)‖ := norm_pos_iff.mpr (ne_of_gt unit_pos)
    have h2 := norm_le_norm_of_abs_le_abs
      (h.trans (le_abs_self _))
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _),
        norm_abs_eq_norm] at h2
    exact le_of_mul_le_mul_right (by linarith) hnpos

private theorem mem_principal_unit (x : X) :
    x ∈ OrderIdeal.principal (unit : X) := by
  by_cases hx : x = 0
  · subst hx; exact ⟨0, le_rfl, by simp⟩
  · rw [OrderIdeal.mem_principal]
    by_contra h
    push_neg at h
    have : OrderIdeal.gaugeNorm (unit : X) x = 0 := by
      unfold OrderIdeal.gaugeNorm
      convert Real.sInf_empty using 2
      ext c; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ⟨hc, hle⟩ => h c hc hle
    linarith [norm_pos_iff.mpr hx, (norm_eq_gaugeNorm x).symm ▸ this]

/-- `‖x‖ ≤ r ↔ |x| ≤ r • e` for `r ≥ 0`. This is the fundamental
characterisation of the norm in an AM-space with unit; it follows from
`OrderIdeal.gaugeNorm_le_of_abs_le` and `OrderIdeal.abs_le_gaugeNorm_smul_abs`
via `norm_eq_gaugeNorm`. -/
theorem norm_le_iff {x : X} {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ ≤ r ↔ |x| ≤ r • e := by
  unfold e
  constructor
  · intro h
    have h1 := OrderIdeal.abs_le_gaugeNorm_smul_abs (unit : X)
      (mem_principal_unit x)
    rw [← norm_eq_gaugeNorm, abs_of_nonneg (le_of_lt unit_pos)] at h1
    exact h1.trans (smul_le_smul_of_nonneg_right h (le_of_lt unit_pos))
  · intro h
    rw [norm_eq_gaugeNorm]
    exact OrderIdeal.gaugeNorm_le_of_abs_le _ hr
      (by rwa [abs_of_nonneg (le_of_lt unit_pos)])

/-- The closed unit ball is `{x | |x| ≤ e}`, i.e. the order interval
`[-e, e]`. Special case of `norm_le_iff` at `r = 1`. -/
theorem norm_le_one_iff {x : X} : ‖x‖ ≤ 1 ↔ |x| ≤ e := by
  rw [norm_le_iff one_pos.le]; simp [e]

/-- Every element satisfies `|x| ≤ ‖x‖ • e`. Follows from
`OrderIdeal.abs_le_gaugeNorm_smul_abs` via `norm_eq_gaugeNorm`. -/
theorem abs_le_norm_smul_unit (x : X) : |x| ≤ ‖x‖ • e :=
  (norm_le_iff (norm_nonneg x)).mp le_rfl

private theorem gauge_lower_bound
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] (u : Y) (hu : 0 < u) [IsStrongUnit Y u] :
    ∀ x : Y, (1 / ‖u‖) * ‖x‖ ≤ OrderIdeal.gaugeNorm u x := by
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr (ne_of_gt hu)
  intro x
  apply le_csInf (IsStrongUnit.principal_eq_top x)
  intro c ⟨hc, hle⟩
  have h := norm_le_norm_of_abs_le_abs (hle.trans (le_abs_self _))
  rw [norm_smul, Real.norm_of_nonneg hc, norm_abs_eq_norm] at h
  rw [one_div, inv_mul_le_iff₀ hu_norm_pos]
  linarith

private theorem gauge_upper_bound
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [BanachLattice Y] (u : Y) [IsStrongUnit Y u] :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Y, OrderIdeal.gaugeNorm u x ≤ C * ‖x‖ := by
  have hu_pos := IsStrongUnit.pos (e := u)
  have hu_nonneg := le_of_lt hu_pos
  -- Order intervals S n = Icc(-(n•u))(n•u) cover Y
  have hcover : ⋃ n : ℕ, Set.Icc (-(↑n : ℝ) • u) ((↑n : ℝ) • u) = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨r, hr, hle⟩ := @IsStrongUnit.dominates Y _ _ _ _ u _ x
    refine ⟨⌈r⌉₊ + 1, ?_⟩
    have hrn : r ≤ (↑(⌈r⌉₊ + 1) : ℝ) :=
      le_trans (Nat.le_ceil r) (by norm_cast; omega)
    have habs : |x| ≤ (↑(⌈r⌉₊ + 1) : ℝ) • u :=
      hle.trans (smul_le_smul_of_nonneg_right hrn hu_nonneg)
    rw [Set.mem_Icc]
    exact ⟨by rw [neg_smul]; exact neg_le.mp (abs_le'.mp habs).2,
           (abs_le'.mp habs).1⟩
  -- By Baire, some interval has nonempty interior
  obtain ⟨n₀, hn₀⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n => isClosed_Icc) hcover
  obtain ⟨p, hp_int⟩ := hn₀
  obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hp_int)
  -- p ∈ S n₀, so |p| ≤ n₀ • u
  have hp_mem : p ∈ Set.Icc (-(↑n₀ : ℝ) • u) ((↑n₀ : ℝ) • u) :=
    interior_subset hp_int
  -- For ‖y‖ < ε: y + p ∈ ball(p, ε) ⊆ S n₀
  -- |y| ≤ |y + p| + |p| ≤ 2 * n₀ • u
  have hbound : ∀ y : Y, ‖y‖ < ε →
      OrderIdeal.gaugeNorm u y ≤ 2 * (↑n₀ + 1) := by
    intro y hy
    have hyp : y + p ∈ Set.Icc (-(↑n₀ : ℝ) • u) ((↑n₀ : ℝ) • u) :=
      hball (by rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right])
    have h1 : |y + p| ≤ (↑n₀ : ℝ) • u := by
      apply abs_le'.mpr; refine ⟨hyp.2, ?_⟩
      have h := hyp.1; rw [neg_smul] at h; exact neg_le.mp h
    have h2 : |p| ≤ (↑n₀ : ℝ) • u := by
      apply abs_le'.mpr; refine ⟨hp_mem.2, ?_⟩
      have h := hp_mem.1; rw [neg_smul] at h; exact neg_le.mp h
    have h3 : |y| ≤ (2 * (↑n₀ + 1) : ℝ) • u := by
      have key : |y| ≤ |y + p| + |(-p)| := by
        conv_lhs => rw [show y = (y + p) + (-p) from by abel]
        exact abs_add_le _ _
      calc |y| ≤ |y + p| + |(-p)| := key
        _ = |y + p| + |p| := by rw [abs_neg]
        _ ≤ (↑n₀ : ℝ) • u + (↑n₀ : ℝ) • u := add_le_add h1 h2
        _ ≤ (2 * (↑n₀ + 1) : ℝ) • u := by
            rw [← add_smul]
            exact smul_le_smul_of_nonneg_right (by linarith) hu_nonneg
    exact OrderIdeal.gaugeNorm_le_of_abs_le _ (by positivity)
      (by rwa [abs_of_nonneg hu_nonneg])
  -- Scale: for x ≠ 0, gaugeNorm x ≤ (4 * n₀ / ε) * ‖x‖
  refine ⟨4 * (↑n₀ + 1) / ε, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, OrderIdeal.gaugeNorm_zero]
  · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hε2 : (0 : ℝ) < ε / (2 * ‖x‖) := div_pos hε_pos (by positivity)
    have hscaled : OrderIdeal.gaugeNorm u ((ε / (2 * ‖x‖)) • x)
        ≤ 2 * (↑n₀ + 1) := by
      apply hbound
      rw [norm_smul, Real.norm_of_nonneg hε2.le]
      field_simp; linarith
    rw [OrderIdeal.gaugeNorm_smul, abs_of_pos hε2] at hscaled
    calc OrderIdeal.gaugeNorm u x
        = (ε / (2 * ‖x‖))⁻¹ * (ε / (2 * ‖x‖) *
            OrderIdeal.gaugeNorm u x) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hε2), one_mul]
      _ ≤ (ε / (2 * ‖x‖))⁻¹ * (2 * (↑n₀ + 1)) :=
          mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hε2.le)
      _ = 4 * (↑n₀ + 1) / ε * ‖x‖ := by rw [inv_div]; ring

/-- Every Banach lattice with a strong unit admits an equivalent AM-norm making
it an AM-space with unit. More precisely, the gauge norm `gaugeNorm u` is an
AM-norm equivalent to the original norm. -/
theorem exists_equiv_amSpaceWithUnit
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [BanachLattice Y] (u : Y) [IsStrongUnit Y u] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      (∀ x : Y, C₁ * ‖x‖ ≤ OrderIdeal.gaugeNorm u x) ∧
      (∀ x : Y, OrderIdeal.gaugeNorm u x ≤ C₂ * ‖x‖) := by
  have hu_pos := IsStrongUnit.pos (e := u)
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr (ne_of_gt hu_pos)
  obtain ⟨C₂, hC₂, hupper⟩ := gauge_upper_bound u
  exact ⟨1 / ‖u‖, C₂, div_pos one_pos hu_norm_pos, hC₂,
    gauge_lower_bound u hu_pos, hupper⟩

/-! ### Maximal ideals in AM-spaces with unit -/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [AMSpaceWithUnit X]

/-- An ideal is the whole space iff it contains the unit. -/
theorem top_iff_unit_mem (I : OrderIdeal X) :
    I = ⊤ ↔ (e : X) ∈ I := by
  constructor
  · intro h; rw [h]; exact OrderIdeal.mem_top
  · intro h
    have : ∀ x : X, x ∈ I := by
      intro x
      -- Use the norm characterization: |x| ≤ ‖x‖ • e and solidity
      have h1 : |x| ≤ ‖x‖ • e := abs_le_norm_smul_unit x
      -- Since e ∈ I, we have ‖x‖ • e ∈ I by smul_mem
      have h2 : ‖x‖ • e ∈ I := I.toSubmodule.smul_mem ‖x‖ h
      -- By solidity, |x| ∈ I
      have h3 : |x| ∈ I := I.mem_of_abs_le_abs h2 (by
        rw [abs_of_nonneg (abs_nonneg x)]
        calc |x| ≤ ‖x‖ • e := h1
          _ ≤ |‖x‖ • e| := le_abs_self _)
      -- Finally, x ∈ I since |x| ∈ I
      exact I.mem_of_abs_mem h3
    -- Use SetLike.ext instead of ext
    apply SetLike.ext
    intro x
    exact ⟨fun _ => OrderIdeal.mem_top, fun _ => this x⟩

/-- The partial order on order ideals induced by set inclusion via the
underlying submodule. -/
instance instPartialOrder : PartialOrder (OrderIdeal X) :=
  PartialOrder.lift (fun J : OrderIdeal X => J.toSubmodule)
    OrderIdeal.toSubmodule_injective

private theorem directedOn_toSubmodule_of_chain {c : Set (OrderIdeal X)}
    (hchain : IsChain (· ≤ ·) c) :
    DirectedOn (· ≤ ·) ((fun J : OrderIdeal X => J.toSubmodule) '' c) := by
  rintro _ ⟨J₁, hJ₁, rfl⟩ _ ⟨J₂, hJ₂, rfl⟩
  by_cases heq : J₁ = J₂
  · exact ⟨J₁.toSubmodule, ⟨J₁, hJ₁, rfl⟩, le_refl _, heq ▸ le_refl _⟩
  · rcases hchain hJ₁ hJ₂ heq with h | h
    · exact ⟨J₂.toSubmodule, ⟨J₂, hJ₂, rfl⟩, h, le_refl _⟩
    · exact ⟨J₁.toSubmodule, ⟨J₁, hJ₁, rfl⟩, le_refl _, h⟩

/-- **Every proper order ideal is contained in a maximal proper order ideal.**
Standard Zorn's lemma argument applied to the poset of proper order ideals
containing `I`, using the union of a chain as the upper bound. -/
theorem exists_le_maximal (I : OrderIdeal X) (hI : I ≠ ⊤) :
    ∃ M : OrderIdeal X, I ≤ M ∧ M ≠ ⊤ ∧
      ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M := by
  classical
  set S : Set (OrderIdeal X) := {J | I ≤ J ∧ J ≠ ⊤} with hS_def
  have hIS : I ∈ S := ⟨le_refl _, hI⟩
  have hzorn : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hchain y hyc
    set SM : Set (Submodule ℝ X) :=
      (fun J : OrderIdeal X => J.toSubmodule) '' c with hSM_def
    have hSMne : SM.Nonempty := ⟨y.toSubmodule, y, hyc, rfl⟩
    have hdir : DirectedOn (· ≤ ·) SM := directedOn_toSubmodule_of_chain hchain
    -- The union (sSup) is an order ideal via `ofSolid`
    refine ⟨OrderIdeal.ofSolid (sSup SM) ?_, ⟨?_, ?_⟩, ?_⟩
    · -- Solid condition
      intro x w hx hxw
      rw [Submodule.mem_sSup_of_directed hSMne hdir] at hx
      obtain ⟨_, ⟨J, hJ, rfl⟩, hxJ⟩ := hx
      rw [Submodule.mem_sSup_of_directed hSMne hdir]
      exact ⟨J.toSubmodule, ⟨J, hJ, rfl⟩, J.mem_of_abs_le_abs hxJ hxw⟩
    · -- I ≤ ofSolid (sSup SM) _
      change I.toSubmodule ≤ sSup SM
      exact le_trans (hcS hyc).1 (le_sSup ⟨y, hyc, rfl⟩)
    · -- ofSolid (sSup SM) _ ≠ ⊤
      intro hU_top
      have hmem : (e : X) ∈ sSup SM := by
        have : (e : X) ∈ (⊤ : OrderIdeal X) := OrderIdeal.mem_top
        rw [← hU_top] at this
        exact this
      rw [Submodule.mem_sSup_of_directed hSMne hdir] at hmem
      obtain ⟨_, ⟨J, hJ, rfl⟩, heJ⟩ := hmem
      exact (hcS hJ).2 ((top_iff_unit_mem J).mpr heJ)
    · -- upper bound
      intro J hJ
      change J.toSubmodule ≤ sSup SM
      exact le_sSup ⟨J, hJ, rfl⟩
  obtain ⟨M, hIM, hMax⟩ := zorn_le_nonempty₀ S hzorn I hIS
  refine ⟨M, hIM, hMax.prop.2, ?_⟩
  intro J hMJ hJne
  have hJS : J ∈ S := ⟨le_trans hIM hMJ, hJne⟩
  exact hMax.eq_of_ge hJS hMJ

end AMSpaceWithUnit
