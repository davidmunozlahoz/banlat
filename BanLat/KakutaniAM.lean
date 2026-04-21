import BanLat.AMSpace
import BanLat.Examples.CofK
import BanLat.RieszDec
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Kakutani's representation theorem for AM-spaces with unit

(Bohnenblust–Kakutani–Krein) Every AM-space with unit `(X, e)` is lattice
isometrically isomorphic to `C(K, ℝ)` for the compact Hausdorff space `K` of
*lattice characters* of `X`: the real-valued vector lattice homomorphisms
`X → ℝ` normalised by `φ e = 1`. Under the isomorphism — the Gelfand transform
sending `x` to evaluation `φ ↦ φ x` — the unit `e` corresponds to the constant
function `1`.
-/

namespace AMSpaceWithUnit

variable (X : Type*) [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [AMSpaceWithUnit X]

/-! ### Lattice characters -/

/-- A **lattice character** of an AM-space with unit `(X, e)` is a real-valued
vector lattice homomorphism `X → ℝ` that maps the unit `e` to `1`. -/
structure LatticeCharacter extends VecLatHom X ℝ where
  /-- A lattice character maps the unit to `1`. -/
  map_unit : toVecLatHom (e : X) = 1

namespace LatticeCharacter

variable {X}

/-- The canonical `FunLike` instance, making `LatticeCharacter X` a type of
functions `X → ℝ`. -/
instance instFunLike : FunLike (LatticeCharacter X) X ℝ where
  coe φ := fun x => φ.toVecLatHom x
  coe_injective' := by
    intro φ ψ h
    cases φ; cases ψ
    congr
    exact DFunLike.coe_injective h

@[simp] theorem coe_mk (f : VecLatHom X ℝ) (hf : f (e : X) = 1) (x : X) :
    (mk f hf : X → ℝ) x = f x := rfl

@[simp] theorem map_unit_apply (φ : LatticeCharacter X) :
    φ (e : X) = 1 := φ.map_unit

/-- A lattice character preserves `⊔`. -/
theorem map_sup (φ : LatticeCharacter X) (x y : X) :
    φ (x ⊔ y) = max (φ x) (φ y) :=
  φ.toVecLatHom.toLatticeHom.map_sup' x y

/-- A lattice character preserves `⊓`. -/
theorem map_inf (φ : LatticeCharacter X) (x y : X) :
    φ (x ⊓ y) = min (φ x) (φ y) :=
  φ.toVecLatHom.toLatticeHom.map_inf' x y

/-- A lattice character is monotone. -/
theorem monotone (φ : LatticeCharacter X) : Monotone (φ : X → ℝ) :=
  φ.toVecLatHom.monotone

/-- A lattice character sends positive elements to non-negative reals. -/
theorem nonneg_apply (φ : LatticeCharacter X) {x : X} (hx : 0 ≤ x) : 0 ≤ φ x :=
  φ.toVecLatHom.map_nonneg hx

/-- The fundamental norm bound for a lattice character: `|φ x| ≤ ‖x‖`. This
follows from `|x| ≤ ‖x‖ • e` and the fact that `φ` is a positive linear map
sending `e` to `1`. -/
theorem abs_apply_le_norm (φ : LatticeCharacter X) (x : X) : |φ x| ≤ ‖x‖ := by
  have h1 : |(φ x : ℝ)| = φ.toVecLatHom |x| := (φ.toVecLatHom.map_abs x).symm
  have h2 : φ.toVecLatHom (‖x‖ • e) = ‖x‖ := by
    rw [map_smul, φ.map_unit, smul_eq_mul, mul_one]
  rw [h1, ← h2]
  exact φ.toVecLatHom.monotone (abs_le_norm_smul_unit x)

/-- A lattice character is a continuous functional. -/
theorem continuous (φ : LatticeCharacter X) : Continuous (φ : X → ℝ) := by
  have h : Continuous (φ.toVecLatHom.toLinearMap : X → ℝ) :=
    AddMonoidHomClass.continuous_of_bound φ.toVecLatHom.toLinearMap 1 fun x => by
      rw [Real.norm_eq_abs, one_mul]; exact abs_apply_le_norm φ x
  exact h

variable (X)

/-- The character space is topologised as a subspace of `X → ℝ` with the
product topology. Equivalently, this is the weak* topology inherited from the
norm dual of `X`. -/
instance instTopologicalSpace : TopologicalSpace (LatticeCharacter X) :=
  TopologicalSpace.induced (fun φ : LatticeCharacter X => (φ : X → ℝ))
    Pi.topologicalSpace

/-- For each `x : X`, the evaluation `φ ↦ φ x` is continuous. -/
theorem continuous_eval (x : X) :
    Continuous (fun φ : LatticeCharacter X => φ x) :=
  (continuous_apply x).comp continuous_induced_dom

/-- The character space is Hausdorff. -/
instance instT2Space : T2Space (LatticeCharacter X) :=
  T2Space.of_injective_continuous (f := fun φ : LatticeCharacter X => (φ : X → ℝ))
    DFunLike.coe_injective continuous_induced_dom

/-! ### Maximal ideals and the construction of characters

We follow Troitsky's approach (Lemma 4.1.6): given a maximal proper ideal `M`,
we construct a lattice character by exploiting the disjunction property of `M`
(every element with disjoint positive and negative parts has one of them in
`M`). For each `x : X` we look at the two sets

```
A(x) := { c : ℝ | (c•e − x)⁺ ∈ M },
B(x) := { c : ℝ | (x − c•e)⁺ ∈ M },
```

show `A(x) ∪ B(x) = ℝ` and `A(x) ∩ B(x)` is at most a single point, deduce
`sSup A(x) = sInf B(x)`, and define the character as this common value.
-/

variable {X}

/-- The sum of an order ideal `M` and the principal ideal of `y` is again an
order ideal: any element `b` whose absolute value is bounded by `|m + u|` (with
`m ∈ M`, `u ∈ I_y`) Riesz-decomposes as `b = b_M + b_I` with `b_M ∈ M` and
`b_I ∈ I_y`. -/
private noncomputable def addPrincipal (M : OrderIdeal X) (y : X) : OrderIdeal X :=
  OrderIdeal.ofSolid (M.toSubmodule + (OrderIdeal.principal y).toSubmodule) <| by
    intro a b hab habs
    obtain ⟨m, hm_mem, u, hu_mem, rfl⟩ := Submodule.mem_sup.mp hab
    -- |b| ≤ |m + u| ≤ |m| + |u|
    have habs' : |b| ≤ |m| + |u| := habs.trans (abs_add_le m u)
    have hm_abs_mem : |m| ∈ M := M.abs_mem hm_mem
    have hu_abs_mem : |u| ∈ OrderIdeal.principal y :=
      (OrderIdeal.principal y).abs_mem hu_mem
    have hpos_le : b⁺ ≤ |m| + |u| :=
      sup_le ((le_abs_self b).trans habs') (add_nonneg (abs_nonneg m) (abs_nonneg u))
    have hneg_le : b⁻ ≤ |m| + |u| :=
      sup_le ((neg_le_abs b).trans habs') (add_nonneg (abs_nonneg m) (abs_nonneg u))
    obtain ⟨p₁, p₂, hp₁_nn, hp₁_le, hp₂_nn, hp₂_le, hp_eq⟩ :=
      riesz_decomposition (b⁺) |m| |u| (posPart_nonneg b)
        (abs_nonneg m) (abs_nonneg u) hpos_le
    obtain ⟨n₁, n₂, hn₁_nn, hn₁_le, hn₂_nn, hn₂_le, hn_eq⟩ :=
      riesz_decomposition (b⁻) |m| |u| (negPart_nonneg b)
        (abs_nonneg m) (abs_nonneg u) hneg_le
    have hp₁_M : p₁ ∈ M := M.solid hm_abs_mem hp₁_nn hp₁_le
    have hp₂_I : p₂ ∈ OrderIdeal.principal y :=
      (OrderIdeal.principal y).solid hu_abs_mem hp₂_nn hp₂_le
    have hn₁_M : n₁ ∈ M := M.solid hm_abs_mem hn₁_nn hn₁_le
    have hn₂_I : n₂ ∈ OrderIdeal.principal y :=
      (OrderIdeal.principal y).solid hu_abs_mem hn₂_nn hn₂_le
    have hb_eq : b = (p₁ - n₁) + (p₂ - n₂) := by
      have hp := posPart_sub_negPart b
      rw [hp_eq, hn_eq] at hp
      rw [← hp]; abel
    rw [hb_eq]
    exact Submodule.add_mem _
      (Submodule.sub_mem _ (Submodule.mem_sup_left hp₁_M)
        (Submodule.mem_sup_left hn₁_M))
      (Submodule.sub_mem _ (Submodule.mem_sup_right hp₂_I)
        (Submodule.mem_sup_right hn₂_I))

private theorem addPrincipal_le (M : OrderIdeal X) (y : X) :
    M.toSubmodule ≤ (addPrincipal M y).toSubmodule := by
  intro x hx
  change x ∈ M.toSubmodule + (OrderIdeal.principal y).toSubmodule
  exact Submodule.mem_sup_left hx

private theorem self_mem_addPrincipal (M : OrderIdeal X) (y : X) :
    y ∈ (addPrincipal M y).toSubmodule := by
  change y ∈ M.toSubmodule + (OrderIdeal.principal y).toSubmodule
  exact Submodule.mem_sup_right (OrderIdeal.self_mem_principal y)

/-- **Maximal proper ideals are prime in the disjunction sense**: if `y, z` are
non-negative disjoint elements and `y ∉ M`, then `z ∈ M`. The argument shows
`addPrincipal M y = ⊤` by maximality, hence `e = m + u` with `u ∈ I_y`; Riesz
decomposes `z` as `z = z_M + z_I` with `z_I ⊥ y`, forcing `z_I = 0` and
`z = z_M ∈ M`. -/
private theorem mem_of_disjoint_notMem (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M)
    {y z : X} (hy_nn : 0 ≤ y) (hz_nn : 0 ≤ z) (hdisj : y ⊓ z = 0)
    (hy_notin : y ∉ M) : z ∈ M := by
  have hM_lt : M ≤ addPrincipal M y := addPrincipal_le M y
  have hM_ne_addP : M ≠ addPrincipal M y := by
    intro heq; apply hy_notin; rw [heq]; exact self_mem_addPrincipal M y
  have htop : addPrincipal M y = ⊤ := by
    by_contra hne; exact hM_ne_addP (hmax _ hM_lt hne).symm
  have hz_in : z ∈ (addPrincipal M y).toSubmodule := by
    rw [htop]; exact Submodule.mem_top
  have hz_in' : z ∈ M.toSubmodule + (OrderIdeal.principal y).toSubmodule := hz_in
  obtain ⟨m, hm, u, hu, hzmu⟩ := Submodule.mem_sup.mp hz_in'
  obtain ⟨c, hc, hu_bound⟩ := hu
  have hz_abs : z ≤ |m| + |u| := by
    calc z = m + u := hzmu.symm
      _ ≤ |m| + |u| := add_le_add (le_abs_self m) (le_abs_self u)
  obtain ⟨z₁, z₂, hz₁_nn, hz₁_le_m, hz₂_nn, hz₂_le_u, hz₁₂⟩ :=
    riesz_decomposition z |m| |u| hz_nn (abs_nonneg m) (abs_nonneg u) hz_abs
  have hz₁_M : z₁ ∈ M := M.solid (M.abs_mem hm) hz₁_nn hz₁_le_m
  -- Show z₂ = 0 from disjointness with y
  have hy_z₂ : y ⊓ z₂ = 0 := by
    apply le_antisymm
    · have : z₂ ≤ z := le_trans (le_add_of_nonneg_left hz₁_nn) hz₁₂.symm.le
      calc y ⊓ z₂ ≤ y ⊓ z := inf_le_inf le_rfl this
        _ = 0 := hdisj
    · exact le_inf hy_nn hz₂_nn
  have hz₂_le_cy : z₂ ≤ c • y := by
    have h1 : z₂ ≤ c • |y| := hz₂_le_u.trans hu_bound
    rwa [abs_of_nonneg hy_nn] at h1
  have hz₂_disj_cy : (c • y) ⊓ z₂ = 0 :=
    inf_eq_zero_of_isVLDisjoint (smul_nonneg hc hy_nn) hz₂_nn
      ((isVLDisjoint_of_inf_eq_zero hy_z₂).smul_left c)
  have hz₂_zero : z₂ = 0 := by
    have h := inf_eq_left.mpr hz₂_le_cy
    rw [inf_comm] at hz₂_disj_cy
    rw [hz₂_disj_cy] at h
    exact h.symm
  -- z = z₁ + z₂ = z₁ + 0 = z₁ ∈ M
  rw [hz₁₂, hz₂_zero, add_zero]
  exact hz₁_M

/-- For a proper ideal `M` and `0 < c`, the element `c • e` is not in `M`. -/
private theorem smul_unit_notMem_of_proper (M : OrderIdeal X) (hMne : M ≠ ⊤)
    {c : ℝ} (hc : 0 < c) : c • (e : X) ∉ M := by
  intro h
  apply hMne
  rw [top_iff_unit_mem]
  have heq : (1 / c) • (c • (e : X)) = e := by
    rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  rw [← heq]
  exact M.toSubmodule.smul_mem _ h

/-- For a proper ideal `M` and `c > 0`, no element bounded below by `c • e` lies
in `M`. -/
private theorem nonneg_le_smul_unit_notMem (M : OrderIdeal X) (hMne : M ≠ ⊤)
    {c : ℝ} (hc : 0 < c) {y : X} (hy : c • (e : X) ≤ y) (hyM : y ∈ M) : False := by
  apply smul_unit_notMem_of_proper M hMne hc
  have h_pos : 0 ≤ c • (e : X) := smul_nonneg hc.le unit_pos.le
  exact M.solid hyM h_pos hy

/-- The set `{c | (c•e − x)⁺ ∈ M}` of "lower estimates" of `x` modulo `M`. -/
private def charSetA (M : OrderIdeal X) (x : X) : Set ℝ :=
  {c : ℝ | (c • e - x)⁺ ∈ M}

/-- The set `{c | (x − c•e)⁺ ∈ M}` of "upper estimates" of `x` modulo `M`. -/
private def charSetB (M : OrderIdeal X) (x : X) : Set ℝ :=
  {c : ℝ | (x - c • e)⁺ ∈ M}

private theorem mem_charSetA {M : OrderIdeal X} {x : X} {c : ℝ} :
    c ∈ charSetA M x ↔ (c • e - x)⁺ ∈ M := Iff.rfl

private theorem mem_charSetB {M : OrderIdeal X} {x : X} {c : ℝ} :
    c ∈ charSetB M x ↔ (x - c • e)⁺ ∈ M := Iff.rfl

private theorem neg_norm_smul_unit_le (x : X) : -((‖x‖ : ℝ) • e) ≤ x :=
  neg_le.mp (abs_le'.mp (abs_le_norm_smul_unit x)).2

private theorem le_norm_smul_unit (x : X) : x ≤ (‖x‖ : ℝ) • e :=
  (abs_le'.mp (abs_le_norm_smul_unit x)).1

private theorem neg_norm_mem_charSetA (M : OrderIdeal X) (x : X) :
    -‖x‖ ∈ charSetA M x := by
  rw [mem_charSetA]
  have hle : (-‖x‖ : ℝ) • e - x ≤ 0 := by
    rw [neg_smul, sub_nonpos]
    exact neg_norm_smul_unit_le x
  rw [posPart_eq_zero.mpr hle]
  exact M.toSubmodule.zero_mem

private theorem norm_mem_charSetB (M : OrderIdeal X) (x : X) :
    ‖x‖ ∈ charSetB M x := by
  rw [mem_charSetB]
  have hle : x - (‖x‖ : ℝ) • e ≤ 0 := sub_nonpos.mpr (le_norm_smul_unit x)
  rw [posPart_eq_zero.mpr hle]
  exact M.toSubmodule.zero_mem

private theorem charSetA_nonempty (M : OrderIdeal X) (x : X) :
    (charSetA M x).Nonempty := ⟨-‖x‖, neg_norm_mem_charSetA M x⟩

private theorem charSetB_nonempty (M : OrderIdeal X) (x : X) :
    (charSetB M x).Nonempty := ⟨‖x‖, norm_mem_charSetB M x⟩

private theorem charSetA_downwardClosed (M : OrderIdeal X) (x : X)
    {c d : ℝ} (hc : c ∈ charSetA M x) (hdc : d ≤ c) : d ∈ charSetA M x := by
  rw [mem_charSetA] at hc ⊢
  apply M.solid hc (posPart_nonneg _)
  apply sup_le_sup_right
  exact sub_le_sub_right
    (smul_le_smul_of_nonneg_right hdc unit_pos.le) _

private theorem charSetB_upwardClosed (M : OrderIdeal X) (x : X)
    {c d : ℝ} (hc : c ∈ charSetB M x) (hcd : c ≤ d) : d ∈ charSetB M x := by
  rw [mem_charSetB] at hc ⊢
  apply M.solid hc (posPart_nonneg _)
  apply sup_le_sup_right
  exact sub_le_sub_left
    (smul_le_smul_of_nonneg_right hcd unit_pos.le) _

private theorem charSetA_bddAbove (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    BddAbove (charSetA M x) := by
  refine ⟨‖x‖, fun c hc => ?_⟩
  by_contra hlt; push_neg at hlt
  have hxle := le_norm_smul_unit x
  have h1 : (c - ‖x‖) • (e : X) ≤ c • e - x := by
    rw [sub_smul]; exact sub_le_sub_left hxle (c • e)
  have hpos : 0 < c - ‖x‖ := sub_pos.mpr hlt
  have h2 : (c - ‖x‖) • (e : X) ≤ (c • e - x)⁺ :=
    h1.trans (le_posPart _)
  exact nonneg_le_smul_unit_notMem M hMne hpos h2 hc

private theorem charSetB_bddBelow (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    BddBelow (charSetB M x) := by
  refine ⟨-‖x‖, fun c hc => ?_⟩
  by_contra hlt; push_neg at hlt
  have hxle := neg_norm_smul_unit_le x
  have h1 : (-‖x‖ - c) • (e : X) ≤ x - c • e := by
    rw [sub_smul, neg_smul]
    have : -(‖x‖ • (e : X)) - c • e ≤ x - c • e := sub_le_sub_right hxle (c • e)
    exact this
  have hpos : 0 < -‖x‖ - c := by linarith
  have h2 : (-‖x‖ - c) • (e : X) ≤ (x - c • e)⁺ :=
    h1.trans (le_posPart _)
  exact nonneg_le_smul_unit_notMem M hMne hpos h2 hc

/-- The "key step": for a maximal proper ideal `M`, every real `c` lies in
either `charSetA M x` or `charSetB M x`, by the prime property of `M`. -/
private theorem charSetA_union_charSetB (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M)
    (x : X) (c : ℝ) :
    c ∈ charSetA M x ∨ c ∈ charSetB M x := by
  set y := (c • (e : X) - x)⁺ with hy_def
  set z := (x - c • (e : X))⁺ with hz_def
  have hyz : y ⊓ z = 0 := by
    have heq : (x - c • (e : X))⁺ = (c • e - x)⁻ := by
      rw [show (x - c • (e : X)) = -(c • e - x) from by abel,
        show ((-(c • (e : X) - x))⁺ : X) = (c • e - x)⁻ from rfl]
    rw [hy_def, hz_def, heq]
    exact posPart_inf_negPart_eq_zero _
  have hy_nn : 0 ≤ y := posPart_nonneg _
  have hz_nn : 0 ≤ z := posPart_nonneg _
  by_cases hy : y ∈ M
  · left; exact hy
  · right
    rw [mem_charSetB]
    exact mem_of_disjoint_notMem M hmax hy_nn hz_nn hyz hy

/-- For maximal proper `M`, both `c, d` in `A(x) ∩ B(x)` would force `(c-d)•e ∈ M`
and so `c = d`. -/
private theorem charSetA_charSetB_unique (M : OrderIdeal X) (hMne : M ≠ ⊤)
    (x : X) {c : ℝ} (hcA : c ∈ charSetA M x) (hcB : c ∈ charSetB M x)
    {d : ℝ} (hdA : d ∈ charSetA M x) (hdB : d ∈ charSetB M x) : c = d := by
  -- From hcA and hcB: c•e - x ∈ M (since both positive and negative parts in M).
  rw [mem_charSetA] at hcA hdA
  rw [mem_charSetB] at hcB hdB
  have hc_neg_in : (c • (e : X) - x)⁻ ∈ M := by
    have h : (c • (e : X) - x)⁻ = (x - c • e)⁺ := by
      rw [show x - c • (e : X) = -(c • e - x) from by abel,
        show ((-(c • (e : X) - x))⁺ : X) = (c • e - x)⁻ from rfl]
    rw [h]; exact hcB
  have hd_neg_in : (d • (e : X) - x)⁻ ∈ M := by
    have h : (d • (e : X) - x)⁻ = (x - d • e)⁺ := by
      rw [show x - d • (e : X) = -(d • e - x) from by abel,
        show ((-(d • (e : X) - x))⁺ : X) = (d • e - x)⁻ from rfl]
    rw [h]; exact hdB
  have hc_in : c • (e : X) - x ∈ M := by
    have h := M.toSubmodule.sub_mem hcA hc_neg_in
    rwa [posPart_sub_negPart] at h
  have hd_in : d • (e : X) - x ∈ M := by
    have h := M.toSubmodule.sub_mem hdA hd_neg_in
    rwa [posPart_sub_negPart] at h
  -- (c - d)•e = (c•e - x) - (d•e - x) ∈ M
  have hcd_in : (c - d) • (e : X) ∈ M := by
    have h := M.toSubmodule.sub_mem hc_in hd_in
    have heq : (c • (e : X) - x) - (d • e - x) = (c - d) • e := by
      rw [sub_smul]; abel
    rwa [heq] at h
  -- If c ≠ d, then |c - d| > 0 and |c - d|•e ∈ M, contradicting M proper
  by_contra hne
  have hne' : c - d ≠ 0 := sub_ne_zero.mpr hne
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · -- c - d < 0, so -(c - d) > 0 and -(c-d)•e = -((c-d)•e) ∈ M
    have h_neg : -((c - d) • (e : X)) ∈ M := M.toSubmodule.neg_mem hcd_in
    rw [← neg_smul] at h_neg
    exact smul_unit_notMem_of_proper M hMne (neg_pos.mpr hlt) h_neg
  · exact smul_unit_notMem_of_proper M hMne hgt hcd_in

/-- All elements of `A(x)` are ≤ all elements of `B(x)`. -/
private theorem charSetA_le_charSetB (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X)
    {a : ℝ} (ha : a ∈ charSetA M x) {b : ℝ} (hb : b ∈ charSetB M x) : a ≤ b := by
  by_contra hlt; push_neg at hlt
  -- b < a; by closures, b ∈ A (downward from a ∈ A) and a ∈ B (upward from b ∈ B)
  have hbA : b ∈ charSetA M x := charSetA_downwardClosed M x ha hlt.le
  have haB : a ∈ charSetB M x := charSetB_upwardClosed M x hb hlt.le
  -- So a, b are both in A ∩ B. By uniqueness, a = b. Contradicts b < a.
  exact absurd (charSetA_charSetB_unique M hMne x hbA hb ha haB) (ne_of_gt hlt).symm

/-- The "inf B" is bounded above by "sup A" (using `A ∪ B = ℝ`). -/
private theorem inf_charSetB_le_sup_charSetA (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    sInf (charSetB M x) ≤ sSup (charSetA M x) := by
  by_contra hgt; push_neg at hgt
  obtain ⟨c, hc1, hc2⟩ := exists_between hgt
  -- hc1 : sSup A < c, hc2 : c < sInf B
  have hcA : c ∉ charSetA M x := fun h => not_lt.mpr
    (le_csSup (charSetA_bddAbove M hMne x) h) hc1
  have hcB : c ∉ charSetB M x := fun h => not_lt.mpr
    (csInf_le (charSetB_bddBelow M hMne x) h) hc2
  rcases charSetA_union_charSetB M hmax x c with h | h
  · exact hcA h
  · exact hcB h

/-- For maximal proper `M`, `sSup A(x) = sInf B(x)`. -/
private theorem sup_charSetA_eq_inf_charSetB (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    sSup (charSetA M x) = sInf (charSetB M x) := by
  apply le_antisymm
  · apply csSup_le (charSetA_nonempty M x)
    intro a ha
    apply le_csInf (charSetB_nonempty M x)
    intro b hb
    exact charSetA_le_charSetB M hMne x ha hb
  · exact inf_charSetB_le_sup_charSetA M hmax hMne x

/-- The character value at `x` modulo a maximal proper ideal `M`. -/
private noncomputable def charValue (M : OrderIdeal X) (x : X) : ℝ :=
  sSup (charSetA M x)

private theorem charValue_eq_inf_charSetB (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    charValue M x = sInf (charSetB M x) :=
  sup_charSetA_eq_inf_charSetB M hmax hMne x

private theorem norm_isUB_charSetA (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    ∀ c ∈ charSetA M x, c ≤ ‖x‖ := by
  intro c hc
  by_contra hlt; push_neg at hlt
  have hxle := le_norm_smul_unit x
  have h1 : (c - ‖x‖) • (e : X) ≤ c • e - x := by
    rw [sub_smul]; exact sub_le_sub_left hxle (c • e)
  have hpos : 0 < c - ‖x‖ := sub_pos.mpr hlt
  have h2 : (c - ‖x‖) • (e : X) ≤ (c • e - x)⁺ :=
    h1.trans (le_posPart _)
  exact nonneg_le_smul_unit_notMem M hMne hpos h2 hc

private theorem charValue_le_norm (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    charValue M x ≤ ‖x‖ :=
  csSup_le (charSetA_nonempty M x) (norm_isUB_charSetA M hMne x)

private theorem neg_norm_le_charValue (M : OrderIdeal X) (hMne : M ≠ ⊤) (x : X) :
    -‖x‖ ≤ charValue M x := by
  apply le_csSup (charSetA_bddAbove M hMne x)
  exact neg_norm_mem_charSetA M x

/-- The character value sends `0` to `0`. -/
private theorem charValue_zero (M : OrderIdeal X) (hmax : ∀ J : OrderIdeal X,
    M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    charValue M (0 : X) = 0 := by
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne]
    apply csInf_le (charSetB_bddBelow M hMne 0)
    rw [mem_charSetB]
    have : (0 - (0 : ℝ) • (e : X))⁺ = 0 := by
      rw [zero_smul, sub_zero, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem
  · apply le_csSup (charSetA_bddAbove M hMne 0)
    rw [mem_charSetA]
    have : ((0 : ℝ) • (e : X) - 0)⁺ = 0 := by
      rw [zero_smul, sub_zero, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem

/-- The character value sends `e` to `1`. -/
private theorem charValue_unit (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    charValue M (e : X) = 1 := by
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne]
    apply csInf_le (charSetB_bddBelow M hMne e)
    rw [mem_charSetB]
    have : ((e : X) - (1 : ℝ) • e)⁺ = 0 := by
      rw [one_smul, sub_self, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem
  · apply le_csSup (charSetA_bddAbove M hMne e)
    rw [mem_charSetA]
    have : ((1 : ℝ) • (e : X) - e)⁺ = 0 := by
      rw [one_smul, sub_self, posPart_eq_zero.mpr le_rfl]
    rw [this]
    exact M.toSubmodule.zero_mem

/-- Additivity of character value (forward direction via `A`). -/
private theorem charValue_add_le_aux (M : OrderIdeal X) (x y : X)
    {c₁ : ℝ} (hc₁ : c₁ ∈ charSetA M x) {c₂ : ℝ} (hc₂ : c₂ ∈ charSetA M y) :
    c₁ + c₂ ∈ charSetA M (x + y) := by
  rw [mem_charSetA] at hc₁ hc₂ ⊢
  -- ((c₁ + c₂)•e - (x+y))⁺ ≤ (c₁•e - x)⁺ + (c₂•e - y)⁺ ∈ M
  have h1 : ((c₁ + c₂) • (e : X) - (x + y))⁺ ≤ (c₁ • e - x)⁺ + (c₂ • e - y)⁺ := by
    have hsum : (c₁ + c₂) • (e : X) - (x + y) = (c₁ • e - x) + (c₂ • e - y) := by
      rw [add_smul]; abel
    rw [hsum]
    exact posPart_add_le _ _
  exact M.solid (M.toSubmodule.add_mem hc₁ hc₂) (posPart_nonneg _) h1

/-- Additivity for `B`-sets. -/
private theorem charValue_add_le_aux' (M : OrderIdeal X) (x y : X)
    {c₁ : ℝ} (hc₁ : c₁ ∈ charSetB M x) {c₂ : ℝ} (hc₂ : c₂ ∈ charSetB M y) :
    c₁ + c₂ ∈ charSetB M (x + y) := by
  rw [mem_charSetB] at hc₁ hc₂ ⊢
  have h1 : ((x + y) - (c₁ + c₂) • (e : X))⁺ ≤ (x - c₁ • e)⁺ + (y - c₂ • e)⁺ := by
    have hsum : (x + y) - (c₁ + c₂) • (e : X) = (x - c₁ • e) + (y - c₂ • e) := by
      rw [add_smul]; abel
    rw [hsum]
    exact posPart_add_le _ _
  exact M.solid (M.toSubmodule.add_mem hc₁ hc₂) (posPart_nonneg _) h1

section CharValueOps

open scoped Pointwise

private theorem charSetA_add_subset (M : OrderIdeal X) (x y : X) :
    (charSetA M x + charSetA M y : Set ℝ) ⊆ charSetA M (x + y) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact charValue_add_le_aux M x y ha hb

private theorem charSetB_add_subset (M : OrderIdeal X) (x y : X) :
    (charSetB M x + charSetB M y : Set ℝ) ⊆ charSetB M (x + y) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact charValue_add_le_aux' M x y ha hb

/-- The character value is additive. -/
private theorem charValue_add (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x y : X) :
    charValue M (x + y) = charValue M x + charValue M y := by
  apply le_antisymm
  · -- ≤ via B-side
    rw [charValue_eq_inf_charSetB M hmax hMne x, charValue_eq_inf_charSetB M hmax hMne y,
      charValue_eq_inf_charSetB M hmax hMne (x + y)]
    have hsub : (charSetB M x + charSetB M y : Set ℝ) ⊆ charSetB M (x + y) :=
      charSetB_add_subset M x y
    have hinf_sum : sInf (charSetB M x + charSetB M y) =
        sInf (charSetB M x) + sInf (charSetB M y) :=
      csInf_add (charSetB_nonempty M x) (charSetB_bddBelow M hMne x)
        (charSetB_nonempty M y) (charSetB_bddBelow M hMne y)
    rw [← hinf_sum]
    apply csInf_le_csInf (charSetB_bddBelow M hMne (x + y))
      ((charSetB_nonempty M x).add (charSetB_nonempty M y))
    exact hsub
  · -- ≥ via A-side
    have hsub : (charSetA M x + charSetA M y : Set ℝ) ⊆ charSetA M (x + y) :=
      charSetA_add_subset M x y
    have hsup_sum : sSup (charSetA M x + charSetA M y) =
        sSup (charSetA M x) + sSup (charSetA M y) :=
      csSup_add (charSetA_nonempty M x) (charSetA_bddAbove M hMne x)
        (charSetA_nonempty M y) (charSetA_bddAbove M hMne y)
    change charValue M x + charValue M y ≤ charValue M (x + y)
    unfold charValue
    rw [← hsup_sum]
    apply csSup_le_csSup (charSetA_bddAbove M hMne (x + y))
      ((charSetA_nonempty M x).add (charSetA_nonempty M y))
    exact hsub

private theorem charSetA_neg_eq (M : OrderIdeal X) (x : X) :
    charSetA M (-x) = -charSetB M x := by
  ext c
  simp only [charSetA, charSetB, Set.mem_setOf_eq, Set.mem_neg]
  constructor
  · intro hc
    have : (c • (e : X) - -x) = (x - (-c) • e) := by rw [neg_smul]; abel
    rw [this] at hc
    exact hc
  · intro hc
    have : (x - (-c) • (e : X)) = (c • e - -x) := by rw [neg_smul]; abel
    rw [this] at hc
    exact hc

private theorem charValue_neg (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) (x : X) :
    charValue M (-x) = -charValue M x := by
  unfold charValue
  rw [charSetA_neg_eq M x]
  rw [csSup_neg (charSetB_nonempty M x) (charSetB_bddBelow M hMne x)]
  rw [← sup_charSetA_eq_inf_charSetB M hmax hMne x]

/-- For `c > 0`, `charSetA M (c • x) = c • charSetA M x`. -/
private theorem charSetA_smul_pos (M : OrderIdeal X) {c : ℝ} (hc : 0 < c) (x : X) :
    charSetA M (c • x) = c • charSetA M x := by
  ext d
  simp only [charSetA, Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · intro hd
    refine ⟨d / c, ?_, ?_⟩
    · have h1 : c • ((d / c) • (e : X) - x) = d • e - c • x := by
        rw [smul_sub, smul_smul, mul_div_cancel₀ _ (ne_of_gt hc)]
      have h2 : (c • ((d / c) • (e : X) - x))⁺ ∈ M := by
        rw [h1]; exact hd
      have h3 : c • ((d / c) • (e : X) - x)⁺ = (c • ((d / c) • (e : X) - x))⁺ := by
        rw [posPart_def, posPart_def, nonneg_smul_sup, smul_zero]
        exact hc.le
      rw [← h3] at h2
      have h4 : (c⁻¹ : ℝ) • c • ((d / c) • (e : X) - x)⁺ ∈ M :=
        M.toSubmodule.smul_mem _ h2
      rwa [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] at h4
    · rw [smul_eq_mul]; field_simp
  · rintro ⟨d', hd', rfl⟩
    show ((c • d') • (e : X) - c • x)⁺ ∈ M
    have h1 : (c • d') • (e : X) - c • x = c • (d' • e - x) := by
      rw [smul_sub, smul_eq_mul, mul_smul]
    rw [h1]
    have h2 : (c • (d' • (e : X) - x))⁺ = c • (d' • e - x)⁺ := by
      rw [posPart_def, posPart_def, nonneg_smul_sup, smul_zero]
      exact hc.le
    rw [h2]
    exact M.toSubmodule.smul_mem _ hd'

private theorem charValue_smul_pos (M : OrderIdeal X) {c : ℝ} (hc : 0 < c) (x : X) :
    charValue M (c • x) = c * charValue M x := by
  unfold charValue
  rw [charSetA_smul_pos M hc x, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]

private theorem charValue_smul (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤)
    (c : ℝ) (x : X) :
    charValue M (c • x) = c * charValue M x := by
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  · rw [show (c • x : X) = -((-c) • x) from by rw [neg_smul, neg_neg]]
    rw [charValue_neg M hmax hMne, charValue_smul_pos M (neg_pos.mpr hlt)]
    ring
  · subst heq; simp [charValue_zero M hmax hMne]
  · exact charValue_smul_pos M hgt x

/-- For `B`-sets, supremum-preservation: `B(x ⊔ y) = B(x) ∩ B(y)`. -/
private theorem charSetB_sup_eq (M : OrderIdeal X) (x y : X) :
    charSetB M (x ⊔ y) = charSetB M x ∩ charSetB M y := by
  ext c
  simp only [mem_charSetB, Set.mem_inter_iff]
  constructor
  · intro h
    have h1 : (x - c • (e : X))⁺ ≤ (x ⊔ y - c • e)⁺ := by
      apply sup_le_sup_right
      exact sub_le_sub_right le_sup_left _
    have h2 : (y - c • (e : X))⁺ ≤ (x ⊔ y - c • e)⁺ := by
      apply sup_le_sup_right
      exact sub_le_sub_right le_sup_right _
    exact ⟨M.solid h (posPart_nonneg _) h1, M.solid h (posPart_nonneg _) h2⟩
  · rintro ⟨hx, hy⟩
    have h1 : x ⊔ y - c • (e : X) = (x - c • e) ⊔ (y - c • e) := by
      rw [sub_eq_add_neg, sup_add]; simp [sub_eq_add_neg]
    rw [h1, posPart_max]
    exact M.sup_mem hx hy

/-- For `A`-sets, infimum-preservation: `A(x ⊓ y) = A(x) ∩ A(y)`. -/
private theorem charSetA_inf_eq (M : OrderIdeal X) (x y : X) :
    charSetA M (x ⊓ y) = charSetA M x ∩ charSetA M y := by
  ext c
  simp only [mem_charSetA, Set.mem_inter_iff]
  constructor
  · intro h
    have h1 : (c • (e : X) - x)⁺ ≤ (c • e - x ⊓ y)⁺ := by
      apply sup_le_sup_right
      exact sub_le_sub_left inf_le_left _
    have h2 : (c • (e : X) - y)⁺ ≤ (c • e - x ⊓ y)⁺ := by
      apply sup_le_sup_right
      exact sub_le_sub_left inf_le_right _
    exact ⟨M.solid h (posPart_nonneg _) h1, M.solid h (posPart_nonneg _) h2⟩
  · rintro ⟨hx, hy⟩
    have h1 : c • (e : X) - x ⊓ y = (c • e - x) ⊔ (c • e - y) := by
      rw [show c • (e : X) - x ⊓ y = c • e + (-(x ⊓ y)) from by abel,
          neg_inf, add_sup, ← sub_eq_add_neg, ← sub_eq_add_neg]
    rw [h1, posPart_max]
    exact M.sup_mem hx hy

/-- The character value is non-negative on positive elements. -/
private theorem charValue_nonneg (M : OrderIdeal X) (hMne : M ≠ ⊤) {x : X}
    (hx : 0 ≤ x) : 0 ≤ charValue M x := by
  apply le_csSup (charSetA_bddAbove M hMne x)
  rw [mem_charSetA]
  have h : (0 : X) = ((0 : ℝ) • e - x)⁺ := by
    rw [zero_smul, zero_sub, posPart_def, ← negPart_def]
    exact (negPart_eq_zero.mpr hx).symm
  rw [← h]
  exact M.toSubmodule.zero_mem

/-- An element in `M` has character value zero. -/
private theorem charValue_eq_zero_of_mem (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤)
    {x : X} (hx : x ∈ M) : charValue M x = 0 := by
  have hposPart : x⁺ ∈ M := by
    rw [posPart_def]; exact M.sup_mem hx M.toSubmodule.zero_mem
  have hnegPart : x⁻ ∈ M := by
    rw [negPart_def]
    exact M.sup_mem (M.toSubmodule.neg_mem hx) M.toSubmodule.zero_mem
  apply le_antisymm
  · rw [charValue_eq_inf_charSetB M hmax hMne]
    apply csInf_le (charSetB_bddBelow M hMne x)
    rw [mem_charSetB, zero_smul, sub_zero]
    exact hposPart
  · apply le_csSup (charSetA_bddAbove M hMne x)
    rw [mem_charSetA, zero_smul, zero_sub]
    have h : (-x)⁺ = x⁻ := by rw [posPart_def, ← negPart_def]
    rw [h]
    exact hnegPart

/-- For `0 ≤ x`, the character value is zero iff `x ∈ M`.

We only need one direction here. -/
private theorem charValue_disjoint (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤)
    {x y : X} (hxy : x ⊓ y = 0) :
    charValue M x ⊓ charValue M y = 0 := by
  have hx_nn : 0 ≤ x := by rw [← hxy]; exact inf_le_left
  have hy_nn : 0 ≤ y := by rw [← hxy]; exact inf_le_right
  have hx_in_or_y_in : x ∈ M ∨ y ∈ M := by
    by_cases hx : x ∈ M
    · left; exact hx
    · right; exact mem_of_disjoint_notMem M hmax hx_nn hy_nn hxy hx
  rcases hx_in_or_y_in with hx | hy
  · rw [charValue_eq_zero_of_mem M hmax hMne hx]
    exact min_eq_left (charValue_nonneg M hMne hy_nn)
  · rw [charValue_eq_zero_of_mem M hmax hMne hy]
    exact min_eq_right (charValue_nonneg M hMne hx_nn)

end CharValueOps

/-- The vector lattice homomorphism `X → ℝ` arising from a maximal proper ideal. -/
private noncomputable def vecLatHomOfMaximal (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    VecLatHom X ℝ :=
  IsVecLatHom.mk' (charValue M)
    (IsVecLatHom.of_disjoint
      ⟨charValue_add M hmax hMne, fun c x => by
        rw [charValue_smul M hmax hMne]; rfl⟩
      (fun _ hx => charValue_nonneg M hMne hx)
      (fun _ _ hxy => charValue_disjoint M hmax hMne hxy))

/-- The lattice character arising from a maximal proper ideal. -/
private noncomputable def characterOfMaximal (M : OrderIdeal X)
    (hmax : ∀ J : OrderIdeal X, M ≤ J → J ≠ ⊤ → J = M) (hMne : M ≠ ⊤) :
    LatticeCharacter X where
  toVecLatHom := vecLatHomOfMaximal M hmax hMne
  map_unit := charValue_unit M hmax hMne

variable (X)

instance instNonempty : Nonempty (LatticeCharacter X) := by
  -- Apply exists_le_maximal to the zero ideal (which is proper since e ≠ 0).
  classical
  let zeroIdeal : OrderIdeal X := OrderIdeal.ofSolid ⊥ <| by
    intro x y hx hxy
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, abs_zero] at hxy
    exact (abs_eq_zero_iff_zero y).mp (le_antisymm hxy (abs_nonneg y))
  have hZero_ne : zeroIdeal ≠ ⊤ := by
    rw [ne_eq, top_iff_unit_mem]
    change (e : X) ∉ (⊥ : Submodule ℝ X)
    rw [Submodule.mem_bot]
    intro h
    have hpos : (0 : X) < AMSpaceWithUnit.unit := unit_pos
    have heq : AMSpaceWithUnit.unit = (0 : X) := h
    rw [heq] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨M, _, hMne, hMmax⟩ := exists_le_maximal zeroIdeal hZero_ne
  exact ⟨characterOfMaximal M hMmax hMne⟩

private theorem range_coe_eq_inter :
    Set.range (fun φ : LatticeCharacter X => (φ : X → ℝ)) =
    (⋂ p : X × X, {g : X → ℝ | g (p.1 + p.2) = g p.1 + g p.2}) ∩
    (⋂ p : ℝ × X, {g : X → ℝ | g (p.1 • p.2) = p.1 * g p.2}) ∩
    (⋂ p : X × X, {g : X → ℝ | g (p.1 ⊔ p.2) = max (g p.1) (g p.2)}) ∩
    (⋂ p : X × X, {g : X → ℝ | g (p.1 ⊓ p.2) = min (g p.1) (g p.2)}) ∩
    {g : X → ℝ | g e = 1} := by
  ext g
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
    Prod.forall]
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact fun x y => map_add φ.toVecLatHom x y
    · exact fun c x => map_smul φ.toVecLatHom c x
    · exact LatticeCharacter.map_sup φ
    · exact LatticeCharacter.map_inf φ
    · exact φ.map_unit
  · rintro ⟨⟨⟨⟨hadd, hsmul⟩, hsup⟩, hinf⟩, hunit⟩
    refine ⟨⟨⟨⟨⟨g, hadd⟩, hsmul⟩, hsup, hinf⟩, hunit⟩, rfl⟩

instance instCompactSpace : CompactSpace (LatticeCharacter X) := by
  let ι : LatticeCharacter X → (X → ℝ) := fun φ x => φ x
  have hι : Topology.IsInducing ι := ⟨rfl⟩
  refine ⟨?_⟩
  rw [Topology.IsInducing.isCompact_iff hι, Set.image_univ]
  set K : Set (X → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-‖x‖) ‖x‖) with hK_def
  have hK_compact : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hrange_sub : Set.range ι ⊆ K := by
    rintro g ⟨φ, rfl⟩ x _
    simp only [Set.mem_Icc]
    exact abs_le.mp (φ.abs_apply_le_norm x)
  have hrange_closed : IsClosed (Set.range ι) := by
    have heq : (Set.range ι) =
        Set.range (fun φ : LatticeCharacter X => (φ : X → ℝ)) := rfl
    rw [heq, range_coe_eq_inter]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 + p.2))
        ((continuous_apply p.1).add (continuous_apply p.2))
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 • p.2))
        (continuous_const.mul (continuous_apply p.2))
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 ⊔ p.2))
        ((continuous_apply p.1).max (continuous_apply p.2))
    · exact isClosed_iInter fun p => isClosed_eq (continuous_apply (p.1 ⊓ p.2))
        ((continuous_apply p.1).min (continuous_apply p.2))
    · exact isClosed_eq (continuous_apply e) continuous_const
  exact hK_compact.of_isClosed_subset hrange_closed hrange_sub

end LatticeCharacter

/-! ### The Gelfand transform -/

variable {X}

/-- The **Gelfand transform** sends an element `x : X` to the continuous
function `φ ↦ φ x` on the character space. -/
noncomputable def gelfand (x : X) : C(LatticeCharacter X, ℝ) where
  toFun φ := φ x
  continuous_toFun := LatticeCharacter.continuous_eval X x

@[simp] theorem gelfand_apply (x : X) (φ : LatticeCharacter X) :
    gelfand x φ = φ x := rfl

@[simp] theorem gelfand_unit : gelfand (e : X) = 1 := by
  ext φ
  exact φ.map_unit

/-- The Gelfand transform is a vector lattice homomorphism. -/
theorem gelfand_isVecLatHom :
    IsVecLatHom (gelfand : X → C(LatticeCharacter X, ℝ)) where
  map_add x y := by ext φ; exact map_add φ.toVecLatHom x y
  map_smul r x := by ext φ; exact map_smul φ.toVecLatHom r x
  map_sup' x y := by
    ext φ
    change φ (x ⊔ y) = max (φ x) (φ y)
    exact LatticeCharacter.map_sup φ x y
  map_inf' x y := by
    ext φ
    change φ (x ⊓ y) = min (φ x) (φ y)
    exact LatticeCharacter.map_inf φ x y

/-- **Key witness lemma** (Troitsky 4.1.6): For `0 ≤ x` with `(x − e)⁺ ≠ 0`,
there exists a lattice character `φ` with `1 ≤ φ x`. -/
private theorem exists_lattice_character_ge_one_of_pos_part_ne_zero
    {x : X} (_ : 0 ≤ x) (hx_ne : (x - e)⁺ ≠ 0) :
    ∃ φ : LatticeCharacter X, 1 ≤ φ x := by
  -- Step 1: I_{(x-e)⁻} is proper.
  have hPnet : OrderIdeal.principal ((x - e)⁻) ≠ ⊤ := by
    rw [ne_eq, AMSpaceWithUnit.top_iff_unit_mem]
    intro he_in
    rw [OrderIdeal.mem_principal] at he_in
    obtain ⟨c, hc_nn, hc_le⟩ := he_in
    rw [show |(e : X)| = e from abs_of_nonneg unit_pos.le,
        abs_of_nonneg (negPart_nonneg _)] at hc_le
    rcases eq_or_lt_of_le hc_nn with h_zero | h_pos
    · -- c = 0: e ≤ 0, contradiction
      rw [← h_zero, zero_smul] at hc_le
      exact lt_irrefl _ (lt_of_lt_of_le unit_pos hc_le)
    · -- c > 0
      have hdisj : (x - e)⁺ ⊓ (x - e)⁻ = 0 := posPart_inf_negPart_eq_zero _
      have hdisj_smul : (x - e)⁺ ⊓ c • (x - e)⁻ = 0 :=
        inf_eq_zero_of_isVLDisjoint (posPart_nonneg _)
          (smul_nonneg hc_nn (negPart_nonneg _))
          ((isVLDisjoint_of_inf_eq_zero hdisj).smul_right c)
      have h_pos_disj_e : (x - e)⁺ ⊓ e = 0 := by
        apply le_antisymm _ (le_inf (posPart_nonneg _) unit_pos.le)
        calc (x - e)⁺ ⊓ e ≤ (x - e)⁺ ⊓ (c • (x - e)⁻) :=
              inf_le_inf le_rfl hc_le
          _ = 0 := hdisj_smul
      have h_pos_le : (x - e)⁺ ≤ ‖(x - e)⁺‖ • e :=
        (abs_le'.mp (abs_le_norm_smul_unit (x - e)⁺)).1
      have h_pos_disj_smul_e : (x - e)⁺ ⊓ (‖(x - e)⁺‖ • e) = 0 :=
        inf_eq_zero_of_isVLDisjoint (posPart_nonneg _)
          (smul_nonneg (norm_nonneg _) unit_pos.le)
          ((isVLDisjoint_of_inf_eq_zero h_pos_disj_e).smul_right _)
      have h_pos_eq : (x - e)⁺ = (x - e)⁺ ⊓ (‖(x - e)⁺‖ • e) := by
        rw [inf_eq_left.mpr h_pos_le]
      rw [h_pos_disj_smul_e] at h_pos_eq
      exact hx_ne h_pos_eq
  -- Step 2: Get a maximal ideal containing I_{(x-e)⁻}.
  obtain ⟨M, hPle, hMne, hMmax⟩ := exists_le_maximal _ hPnet
  have hneg_in : (x - e)⁻ ∈ M := hPle (OrderIdeal.self_mem_principal _)
  -- Step 3: Build character.
  let φ := LatticeCharacter.characterOfMaximal M hMmax hMne
  refine ⟨φ, ?_⟩
  have hφ_apply : ∀ y : X, φ y = LatticeCharacter.charValue M y := fun _ => rfl
  rw [hφ_apply x]
  -- Step 4: charValue M x ≥ 1
  have hφ_neg : LatticeCharacter.charValue M ((x - e)⁻) = 0 :=
    LatticeCharacter.charValue_eq_zero_of_mem M hMmax hMne hneg_in
  have hφ_pos_nn : 0 ≤ LatticeCharacter.charValue M ((x - e)⁺) :=
    LatticeCharacter.charValue_nonneg M hMne (posPart_nonneg _)
  have hφ_e : LatticeCharacter.charValue M (e : X) = 1 :=
    LatticeCharacter.charValue_unit M hMmax hMne
  have hφ_lin : LatticeCharacter.charValue M (x - e) =
      LatticeCharacter.charValue M x - LatticeCharacter.charValue M e := by
    rw [show (x - e : X) = x + (-e) from sub_eq_add_neg x e,
      LatticeCharacter.charValue_add M hMmax hMne]
    rw [show (-e : X) = (-1 : ℝ) • e from by rw [neg_smul, one_smul],
      LatticeCharacter.charValue_smul M hMmax hMne]
    ring
  have h_decomp : x - e = (x - e)⁺ - (x - e)⁻ := (posPart_sub_negPart (x - e)).symm
  have hφ_decomp : LatticeCharacter.charValue M (x - e) =
      LatticeCharacter.charValue M ((x - e)⁺) - LatticeCharacter.charValue M ((x - e)⁻) := by
    conv_lhs => rw [h_decomp, show ((x - e)⁺ - (x - e)⁻ : X) = (x - e)⁺ + (-((x - e)⁻)) from
      sub_eq_add_neg _ _]
    rw [LatticeCharacter.charValue_add M hMmax hMne,
      show (-(x - e)⁻ : X) = (-1 : ℝ) • (x - e)⁻ from by rw [neg_smul, one_smul],
      LatticeCharacter.charValue_smul M hMmax hMne]
    ring
  rw [hφ_lin] at hφ_decomp
  rw [hφ_e] at hφ_decomp
  rw [hφ_neg] at hφ_decomp
  linarith

/-- The norm can be characterized using lattice characters. -/
private theorem attains_norm_at_characters (x : X) :
    ‖x‖ = sSup { |φ x| | φ : LatticeCharacter X } := by
  set S : Set ℝ := { |φ x| | φ : LatticeCharacter X } with hS_def
  have hS_ne : S.Nonempty := by
    have ⟨φ⟩ := @LatticeCharacter.instNonempty X _ _ _ _
    exact ⟨|φ x|, φ, rfl⟩
  have hS_bdd : BddAbove S := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact φ.abs_apply_le_norm x
  -- Helper: for any 0 < t < ‖x‖, there's a character with t ≤ |φ x|.
  have hwit : ∀ t : ℝ, 0 < t → t < ‖x‖ → ∃ φ : LatticeCharacter X, t ≤ |φ x| := by
    intro t ht_pos ht_lt
    -- Apply witness to (1/t) • |x|
    have hyabs_nn : (0 : X) ≤ (1 / t) • |x| :=
      smul_nonneg (one_div_pos.mpr ht_pos).le (abs_nonneg _)
    have hpos_ne : (((1 / t) • |x| : X) - e)⁺ ≠ 0 := by
      intro hzero
      have h := posPart_eq_zero.mp hzero
      have hle : (1 / t) • |x| ≤ e := sub_nonpos.mp h
      -- Then ‖(1/t) • |x|‖ ≤ ‖e‖ = 1
      have hnle : ‖((1 / t) • |x| : X)‖ ≤ ‖(e : X)‖ :=
        norm_le_norm_of_abs_le_abs (by
          rw [abs_of_nonneg hyabs_nn]
          have hee : |(e : X)| = e := abs_of_nonneg unit_pos.le
          rw [hee]
          exact hle)
      rw [norm_smul, Real.norm_of_nonneg (one_div_pos.mpr ht_pos).le,
          norm_abs_eq_norm, norm_unit] at hnle
      have hbad : 1 / t * ‖x‖ ≤ 1 := hnle
      rw [div_mul_eq_mul_div, div_le_one ht_pos] at hbad
      linarith
    obtain ⟨φ, hφ⟩ := exists_lattice_character_ge_one_of_pos_part_ne_zero
      hyabs_nn hpos_ne
    have hφ_smul : φ ((1 / t) • |x|) = (1 / t) * φ |x| := map_smul φ.toVecLatHom _ _
    rw [hφ_smul] at hφ
    refine ⟨φ, ?_⟩
    have hφ_abs : t ≤ φ |x| := by
      have h2 : t * 1 ≤ t * (1 / t * φ |x|) :=
        mul_le_mul_of_nonneg_left hφ ht_pos.le
      rw [mul_one, ← mul_assoc, mul_one_div_cancel (ne_of_gt ht_pos), one_mul] at h2
      exact h2
    rw [show |φ x| = φ |x| from (φ.toVecLatHom.map_abs x).symm]
    exact hφ_abs
  apply le_antisymm
  · -- ‖x‖ ≤ sSup S
    apply le_of_forall_lt
    intro t ht
    -- Need: t < sSup S, given t < ‖x‖
    by_cases ht_pos : 0 < t
    · -- 0 < t < ‖x‖, use witness
      obtain ⟨φ, hφ⟩ := hwit t ht_pos ht
      have h_in : |φ x| ∈ S := ⟨φ, rfl⟩
      have h_le : t ≤ sSup S := hφ.trans (le_csSup hS_bdd h_in)
      -- We have t ≤ sSup S, but we need t < sSup S. Use dense ordering.
      -- Actually, since we can find arbitrary t' > t with t' < ‖x‖,
      -- we can repeat the argument with t' to get t < t' ≤ sSup S.
      by_cases hgap : t < ‖x‖
      · obtain ⟨t', ht_lt_t', ht'_lt⟩ := exists_between hgap
        by_cases ht'_pos : 0 < t'
        · obtain ⟨φ', hφ'⟩ := hwit t' ht'_pos ht'_lt
          exact lt_of_lt_of_le ht_lt_t' (hφ'.trans (le_csSup hS_bdd ⟨φ', rfl⟩))
        · push_neg at ht'_pos
          linarith
      · push_neg at hgap; linarith
    · -- t ≤ 0, t < sSup S since sSup S ≥ 0
      push_neg at ht_pos
      have ⟨φ⟩ := @LatticeCharacter.instNonempty X _ _ _ _
      have h_nn : 0 ≤ sSup S := (abs_nonneg (φ x)).trans (le_csSup hS_bdd ⟨φ, rfl⟩)
      -- t ≤ 0 ≤ sSup S, but need strict inequality
      by_cases ht_eq : t = 0
      · -- Need: 0 < sSup S. This holds iff some |φ x| > 0, i.e., x ≠ 0 essentially.
        -- For now, use the fact ht : t < ‖x‖, so 0 < ‖x‖, so x ≠ 0.
        rw [ht_eq] at ht
        -- ht : 0 < ‖x‖, so use hwit at some small t'
        obtain ⟨t', ht'1, ht'2⟩ := exists_between ht
        obtain ⟨φ', hφ'⟩ := hwit t' ht'1 ht'2
        rw [ht_eq]
        exact lt_of_lt_of_le ht'1 (hφ'.trans (le_csSup hS_bdd ⟨φ', rfl⟩))
      · -- t < 0 ≤ sSup S
        have : t < 0 := lt_of_le_of_ne ht_pos ht_eq
        linarith
  · exact csSup_le hS_ne (by rintro _ ⟨φ, rfl⟩; exact φ.abs_apply_le_norm x)

/-- The Gelfand transform separates points: for every nonzero `x : X` there is
a lattice character `φ` with `φ x ≠ 0`. -/
theorem exists_latticeCharacter_ne_zero {x : X} (hx : x ≠ 0) :
    ∃ φ : LatticeCharacter X, φ x ≠ 0 := by
  by_contra h
  push_neg at h
  have h_zero : ‖x‖ = 0 := by
    rw [attains_norm_at_characters]
    apply le_antisymm
    · apply csSup_le
      · have ⟨φ⟩ := @LatticeCharacter.instNonempty X _ _ _ _
        exact ⟨|φ x|, φ, rfl⟩
      · rintro _ ⟨φ, rfl⟩
        rw [h φ, abs_zero]
    · apply le_csSup
      · refine ⟨‖x‖, ?_⟩
        rintro _ ⟨φ, rfl⟩
        exact φ.abs_apply_le_norm x
      · have ⟨φ⟩ := @LatticeCharacter.instNonempty X _ _ _ _
        exact ⟨φ, by rw [h φ, abs_zero]⟩
  exact hx (norm_le_zero_iff.mp (le_of_eq h_zero))

/-- The Gelfand transform is an isometry: `‖gelfand x‖ = ‖x‖` for every `x`. -/
theorem norm_gelfand (x : X) :
    ‖(gelfand x : C(LatticeCharacter X, ℝ))‖ = ‖x‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm, attains_norm_at_characters x]
  have hbdd : BddAbove (Set.range fun φ : LatticeCharacter X => ‖gelfand x φ‖) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨φ, rfl⟩
    change ‖gelfand x φ‖ ≤ ‖x‖
    rw [gelfand_apply, Real.norm_eq_abs]
    exact φ.abs_apply_le_norm x
  apply le_antisymm
  · apply ciSup_le
    intro φ
    apply le_csSup
    · refine ⟨‖x‖, ?_⟩
      rintro _ ⟨ψ, rfl⟩; exact ψ.abs_apply_le_norm x
    · exact ⟨φ, by simp [gelfand_apply, Real.norm_eq_abs]⟩
  · apply csSup_le
    · obtain ⟨φ⟩ := @LatticeCharacter.instNonempty X _ _ _ _
      exact ⟨|φ x|, φ, rfl⟩
    · rintro _ ⟨φ, rfl⟩
      have : |(φ : X → ℝ) x| = ‖gelfand x φ‖ := by
        simp [gelfand_apply, Real.norm_eq_abs]
      rw [this]
      exact le_ciSup hbdd φ

/-- The Gelfand transform is an isometry from `X` to `C(K, ℝ)`. -/
private theorem gelfand_isometry :
    Isometry (gelfand : X → C(LatticeCharacter X, ℝ)) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : gelfand x - gelfand y = gelfand (x - y) := by
    have h2 : gelfand (x - y) + gelfand y = gelfand x := by
      rw [← gelfand_isVecLatHom.map_add, sub_add_cancel]
    rw [← h2]; abel
  rw [h1, norm_gelfand]

/-- The Gelfand transform is surjective. The image is a unital sublattice of
`C(K, ℝ)` that separates points, and the lattice version of the
Stone–Weierstrass theorem identifies the closed unital sublattice generated by
such a family with all of `C(K, ℝ)`. -/
theorem gelfand_surjective :
    Function.Surjective (gelfand : X → C(LatticeCharacter X, ℝ)) := by
  set L : Set C(LatticeCharacter X, ℝ) := Set.range gelfand with hL_def
  -- L is a sublattice
  have hL_inf : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨x ⊓ y, gelfand_isVecLatHom.map_inf' x y⟩
  have hL_sup : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨x ⊔ y, gelfand_isVecLatHom.map_sup' x y⟩
  have hL_ne : L.Nonempty := ⟨gelfand 0, 0, rfl⟩
  -- L separates points strongly
  have hL_sep : L.SeparatesPointsStrongly := by
    intro v φ ψ
    by_cases hφψ : φ = ψ
    · subst hφψ
      refine ⟨gelfand ((v φ) • e), ⟨(v φ) • e, rfl⟩, ?_, ?_⟩
      · change φ ((v φ) • e) = v φ
        have h1 : φ ((v φ) • e) = (v φ) * φ e := map_smul φ.toVecLatHom _ _
        rw [h1, φ.map_unit_apply, mul_one]
      · change φ ((v φ) • e) = v φ
        have h1 : φ ((v φ) • e) = (v φ) * φ e := map_smul φ.toVecLatHom _ _
        rw [h1, φ.map_unit_apply, mul_one]
    · -- φ ≠ ψ, find x ∈ X with φ x ≠ ψ x
      have hex : ∃ x : X, φ x ≠ ψ x := by
        by_contra h
        push_neg at h
        apply hφψ
        exact DFunLike.ext _ _ h
      obtain ⟨x, hx⟩ := hex
      set d := φ x - ψ x with hd_def
      have hd_ne : d ≠ 0 := sub_ne_zero.mpr hx
      set α := (v φ - v ψ) / d with hα_def
      set β := v φ - α * φ x with hβ_def
      refine ⟨gelfand (α • x + β • e), ⟨α • x + β • e, rfl⟩, ?_, ?_⟩
      · change φ (α • x + β • e) = v φ
        have h1 : φ (α • x + β • e) = α * φ x + β * φ e := by
          rw [show φ (α • x + β • e) = φ (α • x) + φ (β • e) from
            map_add φ.toVecLatHom _ _]
          rw [show φ (α • x) = α * φ x from map_smul φ.toVecLatHom _ _]
          rw [show φ (β • e) = β * φ e from map_smul φ.toVecLatHom _ _]
        rw [h1, φ.map_unit_apply, mul_one, hβ_def]
        ring
      · change ψ (α • x + β • e) = v ψ
        have h1 : ψ (α • x + β • e) = α * ψ x + β * ψ e := by
          rw [show ψ (α • x + β • e) = ψ (α • x) + ψ (β • e) from
            map_add ψ.toVecLatHom _ _]
          rw [show ψ (α • x) = α * ψ x from map_smul ψ.toVecLatHom _ _]
          rw [show ψ (β • e) = β * ψ e from map_smul ψ.toVecLatHom _ _]
        rw [h1, ψ.map_unit_apply, mul_one]
        have key : α * (φ x - ψ x) = v φ - v ψ := by
          rw [hα_def, ← hd_def]; field_simp
        rw [hβ_def]
        linarith [key]
  -- Apply Stone-Weierstrass for sublattices
  have hL_closure : closure L = Set.univ :=
    ContinuousMap.sublattice_closure_eq_top L hL_ne hL_inf hL_sup hL_sep
  -- L is closed (gelfand is isometry from complete space)
  have hL_closed : IsClosed L := gelfand_isometry.isClosedEmbedding.isClosed_range
  rw [hL_closed.closure_eq] at hL_closure
  intro f
  exact (Set.eq_univ_iff_forall.mp hL_closure f)

/-! ### Kakutani's theorem -/

variable (X)

/-- The Gelfand transform as a real-linear map. -/
private noncomputable def gelfandLinear :
    X →ₗ[ℝ] C(LatticeCharacter X, ℝ) where
  toFun := gelfand
  map_add' := gelfand_isVecLatHom.map_add
  map_smul' := gelfand_isVecLatHom.map_smul

/-- **Kakutani's representation theorem** for AM-spaces with unit. Every
AM-space with unit `(X, e)` is Banach-lattice isomorphic to `C(K, ℝ)` for the
compact Hausdorff space `K = LatticeCharacter X` of its lattice characters,
via the Gelfand transform `x ↦ (φ ↦ φ x)`. -/
noncomputable def kakutaniEquiv :
    BanachLatEquiv X C(LatticeCharacter X, ℝ) where
  toLinearEquiv := LinearEquiv.ofBijective (gelfandLinear (X := X))
    ⟨gelfand_isometry.injective, gelfand_surjective⟩
  norm_map' := fun x => norm_gelfand x
  map_sup' := fun a b => gelfand_isVecLatHom.map_sup' a b
  map_inf' := fun a b => gelfand_isVecLatHom.map_inf' a b

@[simp] theorem kakutaniEquiv_apply (x : X) (φ : LatticeCharacter X) :
    kakutaniEquiv X x φ = φ x := rfl

/-- Under the Kakutani isomorphism, the unit `e` corresponds to the constant
function `1`. -/
theorem kakutaniEquiv_unit :
    kakutaniEquiv X (e : X) = 1 := by
  -- This follows from gelfand_unit and the definition of kakutaniEquiv
  ext φ
  rw [kakutaniEquiv_apply]
  rw [ContinuousMap.coe_one, Pi.one_apply]
  exact φ.map_unit

end AMSpaceWithUnit
