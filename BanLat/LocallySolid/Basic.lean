import BanLat.Substructures.Band.Generated
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Locally solid topological vector lattices

This file develops basic properties of locally solid vector lattices.
-/

open scoped Topology Pointwise

/-- A locally solid vector lattice is a real vector lattice whose topology makes it a
topological real vector space and whose zero-neighborhoods have a basis of solid sets. -/
class IsLocallySolidVectorLattice (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [TopologicalSpace X] : Prop
    extends IsTopologicalAddGroup X, ContinuousSMul ℝ X where
  hasBasis_solid : (𝓝 (0 : X)).HasBasis
    (fun s : Set X => s ∈ 𝓝 (0 : X) ∧ LatticeOrderedAddCommGroup.IsSolid s) id

section Properties

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]

section UniformContinuity

variable [VectorLattice E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]

private lemma uniformContinuous_of_nhds_zero {α β : Type*} [UniformSpace α] [UniformSpace β]
    [AddGroup β] [IsUniformAddGroup β] {f : α → β}
    (h : ∀ U ∈ 𝓝 (0 : β), {p : α × α | f p.2 - f p.1 ∈ U} ∈ uniformity α) :
    UniformContinuous f := by
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero β]
  intro U hU
  rcases Filter.mem_comap.mp hU with ⟨V, hV, hVU⟩
  exact Filter.mem_of_superset (h V hV) fun p hp => hVU hp

omit [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E] [ContinuousSMul ℝ E] in
private lemma prod_coord_diff_mem_uniformity {S : Set E} (hS : S ∈ 𝓝 (0 : E)) :
    {q : (E × E) × (E × E) | q.2.1 - q.1.1 ∈ S ∧ q.2.2 - q.1.2 ∈ S}
      ∈ uniformity (E × E) := by
  rw [uniformity_prod_eq_comap_prod]
  refine Filter.mem_comap.mpr ?_
  let V : Set (E × E) := {p | p.2 - p.1 ∈ S}
  have hV : V ∈ uniformity E := by
    rw [uniformity_eq_comap_nhds_zero E]
    exact Filter.preimage_mem_comap hS
  exact ⟨V ×ˢ V, Filter.prod_mem_prod hV hV, fun _ hq => hq⟩

omit [VectorLattice E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] in
private lemma abs_sup_sub_sup_le_add (a b c d : E) :
    |(a ⊔ b) - (c ⊔ d)| ≤ |a - c| + |b - d| := by
  calc
    |(a ⊔ b) - (c ⊔ d)|
        = |((a ⊔ b) - (c ⊔ b)) + ((c ⊔ b) - (c ⊔ d))| := by
          congr 1
          abel
    _ ≤ |(a ⊔ b) - (c ⊔ b)| + |(c ⊔ b) - (c ⊔ d)| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      exact add_le_add (abs_sup_sub_sup_le_abs a c b) (by
        rw [sup_comm c b, sup_comm c d]
        exact abs_sup_sub_sup_le_abs b d c)

omit [VectorLattice E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] in
private lemma solid_abs_mem {S : Set E} (hS : LatticeOrderedAddCommGroup.IsSolid S)
    {x : E} (hx : x ∈ S) : |x| ∈ S :=
  hS hx (by rw [abs_abs])

omit [ContinuousSMul ℝ E] in
private lemma locallySolid_uniformContinuous_sup (hls : IsLocallySolidVectorLattice E) :
    UniformContinuous (fun p : E × E => p.1 ⊔ p.2) := by
  letI : IsLocallySolidVectorLattice E := hls
  refine uniformContinuous_of_nhds_zero ?_
  intro U hU
  rcases IsLocallySolidVectorLattice.hasBasis_solid.mem_iff.mp hU with ⟨T, hT, hTU⟩
  rcases exists_open_nhds_zero_add_subset hT.1 with ⟨A, hAopen, hA0, hAAT⟩
  rcases IsLocallySolidVectorLattice.hasBasis_solid.mem_iff.mp (hAopen.mem_nhds hA0) with
    ⟨S, hS, hSA⟩
  refine Filter.mem_of_superset (prod_coord_diff_mem_uniformity hS.1) ?_
  intro q hq
  rcases hq with ⟨h1, h2⟩
  have h1abs : |q.2.1 - q.1.1| ∈ S := solid_abs_mem hS.2 h1
  have h2abs : |q.2.2 - q.1.2| ∈ S := solid_abs_mem hS.2 h2
  have hsumT : |q.2.1 - q.1.1| + |q.2.2 - q.1.2| ∈ T :=
    hAAT ⟨_, hSA h1abs, _, hSA h2abs, rfl⟩
  apply hTU
  exact hT.2 hsumT (by
    have hineq := abs_sup_sub_sup_le_add q.2.1 q.2.2 q.1.1 q.1.2
    have hnonneg : 0 ≤ |q.2.1 - q.1.1| + |q.2.2 - q.1.2| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [abs_of_nonneg hnonneg] using hineq)

omit [IsOrderedAddMonoid E] [VectorLattice E] [ContinuousSMul ℝ E] in
private lemma uniformContinuous_abs_of_sup
    (hsup : UniformContinuous (fun p : E × E => p.1 ⊔ p.2)) :
    UniformContinuous (|·| : E → E) := by
  simpa [abs] using hsup.comp (UniformContinuous.prodMk uniformContinuous_id uniformContinuous_neg)

omit [VectorLattice E] [ContinuousSMul ℝ E] in
private lemma uniformContinuous_inf_of_sup
    (hsup : UniformContinuous (fun p : E × E => p.1 ⊔ p.2)) :
    UniformContinuous (fun p : E × E => p.1 ⊓ p.2) := by
  have hnegpair : UniformContinuous (fun p : E × E => (-p.1, -p.2)) :=
    UniformContinuous.prodMk (uniformContinuous_neg.comp uniformContinuous_fst)
      (uniformContinuous_neg.comp uniformContinuous_snd)
  have hcomp : UniformContinuous (fun p : E × E => (-p.1) ⊔ (-p.2)) :=
    hsup.comp hnegpair
  have hneg : UniformContinuous (fun p : E × E => -((-p.1) ⊔ (-p.2))) :=
    uniformContinuous_neg.comp hcomp
  convert hneg using 1
  ext p
  rw [neg_sup, neg_neg, neg_neg]

local instance : UniformContinuousConstSMul ℝ E :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ E

omit [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] in
private lemma posPart_eq_half_smul (x : E) :
    x⁺ = ((2 : ℝ)⁻¹) • (x + |x|) := by
  rw [posPart_def]
  simpa [sub_eq_add_neg] using (sup_eq_half_smul_add_add_abs_sub' ℝ x 0)

private lemma uniformContinuous_posPart_of_abs
    (habs : UniformContinuous (|·| : E → E)) : UniformContinuous (posPart : E → E) := by
  have h : UniformContinuous (fun x : E => ((2 : ℝ)⁻¹) • (x + |x|)) :=
    (uniformContinuous_id.add habs).const_smul _
  convert h using 1
  ext x
  exact posPart_eq_half_smul x

private lemma uniformContinuous_sup_of_abs
    (habs : UniformContinuous (|·| : E → E)) :
    UniformContinuous (fun p : E × E => p.1 ⊔ p.2) := by
  have hsub : UniformContinuous (fun p : E × E => p.2 - p.1) :=
    uniformContinuous_snd.sub uniformContinuous_fst
  have hpos : UniformContinuous (fun p : E × E => (p.2 - p.1)⁺) :=
    (uniformContinuous_posPart_of_abs habs).comp hsub
  have h : UniformContinuous (fun p : E × E => p.1 + (p.2 - p.1)⁺) :=
    uniformContinuous_fst.add hpos
  convert h using 1
  ext p
  exact sup_eq_add_posPart p.1 p.2

omit [VectorLattice E] [ContinuousSMul ℝ E] in
private lemma uniformContinuous_sup_of_inf
    (hinf : UniformContinuous (fun p : E × E => p.1 ⊓ p.2)) :
    UniformContinuous (fun p : E × E => p.1 ⊔ p.2) := by
  have hnegpair : UniformContinuous (fun p : E × E => (-p.1, -p.2)) :=
    UniformContinuous.prodMk (uniformContinuous_neg.comp uniformContinuous_fst)
      (uniformContinuous_neg.comp uniformContinuous_snd)
  have hcomp : UniformContinuous (fun p : E × E => (-p.1) ⊓ (-p.2)) :=
    hinf.comp hnegpair
  have hneg : UniformContinuous (fun p : E × E => -((-p.1) ⊓ (-p.2))) :=
    uniformContinuous_neg.comp hcomp
  convert hneg using 1
  ext p
  rw [neg_inf, neg_neg, neg_neg]

omit [IsOrderedAddMonoid E] [VectorLattice E] [ContinuousSMul ℝ E] in
private lemma exists_nhds_zero_forall_inf_sub_inf_mem
    (hinf : UniformContinuous (fun p : E × E => p.1 ⊓ p.2)) {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) :
    ∃ N ∈ 𝓝 (0 : E), ∀ a z : E, a ∈ N → (a ⊓ z) - (0 ⊓ z) ∈ U := by
  let T : Set (E × E) := {p | p.2 - p.1 ∈ U}
  have hT : T ∈ uniformity E := by
    rw [uniformity_eq_comap_nhds_zero E]
    exact Filter.preimage_mem_comap hU
  have hpre :
      {q : (E × E) × (E × E) | (q.2.1 ⊓ q.2.2) - (q.1.1 ⊓ q.1.2) ∈ U}
        ∈ uniformity (E × E) := by
    simpa [UniformContinuous, T] using hinf hT
  rw [uniformity_prod_eq_comap_prod] at hpre
  rcases Filter.mem_comap.mp hpre with ⟨R, hR, hRsub⟩
  rcases Filter.mem_prod_iff.mp hR with ⟨R₁, hR₁, R₂, hR₂, hRprod⟩
  rw [uniformity_eq_comap_nhds_zero E] at hR₁
  rcases Filter.mem_comap.mp hR₁ with ⟨N, hN, hNsub⟩
  refine ⟨N, hN, ?_⟩
  intro a z ha
  have hpair₁ : (0, a) ∈ R₁ := hNsub (by simpa using ha)
  have hpair₂ : (z, z) ∈ R₂ := refl_mem_uniformity hR₂
  exact hRsub (show
    (((0, z), (a, z)) : (E × E) × (E × E)) ∈
      (fun p : (E × E) × (E × E) => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' R from
    hRprod ⟨hpair₁, hpair₂⟩)

private lemma locallySolid_of_uniformContinuous_sup
    (hsup : UniformContinuous (fun p : E × E => p.1 ⊔ p.2)) :
    IsLocallySolidVectorLattice E := by
  have hinf := uniformContinuous_inf_of_sup hsup
  have habs := uniformContinuous_abs_of_sup hsup
  refine { hasBasis_solid := ?_ }
  rw [Filter.hasBasis_self]
  intro U hU
  rcases exists_open_nhds_zero_add_subset hU with ⟨A₀, hA₀open, hA₀zero, hA₀A₀U⟩
  let A : Set E := A₀ ∩ {x | -x ∈ A₀}
  have hA : A ∈ 𝓝 (0 : E) := by
    refine Filter.inter_mem (hA₀open.mem_nhds hA₀zero) ?_
    simpa [A] using
      (continuous_neg.tendsto (0 : E)) (hA₀open.mem_nhds (by simpa using hA₀zero))
  rcases exists_nhds_zero_forall_inf_sub_inf_mem hinf hA with ⟨B, hB, hBU⟩
  have hBabs : (|·| : E → E) ⁻¹' B ∈ 𝓝 (0 : E) := by
    simpa using habs.continuous.tendsto' 0 0 (by simp) hB
  let S : Set E := LatticeOrderedAddCommGroup.solidClosure ((|·| : E → E) ⁻¹' B)
  refine ⟨S, ?_, LatticeOrderedAddCommGroup.isSolid_solidClosure _, ?_⟩
  · exact Filter.mem_of_superset hBabs fun x hx => ⟨x, hx, le_rfl⟩
  · rintro y ⟨x, hx, hyx⟩
    have hpos_le : y ≤ |x| := (le_abs_self y).trans hyx
    have hneg_le : -y ≤ |x| := (neg_le_abs y).trans hyx
    have hpos_mem : y⁺ ∈ A := by
      have h := hBU |x| y hx
      rw [inf_eq_right.mpr hpos_le, inf_comm 0 y, sub_inf_eq_posPart] at h
      simpa using h
    have hneg_mem : y⁻ ∈ A := by
      have h := hBU |x| (-y) hx
      rw [inf_eq_right.mpr hneg_le, inf_comm 0 (-y), sub_inf_eq_posPart] at h
      simpa using h
    apply hA₀A₀U
    refine ⟨y⁺, hpos_mem.1, -y⁻, ?_, ?_⟩
    · exact hneg_mem.2
    · change y⁺ + -y⁻ = y
      rw [← sub_eq_add_neg, posPart_sub_negPart]

/-- For a topological vector lattice, local solidity and uniform continuity of binary
suprema, binary infima, and absolute value are equivalent. -/
theorem isLocallySolidVectorLattice_tfae :
    List.TFAE [
      IsLocallySolidVectorLattice E,
      UniformContinuous (fun p : E × E => p.1 ⊔ p.2),
      UniformContinuous (fun p : E × E => p.1 ⊓ p.2),
      UniformContinuous (|·| : E → E)] := by
  tfae_have 1 → 2 := locallySolid_uniformContinuous_sup
  tfae_have 2 → 3 := uniformContinuous_inf_of_sup
  tfae_have 2 → 4 := uniformContinuous_abs_of_sup
  tfae_have 4 → 2 := uniformContinuous_sup_of_abs
  tfae_have 3 → 2 := uniformContinuous_sup_of_inf
  tfae_have 2 → 1 := locallySolid_of_uniformContinuous_sup
  tfae_finish

/-- A topological vector lattice is locally solid iff binary suprema are uniformly continuous. -/
theorem isLocallySolidVectorLattice_iff_uniformContinuous_sup :
    IsLocallySolidVectorLattice E ↔ UniformContinuous (fun p : E × E => p.1 ⊔ p.2) := by
  exact (isLocallySolidVectorLattice_tfae (E := E)).out 0 1

/-- A topological vector lattice is locally solid iff binary infima are uniformly continuous. -/
theorem isLocallySolidVectorLattice_iff_uniformContinuous_inf :
    IsLocallySolidVectorLattice E ↔ UniformContinuous (fun p : E × E => p.1 ⊓ p.2) := by
  exact (isLocallySolidVectorLattice_tfae (E := E)).out 0 2

/-- A topological vector lattice is locally solid iff the absolute-value map is uniformly
continuous. -/
theorem isLocallySolidVectorLattice_iff_uniformContinuous_abs :
    IsLocallySolidVectorLattice E ↔ UniformContinuous (|·| : E → E) := by
  exact (isLocallySolidVectorLattice_tfae (E := E)).out 0 3

end UniformContinuity

section IsLocallySolidVectorLattice

variable [VectorLattice E] [TopologicalSpace E] [IsLocallySolidVectorLattice E]

omit [VectorLattice E] [TopologicalSpace E] [IsLocallySolidVectorLattice E] in
private lemma abs_le_abs_sup_abs_of_mem_Icc {a b x : E} (hx : x ∈ Set.Icc a b) :
    |x| ≤ |a| ⊔ |b| := by
  rw [abs]
  exact sup_le
    (hx.2.trans ((le_abs_self b).trans le_sup_right))
    ((neg_le_neg hx.1).trans ((neg_le_abs a).trans le_sup_left))

/-- In a locally solid vector lattice, every order-bounded set is von Neumann bounded. -/
theorem Bornology.IsVonNBounded.of_bddBelow_bddAbove {s : Set E}
    (hl : BddBelow s) (hu : BddAbove s) : Bornology.IsVonNBounded ℝ s := by
  intro U hU
  rcases IsLocallySolidVectorLattice.hasBasis_solid.mem_iff.mp hU with ⟨V, hV, hVU⟩
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hu
  let w : E := |a| ⊔ |b|
  have hV_absorbent : Absorbent ℝ V := absorbent_nhds_zero hV.1
  obtain ⟨r, hrpos, hr⟩ := (hV_absorbent w).exists_pos
  refine (Absorbs.of_norm ⟨r, fun c hc => ?_⟩).mono_left hVU
  intro x hx
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, norm_zero] at hc
    linarith
  have hw_mem : w ∈ c • V := hr c hc (Set.mem_singleton w)
  have hinvw_mem : c⁻¹ • w ∈ V := by
    rcases hw_mem with ⟨v, hv, hvw⟩
    rw [← hvw, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    exact hv
  have hx_abs : |x| ≤ w := abs_le_abs_sup_abs_of_mem_Icc ⟨ha hx, hb hx⟩
  have hw_nonneg : 0 ≤ w := le_sup_of_le_left (abs_nonneg a)
  have hinvx_abs : |c⁻¹ • x| ≤ |c⁻¹ • w| := by
    rw [abs_smul' (x := x), abs_smul' (x := w), abs_of_nonneg hw_nonneg]
    exact smul_le_smul_of_nonneg_left hx_abs (abs_nonneg c⁻¹)
  have hinvx_mem : c⁻¹ • x ∈ V := hV.2 hinvw_mem hinvx_abs
  exact ⟨c⁻¹ • x, hinvx_mem, by
    change c • (c⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hcne, one_smul]⟩

/-- In a locally solid vector lattice, the closure of a solid set is solid. -/
theorem LatticeOrderedAddCommGroup.IsSolid.closure {s : Set E}
    (hs : LatticeOrderedAddCommGroup.IsSolid s) :
    LatticeOrderedAddCommGroup.IsSolid (closure s) := by
  intro x hx y hy_abs
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let f : E → E := fun z => (y ⊔ -|z|) ⊓ |z|
  have hcont_abs : Continuous (|·| : E → E) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_abs (E := E)).mp inferInstance).continuous
  have hcont_sup : Continuous (fun p : E × E => p.1 ⊔ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_sup (E := E)).mp inferInstance).continuous
  have hcont_inf : Continuous (fun p : E × E => p.1 ⊓ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_inf (E := E)).mp inferInstance).continuous
  have hcont : Continuous f := by
    exact hcont_inf.comp
      (Continuous.prodMk (hcont_sup.comp
        (Continuous.prodMk continuous_const (continuous_neg.comp hcont_abs))) hcont_abs)
  have hmaps : Set.MapsTo f s s := by
    intro z hz
    apply hs hz
    have hf_le : f z ≤ |z| := inf_le_right
    have hneg_le : -|z| ≤ f z :=
      le_inf le_sup_right (le_trans (neg_nonpos_of_nonneg (abs_nonneg z)) (abs_nonneg z))
    rw [abs_le']
    exact ⟨hf_le, by rwa [neg_le]⟩
  have hfx : f x ∈ _root_.closure s := map_mem_closure (t := s) hcont hx hmaps
  have hle_abs : y ≤ |x| := (le_abs_self y).trans hy_abs
  have hneg_le : -|x| ≤ y := by
    rw [neg_le]
    exact (neg_le_abs y).trans hy_abs
  have hfx_eq : f x = y := by
    rw [show f x = (y ⊔ -|x|) ⊓ |x| from rfl,
      sup_eq_left.mpr hneg_le, inf_eq_left.mpr hle_abs]
  rwa [hfx_eq] at hfx

/-- In a locally solid vector lattice, the closure of a vector sublattice is again a vector
sublattice. -/
theorem VectorSublattice.exists_coe_eq_closure (Y : VectorSublattice E) :
    ∃ Z : VectorSublattice E, (Z : Set E) = closure (Y : Set E) := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hcont_sup : Continuous (fun p : E × E => p.1 ⊔ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_sup (E := E)).mp inferInstance).continuous
  let Z : VectorSublattice E :=
    { toSubmodule := Submodule.topologicalClosure Y.toSubmodule
      sup_mem' := fun {x y} hx hy => by
        have hx' : x ∈ _root_.closure (Y.toSubmodule : Set E) := by
          rw [← Submodule.topologicalClosure_coe]
          exact hx
        have hy' : y ∈ _root_.closure (Y.toSubmodule : Set E) := by
          rw [← Submodule.topologicalClosure_coe]
          exact hy
        have hxy : x ⊔ y ∈ _root_.closure (Y.toSubmodule : Set E) :=
          map_mem_closure₂ (f := fun a b : E => a ⊔ b)
            (by simpa [Function.uncurry] using hcont_sup) hx' hy'
            (fun _ ha _ hb => Y.sup_mem ha hb)
        rwa [← Submodule.topologicalClosure_coe] at hxy }
  refine ⟨Z, ?_⟩
  change _root_.closure (Y.toSubmodule : Set E) = _root_.closure (Y : Set E)
  rfl

/-- In a locally solid vector lattice, the closure of an order ideal is again an order ideal. -/
theorem OrderIdeal.exists_coe_eq_closure (J : OrderIdeal E) :
    ∃ K : OrderIdeal E, (K : Set E) = closure (J : Set E) := by
  have hJsolid : LatticeOrderedAddCommGroup.IsSolid (J.toSubmodule : Set E) := by
    intro x hx y hy
    exact J.mem_of_abs_le_abs hx hy
  let K : OrderIdeal E :=
    OrderIdeal.ofSolid (Submodule.topologicalClosure J.toSubmodule) (by
      intro x y hx hy
      have hx' : x ∈ _root_.closure (J.toSubmodule : Set E) := by
        rw [← Submodule.topologicalClosure_coe]
        exact hx
      have hy' : y ∈ _root_.closure (J.toSubmodule : Set E) :=
        (LatticeOrderedAddCommGroup.IsSolid.closure hJsolid) hx' hy
      rwa [← Submodule.topologicalClosure_coe] at hy')
  refine ⟨K, ?_⟩
  change _root_.closure (J.toSubmodule : Set E) = _root_.closure (J : Set E)
  rfl

private lemma eq_zero_of_forall_mem_nhds_zero {F : Type*} [Zero F] [TopologicalSpace F]
    [T1Space F] {x : F} (h : ∀ U ∈ 𝓝 (0 : F), x ∈ U) : x = 0 := by
  by_contra hx
  have hU : ({x}ᶜ : Set F) ∈ 𝓝 (0 : F) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simpa using Ne.symm hx)
  exact (h {x}ᶜ hU) rfl

section Hausdorff

variable [T2Space E]

/-- A Hausdorff locally solid vector lattice is Archimedean. -/
theorem isVLArchimedean_of_t2_locallySolidVectorLattice : IsVLArchimedean E := by
  apply isVLArchimedean_of_eq_zero_of_nonneg_of_forall_nsmul_le
  intro x y hx hxy
  have hy : 0 ≤ y := by simpa using hxy 0
  apply eq_zero_of_forall_mem_nhds_zero
  intro U hU
  rcases IsLocallySolidVectorLattice.hasBasis_solid.mem_iff.mp hU with ⟨V, hV, hVU⟩
  apply hVU
  have hV_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ)⁻¹ • y : E) ∈ V := by
    have htend : Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ • y : E)) Filter.atTop
        (𝓝 (0 : E)) := by
      simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const y)
    exact htend hV.1
  have hpos_eventually : ∀ᶠ n : ℕ in Filter.atTop, 0 < n :=
    Filter.eventually_ge_atTop 1
  rcases (hV_eventually.and hpos_eventually).exists with ⟨n, hnV, hnpos⟩
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have hn_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hx_le : x ≤ (n : ℝ)⁻¹ • y := by
    have hle : (n : ℝ) • x ≤ y := by
      simpa [Nat.cast_smul_eq_nsmul] using hxy n
    have hscaled : (n : ℝ)⁻¹ • ((n : ℝ) • x) ≤ (n : ℝ)⁻¹ • y :=
      smul_le_smul_of_nonneg_left hle hn_nonneg
    rwa [inv_smul_smul₀ hn_ne] at hscaled
  have habs : |x| ≤ |(n : ℝ)⁻¹ • y| := by
    rw [abs_of_nonneg hx, abs_of_nonneg (smul_nonneg hn_nonneg hy)]
    exact hx_le
  exact hV.2 hnV habs

/-- In a Hausdorff locally solid vector lattice, the positive cone is closed. -/
theorem isClosed_nonneg_cone_of_t2_locallySolidVectorLattice :
    IsClosed {x : E | 0 ≤ x} := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hcont_sup : Continuous (fun p : E × E => p.1 ⊔ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_sup (E := E)).mp inferInstance).continuous
  have hcont_negPart : Continuous (fun x : E => x⁻) := by
    simpa [negPart_def] using
      hcont_sup.comp (Continuous.prodMk continuous_neg continuous_const)
  rw [show {x : E | 0 ≤ x} = (fun x : E => x⁻) ⁻¹' ({0} : Set E) by
    ext x
    simp [negPart_eq_zero]]
  exact isClosed_singleton.preimage hcont_negPart

/-- Monotone convergence theorem: an increasing net in a Hausdorff locally solid vector lattice
that converges topologically has its limit as least upper bound. -/
theorem isLUB_of_monotone_tendsto_of_t2_locallySolidVectorLattice {ι : Type*}
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] {u : ι → E} {x : E}
    (hmono : Monotone u) (hlim : Filter.Tendsto u Filter.atTop (nhds x)) :
    IsLUB (Set.range u) x := by
  have hclosed : IsClosed {z : E | 0 ≤ z} :=
    isClosed_nonneg_cone_of_t2_locallySolidVectorLattice (E := E)
  refine ⟨?_, ?_⟩
  · rintro y ⟨i, rfl⟩
    have htend : Filter.Tendsto (fun j : ι => u j - u i) Filter.atTop
        (𝓝 (x - u i)) :=
      hlim.sub tendsto_const_nhds
    have heventually : ∀ᶠ j : ι in Filter.atTop, 0 ≤ u j - u i :=
      (Filter.eventually_ge_atTop i).mono fun j hij => sub_nonneg.mpr (hmono hij)
    exact sub_nonneg.mp (hclosed.mem_of_tendsto htend heventually)
  · intro y hy
    have htend : Filter.Tendsto (fun i : ι => y - u i) Filter.atTop (𝓝 (y - x)) :=
      tendsto_const_nhds.sub hlim
    have heventually : ∀ᶠ i : ι in Filter.atTop, 0 ≤ y - u i :=
      Filter.Eventually.of_forall fun i => sub_nonneg.mpr (hy ⟨i, rfl⟩)
    exact sub_nonneg.mp (hclosed.mem_of_tendsto htend heventually)

private theorem isClosed_disjointComplement_of_t2_locallySolidVectorLattice (A : Set E) :
    IsClosed (Aᵈ : Set E) := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hcont_abs : Continuous (|·| : E → E) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_abs (E := E)).mp inferInstance).continuous
  have hcont_inf : Continuous (fun p : E × E => p.1 ⊓ p.2) :=
    ((isLocallySolidVectorLattice_iff_uniformContinuous_inf (E := E)).mp inferInstance).continuous
  have heq : (Aᵈ : Set E) = ⋂ a ∈ A, (fun x : E => |x| ⊓ |a|) ⁻¹' ({0} : Set E) := by
    ext x
    simp [disjointComplement, IsVLDisjoint]
  rw [heq]
  refine isClosed_iInter fun a => isClosed_iInter fun _ => ?_
  exact isClosed_singleton.preimage
    (hcont_inf.comp (Continuous.prodMk hcont_abs continuous_const))

/-- Every band in a Hausdorff locally solid vector lattice is closed. -/
theorem Band.isClosed_coe_of_t2_locallySolidVectorLattice (B : Band E) :
    IsClosed (B : Set E) := by
  haveI : IsVLArchimedean E := isVLArchimedean_of_t2_locallySolidVectorLattice (E := E)
  rw [← Band.eq_disjointComplement_disjointComplement B]
  exact isClosed_disjointComplement_of_t2_locallySolidVectorLattice (A := (B : Set E)ᵈ)

end Hausdorff

end IsLocallySolidVectorLattice

end Properties
