import BanLat.LocallySolid.Basic
import BanLat.Operators.Hom
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Topology.Algebra.GroupCompletion

/-!
# Completion of locally solid vector lattices

This file states completion results for Hausdorff locally solid vector lattices.
The completion is taken with respect to the canonical uniformity associated to
the topological additive group structure.
-/

open scoped Topology

namespace IsLocallySolidVectorLattice

open Filter UniformSpace

section Completion

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [VectorLattice E] [TopologicalSpace E] [T2Space E] [IsLocallySolidVectorLattice E]

local instance : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
local instance : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
local instance : UniformContinuousConstSMul ℝ E :=
  uniformContinuousConstSMul_of_continuousConstSMul ℝ E

omit [T2Space E] in
private lemma uniformContinuous₂_sup :
    UniformContinuous₂ (fun x y : E => x ⊔ y) := by
  simpa [UniformContinuous₂, Function.uncurry] using
    ((isLocallySolidVectorLattice_iff_uniformContinuous_sup (E := E)).mp inferInstance)

omit [T2Space E] in
private lemma uniformContinuous₂_inf :
    UniformContinuous₂ (fun x y : E => x ⊓ y) := by
  simpa [UniformContinuous₂, Function.uncurry] using
    ((isLocallySolidVectorLattice_iff_uniformContinuous_inf (E := E)).mp inferInstance)

/-- The topological completion of a Hausdorff locally solid vector lattice is a lattice. -/
noncomputable instance instLatticeCompletion : Lattice (Completion E) := by
  letI : Max (Completion E) := ⟨Completion.map₂ (fun x y : E => x ⊔ y)⟩
  letI : Min (Completion E) := ⟨Completion.map₂ (fun x y : E => x ⊓ y)⟩
  have coe_sup : ∀ x y : E, ((x ⊔ y : E) : Completion E) =
      (x : Completion E) ⊔ (y : Completion E) := by
    intro x y
    rw [show (x : Completion E) ⊔ (y : Completion E) =
        Completion.map₂ (fun x y : E => x ⊔ y) x y from rfl,
      Completion.map₂_coe_coe x y (fun x y : E => x ⊔ y) uniformContinuous₂_sup]
  have coe_inf : ∀ x y : E, ((x ⊓ y : E) : Completion E) =
      (x : Completion E) ⊓ (y : Completion E) := by
    intro x y
    rw [show (x : Completion E) ⊓ (y : Completion E) =
        Completion.map₂ (fun x y : E => x ⊓ y) x y from rfl,
      Completion.map₂_coe_coe x y (fun x y : E => x ⊓ y) uniformContinuous₂_inf]
  refine Lattice.mk' ?sup_comm ?sup_assoc ?inf_comm ?inf_assoc ?sup_inf_self ?inf_sup_self
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq (Completion.continuous_map₂ continuous_fst continuous_snd)
        (Completion.continuous_map₂ continuous_snd continuous_fst)
    · intro x y
      rw [← coe_sup, ← coe_sup, sup_comm]
  · intro x y z
    refine Completion.induction_on₃ x y z ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂
          (Completion.continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
          (continuous_snd.comp continuous_snd))
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd)))
    · intro x y z
      rw [← coe_sup, ← coe_sup, ← coe_sup, ← coe_sup, sup_assoc]
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq (Completion.continuous_map₂ continuous_fst continuous_snd)
        (Completion.continuous_map₂ continuous_snd continuous_fst)
    · intro x y
      rw [← coe_inf, ← coe_inf, inf_comm]
  · intro x y z
    refine Completion.induction_on₃ x y z ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂
          (Completion.continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
          (continuous_snd.comp continuous_snd))
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd)))
    · intro x y z
      rw [← coe_inf, ← coe_inf, ← coe_inf, ← coe_inf, inf_assoc]
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ continuous_fst continuous_snd))
        continuous_fst
    · intro x y
      rw [← coe_inf, ← coe_sup, sup_inf_self]
  · intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · exact isClosed_eq
        (Completion.continuous_map₂ continuous_fst
          (Completion.continuous_map₂ continuous_fst continuous_snd))
        continuous_fst
    · intro x y
      rw [← coe_sup, ← coe_inf, inf_sup_self]

omit [T2Space E] in
@[simp, norm_cast]
private theorem coe_sup (x y : E) :
    ((x ⊔ y : E) : Completion E) = (x : Completion E) ⊔ (y : Completion E) := by
  rw [show (x : Completion E) ⊔ (y : Completion E) =
      Completion.map₂ (fun x y : E => x ⊔ y) x y from rfl,
    Completion.map₂_coe_coe x y (fun x y : E => x ⊔ y) uniformContinuous₂_sup]

omit [T2Space E] in
@[simp, norm_cast]
private theorem coe_inf (x y : E) :
    ((x ⊓ y : E) : Completion E) = (x : Completion E) ⊓ (y : Completion E) := by
  rw [show (x : Completion E) ⊓ (y : Completion E) =
      Completion.map₂ (fun x y : E => x ⊓ y) x y from rfl,
    Completion.map₂_coe_coe x y (fun x y : E => x ⊓ y) uniformContinuous₂_inf]

omit [T2Space E] in
@[simp, norm_cast]
private theorem coe_abs (x : E) : ((|x| : E) : Completion E) = |(x : Completion E)| := by
  rw [abs, abs, ← Completion.coe_neg, ← coe_sup]

omit [T2Space E] in
private theorem completion_sup_add (x y z : Completion E) :
    (x + z) ⊔ (y + z) = (x ⊔ y) + z := by
  refine Completion.induction_on₃ x y z ?_ ?_
  · exact isClosed_eq
      (Completion.continuous_map₂
        (Completion.continuous_map₂ continuous_fst (continuous_snd.comp continuous_snd))
        (Completion.continuous_map₂ (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd)))
      (Completion.continuous_map₂
        (Completion.continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
  · intro x y z
    rw [← Completion.coe_add, ← Completion.coe_add, ← coe_sup,
      ← coe_sup, ← Completion.coe_add, add_comm x z, add_comm y z,
      add_comm (x ⊔ y) z, ← add_sup]

/-- The additive order on the topological completion of a Hausdorff locally solid vector lattice
is compatible with addition. -/
noncomputable instance instIsOrderedAddMonoidCompletion : IsOrderedAddMonoid (Completion E) := by
  refine
    { add_le_add_left := fun x y hxy z => ?_
      add_le_add_right := fun x y hxy z => ?_ }
  · rw [← sup_eq_right] at hxy ⊢
    rw [completion_sup_add, hxy]
  · rw [← sup_eq_right] at hxy ⊢
    rw [add_comm z x, add_comm z y, completion_sup_add, hxy]

omit [T2Space E] in
private theorem completion_smul_sup_of_nonneg {r : ℝ} (hr : 0 ≤ r)
    (x y : Completion E) : r • (x ⊔ y) = r • x ⊔ r • y := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((Completion.continuous_map₂ continuous_fst continuous_snd).const_smul r)
      (Completion.continuous_map₂ (continuous_fst.const_smul r) (continuous_snd.const_smul r))
  · intro x y
    rw [← coe_sup, ← Completion.coe_smul, ← Completion.coe_smul, ← Completion.coe_smul,
      ← coe_sup, nonneg_smul_sup x y r hr]

noncomputable instance instVectorLatticeCompletion : VectorLattice (Completion E) where
  smul_le_smul_of_nonneg_left := by
    intro r hr x y hxy
    rw [← sup_eq_right] at hxy ⊢
    rw [← completion_smul_sup_of_nonneg hr, hxy]

/-- The canonical inclusion into the completion as a vector lattice homomorphism. -/
noncomputable def toCompletionVecLatHom : VecLatHom E (Completion E) where
  toFun := ((↑) : E → Completion E)
  map_add' := Completion.coe_add
  map_smul' := Completion.coe_smul
  map_sup' := coe_sup
  map_inf' := coe_inf

/-- The canonical vector lattice homomorphism into the completion is injective. -/
theorem toCompletionVecLatHom_injective :
    Function.Injective (toCompletionVecLatHom : E → Completion E) :=
  Completion.coe_injective E

/-- The topological completion of a Hausdorff locally solid vector lattice is Hausdorff. -/
instance instT2SpaceCompletion : T2Space (Completion E) := by
  infer_instance

/-- The positive cone of the topological completion is the closure of the image of the original
positive cone. -/
theorem nonneg_completion_eq_closure_image_nonneg :
    (AddGroupCone.nonneg (Completion E) : Set (Completion E))
      = closure (((↑) : E → Completion E) '' (AddGroupCone.nonneg E : Set E)) := by
  have _ : T2Space E := inferInstance
  have hcont_negPart : Continuous (fun x : Completion E => x⁻) := by
    simpa [negPart_def] using
      (Completion.continuous_map₂ continuous_neg continuous_const :
        Continuous fun x : Completion E => (-x) ⊔ 0)
  have hclosed : IsClosed (AddGroupCone.nonneg (Completion E) : Set (Completion E)) := by
    rw [show (AddGroupCone.nonneg (Completion E) : Set (Completion E)) =
        (fun x : Completion E => x⁻) ⁻¹' ({0} : Set (Completion E)) by
      ext x
      change (0 ≤ x) ↔ x⁻ = 0
      rw [negPart_eq_zero]]
    exact isClosed_singleton.preimage hcont_negPart
  apply Set.Subset.antisymm
  · intro x hx
    change 0 ≤ x at hx
    have hcont_posPart : Continuous (fun x : Completion E => x⁺) := by
      simpa [posPart_def] using
        (Completion.continuous_map₂ continuous_id continuous_const :
          Continuous fun x : Completion E => x ⊔ 0)
    have hxrange : x ∈ closure (Set.range ((↑) : E → Completion E)) := by
      rw [(Completion.denseRange_coe (α := E)).closure_range]
      trivial
    have hmaps : Set.MapsTo (fun x : Completion E => x⁺)
        (Set.range ((↑) : E → Completion E))
        (((↑) : E → Completion E) '' (AddGroupCone.nonneg E : Set E)) := by
      rintro _ ⟨a, rfl⟩
      refine ⟨a⁺, ?_, ?_⟩
      · change 0 ≤ a⁺
        exact posPart_nonneg a
      · change ((a ⊔ 0 : E) : Completion E) = (a : Completion E) ⊔ 0
        rw [← Completion.coe_zero, ← coe_sup]
    have hxpos : x⁺ ∈ closure (((↑) : E → Completion E) ''
        (AddGroupCone.nonneg E : Set E)) :=
      map_mem_closure hcont_posPart hxrange hmaps
    simpa [posPart_of_nonneg hx] using hxpos
  · refine closure_minimal ?_ hclosed
    rintro _ ⟨a, ha, rfl⟩
    change 0 ≤ a at ha
    change 0 ≤ (a : Completion E)
    rw [← sup_eq_right] at ha ⊢
    rw [← Completion.coe_zero, ← coe_sup, ha]

omit [T2Space E] in
private theorem mem_closure_image_of_abs_le_coe {s : Set E}
    (hs : LatticeOrderedAddCommGroup.IsSolid s) {a : E} (ha : a ∈ s)
    {y : Completion E} (hy : |y| ≤ |(a : Completion E)|) :
    y ∈ closure (((↑) : E → Completion E) '' s) := by
  let g : Completion E → Completion E := fun z => (z ⊔ -|(a : Completion E)|) ⊓ |(a : Completion E)|
  have hcont : Continuous g := by
    exact Completion.continuous_map₂
      (Completion.continuous_map₂ continuous_id continuous_const) continuous_const
  have hxrange : y ∈ closure (Set.range ((↑) : E → Completion E)) := by
    rw [(Completion.denseRange_coe (α := E)).closure_range]
    trivial
  have hmaps : Set.MapsTo g (Set.range ((↑) : E → Completion E))
      (((↑) : E → Completion E) '' s) := by
    rintro _ ⟨b, rfl⟩
    let c : E := (b ⊔ -|a|) ⊓ |a|
    have hc_le : c ≤ |a| := inf_le_right
    have hneg_le : -|a| ≤ c :=
      le_inf le_sup_right (le_trans (neg_nonpos_of_nonneg (abs_nonneg a)) (abs_nonneg a))
    have hc_abs : |c| ≤ |a| := by
      rw [abs_le']
      exact ⟨hc_le, by rwa [neg_le]⟩
    refine ⟨c, hs ha hc_abs, ?_⟩
    change ((c : E) : Completion E) =
      (((b : Completion E) ⊔ -|(a : Completion E)|) ⊓ |(a : Completion E)|)
    rw [show c = (b ⊔ -|a|) ⊓ |a| from rfl, coe_inf, coe_sup,
      Completion.coe_neg, coe_abs]
  have hgy : g y = y := by
    have hle_abs : y ≤ |(a : Completion E)| := (le_abs_self y).trans hy
    have hneg_le : -|(a : Completion E)| ≤ y := by
      rw [neg_le]
      exact (neg_le_abs y).trans hy
    rw [show g y = (y ⊔ -|(a : Completion E)|) ⊓ |(a : Completion E)| from rfl,
      sup_eq_left.mpr hneg_le, inf_eq_left.mpr hle_abs]
  have hmem : g y ∈ closure (((↑) : E → Completion E) '' s) :=
    map_mem_closure hcont hxrange hmaps
  rwa [hgy] at hmem

/-- The closure in the completion of the image of a solid set is solid. -/
theorem isSolid_closure_image_coe {s : Set E}
    (hs : LatticeOrderedAddCommGroup.IsSolid s) :
    LatticeOrderedAddCommGroup.IsSolid
      (closure (((↑) : E → Completion E) '' s)) := by
  have _ : T2Space E := inferInstance
  intro x hx y hy
  let C : Set (Completion E) := closure (((↑) : E → Completion E) '' s)
  let f : Completion E → Completion E := fun z => (y ⊔ -|z|) ⊓ |z|
  have hcont_abs : Continuous (|·| : Completion E → Completion E) := by
    simpa [abs] using
      (Completion.continuous_map₂ continuous_id continuous_neg :
        Continuous fun z : Completion E => z ⊔ -z)
  have hcont : Continuous f := by
    exact Completion.continuous_map₂
      (Completion.continuous_map₂ continuous_const (continuous_neg.comp hcont_abs)) hcont_abs
  have hmaps : Set.MapsTo f (((↑) : E → Completion E) '' s) C := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_closure_image_of_abs_le_coe hs ha
    have hf_le : f (a : Completion E) ≤ |(a : Completion E)| := inf_le_right
    have hneg_le : -|(a : Completion E)| ≤ f (a : Completion E) :=
      le_inf le_sup_right
        (le_trans (neg_nonpos_of_nonneg (abs_nonneg (a : Completion E)))
          (abs_nonneg (a : Completion E)))
    rw [abs_le']
    exact ⟨hf_le, by rwa [neg_le]⟩
  have hfx : f x ∈ C := by
    have hmem : f x ∈ closure C := map_mem_closure hcont hx hmaps
    simpa [C] using hmem
  have hle_abs : y ≤ |x| := (le_abs_self y).trans hy
  have hneg_le : -|x| ≤ y := by
    rw [neg_le]
    exact (neg_le_abs y).trans hy
  have hfx_eq : f x = y := by
    rw [show f x = (y ⊔ -|x|) ⊓ |x| from rfl,
      sup_eq_left.mpr hneg_le, inf_eq_left.mpr hle_abs]
  simpa [C, hfx_eq] using hfx

omit [T2Space E] in
private lemma completion_hasBasis_solid_closure : (𝓝 (0 : Completion E)).HasBasis
    (fun V : Set E => V ∈ 𝓝 (0 : E) ∧ LatticeOrderedAddCommGroup.IsSolid V)
    (fun V => closure (((↑) : E → Completion E) '' V)) := by
  simpa [Completion.coe_zero] using
    (IsLocallySolidVectorLattice.hasBasis_solid (X := E)).hasBasis_of_isDenseInducing
      (Completion.isDenseInducing_coe (α := E))

private lemma real_abs_lt_one_mem_nhds_zero : {r : ℝ | |r| < 1} ∈ 𝓝 (0 : ℝ) := by
  have hI : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩
  exact Filter.mem_of_superset hI fun r hr => by
    simpa [abs_lt] using hr

private lemma smul_mem_solid_closure_image {V : Set E}
    (hV : LatticeOrderedAddCommGroup.IsSolid V) {r : ℝ} (hr : |r| ≤ 1)
    {x : Completion E} (hx : x ∈ closure (((↑) : E → Completion E) '' V)) :
    r • x ∈ closure (((↑) : E → Completion E) '' V) := by
  apply (isSolid_closure_image_coe hV) hx
  rw [abs_smul']
  simpa using smul_le_smul_of_nonneg_right hr (abs_nonneg x)

private lemma tendsto_completion_smul_zero_zero :
    Tendsto (fun p : ℝ × Completion E => p.1 • p.2)
      (𝓝 (0 : ℝ) ×ˢ 𝓝 (0 : Completion E)) (𝓝 (0 : Completion E)) := by
  intro U hU
  change {p : ℝ × Completion E | p.1 • p.2 ∈ U}
    ∈ 𝓝 (0 : ℝ) ×ˢ 𝓝 (0 : Completion E)
  rcases completion_hasBasis_solid_closure.mem_iff.mp hU with ⟨V, hV, hVU⟩
  let C : Set (Completion E) := closure (((↑) : E → Completion E) '' V)
  have hC : C ∈ 𝓝 (0 : Completion E) :=
    completion_hasBasis_solid_closure.mem_iff.mpr ⟨V, hV, subset_rfl⟩
  refine Filter.mem_of_superset
    (Filter.prod_mem_prod real_abs_lt_one_mem_nhds_zero hC) ?_
  rintro ⟨r, x⟩ hx
  exact hVU (smul_mem_solid_closure_image hV.2 (le_of_lt hx.1) hx.2)

private lemma tendsto_completion_smul_left_zero (m : Completion E) :
    Tendsto (fun r : ℝ => r • m) (𝓝 (0 : ℝ)) (𝓝 (0 : Completion E)) := by
  intro U hU
  change {r : ℝ | r • m ∈ U} ∈ 𝓝 (0 : ℝ)
  rcases completion_hasBasis_solid_closure.mem_iff.mp hU with ⟨V, hV, hVU⟩
  let C : Set (Completion E) := closure (((↑) : E → Completion E) '' V)
  have hC : C ∈ 𝓝 (0 : Completion E) :=
    completion_hasBasis_solid_closure.mem_iff.mpr ⟨V, hV, subset_rfl⟩
  rcases exists_open_nhds_zero_add_subset hC with ⟨A, hAopen, hA0, hAA⟩
  rcases completion_hasBasis_solid_closure.mem_iff.mp (hAopen.mem_nhds hA0) with
    ⟨W, hW, hWA⟩
  let D : Set (Completion E) := closure (((↑) : E → Completion E) '' W)
  have hD : D ∈ 𝓝 (0 : Completion E) :=
    completion_hasBasis_solid_closure.mem_iff.mpr ⟨W, hW, subset_rfl⟩
  have hpre : {z : Completion E | m - z ∈ D} ∈ 𝓝 m := by
    have hD' : D ∈ 𝓝 (m - m) := by simpa [sub_self] using hD
    simpa using ((continuous_const.sub continuous_id).tendsto m) hD'
  obtain ⟨a, ha⟩ := (Completion.denseRange_coe (α := E)).mem_nhds hpre
  have haD : {r : ℝ | r • (a : Completion E) ∈ D} ∈ 𝓝 (0 : ℝ) := by
    have hcont : Continuous fun r : ℝ => r • a := continuous_id.smul continuous_const
    have htend : Tendsto (fun r : ℝ => r • a) (𝓝 (0 : ℝ)) (𝓝 (0 : E)) := by
      simpa using hcont.tendsto (0 : ℝ)
    have hpreW : {r : ℝ | r • a ∈ W} ∈ 𝓝 (0 : ℝ) := htend hW.1
    refine Filter.mem_of_superset hpreW ?_
    intro r hr
    change r • (a : Completion E) ∈ D
    rw [← Completion.coe_smul]
    exact subset_closure ⟨r • a, hr, rfl⟩
  refine Filter.mem_of_superset (Filter.inter_mem real_abs_lt_one_mem_nhds_zero haD) ?_
  intro r hr
  have hdiff : r • (m - (a : Completion E)) ∈ D :=
    smul_mem_solid_closure_image hW.2 (le_of_lt hr.1) ha
  have hsum : r • (m - (a : Completion E)) + r • (a : Completion E) ∈ C :=
    hAA ⟨_, hWA hdiff, _, hWA hr.2, rfl⟩
  exact hVU (by simpa [smul_sub] using hsum)

/-- Scalar multiplication is continuous on the topological completion of a Hausdorff locally solid
vector lattice. -/
noncomputable instance instContinuousSMulCompletion : ContinuousSMul ℝ (Completion E) := by
  refine ContinuousSMul.of_nhds_zero tendsto_completion_smul_zero_zero
    tendsto_completion_smul_left_zero ?_
  intro r
  simpa using (continuous_const_smul r).tendsto (0 : Completion E)

/-- The topological completion of a Hausdorff locally solid vector lattice is a locally solid
vector lattice. -/
noncomputable instance instIsLocallySolidVectorLatticeCompletion :
    IsLocallySolidVectorLattice (Completion E) := by
  have hsup : UniformContinuous (fun p : Completion E × Completion E => p.1 ⊔ p.2) := by
    simpa [UniformContinuous₂, Function.uncurry] using
      (Completion.uniformContinuous_map₂ (fun x y : E => x ⊔ y))
  exact (isLocallySolidVectorLattice_iff_uniformContinuous_sup (E := Completion E)).mpr hsup

end Completion

end IsLocallySolidVectorLattice
