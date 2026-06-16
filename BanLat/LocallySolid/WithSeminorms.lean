import BanLat.LocallySolid.LocallyConvexSolid
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Locally convex-solid topologies induced by lattice seminorms

This file introduces lattice seminorms and states the characterization of locally convex-solid
linear topologies as those induced by families of lattice seminorms.
-/

open scoped Topology Pointwise

universe u v

/-- A lattice seminorm on a vector lattice is a seminorm that is monotone with respect to the
lattice absolute value. -/
structure LatticeSeminorm (E : Type u) [AddCommGroup E] [Lattice E]
    [IsOrderedAddMonoid E] [VectorLattice E] extends Seminorm ℝ E where
  /-- Monotonicity with respect to the lattice absolute value. -/
  monotone_abs' : ∀ {x y : E}, |x| ≤ |y| → toSeminorm x ≤ toSeminorm y

namespace LatticeSeminorm

variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]

/-- The underlying seminorm family of a lattice seminorm family. -/
abbrev toSeminormFamily {ι : Type v} (p : ι → LatticeSeminorm E) : SeminormFamily ℝ E ι :=
  fun i => (p i).toSeminorm

private lemma finset_sup_mono_abs {ι : Type v} (p : ι → LatticeSeminorm E) (I : Finset ι)
    {x y : E} (hxy : |x| ≤ |y|) :
    I.sup (toSeminormFamily p) x ≤ I.sup (toSeminormFamily p) y := by
  refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi => ?_
  exact (p i).monotone_abs' hxy |>.trans
    (Seminorm.le_finset_sup_apply (p := toSeminormFamily p) (s := I) (x := y) hi)

/-- Every basis set of the seminorm family associated to a family of lattice seminorms is solid. -/
theorem isSolid_of_mem_basisSets {ι : Type v} (p : ι → LatticeSeminorm E) {s : Set E}
    (hs : s ∈ (toSeminormFamily p).basisSets) : LatticeOrderedAddCommGroup.IsSolid s := by
  rcases (SeminormFamily.basisSets_iff (p := toSeminormFamily p)).mp hs with ⟨I, r, hr, rfl⟩
  intro x hx y hy
  rw [Seminorm.mem_ball_zero] at hx ⊢
  exact (finset_sup_mono_abs p I hy).trans_lt hx

end LatticeSeminorm

namespace IsLocallyConvexSolidVectorLattice

variable {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

private abbrev ConvexSolidNhd : Type u :=
  { s : Set E // s ∈ 𝓝 (0 : E) ∧ Convex ℝ s ∧ LatticeOrderedAddCommGroup.IsSolid s }

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
private lemma balanced_of_solid {s : Set E}
    (hsolid : LatticeOrderedAddCommGroup.IsSolid s) : Balanced ℝ s := by
  rw [balanced_iff_smul_mem]
  intro a ha x hx
  apply hsolid hx
  rw [abs_smul']
  have ha' : |a| ≤ 1 := by rwa [Real.norm_eq_abs] at ha
  calc
    |a| • |x| ≤ (1 : ℝ) • |x| := smul_le_smul_of_nonneg_right ha' (abs_nonneg x)
    _ = |x| := one_smul ℝ |x|

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
private lemma gauge_mono_abs_of_solid {s : Set E} (hs : Absorbent ℝ s)
    (hsolid : LatticeOrderedAddCommGroup.IsSolid s) {x y : E} (hxy : |x| ≤ |y|) :
    gauge s x ≤ gauge s y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases exists_lt_of_gauge_lt hs (lt_add_of_pos_right (gauge s y) hε) with
    ⟨r, hr0, hrg, hy⟩
  have hy' : r⁻¹ • y ∈ s := by
    exact (Set.mem_smul_set_iff_inv_smul_mem₀ hr0.ne' s y).mp hy
  have hscaled : |r⁻¹ • x| ≤ |r⁻¹ • y| := by
    rw [abs_smul', abs_smul']
    exact smul_le_smul_of_nonneg_left hxy (abs_nonneg r⁻¹)
  have hx' : r⁻¹ • x ∈ s := hsolid hy' hscaled
  have hx : x ∈ r • s := by
    exact (Set.mem_smul_set_iff_inv_smul_mem₀ hr0.ne' s x).mpr hx'
  exact (gauge_le_of_mem hr0.le hx).trans hrg.le

private noncomputable def convexSolidNhdGaugeLatticeSeminorm (s : ConvexSolidNhd (E := E)) :
    LatticeSeminorm E where
  toSeminorm :=
    gaugeSeminorm
      (balanced_of_solid s.2.2.2) s.2.2.1 (absorbent_nhds_zero s.2.1)
  monotone_abs' := by
    intro x y hxy
    simpa [gaugeSeminorm_toFun] using
      gauge_mono_abs_of_solid (absorbent_nhds_zero s.2.1) s.2.2.2 hxy

private lemma continuous_convexSolidNhdGaugeLatticeSeminorm (s : ConvexSolidNhd (E := E)) :
    Continuous (convexSolidNhdGaugeLatticeSeminorm s).toSeminorm := by
  simpa [convexSolidNhdGaugeLatticeSeminorm, gaugeSeminorm_toFun] using
    continuous_gauge s.2.2.1 s.2.1

private theorem with_convexSolidNhdGaugeSeminormFamily [IsLocallyConvexSolidVectorLattice E] :
    WithSeminorms
      (LatticeSeminorm.toSeminormFamily
        (convexSolidNhdGaugeLatticeSeminorm (E := E))) := by
  let p : ConvexSolidNhd (E := E) → LatticeSeminorm E :=
    convexSolidNhdGaugeLatticeSeminorm
  change WithSeminorms (LatticeSeminorm.toSeminormFamily p)
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (IsLocallyConvexSolidVectorLattice.hasBasis_convex_solid (E := E)).to_hasBasis ?_ ?_
  · rintro U ⟨hU_nhds, hU_convex, hU_solid⟩
    let S : ConvexSolidNhd (E := E) := ⟨U, hU_nhds, hU_convex, hU_solid⟩
    refine ⟨(p S).toSeminorm.ball 0 1, ?_, ?_⟩
    · exact (LatticeSeminorm.toSeminormFamily p).basisSets_singleton_mem S one_pos
    · intro x hx
      change x ∈ (p S).toSeminorm.ball 0 1 at hx
      change x ∈ U
      rw [Seminorm.mem_ball_zero] at hx
      apply gauge_lt_one_subset_self hU_convex (mem_of_mem_nhds hU_nhds)
        (absorbent_nhds_zero hU_nhds)
      simpa [p, S, convexSolidNhdGaugeLatticeSeminorm, gaugeSeminorm_toFun] using hx
  · intro U hU
    have hU_nhds : U ∈ 𝓝 (0 : E) :=
      SeminormFamily.basisSets_mem_nhds (LatticeSeminorm.toSeminormFamily p)
        (fun S => continuous_convexSolidNhdGaugeLatticeSeminorm S) U hU
    have hU_convex : Convex ℝ U := by
      rcases (SeminormFamily.basisSets_iff
        (p := LatticeSeminorm.toSeminormFamily p)).mp hU with ⟨I, r, hr, rfl⟩
      exact Seminorm.convex_ball _ _ _
    have hU_solid : LatticeOrderedAddCommGroup.IsSolid U :=
      LatticeSeminorm.isSolid_of_mem_basisSets p hU
    exact ⟨U, ⟨hU_nhds, hU_convex, hU_solid⟩, rfl.subset⟩

end IsLocallyConvexSolidVectorLattice

/-- A family of lattice seminorms induces the given topology when the underlying seminorm family
induces it in the sense of `WithSeminorms`. -/
def WithLatticeSeminorms {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
    [VectorLattice E] [TopologicalSpace E] {ι : Type v} (p : ι → LatticeSeminorm E) : Prop :=
  WithSeminorms (LatticeSeminorm.toSeminormFamily p)

/-- A linear topology on a vector lattice is locally convex-solid iff it is induced by a family of
lattice seminorms. -/
theorem isLocallyConvexSolidVectorLattice_iff_exists_withLatticeSeminorms
    {E : Type u} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
    [TopologicalSpace E] :
    IsLocallyConvexSolidVectorLattice E ↔
      ∃ (ι : Type u) (p : ι → LatticeSeminorm E), WithLatticeSeminorms p := by
  constructor
  · intro h
    letI : IsLocallyConvexSolidVectorLattice E := h
    exact
      ⟨IsLocallyConvexSolidVectorLattice.ConvexSolidNhd (E := E),
        IsLocallyConvexSolidVectorLattice.convexSolidNhdGaugeLatticeSeminorm (E := E),
        IsLocallyConvexSolidVectorLattice.with_convexSolidNhdGaugeSeminormFamily (E := E)⟩
  · rintro ⟨ι, p, hp⟩
    have hTopAdd : IsTopologicalAddGroup E := hp.topologicalAddGroup
    have hSMul : ContinuousSMul ℝ E := hp.continuousSMul
    letI : IsTopologicalAddGroup E := hTopAdd
    letI : ContinuousSMul ℝ E := hSMul
    have hLocalSolid : IsLocallySolidVectorLattice E := by
      refine { hasBasis_solid := ?_ }
      refine hp.hasBasis.to_hasBasis ?_ ?_
      · intro U hU
        refine ⟨U, ⟨?_, LatticeSeminorm.isSolid_of_mem_basisSets p hU⟩, rfl.subset⟩
        exact hp.hasBasis.mem_iff.mpr ⟨U, hU, rfl.subset⟩
      · intro U hU
        rcases hp.hasBasis.mem_iff.mp hU.1 with ⟨V, hV, hVU⟩
        exact ⟨V, hV, hVU⟩
    exact
      { toIsLocallySolidVectorLattice := hLocalSolid
        toLocallyConvexSpace := hp.toLocallyConvexSpace }
