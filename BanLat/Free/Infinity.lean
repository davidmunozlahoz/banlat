/-
Authors: Pedro Tradacete
-/

import BanLat.Free.FBLp
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The function representation of the free infinity-convex Banach lattice

For a real normed space `E`, `infinity_representation` identifies the elements of
`FBLp ∞ E` with the positively homogeneous functions `f : E* → ℝ` whose restrictions
to the closed dual unit ball are weak-star continuous. The free infinity-norm is the
supremum norm on that ball. The proof uses two-point interpolation by algebraic free
lattice elements and lattice approximation on the dual unit ball, followed by positive
homogeneity to recover the function on all of `E*`. Completeness of `E` is not required.
-/

noncomputable section

open scoped ENNReal Topology
open Filter Set

universe u

namespace FBLp

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak-star continuity of the restriction of a dual function to the closed dual unit ball.
The domain carries the subspace topology from `WeakDual ℝ E`. -/
def WeakStarContinuousOnBall (f : StrongDual ℝ E → ℝ) : Prop :=
  Continuous (fun φ : FVLv.dualUnitBall E ↦ f (WeakDual.toStrongDual φ.1))

/-- Every function representing an element of `FBLp ∞ E` is positively homogeneous and
weak-star continuous on the closed dual unit ball. These are the necessary conditions
in the function-space characterization at infinity. -/
theorem inFree_infinity_imp (f : StrongDual ℝ E → ℝ)
    (hf : InFree ∞ f) :
    PosHomogeneous f ∧ WeakStarContinuousOnBall f := by
  obtain ⟨g, hg⟩ := hf
  constructor
  · intro a ha φ
    calc
      f (a • φ) = g (a • φ) := (hg _).symm
      _ = a * g φ := g.1.2.1 a ha φ
      _ = a * f φ := by rw [hg]
  · have hc : Continuous (fun ψ : FVLv.dualUnitBall E ↦
        g (WeakDual.toStrongDual ψ.1)) :=
      (weakStar_continuous_bounded ∞ g 1).comp_continuous
        continuous_subtype_val (fun ψ ↦ by
          have hψ := ψ.2
          change WeakDual.toStrongDual ψ.1 ∈
            Metric.closedBall (0 : StrongDual ℝ E) 1 at hψ
          change ‖WeakDual.toStrongDual ψ.1‖ ≤ 1
          simpa only [Metric.mem_closedBall, dist_zero_right] using hψ)
    change Continuous (fun ψ : FVLv.dualUnitBall E ↦
      f (WeakDual.toStrongDual ψ.1))
    convert hc using 1
    funext ψ
    exact (hg _).symm

/-- A positively homogeneous function on the dual `E^*` that is weak-star continuous on the closed
unit ball has finite free infinity-norm and hence belongs to the ambient function lattice. -/
theorem weakStar_homogeneous_mem_finiteNormSublattice_infinity (f : StrongDual ℝ E → ℝ)
    (hhom : PosHomogeneous f) (hcont : WeakStarContinuousOnBall f) :
    f ∈ finiteNormSublattice ∞ E := by
  refine ⟨hhom, ?_⟩
  let g : C(FVLv.dualUnitBall E, ℝ) := ⟨fun ψ ↦ f (WeakDual.toStrongDual ψ.1), hcont⟩
  have hbound (φ : StrongDual ℝ E) (hφ : ‖φ‖ ≤ 1) : |f φ| ≤ ‖g‖ := by
    have hm : WeakDual.toStrongDual (StrongDual.toWeakDual φ) ∈
        Metric.closedBall (0 : StrongDual ℝ E) 1 := by
      change φ ∈ Metric.closedBall (0 : StrongDual ℝ E) 1
      simpa only [Metric.mem_closedBall, dist_zero_right] using hφ
    let ψ : FVLv.dualUnitBall E := ⟨StrongDual.toWeakDual φ, hm⟩
    have h := ContinuousMap.norm_coe_le_norm g ψ
    simpa [g, ψ, Real.norm_eq_abs] using h
  have hle : freeNormExt ∞ f ≤ ENNReal.ofReal ‖g‖ := by
    rw [freeNormExt, if_pos (show (∞ : ℝ≥0∞) = ⊤ by rfl)]
    exact iSup_le fun φ ↦ iSup_le fun hφ ↦ ENNReal.ofReal_le_ofReal (hbound φ hφ)
  exact hle.trans_lt ENNReal.ofReal_lt_top

private lemma relative_sublattice_stone_weierstrass
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (L : Set C(K, ℝ)) (hL : L.Nonempty)
    (hInf : ∀ a ∈ L, ∀ b ∈ L, a ⊓ b ∈ L)
    (hSup : ∀ a ∈ L, ∀ b ∈ L, a ⊔ b ∈ L)
    (f : C(K, ℝ))
    (hInterp : ∀ x y : K, ∃ g ∈ L, g x = f x ∧ g y = f y) :
    f ∈ closure L := by
  refine Filter.Frequently.mem_closure
    ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε hε ↦ ?_)
  simp only [Metric.mem_ball]
  by_cases hK : Nonempty K
  swap
  · exact ⟨hL.some, (ContinuousMap.dist_lt_iff hε).mpr fun x ↦ False.elim (hK ⟨x⟩),
      hL.choose_spec⟩
  choose g hg gx gy using hInterp
  let V : K → K → Set K := fun x y ↦ {z | f z - ε < g x y z}
  have hV (x y : K) : V x y ∈ 𝓝 y := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (f.continuous.sub continuous_const) (g x y).continuous
    · dsimp [V]
      rw [gy]
      linarith
  let ys : K → Finset K := fun x ↦
    (CompactSpace.elim_nhds_subcover (V x) (hV x)).choose
  have hys (x : K) : ⋃ y ∈ ys x, V x y = ⊤ :=
    (CompactSpace.elim_nhds_subcover (V x) (hV x)).choose_spec
  have hys_ne (x : K) : (ys x).Nonempty :=
    Set.nonempty_of_union_eq_top_of_nonempty _ _ hK (hys x)
  let a : K → C(K, ℝ) := fun x ↦ (ys x).sup' (hys_ne x) (g x)
  have haL (x : K) : a x ∈ L := by
    dsimp [a]
    exact Finset.sup'_mem _ hSup _ _ _ (fun y _ ↦ hg x y)
  have halow (x z : K) : f z - ε < a x z := by
    obtain ⟨y, hym, hz⟩ := Set.exists_set_mem_of_union_eq_top _ _ (hys x) z
    dsimp [a]
    simp only [ContinuousMap.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, hym, hz⟩
  have haeq (x : K) : a x x = f x := by
    dsimp [a]
    simp [gx]
  let W : K → Set K := fun x ↦ {z | a x z < f z + ε}
  have hW (x : K) : W x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (a x).continuous (f.continuous.add continuous_const)
    · dsimp [W]
      rw [haeq]
      linarith
  let xs : Finset K := (CompactSpace.elim_nhds_subcover W hW).choose
  have hxs : ⋃ x ∈ xs, W x = ⊤ :=
    (CompactSpace.elim_nhds_subcover W hW).choose_spec
  have hxs_ne : xs.Nonempty :=
    Set.nonempty_of_union_eq_top_of_nonempty _ _ hK hxs
  let b : C(K, ℝ) := xs.inf' hxs_ne a
  have hbL : b ∈ L := by
    dsimp [b]
    exact Finset.inf'_mem _ hInf _ _ _ (fun x _ ↦ haL x)
  refine ⟨b, ?_, hbL⟩
  rw [ContinuousMap.dist_lt_iff hε]
  intro z
  rw [show ∀ c d ε : ℝ, dist c d < ε ↔ c < d + ε ∧ d - ε < c by
    intros; simp only [← Metric.mem_ball, Real.ball_eq_Ioo, Set.mem_Ioo, and_comm]]
  constructor
  · simp only [b, Finset.inf'_lt_iff, ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ hxs z
  · simp only [b, Finset.lt_inf'_iff, ContinuousMap.inf'_apply]
    intro x _
    exact halow x z

private lemma exists_eval_ne_zero (φ : StrongDual ℝ E) (hφ : φ ≠ 0) :
    ∃ x : E, φ x ≠ 0 := by
  by_contra h
  push Not at h
  apply hφ
  ext x
  exact h x

private lemma fvl_two_point_interp (f : StrongDual ℝ E → ℝ) (hhom : PosHomogeneous f)
    (φ ψ : FVLv.dualUnitBall E) :
    ∃ v : FVLv E,
      v φ = f (WeakDual.toStrongDual φ.1) ∧
      v ψ = f (WeakDual.toStrongDual ψ.1) := by
  let φD : StrongDual ℝ E := WeakDual.toStrongDual φ.1
  let ψD : StrongDual ℝ E := WeakDual.toStrongDual ψ.1
  have hfzero : f 0 = 0 := by
    simpa using hhom 0 le_rfl (0 : StrongDual ℝ E)
  by_cases hφ : φD = 0
  · by_cases hψ : ψD = 0
    · refine ⟨0, ?_, ?_⟩ <;> simp [φD, ψD, hφ, hψ, hfzero]
    · obtain ⟨x, hx⟩ := exists_eval_ne_zero ψD hψ
      let v : FVLv E := (f ψD / ψD x) • FVLv.of x
      refine ⟨v, ?_, ?_⟩
      · change (f ψD / ψD x) * φD x = f φD
        simp [hφ, hfzero]
      · change (f ψD / ψD x) * ψD x = f ψD
        field_simp
  · by_cases hψ : ψD = 0
    · obtain ⟨x, hx⟩ := exists_eval_ne_zero φD hφ
      let v : FVLv E := (f φD / φD x) • FVLv.of x
      refine ⟨v, ?_, ?_⟩
      · change (f φD / φD x) * φD x = f φD
        field_simp
      · change (f φD / φD x) * ψD x = f ψD
        simp [hψ, hfzero]
    · obtain ⟨x, hx⟩ := exists_eval_ne_zero φD hφ
      obtain ⟨y, hy⟩ := exists_eval_ne_zero ψD hψ
      let u : FVLv E := |FVLv.of x| + |FVLv.of y|
      have hu (θ : FVLv.dualUnitBall E) :
          u θ = |(WeakDual.toStrongDual θ.1 : StrongDual ℝ E) x| +
            |(WeakDual.toStrongDual θ.1 : StrongDual ℝ E) y| := rfl
      have huφ : 0 < u φ := by
        rw [hu]
        have hx' : 0 < |φD x| := abs_pos.mpr hx
        change 0 < |φD x| + |φD y|
        positivity
      have huψ : 0 < u ψ := by
        rw [hu]
        have hy' : 0 < |ψD y| := abs_pos.mpr hy
        change 0 < |ψD x| + |ψD y|
        positivity
      by_cases hsep : ∃ z : E, φD z * u ψ ≠ ψD z * u φ
      · obtain ⟨z, hz⟩ := hsep
        let d : ℝ := φD z * u ψ - ψD z * u φ
        have hd : d ≠ 0 := sub_ne_zero.mpr hz
        let a : ℝ := (f φD * u ψ - f ψD * u φ) / d
        let b : ℝ := (φD z * f ψD - ψD z * f φD) / d
        let v : FVLv E := a • FVLv.of z + b • u
        refine ⟨v, ?_, ?_⟩
        · change a * φD z + b * u φ = f φD
          dsimp [a, b]
          field_simp [hd]
          dsimp [d] at *
          ring
        · change a * ψD z + b * u ψ = f ψD
          dsimp [a, b]
          field_simp [hd]
          dsimp [d] at *
          ring
      · push Not at hsep
        let c : ℝ := u ψ / u φ
        have hc : 0 ≤ c := by dsimp [c]; positivity
        have hψeq : ψD = c • φD := by
          ext z
          change ψD z = c * φD z
          dsimp [c]
          have hz := hsep z
          field_simp [huφ.ne']
          nlinarith
        let v : FVLv E := (f φD / u φ) • u
        refine ⟨v, ?_, ?_⟩
        · change (f φD / u φ) * u φ = f φD
          field_simp
        · change (f φD / u φ) * u ψ = f ψD
          rw [hψeq, hhom c hc φD]
          dsimp [c]
          field_simp

private def infinityRestriction : FBLp ∞ E →ₗᵢ[ℝ]
    C(FVLv.dualUnitBall E, ℝ) where
  toFun g :=
    ⟨fun ψ ↦ g (WeakDual.toStrongDual ψ.1),
      (inFree_infinity_imp (fun φ ↦ g φ) ⟨g, fun _ ↦ rfl⟩).2⟩
  map_add' := by
    intro g h
    ext ψ
    rfl
  map_smul' := by
    intro c g
    ext ψ
    rfl
  norm_map' := by
    intro g
    apply le_antisymm
    · apply (ContinuousMap.norm_le (f :=
        (⟨fun ψ ↦ g (WeakDual.toStrongDual ψ.1),
          (inFree_infinity_imp (fun φ ↦ g φ) ⟨g, fun _ ↦ rfl⟩).2⟩ :
            C(FVLv.dualUnitBall E, ℝ))) (norm_nonneg g)).2
      intro ψ
      have hψ : ‖WeakDual.toStrongDual ψ.1‖ ≤ 1 := by
        have hm := ψ.2
        change WeakDual.toStrongDual ψ.1 ∈
          Metric.closedBall (0 : StrongDual ℝ E) 1 at hm
        simpa only [Metric.mem_closedBall, dist_zero_right] using hm
      change |g (WeakDual.toStrongDual ψ.1)| ≤ ‖g‖
      exact functionSpace_unit_eval_le ∞ g.1 (WeakDual.toStrongDual ψ.1) hψ
    · change (freeNormExt ∞ g).toReal ≤
        ‖(⟨fun ψ ↦ g (WeakDual.toStrongDual ψ.1),
          (inFree_infinity_imp (fun φ ↦ g φ) ⟨g, fun _ ↦ rfl⟩).2⟩ :
            C(FVLv.dualUnitBall E, ℝ))‖
      apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
      rw [freeNormExt, if_pos (show (∞ : ℝ≥0∞) = ⊤ by rfl)]
      refine iSup_le fun φ ↦ iSup_le fun hφ ↦ ?_
      let ψ : FVLv.dualUnitBall E := ⟨StrongDual.toWeakDual φ, by
        change φ ∈ Metric.closedBall (0 : StrongDual ℝ E) 1
        simpa only [Metric.mem_closedBall, dist_zero_right] using hφ⟩
      have hval := ContinuousMap.norm_coe_le_norm
        (⟨fun ψ ↦ g (WeakDual.toStrongDual ψ.1),
          (inFree_infinity_imp (fun φ ↦ g φ) ⟨g, fun _ ↦ rfl⟩).2⟩ :
            C(FVLv.dualUnitBall E, ℝ)) ψ
      exact ENNReal.ofReal_le_ofReal (by
        simpa [ψ, Real.norm_eq_abs] using hval)

private lemma exists_infinityRestriction_eq (f : StrongDual ℝ E → ℝ)
    (hhom : PosHomogeneous f) (hcont : WeakStarContinuousOnBall f) :
    ∃ g : FBLp ∞ E, infinityRestriction g =
      (⟨fun ψ ↦ f (WeakDual.toStrongDual ψ.1), hcont⟩ : C(FVLv.dualUnitBall E, ℝ)) := by
  let r : FBLp ∞ E →ₗᵢ[ℝ] C(FVLv.dualUnitBall E, ℝ) :=
    infinityRestriction
  let L : Set C(FVLv.dualUnitBall E, ℝ) := Set.range r
  let fBall : C(FVLv.dualUnitBall E, ℝ) :=
    ⟨fun ψ ↦ f (WeakDual.toStrongDual ψ.1), hcont⟩
  have hL : L.Nonempty := ⟨r 0, 0, rfl⟩
  have hInf : ∀ a ∈ L, ∀ b ∈ L, a ⊓ b ∈ L := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨a ⊓ b, ?_⟩
    ext ψ
    rfl
  have hSup : ∀ a ∈ L, ∀ b ∈ L, a ⊔ b ∈ L := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨a ⊔ b, ?_⟩
    ext ψ
    rfl
  have hInterp (ψ χ : FVLv.dualUnitBall E) :
      ∃ g ∈ L, g ψ = fBall ψ ∧ g χ = fBall χ := by
    obtain ⟨v, hvψ, hvχ⟩ := fvl_two_point_interp f hhom ψ χ
    refine ⟨r (ofFVLv ∞ v),
      ⟨ofFVLv ∞ v, rfl⟩, ?_, ?_⟩
    · exact (ofFVLv_apply_ball ∞ v ψ).trans hvψ
    · exact (ofFVLv_apply_ball ∞ v χ).trans hvχ
  have hclosure : fBall ∈ closure L :=
    relative_sublattice_stone_weierstrass L hL hInf hSup fBall hInterp
  have hclosed : IsClosed L :=
    r.isometry.isUniformInducing.isComplete_range.isClosed
  obtain ⟨g, hg⟩ : fBall ∈ L := hclosed.closure_eq ▸ hclosure
  exact ⟨g, hg⟩

private lemma eq_of_infinityRestriction_eq (f : StrongDual ℝ E → ℝ)
    (hhom : PosHomogeneous f) (hcont : WeakStarContinuousOnBall f) (g : FBLp ∞ E)
    (hg : infinityRestriction g =
      (⟨fun ψ ↦ f (WeakDual.toStrongDual ψ.1), hcont⟩ : C(FVLv.dualUnitBall E, ℝ)))
    (φ : StrongDual ℝ E) : g φ = f φ := by
  let ψ := normalizedDual φ
  have hscale : ‖φ‖ • WeakDual.toStrongDual ψ.1 = φ := by
    change ‖φ‖ • (‖φ‖⁻¹ • φ) = φ
    by_cases hφ : φ = 0
    · subst φ
      simp
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hφ), one_smul]
  have hball : g (WeakDual.toStrongDual ψ.1) =
      f (WeakDual.toStrongDual ψ.1) := by
    have h := congrArg (fun a : C(FVLv.dualUnitBall E, ℝ) ↦ a ψ) hg
    exact h
  calc
    g φ = g (‖φ‖ • WeakDual.toStrongDual ψ.1) :=
      congrArg (fun θ ↦ g θ) hscale.symm
    _ = ‖φ‖ * g (WeakDual.toStrongDual ψ.1) :=
      g.1.2.1 ‖φ‖ (norm_nonneg φ) _
    _ = ‖φ‖ * f (WeakDual.toStrongDual ψ.1) := by rw [hball]
    _ = f φ := by rw [← hhom ‖φ‖ (norm_nonneg φ) _, hscale]

/-- The functions representing elements of `FBLp ∞ E` are exactly the positively homogeneous
functions on the dual `E^*` that are weak-star continuous on the closed dual unit ball.
Their free infinity-norm is the supremum norm on that ball. -/
theorem infinity_representation (f : StrongDual ℝ E → ℝ) :
    InFree ∞ f ↔ PosHomogeneous f ∧ WeakStarContinuousOnBall f := by
  constructor
  · exact inFree_infinity_imp f
  · rintro ⟨hhom, hcont⟩
    obtain ⟨g, hg⟩ := exists_infinityRestriction_eq f hhom hcont
    exact ⟨g, eq_of_infinityRestriction_eq f hhom hcont g hg⟩

end FBLp
