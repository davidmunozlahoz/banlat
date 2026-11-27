/-
Authors: Alberto Salguero-Alarcón
-/

import BanLat.Examples.CofK.Basic
import BanLat.Operators.Hom
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.TietzeExtension

/-!
# Functionals on real C(K)-spaces

Vector lattice homomorphisms from `C(K, ℝ)` to `ℝ` are non-negative multiples
of point evaluations when `K` is compact Hausdorff.
-/

namespace ContinuousMap

section CofKFunctionals

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private lemma map_one_pos_of_ne_zero (φ : VecLatHom C(K, ℝ) ℝ) (hφ : φ.toLinearMap ≠ 0) :
    0 < φ 1 := by
  refine lt_of_le_of_ne
    (φ.map_nonneg (ContinuousMap.le_def.mpr fun _ ↦ zero_le_one)) ?_
  exact fun h ↦ hφ (LinearMap.ext fun f ↦ abs_eq_zero.mp
    (le_antisymm ((abs_apply_le_norm_mul_one (φ := φ.toLinearMap)
      (fun _ hf ↦ φ.map_nonneg hf) f).trans_eq
      ((congrArg (‖f‖ * ·) h.symm).trans (mul_zero _))) (abs_nonneg _)))

private lemma exists_apply_eq_zero_of_nonneg_of_map_eq_zero
    (φ : VecLatHom C(K, ℝ) ℝ) (hφ : 0 < φ 1)
    (g : C(K, ℝ)) (hg : 0 ≤ g) (hzero : φ g = 0) : ∃ x : K, g x = 0 := by
  by_contra hnone
  obtain ⟨δ, hδ, hbound⟩ := isCompact_univ.exists_forall_le' g.continuous.continuousOn
    (fun x _ ↦ lt_of_le_of_ne (ContinuousMap.le_def.mp hg x)
      (fun hx ↦ hnone ⟨x, hx.symm⟩))
  have hmap := φ.monotone (a := δ • (1 : C(K, ℝ))) (b := g)
    (ContinuousMap.le_def.mpr fun x ↦ by
      simpa only [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
        mul_one] using hbound x (Set.mem_univ x))
  exact (not_le_of_gt (mul_pos hδ hφ))
    (by simpa only [map_smul, smul_eq_mul, hzero] using hmap)

/-- For a nonzero lattice homomorphism `φ : C(K, ℝ) → ℝ` and a finite family
of functions in `C(K, ℝ)`, there exists `x : K` such that `φ f = φ 1 * f x`
for every `f` in the family. -/
private lemma exists_common_evaluation_point (φ : VecLatHom C(K, ℝ) ℝ)
    (hφ : 0 < φ 1) (s : Finset C(K, ℝ)) :
    ∃ x : K, ∀ f ∈ s, φ f = φ 1 * f x := by
  classical
  let g : C(K, ℝ) := ∑ f ∈ s, |φ 1 • f - φ f • 1|
  have hg : 0 ≤ g := Finset.sum_nonneg fun f _ ↦ abs_nonneg _
  have hmap : φ g = 0 := by
    simp only [g, map_sum, φ.map_abs, map_sub, map_smul, smul_eq_mul, mul_comm,
      sub_self, abs_zero, Finset.sum_const_zero]
  obtain ⟨x, hx⟩ := exists_apply_eq_zero_of_nonneg_of_map_eq_zero φ hφ g hg hmap
  refine ⟨x, fun f hf ↦ ?_⟩
  have hle : |φ 1 * f x - φ f| ≤ g x := by
    simpa only [ContinuousMap.abs_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one] using
      ContinuousMap.le_def.mp
        (show |φ 1 • f - φ f • 1| ≤ g from
          Finset.single_le_sum (f := fun j : C(K, ℝ) ↦ |φ 1 • j - φ j • 1|)
            (fun j _ ↦ abs_nonneg _) hf) x
  exact (sub_eq_zero.mp (abs_eq_zero.mp
    (le_antisymm (hle.trans_eq hx) (abs_nonneg _)))).symm

/-- For a nonzero vector lattice homomorphism `φ : C(K, ℝ) → ℝ`, there exists
`x : K` such that `φ f = φ 1 * f x` for all `f : C(K, ℝ)`. -/
private lemma exists_evaluation_point (φ : VecLatHom C(K, ℝ) ℝ) (hφ : 0 < φ 1) :
    ∃ x : K, ∀ f : C(K, ℝ), φ f = φ 1 * f x := by
  obtain ⟨x, hx⟩ := isCompact_univ.inter_iInter_nonempty
    (fun f : C(K, ℝ) ↦ {x : K | φ f = φ 1 * f x})
    (fun f ↦ isClosed_eq continuous_const (continuous_const.mul f.continuous))
    (fun s ↦ by
      obtain ⟨x, hx⟩ := exists_common_evaluation_point φ hφ s
      exact ⟨x, Set.mem_univ x, Set.mem_iInter.mpr fun f ↦
        Set.mem_iInter.mpr fun hf ↦ hx f hf⟩)
  exact ⟨x, fun f ↦ Set.mem_iInter.mp hx.2 f⟩

variable [T2Space K]

/-- A nonzero real-valued vector lattice homomorphism on `C(K, ℝ)` is a
positive multiple of evaluation at a unique point of `K`. -/
theorem existsUnique_eq_mul_eval_of_ne_zero
    (φ : VecLatHom C(K, ℝ) ℝ) (hφ : φ.toLinearMap ≠ 0) :
    0 < φ 1 ∧ ∃! x : K, ∀ f : C(K, ℝ), φ f = φ 1 * f x := by
  have hpos := map_one_pos_of_ne_zero φ hφ
  obtain ⟨x, hx⟩ := exists_evaluation_point φ hpos
  refine ⟨hpos, x, hx, fun y hy ↦ ?_⟩
  by_contra hne
  obtain ⟨f, hf, hneq⟩ := separatesPoints_continuous_of_t35Space hne
  exact hneq (mul_left_cancel₀ hpos.ne'
    ((hy ⟨f, hf⟩).symm.trans (hx ⟨f, hf⟩)))

/-- A unital real-valued vector lattice homomorphism on `C(K, ℝ)` is the evaluation
at a unique point of `K`. -/
theorem existsUnique_eq_eval_of_map_one
    (φ : VecLatHom C(K, ℝ) ℝ) (hφ : φ 1 = 1) :
    ∃! x : K, ∀ f : C(K, ℝ), φ f = f x := by
  simpa only [hφ, one_mul] using
    (existsUnique_eq_mul_eval_of_ne_zero φ (fun h ↦
      one_ne_zero (hφ.symm.trans
        (congrArg (fun f : C(K, ℝ) →ₗ[ℝ] ℝ ↦ f 1) h)))).2

end CofKFunctionals

/-!
# Vector lattice homomorphisms between real C(K)-spaces

For compact Hausdorff spaces `K` and `L`, vector lattice homomorphisms from
`C(K, ℝ)` to `C(L, ℝ)` are characterized by a nonnegative function `h : C(L, ℝ)`
and a continuous map `θ : {h > 0} → K`.
This representation is also used to characterize  injectivity and surjectivity,
and it also yields *Kaplansky's theorem*: `C(K, ℝ)` and `C(L, ℝ)` are lattice
isomorphic precisely when `K` and `L` are homeomorphic.
-/

section CofKHomomorphisms

variable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
  [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

open scoped Topology in
omit [CompactSpace L] [T2Space K] [T2Space L] in
private lemma continuous_weighted_composition (w : C(L, ℝ)) (hw : 0 ≤ w)
    (θ : C({y : L | 0 < w y}, K)) (f : C(K, ℝ))
    [DecidablePred (fun y : L ↦ 0 < w y)] :
    Continuous (fun y : L ↦ if hy : 0 < w y then w y * f (θ ⟨y, hy⟩) else 0) := by
  let g (y : L) : ℝ := if hy : 0 < w y then w y * f (θ ⟨y, hy⟩) else 0
  have hw' := ContinuousMap.le_def.mp hw
  have hg : ContinuousOn g {y | 0 < w y} :=
    continuousOn_iff_continuous_domRestrict.mpr <|
      ((w.continuous.comp continuous_subtype_val).mul (f.continuous.comp θ.continuous)).congr
        (fun y ↦ by
          change w y * f (θ y) = g y
          simp only [g, dite_eq_left (show 0 < w y from y.property)])
  refine continuous_iff_continuousAt.mpr fun y ↦ ?_
  by_cases hy : 0 < w y
  · exact (hg y hy).continuousAt ((isOpen_lt continuous_const w.continuous).mem_nhds hy)
  · have hwy : w y = 0 := le_antisymm (le_of_not_gt hy) (hw' y)
    have hbound : ∀ z, ‖g z‖ ≤ w z * ‖f‖ := fun z ↦ by
      by_cases hz : 0 < w z
      · simpa only [g, dite_eq_left hz, norm_mul, Real.norm_of_nonneg (hw' z)] using
          mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (θ ⟨z, hz⟩)) (hw' z)
      · simpa only [g, dite_eq_right hz, norm_zero] using mul_nonneg (hw' z) (norm_nonneg f)
    have hlim : Filter.Tendsto (fun z ↦ w z * ‖f‖) (𝓝 y) (𝓝 0) := by
      simpa only [ContinuousAt, hwy, zero_mul] using
        (w.continuous.continuousAt (x := y)).mul_const ‖f‖
    simpa only [ContinuousAt, g, dite_eq_right hy] using
      (tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun z ↦ norm_nonneg _) hbound hlim) :
        Filter.Tendsto g (𝓝 y) (𝓝 0))

omit [CompactSpace L] [T2Space K] [T2Space L] in
/-- A nonnegative continuous weight and a continuous map on its positive set induce
a vector lattice homomorphism by weighted composition, taking value zero elsewhere. -/
theorem exists_weighted_composition (w : C(L, ℝ)) (hw : 0 ≤ w)
    (θ : C({y : L | 0 < w y}, K)) :
    ∃ T : VecLatHom C(K, ℝ) C(L, ℝ),
      (∀ (f : C(K, ℝ)) (y : {y : L | 0 < w y}), T f y = w y * f (θ y)) ∧
      (∀ (f : C(K, ℝ)) (y : L), w y = 0 → T f y = 0) := by
  classical
  let A : C(K, ℝ) →ₗ[ℝ] C(L, ℝ) :=
    { toFun := fun f ↦ ⟨_, continuous_weighted_composition w hw θ f⟩
      map_add' := fun f g ↦ ContinuousMap.ext fun y ↦ by
        by_cases hy : 0 < w y <;> simp [hy, mul_add]
      map_smul' := fun c f ↦ ContinuousMap.ext fun y ↦ by
        by_cases hy : 0 < w y <;> simp [hy, smul_eq_mul, mul_left_comm] }
  have habs : ∀ f : C(K, ℝ), A |f| = |A f| := fun f ↦ ContinuousMap.ext fun y ↦ by
    by_cases hy : 0 < w y
    · simp [A, hy, abs_mul, abs_of_nonneg hy.le]
    · simp [A, hy]
  exact ⟨VecLatHom.ofAbs A habs, fun f y ↦ dite_eq_left y.property,
    fun f y hy ↦ dite_eq_right (by simp [hy])⟩

private def evalVecLatHom (y : L) : VecLatHom C(L, ℝ) ℝ :=
  { (evalCLM ℝ y).toLinearMap with
    map_sup' := fun _ _ ↦ rfl
    map_inf' := fun _ _ ↦ rfl }

omit [CompactSpace L] [T2Space K] [T2Space L] in
private lemma apply_eq_zero_of_map_one_eq_zero (T : VecLatHom C(K, ℝ) C(L, ℝ))
    (f : C(K, ℝ)) (y : L) (hy : T 1 y = 0) : T f y = 0 := by
  have hbound := abs_apply_le_norm_mul_one
    (φ := ((evalVecLatHom y).comp T).toLinearMap)
    (fun _ hf ↦ ContinuousMap.le_def.mp (T.map_nonneg hf) y) f
  change |T f y| ≤ ‖f‖ * T 1 y at hbound
  exact abs_eq_zero.mp (le_antisymm
    (by simpa only [hy, mul_zero] using hbound) (abs_nonneg _))

omit [CompactSpace L] [T2Space L] in
private lemma existsUnique_weighted_point (T : VecLatHom C(K, ℝ) C(L, ℝ))
    (y : {y : L | 0 < T 1 y}) :
    ∃! x : K, ∀ f : C(K, ℝ), T f y = T 1 y * f x := by
  exact (existsUnique_eq_mul_eval_of_ne_zero ((evalVecLatHom (y : L)).comp T)
    (fun h ↦ ne_of_gt y.property
      (congrArg (fun l : C(K, ℝ) →ₗ[ℝ] ℝ ↦ l 1) h))).2

private lemma continuous_of_continuous_comp {X : Type*} [TopologicalSpace X]
    (θ : X → K) (hθ : ∀ f : C(K, ℝ), Continuous (fun x ↦ f (θ x))) :
    Continuous θ := by
  have he : Continuous (fun x : K ↦ fun f : C(K, ℝ) ↦ f x) :=
    continuous_pi fun f ↦ f.continuous
  have hi : Function.Injective (fun x : K ↦ fun f : C(K, ℝ) ↦ f x) := fun x y h ↦ by
    by_contra hxy
    obtain ⟨f, hf, hne⟩ := separatesPoints_continuous_of_t35Space hxy
    exact hne (congrFun h ⟨f, hf⟩)
  exact (he.isClosedEmbedding hi).isEmbedding.continuous_iff.mpr (continuous_pi hθ)

omit [CompactSpace L] [T2Space L] in
/-- A vector lattice homomorphism `T : C(K, ℝ) → C(L, ℝ)` can be represented as
the product of the nonnegative weight `T 1` and composition with a continuous map
`θ : {T 1 > 0} → K`. -/
theorem existsUnique_weighted_composition (T : VecLatHom C(K, ℝ) C(L, ℝ)) :
    0 ≤ T 1 ∧
      ∃! θ : C({y : L | 0 < T 1 y}, K),
        (∀ (f : C(K, ℝ)) (y : {y : L | 0 < T 1 y}),
          T f y = T 1 y * f (θ y)) ∧
        (∀ (f : C(K, ℝ)) (y : L), T 1 y = 0 → T f y = 0) := by
  classical
  choose θ hθ huniq using fun y : {y : L | 0 < T 1 y} ↦ existsUnique_weighted_point T y
  have hc : Continuous θ := by
    refine continuous_of_continuous_comp θ fun f ↦ ?_
    have hval : (fun y ↦ f (θ y)) =
        fun y : {y : L | 0 < T 1 y} ↦ T f y / T 1 y :=
      funext fun y ↦ (eq_div_iff y.property.ne').mpr
        ((mul_comm _ _).trans (hθ y f).symm)
    rw [hval]
    exact ((T f).continuous.comp continuous_subtype_val).div
      ((T 1).continuous.comp continuous_subtype_val) (fun y ↦ y.property.ne')
  refine ⟨T.map_nonneg (ContinuousMap.le_def.mpr fun _ ↦ zero_le_one),
    ⟨θ, hc⟩, ⟨fun f y ↦ hθ y f, apply_eq_zero_of_map_one_eq_zero T⟩, ?_⟩
  exact fun ψ hψ ↦ ContinuousMap.ext fun y ↦ huniq y (ψ y) (fun f ↦ hψ.1 f y)

omit [CompactSpace L] [T2Space L] in
/-- A unital vector lattice homomorphism `T : C(K, ℝ) → C(L, ℝ)` is
composition with a unique continuous map `θ : L → K`. -/
theorem existsUnique_composition_of_map_one
    (T : VecLatHom C(K, ℝ) C(L, ℝ)) (hT : T 1 = 1) :
    ∃! θ : C(L, K), ∀ (f : C(K, ℝ)) (y : L), T f y = f (θ y) := by
  classical
  choose θ hθ huniq using fun y : L ↦
    existsUnique_eq_eval_of_map_one ((evalVecLatHom y).comp T)
      (show T 1 y = 1 from congrArg (fun f : C(L, ℝ) ↦ f y) hT)
  have hc : Continuous θ := continuous_of_continuous_comp θ
    (fun f ↦ (T f).continuous.congr (fun y ↦ hθ y f))
  exact ⟨⟨θ, hc⟩, fun f y ↦ hθ y f,
    fun ψ hψ ↦ ContinuousMap.ext fun y ↦ huniq y (ψ y) (fun f ↦ hψ f y)⟩

omit [CompactSpace L] [T2Space K] [T2Space L] in
private lemma map_eq_zero_of_vanishes_on_range (T : VecLatHom C(K, ℝ) C(L, ℝ))
    (θ : C({y : L | 0 < T 1 y}, K))
    (hθ : ∀ (f : C(K, ℝ)) (y : {y : L | 0 < T 1 y}),
      T f y = T 1 y * f (θ y))
    (f : C(K, ℝ)) (hf : ∀ y, f (θ y) = 0) : T f = 0 := by
  ext y
  by_cases hy : 0 < T 1 y
  · simpa only [hf, mul_zero, ContinuousMap.zero_apply] using hθ f ⟨y, hy⟩
  · exact apply_eq_zero_of_map_one_eq_zero T f y (le_antisymm (le_of_not_gt hy)
      (ContinuousMap.le_def.mp
        (T.map_nonneg (ContinuousMap.le_def.mpr fun _ ↦ zero_le_one)) y))

omit [CompactSpace L] [T2Space L] in
private lemma denseRange_of_injective_weighted_composition
    (T : VecLatHom C(K, ℝ) C(L, ℝ)) (θ : C({y : L | 0 < T 1 y}, K))
    (hθ : ∀ (f : C(K, ℝ)) (y : {y : L | 0 < T 1 y}),
      T f y = T 1 y * f (θ y)) (hT : Function.Injective T) : DenseRange θ := by
  by_contra hd
  obtain ⟨x, hx⟩ := not_forall.mp hd
  obtain ⟨f, hf, hxone, _⟩ := exists_continuous_zero_one_of_isClosed
    isClosed_closure (isClosed_singleton : IsClosed ({x} : Set K))
    (Set.disjoint_singleton_right.mpr hx)
  have hz : T f = 0 := map_eq_zero_of_vanishes_on_range T θ hθ f
    (fun y ↦ hf (subset_closure ⟨y, rfl⟩))
  have hfx : f x = 0 := congrArg (fun g : C(K, ℝ) ↦ g x)
    (hT (hz.trans (map_zero T).symm))
  exact zero_ne_one (hfx.symm.trans (hxone (Set.mem_singleton x)))

omit [CompactSpace L] [T2Space L] in
/-- A vector lattice homomorphism `T : C(K, ℝ) → C(L, ℝ)` is injective iff the map
`θ : {T 1 > 0} → K` in its weighted composition representation has dense range. -/
theorem injective_iff_denseRange_of_weighted_composition
    (T : VecLatHom C(K, ℝ) C(L, ℝ)) (θ : C({y : L | 0 < T 1 y}, K))
    (hθ : ∀ (f : C(K, ℝ)) (y : {y : L | 0 < T 1 y}),
      T f y = T 1 y * f (θ y)) :
    Function.Injective T ↔ DenseRange θ := by
  refine ⟨denseRange_of_injective_weighted_composition T θ hθ, fun hd f g hfg ↦ ?_⟩
  apply ContinuousMap.coe_injective
  exact hd.equalizer f.continuous g.continuous (funext fun y ↦
    mul_left_cancel₀ y.property.ne' ((hθ f y).symm.trans
      ((congrArg (fun u : C(L, ℝ) ↦ u y) hfg).trans (hθ g y))))

omit [CompactSpace L] [T2Space K] [T2Space L] in
private lemma map_one_pos_of_surjective (T : VecLatHom C(K, ℝ) C(L, ℝ))
    (hT : Function.Surjective T) (y : L) : 0 < T 1 y := by
  obtain ⟨f, hf⟩ := hT 1
  refine lt_of_le_of_ne (ContinuousMap.le_def.mp
    (T.map_nonneg (ContinuousMap.le_def.mpr fun _ ↦ zero_le_one)) y) ?_
  exact fun hy ↦ zero_ne_one ((apply_eq_zero_of_map_one_eq_zero T f y hy.symm).symm.trans
    (congrArg (fun g : C(L, ℝ) ↦ g y) hf))

omit [CompactSpace K] [T2Space K] in
private lemma injective_of_surjective_weighted_composition
    (T : VecLatHom C(K, ℝ) C(L, ℝ)) (θ : C({y : L | 0 < T 1 y}, K))
    (hθ : ∀ (f : C(K, ℝ)) (y : {y : L | 0 < T 1 y}),
      T f y = T 1 y * f (θ y)) (hT : Function.Surjective T) :
    Function.Injective θ := by
  intro y z hyz
  apply Subtype.ext
  by_contra hne
  obtain ⟨g, hg, hdiff⟩ := separatesPoints_continuous_of_t35Space hne
  obtain ⟨f, hf⟩ := hT (T 1 * (⟨g, hg⟩ : C(L, ℝ)))
  have heq (u : {y : L | 0 < T 1 y}) : f (θ u) = g u :=
    mul_left_cancel₀ u.property.ne' ((hθ f u).symm.trans
      (congrArg (fun q : C(L, ℝ) ↦ q u) hf))
  exact hdiff ((heq y).symm.trans ((congrArg f hyz).trans (heq z)))

omit [T2Space L] in
private lemma surjective_of_weighted_embedding (T : VecLatHom C(K, ℝ) C(L, ℝ))
    (ψ : C(L, K)) (hpos : ∀ y : L, 0 < T 1 y) (hψ : Function.Injective ψ)
    (hform : ∀ (f : C(K, ℝ)) (y : L), T f y = T 1 y * f (ψ y)) :
    Function.Surjective T := by
  intro g
  let q : C(L, ℝ) := ⟨fun y ↦ g y / T 1 y,
    g.continuous.div (T 1).continuous (fun y ↦ (hpos y).ne')⟩
  obtain ⟨f, hf⟩ := q.exists_extension (ψ.continuous.isClosedEmbedding hψ)
  refine ⟨f, ContinuousMap.ext fun y ↦ ?_⟩
  calc
    T f y = T 1 y * f (ψ y) := hform f y
    _ = T 1 y * (g y / T 1 y) :=
      congrArg (T 1 y * ·) (congrArg (fun u : C(L, ℝ) ↦ u y) hf)
    _ = g y := mul_div_cancel₀ _ (hpos y).ne'

/-- A vector lattice homomorphism `T : C(K, ℝ) → C(L, ℝ)` is surjective iff
`T 1` is strictly positive everywhere and the map `θ : {T 1 > 0} → K` in its
weighted composition representation is injective. -/
theorem surjective_iff_pos_and_injective_of_weighted_composition
    (T : VecLatHom C(K, ℝ) C(L, ℝ)) (θ : C({y : L | 0 < T 1 y}, K))
    (hθ : ∀ (f : C(K, ℝ)) (y : {y : L | 0 < T 1 y}),
      T f y = T 1 y * f (θ y)) :
    Function.Surjective T ↔ (∀ y : L, 0 < T 1 y) ∧ Function.Injective θ := by
  refine ⟨fun hT ↦ ⟨map_one_pos_of_surjective T hT,
    injective_of_surjective_weighted_composition T θ hθ hT⟩, ?_⟩
  rintro ⟨hpos, hi⟩
  let ψ : C(L, K) := ⟨fun y ↦ θ ⟨y, hpos y⟩,
    θ.continuous.comp (continuous_id.subtype_mk hpos)⟩
  exact surjective_of_weighted_embedding T ψ hpos
    (fun y z h ↦ congrArg Subtype.val (hi h)) (fun f y ↦ hθ f ⟨y, hpos y⟩)

/-- A vector lattice isomorphism between real C(K)-spaces is a weighted composition
with a homeomorphism and a strictly positive continuous function. -/
theorem exists_homeomorph_weighted_composition (e : VecLatEquiv C(K, ℝ) C(L, ℝ)) :
    ∃ θ : L ≃ₜ K, (∀ y : L, 0 < e 1 y) ∧
      ∀ (f : C(K, ℝ)) (y : L), e f y = e 1 y * f (θ y) := by
  obtain ⟨_, θ, ⟨hθ, _⟩, _⟩ := existsUnique_weighted_composition e.toVecLatHom
  have hpos := map_one_pos_of_surjective e.toVecLatHom e.toLinearEquiv.surjective
  let ψ : C(L, K) := ⟨fun y ↦ θ ⟨y, hpos y⟩,
    θ.continuous.comp (continuous_id.subtype_mk hpos)⟩
  have hi : Function.Injective θ :=
    injective_of_surjective_weighted_composition e.toVecLatHom θ hθ e.toLinearEquiv.surjective
  have hψ : Function.Injective ψ := fun y z h ↦ congrArg Subtype.val (hi h)
  have hd : DenseRange ψ := Dense.mono (s₁ := Set.range θ) (s₂ := Set.range ψ)
    (fun _ ⟨y, hy⟩ ↦ ⟨y.val, hy⟩)
    (denseRange_of_injective_weighted_composition e.toVecLatHom θ hθ e.toLinearEquiv.injective)
  have hs : Function.Surjective ψ := fun x ↦ by
    simpa only [(ψ.continuous.isClosedEmbedding hψ).isClosed_range.closure_eq,
      Set.mem_range] using hd x
  exact ⟨ψ.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ψ ⟨hψ, hs⟩),
    hpos, fun f y ↦ hθ f ⟨y, hpos y⟩⟩

/-- *Kaplansky's theorem*. Two real C(K)-spaces are vector lattice isomorphic precisely
when their underlying compact Hausdorff spaces are homeomorphic. -/
theorem nonempty_homeomorph_iff_nonempty_vecLatEquiv :
    Nonempty (K ≃ₜ L) ↔ Nonempty (VecLatEquiv C(K, ℝ) C(L, ℝ)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨{ e.continuousMapCongr (Homeomorph.refl ℝ) with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }⟩
  · rintro ⟨e⟩
    exact ⟨(exists_homeomorph_weighted_composition e).choose.symm⟩

end CofKHomomorphisms

end ContinuousMap
