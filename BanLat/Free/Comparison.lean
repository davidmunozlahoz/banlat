/-
Authors: Pedro Tradacete
-/

import BanLat.Free.FBLp

/-!
# Comparison of free p-convex Banach lattices

For a real normed space `E` and exponents `1 ≤ p ≤ q ≤ ∞`, the free lattice `FBLp q E`
is p-convex with constant one. The universal property therefore gives a canonical
continuous lattice homomorphism `inclusion hpq : FBLp p E →L[ℝ] FBLp q E` extending
the identity on the generating space `E`. This map is contractive and injective,
has norm-dense range, and leaves the underlying functions on the continuous dual
unchanged. It also identifies the two copies of the algebraic free vector lattice,
on which the free norms decrease as the exponent increases. These maps compare
the free lattices at different exponents within their common representation as functions
on the dual space. -/

noncomputable section

open scoped ENNReal Topology
open Filter Set

universe u v

namespace FBLp

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

private lemma realLp_finset_sum_le {ι κ : Type*}
    [Fintype κ] {r : ℝ} (hr : 1 ≤ r) (s : Finset ι)
    (a : ι → κ → ℝ) (ha : ∀ i ∈ s, ∀ j, 0 ≤ a i j) :
    (∑ j, (∑ i ∈ s, a i j) ^ r) ^ (1 / r) ≤
      ∑ i ∈ s, (∑ j, a i j ^ r) ^ (1 / r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    simp [Real.zero_rpow hrpos.ne', Real.zero_rpow (inv_ne_zero hrpos.ne')]
  | @insert i s his ih =>
    have hai : ∀ j, 0 ≤ a i j := fun j ↦ ha i (Finset.mem_insert_self ..) j
    have has : ∀ k ∈ s, ∀ j, 0 ≤ a k j := by
      intro k hk j
      exact ha k (Finset.mem_insert_of_mem hk) j
    simp only [Finset.sum_insert his]
    calc
      (∑ j, (a i j + ∑ k ∈ s, a k j) ^ r) ^ (1 / r) ≤
          (∑ j, a i j ^ r) ^ (1 / r) +
            (∑ j, (∑ k ∈ s, a k j) ^ r) ^ (1 / r) :=
        Real.Lp_add_le_of_nonneg Finset.univ hr
          (by intro j hj; exact hai j)
          (by intro j hj; exact Finset.sum_nonneg fun k hk ↦ has k hk j)
      _ ≤ (∑ j, a i j ^ r) ^ (1 / r) +
            ∑ k ∈ s, (∑ j, a k j ^ r) ^ (1 / r) := by
        gcongr
        exact ih has

private lemma realMixedPSum_mono {n m : ℕ} {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) (a : Fin n → Fin m → ℝ) :
    (∑ j, ((∑ i, |a i j| ^ p) ^ (1 / p)) ^ q) ^ (1 / q) ≤
      (∑ i, ((∑ j, |a i j| ^ q) ^ (1 / q)) ^ p) ^ (1 / p) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  let r : ℝ := q / p
  have hr : 1 ≤ r := (one_le_div hp).mpr hpq
  let b : Fin n → Fin m → ℝ := fun i j ↦ |a i j| ^ p
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j, 0 ≤ b i j := by
    intro i hi j
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hMink := realLp_finset_sum_le hr Finset.univ b hb
  have hMLnonneg : 0 ≤ (∑ j, (∑ i ∈ Finset.univ, b i j) ^ r) ^ (1 / r) := by
    apply Real.rpow_nonneg
    exact Finset.sum_nonneg fun j hj ↦
      Real.rpow_nonneg (Finset.sum_nonneg fun i hi ↦ hb i hi j) _
  have hpow := Real.rpow_le_rpow hMLnonneg hMink (one_div_nonneg.mpr hp.le)
  convert hpow using 1
  · have hterm (j : Fin m) : ((∑ i, |a i j| ^ p) ^ (1 / p)) ^ q =
        (∑ i, b i j) ^ r := by
      change ((∑ i, |a i j| ^ p) ^ (1 / p)) ^ q =
        (∑ i, |a i j| ^ p) ^ r
      rw [← Real.rpow_mul (Finset.sum_nonneg fun i hi ↦
        Real.rpow_nonneg (abs_nonneg _) _)]
      congr 1
      dsimp [r]
      field_simp
    simp_rw [hterm]
    rw [← Real.rpow_mul (Finset.sum_nonneg fun j hj ↦
      Real.rpow_nonneg (Finset.sum_nonneg fun i hi ↦ hb i hi j) _)]
    congr 1
    dsimp [r]
    field_simp
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hinner : (∑ j, b i j ^ r) = ∑ j, |a i j| ^ q := by
      apply Finset.sum_congr rfl
      intro j hj
      change (|a i j| ^ p) ^ r = |a i j| ^ q
      rw [← Real.rpow_mul (abs_nonneg _)]
      congr 1
      dsimp [r]
      field_simp
    rw [hinner]
    rw [← Real.rpow_mul (Finset.sum_nonneg fun j hj ↦
      Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    dsimp [r]
    field_simp

private lemma norm_mixed_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q < ∞) {n m : ℕ} (a : Fin n → Fin m → ℝ) :
    ‖WithLp.toLp q (fun j ↦ ‖WithLp.toLp p (fun i ↦ a i j)‖)‖ ≤
      ‖WithLp.toLp p (fun i ↦ ‖WithLp.toLp q (fun j ↦ a i j)‖)‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out))
    (ne_of_lt (hpq.trans_lt hq))
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out))
    (ne_of_lt hq)
  simpa only [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hq0, Real.norm_eq_abs,
    PiLp.toLp_apply, abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦
      Real.rpow_nonneg (abs_nonneg _) _) _)] using
    realMixedPSum_mono hp0 (ENNReal.toReal_mono (ne_of_lt hq) hpq) a

/-- The free lattice at infinity satisfies the p-convexity estimate with constant one
for every `1 ≤ p ≤ ∞`, using its supremum norm on the closed dual unit ball. -/
theorem convexWith_infinity :
    ConvexWith p 1 (ContinuousLinearMap.id ℝ (FBLp ∞ E)) := by
  refine ⟨zero_le_one, fun n f ↦ ?_⟩
  change (freeNormExt ∞ (latticePSum p f : FBLp ∞ E).1.1).toReal ≤
    1 * ‖WithLp.toLp p (fun i ↦ ‖f i‖)‖
  rw [one_mul]
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
  rw [freeNormExt, if_pos rfl]
  refine iSup_le fun φ ↦ iSup_le fun hφ ↦ ENNReal.ofReal_le_ofReal ?_
  rw [latticePSum_apply, abs_of_nonneg (norm_nonneg _)]
  apply norm_le_norm_of_abs_le_abs
  intro i
  change |f i φ| ≤ |‖f i‖|
  rw [abs_norm]
  exact functionSpace_unit_eval_le ∞ (f i).1 φ hφ

/-- If `1 ≤ p ≤ q ≤ ∞`, the identity on `FBLp q E` satisfies the p-convexity estimate
with constant one. This allows the universal property at `p` to target the free lattice at `q`. -/
theorem convexWith_of_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) : ConvexWith p 1 (ContinuousLinearMap.id ℝ (FBLp q E)) := by
  by_cases hq : q = ∞
  · subst q
    exact convexWith_infinity p
  refine ⟨zero_le_one, fun n f ↦ ?_⟩
  change (freeNormExt q (latticePSum p f : FBLp q E).1.1).toReal ≤
    1 * ‖WithLp.toLp p (fun i ↦ ‖f i‖)‖
  rw [one_mul]
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
  rw [freeNormExt, if_neg hq]
  refine iSup_le fun m ↦ iSup_le fun φ ↦ iSup_le fun hφ ↦ ENNReal.ofReal_le_ofReal ?_
  simp_rw [latticePSum_apply]
  refine (norm_mixed_le hpq (lt_top_iff_ne_top.mpr hq) _).trans ?_
  apply norm_le_norm_of_abs_le_abs
  intro i
  change |‖WithLp.toLp q (fun j ↦ f i (φ j))‖| ≤ |‖f i‖|
  rw [abs_norm, abs_norm]
  exact functionSpace_admissible_eval_le q hq (f i).1 φ hφ

private lemma exists_inclusion {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) :
    ∃ L : FBLp p E →L[ℝ] FBLp q E, IsVecLatHom L ∧
      (∀ x, L (of p x) = of q x) ∧ ‖L‖ ≤ 1 := by
  obtain ⟨L, hlat, hgen, hnorm, _⟩ := universal_property_of_fvl_bound p
    (of q (E := E)).toContinuousLinearMap 1 zero_le_one (fun v ↦
      (fvl_lift_pConvex_norm_le p (convexWith_of_le hpq)
        (of q).toContinuousLinearMap v).trans
          (mul_le_mul_of_nonneg_right
            (by simpa using (of q (E := E)).norm_toContinuousLinearMap_le)
            (norm_nonneg _)))
  exact ⟨L, hlat, hgen, hnorm⟩

/-- The canonical continuous linear map `FBLp p E → FBLp q E` for `p ≤ q`, extending
the identity on the generating space. It is a contractive lattice homomorphism and,
in the dual-function models, sends each function to itself. -/
def inclusion {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) :
    FBLp p E →L[ℝ] FBLp q E :=
  (exists_inclusion (E := E) hpq).choose

/-- The canonical map between exponents preserves suprema and infima as well as the
linear operations, so it is a vector lattice homomorphism. -/
theorem inclusion_isVecLatHom {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) : IsVecLatHom (inclusion (E := E) hpq) :=
  (exists_inclusion (E := E) hpq).choose_spec.1

/-- The canonical map sends the evaluation generator `of p x` to `of q x`.
It therefore extends the identity between the two canonical copies of `E`. -/
@[simp] theorem inclusion_of {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (x : E) : inclusion hpq (of p x) = of q x :=
  (exists_inclusion (E := E) hpq).choose_spec.2.1 x

/-- The operator norm of the canonical map from exponent `p` to exponent `q ≥ p`
is at most one, so passage to the larger exponent cannot increase the norm. -/
theorem norm_inclusion_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) : ‖inclusion (E := E) hpq‖ ≤ 1 :=
  (exists_inclusion (E := E) hpq).choose_spec.2.2

/-- The canonical map intertwines the embeddings of `FVLv E` at the two exponents.
Thus every algebraic vector lattice expression in generators represents the same
element after applying the map. -/
@[simp] theorem inclusion_ofFVLv {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (v : FVLv E) : inclusion hpq (ofFVLv p v) = ofFVLv q v := by
  have h : (VecLatHom.ofIsVecLatHom (inclusion hpq) (inclusion_isVecLatHom hpq)).comp
      (ofFVLv p (E := E)) = ofFVLv q := FVLv.hom_ext (fun x ↦ by
        change inclusion hpq (ofFVLv p (FVLv.of x)) = ofFVLv q (FVLv.of x)
        rw [ofFVLv_of, ofFVLv_of, inclusion_of])
  exact DFunLike.congr_fun h v

/-- For every dual functional `φ`, the image of `f` under the canonical map has value `f φ`.
Consequently, the map identifies free lattice elements with the same underlying dual function. -/
@[simp] theorem inclusion_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (f : FBLp p E) (φ : StrongDual ℝ E) : inclusion hpq f φ = f φ := by
  have hleft : Continuous (fun g : FBLp p E ↦ inclusion hpq g φ) :=
    ((functionSpaceEvaluation q φ).continuous.comp continuous_subtype_val).comp
      (inclusion hpq).continuous
  have hright : Continuous (fun g : FBLp p E ↦ g φ) :=
    (functionSpaceEvaluation p φ).continuous.comp continuous_subtype_val
  exact congrFun ((denseRange_ofFVLv p).equalizer hleft hright (by
    funext v
    change inclusion hpq (ofFVLv p v) φ = ofFVLv p v φ
    rw [inclusion_ofFVLv]
    rfl)) f

/-- The canonical map from `FBLp p E` to `FBLp q E` is injective:
equality of the images forces equality of their values at every dual functional. -/
theorem inclusion_injective {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) : Function.Injective (inclusion (E := E) hpq) := by
  intro f g h
  apply Subtype.ext ∘ Subtype.ext
  funext φ
  simpa only [inclusion_apply] using congrArg (fun k : FBLp q E ↦ k φ) h

/-- The range of the canonical map is dense in `FBLp q E` for the free q-norm.
It contains the canonical image of the algebraic free vector lattice in the target. -/
theorem denseRange_inclusion {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) : DenseRange (inclusion (E := E) hpq) := by
  exact Dense.mono (s₁ := Set.range (ofFVLv q (E := E)))
    (fun _ ⟨v, hv⟩ ↦ ⟨ofFVLv p v, (inclusion_ofFVLv hpq v).trans hv⟩)
    (denseRange_ofFVLv q)

/-- For `v : FVLv E` and `p ≤ q`, its free q-norm is at most its free p-norm:
`‖ofFVLv q v‖ ≤ ‖ofFVLv p v‖`. This compares the norms on the common algebraic model. -/
theorem norm_ofFVLv_mono {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (v : FVLv E) : ‖ofFVLv q v‖ ≤ ‖ofFVLv p v‖ := by
  rw [← inclusion_ofFVLv hpq v]
  simpa only [one_mul] using
    (inclusion hpq).le_of_opNorm_le (norm_inclusion_le hpq) (ofFVLv p v)

end FBLp
