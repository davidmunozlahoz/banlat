/-
Authors: David Muñoz-Lahoz
-/

import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Topology.Compactness.CountablyCompact

/-!
# The Eberlein--Smulian theorem

This file proves that compactness and sequential compactness agree for the weak topology of a
normed space.
-/

noncomputable section

open Bornology Filter Function Metric Set Topology

namespace WeakSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private structure ConstructionState (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  points : List (WeakSpace ℝ X)
  functionals : Finset (StrongDual ℝ X)
  norm_functionals : ∀ f ∈ functionals, ‖f‖ < 1

private lemma isBounded_preimage_of_isSeqCompact
    {s : Set (WeakSpace ℝ X)} (hs : IsSeqCompact s) :
    IsBounded ((toWeakSpace ℝ X) ⁻¹' s) := by
  let J : X →L[ℝ] StrongDual ℝ (StrongDual ℝ X) :=
    NormedSpace.inclusionInDoubleDual ℝ X
  obtain ⟨C, hC⟩ :=
    banach_steinhaus (g := fun x : (toWeakSpace ℝ X) ⁻¹' s ↦ J x) fun f ↦ by
    have hseq : IsSeqCompact ((fun x : WeakSpace ℝ X ↦ f ((toWeakSpace ℝ X).symm x)) '' s) :=
      hs.image <| (WeakBilin.eval_continuous (topDualPairing ℝ X).flip f).seqContinuous
    have hcompact : IsCompact
        ((fun x : WeakSpace ℝ X ↦ f ((toWeakSpace ℝ X).symm x)) '' s) :=
      isCompact_iff_isSeqCompact.mpr hseq
    obtain ⟨D, hD⟩ := hcompact.isBounded.exists_norm_le
    refine ⟨D, fun x ↦ ?_⟩
    exact hD _ ⟨toWeakSpace ℝ X x, x.property, rfl⟩
  rw [isBounded_iff_forall_norm_le]
  exact ⟨C, fun x hx ↦ by
    rw [← (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ).norm_map x]
    exact hC ⟨x, hx⟩⟩

private lemma exists_finset_norming_span
    (v : Finset (StrongDual ℝ (StrongDual ℝ X))) :
    ∃ g : Finset (StrongDual ℝ X),
      (∀ f ∈ g, ‖f‖ < 1) ∧
      ∀ y ∈ Submodule.span ℝ (v : Set (StrongDual ℝ (StrongDual ℝ X))),
        ∃ f ∈ g, ‖y‖ / 2 ≤ ‖y f‖ := by
  classical
  let hBnorm : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ X)) := inferInstance
  let hBspace : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ X)) := inferInstance
  let : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ X)) := hBnorm
  let : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ X)) := hBspace
  let F : Submodule ℝ (StrongDual ℝ (StrongDual ℝ X)) :=
    Submodule.span ℝ (v : Set (StrongDual ℝ (StrongDual ℝ X)))
  let : FiniteDimensional ℝ F := FiniteDimensional.span_finset ℝ v
  let : ProperSpace F := FiniteDimensional.proper_real F
  let U : StrongDual ℝ X → Set F := fun f ↦
    {y | 1 / 2 < ‖(y : StrongDual ℝ (StrongDual ℝ X)) f‖}
  have hU_open (f : StrongDual ℝ X) : IsOpen (U f) := by
    exact isOpen_lt continuous_const
      (((ContinuousLinearMap.apply ℝ ℝ f).continuous.comp continuous_subtype_val).norm)
  have hcover : sphere (0 : F) 1 ⊆ ⋃ f ∈ {f : StrongDual ℝ X | ‖f‖ < 1}, U f := by
    intro y hy
    have hy_norm : ‖(y : StrongDual ℝ (StrongDual ℝ X))‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hy
    obtain ⟨f, hf_norm, hf⟩ :=
      (y : StrongDual ℝ (StrongDual ℝ X)).exists_lt_apply_of_lt_opNorm
        (show (1 / 2 : ℝ) < ‖(y : StrongDual ℝ (StrongDual ℝ X))‖ by
          rw [hy_norm]
          norm_num)
    exact mem_iUnion₂.2 ⟨f, hf_norm, hf⟩
  obtain ⟨g, hg_unit, hg_finite, hg_cover⟩ :=
    (isCompact_sphere (0 : F) 1).elim_finite_subcover_image
      (fun f _ ↦ hU_open f) hcover
  let G := hg_finite.toFinset
  refine ⟨(insert 0 G : Finset (StrongDual ℝ X)), ?_, ?_⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · norm_num
    · exact hg_unit (hg_finite.mem_toFinset.mp hf)
  · intro y hy
    by_cases hy0 : y = 0
    · subst y
      refine ⟨0, Finset.mem_insert_self 0 G, ?_⟩
      simp
    let z : F := ⟨‖y‖⁻¹ • y, Submodule.smul_mem _ _ hy⟩
    have hz_sphere : z ∈ sphere (0 : F) 1 := by
      rw [mem_sphere, dist_zero_right]
      change ‖‖y‖⁻¹ • y‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
      exact norm_ne_zero_iff.mpr hy0
    obtain ⟨f, hfG, hzf⟩ := mem_iUnion₂.mp (hg_cover hz_sphere)
    refine ⟨f, Finset.mem_insert_of_mem (hg_finite.mem_toFinset.mpr hfG), ?_⟩
    dsimp [U, z] at hzf
    have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hzf' : 1 / 2 < ‖y‖⁻¹ * ‖y f‖ := by
      simpa [abs_mul, abs_inv, abs_of_nonneg (norm_nonneg y)] using hzf
    have := mul_lt_mul_of_pos_left hzf' hy_pos
    have hlt : ‖y‖ / 2 < ‖y f‖ := by
      simpa [div_eq_mul_inv, hy_pos.ne'] using this
    exact hlt.le

private lemma exists_mem_norm_eval_sub_lt_of_mem_closure
    {s : Set (WeakSpace ℝ X)} {z : WeakDual ℝ (StrongDual ℝ X)}
    (hz : z ∈ closure (NormedSpace.inclusionInDoubleDualWeak ℝ X '' s))
    (g : Finset (StrongDual ℝ X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ s, ∀ f ∈ g, ‖z f - f ((toWeakSpace ℝ X).symm a)‖ < ε := by
  let U : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    {y | ∀ f ∈ g, ‖y f - z f‖ < ε}
  have hU_open : IsOpen U := by
    dsimp only [U]
    rw [show {y : WeakDual ℝ (StrongDual ℝ X) | ∀ f ∈ g, ‖y f - z f‖ < ε} =
        ⋂ f ∈ g, {y | ‖y f - z f‖ < ε} by ext; simp]
    exact isOpen_biInter_finset fun f _ ↦
      isOpen_lt (((WeakBilin.eval_continuous (topDualPairing ℝ (StrongDual ℝ X)) f).sub
        continuous_const).norm) continuous_const
  have hzU : z ∈ U := by
    intro f hf
    simpa using hε
  obtain ⟨y, hyU, hy_image⟩ := mem_closure_iff.mp hz U hU_open hzU
  obtain ⟨a, ha, rfl⟩ := hy_image
  refine ⟨a, ha, fun f hf ↦ ?_⟩
  rw [norm_sub_rev]
  change ‖NormedSpace.inclusionInDoubleDualWeak ℝ X a f - z f‖ < ε
  exact hyU f hf

private lemma exists_next_state
    {s : Set (WeakSpace ℝ X)} {z : WeakDual ℝ (StrongDual ℝ X)}
    (hz : z ∈ closure (NormedSpace.inclusionInDoubleDualWeak ℝ X '' s))
    (q : ConstructionState X) (n : ℕ) :
    ∃ a ∈ s, ∃ q' : ConstructionState X,
      q'.points = q.points ++ [a] ∧
      q.functionals ⊆ q'.functionals ∧
      (∀ y ∈ Submodule.span ℝ
          (insert (WeakDual.toStrongDual z)
            ((fun b ↦
              WeakDual.toStrongDual z - NormedSpace.inclusionInDoubleDual ℝ X
                ((toWeakSpace ℝ X).symm b)) '' {b | b ∈ q.points})),
        ∃ f ∈ q'.functionals, ‖y‖ / 2 ≤ ‖y f‖) ∧
      ∀ f ∈ q'.functionals,
        ‖WeakDual.toStrongDual z f - f ((toWeakSpace ℝ X).symm a)‖ < (n + 1 : ℝ)⁻¹ := by
  classical
  let v : Finset (StrongDual ℝ (StrongDual ℝ X)) :=
    insert (WeakDual.toStrongDual z)
      (q.points.toFinset.image fun b ↦
        WeakDual.toStrongDual z - NormedSpace.inclusionInDoubleDual ℝ X
          ((toWeakSpace ℝ X).symm b))
  obtain ⟨h, hh_norm, hh⟩ := exists_finset_norming_span v
  let g := q.functionals ∪ h
  have hg_norm : ∀ f ∈ g, ‖f‖ < 1 := by
    intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact q.norm_functionals f hf
    · exact hh_norm f hf
  have hε : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨a, ha, ha_approx⟩ := exists_mem_norm_eval_sub_lt_of_mem_closure hz g hε
  let q' : ConstructionState X :=
    { points := q.points ++ [a]
      functionals := g
      norm_functionals := hg_norm }
  refine ⟨a, ha, q', rfl, ?_, ?_, ?_⟩
  · exact Finset.subset_union_left
  · intro y hy
    obtain ⟨f, hfh, hfy⟩ := hh y (by
      simpa only [v, Finset.coe_insert, Finset.coe_image, List.coe_toFinset] using hy)
    exact ⟨f, Finset.mem_union_right _ hfh, hfy⟩
  · simpa only [q', WeakDual.toStrongDual_apply] using ha_approx

private lemma isCompact_of_isSeqCompact
    {s : Set (WeakSpace ℝ X)} (hs : IsSeqCompact s) : IsCompact s := by
  classical
  let hBnorm : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ X)) := inferInstance
  let hBspace : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ X)) := inferInstance
  let : NormedAddCommGroup (StrongDual ℝ (StrongDual ℝ X)) := hBnorm
  let : NormedSpace ℝ (StrongDual ℝ (StrongDual ℝ X)) := hBspace
  let e := NormedSpace.inclusionInDoubleDualWeak ℝ X
  have hb : IsBounded ((toWeakSpace ℝ X) ⁻¹' s) :=
    isBounded_preimage_of_isSeqCompact hs
  have he_closed : IsClosed (e '' s) := by
    apply isClosed_of_closure_subset
    intro z hz
    choose a ha next hnext_points hnext_functionals hnext_norming hnext_approx using
      fun (q : ConstructionState X) (n : ℕ) ↦ exists_next_state hz q n
    let q₀ : ConstructionState X :=
      { points := []
        functionals := ∅
        norm_functionals := by simp }
    let q : ℕ → ConstructionState X := fun n ↦
      Nat.rec q₀ (fun n qn ↦ next qn n) n
    let u : ℕ → WeakSpace ℝ X := fun n ↦ a (q n) n
    have hq_succ (n : ℕ) : q (n + 1) = next (q n) n := by
      simp only [q]
    have hu_mem (n : ℕ) : u n ∈ s := ha (q n) n
    have hq_points (n : ℕ) : (q (n + 1)).points = (q n).points ++ [u n] := by
      rw [hq_succ]
      exact hnext_points (q n) n
    have hq_functionals (n : ℕ) : (q n).functionals ⊆ (q (n + 1)).functionals := by
      rw [hq_succ]
      exact hnext_functionals (q n) n
    have hfunctionals_mono : Monotone fun n ↦ (q n).functionals :=
      monotone_nat_of_le_succ hq_functionals
    have hu_points (n : ℕ) : u n ∈ (q (n + 1)).points := by
      rw [hq_points]
      simp
    let F : ℕ → Submodule ℝ (StrongDual ℝ (StrongDual ℝ X)) := fun n ↦
      Submodule.span ℝ (Set.insert (WeakDual.toStrongDual z)
        ((fun b ↦ WeakDual.toStrongDual z - NormedSpace.inclusionInDoubleDual ℝ X
          ((toWeakSpace ℝ X).symm b)) '' {b | b ∈ (q n).points}))
    have hF_norming (n : ℕ) (y : StrongDual ℝ (StrongDual ℝ X)) (hy : y ∈ F n) :
        ∃ f ∈ (q (n + 1)).functionals, ‖y‖ / 2 ≤ ‖y f‖ := by
      rw [hq_succ]
      exact hnext_norming (q n) n y hy
    have hF_step (n : ℕ) : F n ≤ F (n + 1) := by
      apply Submodule.span_mono
      apply Set.insert_subset_insert
      rintro _ ⟨b, hbq, rfl⟩
      refine ⟨b, ?_, rfl⟩
      change b ∈ (q (n + 1)).points
      rw [hq_points]
      exact List.mem_append_left _ hbq
    have hF_mono : Monotone F := monotone_nat_of_le_succ hF_step
    obtain ⟨xw, hxw, φ, hφ, hφ_lim⟩ := hs hu_mem
    let x : X := (toWeakSpace ℝ X).symm xw
    have hcanonical_eval (n : ℕ) (f : StrongDual ℝ X) (hf : f ∈ (q n).functionals) :
        WeakDual.toStrongDual z f = f x := by
      have hf_eventually : ∀ᶠ k in atTop, f ∈ (q (φ k + 1)).functionals := by
        filter_upwards [hφ.tendsto_atTop.eventually (Ici_mem_atTop n)] with k hk
        exact hfunctionals_mono (hk.trans (Nat.le_succ _)) hf
      have hbound : ∀ᶠ k in atTop,
          ‖f ((toWeakSpace ℝ X).symm (u (φ k))) - WeakDual.toStrongDual z f‖ ≤
            (φ k + 1 : ℝ)⁻¹ := by
        filter_upwards [hf_eventually] with k hk
        rw [norm_sub_rev]
        exact (by
          rw [hq_succ] at hk
          exact (hnext_approx (q (φ k)) (φ k) f hk).le)
      have hinv : Tendsto (fun k ↦ (φ k + 1 : ℝ)⁻¹) atTop (nhds 0) := by
        have h :=
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
        exact h.congr' <| Eventually.of_forall fun k ↦ by
          simp only [Function.comp_apply, one_div]
      have h_to_z : Tendsto
          (fun k ↦ f ((toWeakSpace ℝ X).symm (u (φ k)))) atTop
          (nhds (WeakDual.toStrongDual z f)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hinv
      have h_to_x : Tendsto
          (fun k ↦ f ((toWeakSpace ℝ X).symm (u (φ k)))) atTop (nhds (f x)) := by
        have heval (w : WeakSpace ℝ X) :
            ((topDualPairing ℝ X).flip w) f = f ((toWeakSpace ℝ X).symm w) := rfl
        have h :=
          ((WeakBilin.eval_continuous (topDualPairing ℝ X).flip f).tendsto xw).comp hφ_lim
        have h' : Tendsto (fun k ↦ f ((toWeakSpace ℝ X).symm (u (φ k)))) atTop
            (nhds (((topDualPairing ℝ X).flip xw) f)) :=
          h.congr' <| Eventually.of_forall fun _ ↦ rfl
        simpa only [x, heval] using h'
      exact tendsto_nhds_unique h_to_z h_to_x
    have hx_span : x ∈ closure (Submodule.span ℝ (Set.range fun n ↦
        (toWeakSpace ℝ X).symm (u n)) : Set X) := by
      have hx_weak : xw ∈ closure (toWeakSpace ℝ X ''
          (Submodule.span ℝ (Set.range fun n ↦
            (toWeakSpace ℝ X).symm (u n)) : Set X)) := by
        apply mem_closure_of_tendsto hφ_lim
        filter_upwards with n
        refine ⟨(toWeakSpace ℝ X).symm (u (φ n)), ?_, ?_⟩
        · exact Submodule.subset_span ⟨φ n, rfl⟩
        · exact (toWeakSpace ℝ X).apply_symm_apply _
      rw [← (Submodule.convex _).toWeakSpace_closure ℝ] at hx_weak
      obtain ⟨y, hy, hyx⟩ := hx_weak
      have : y = x := (toWeakSpace ℝ X).injective (by simpa [x] using hyx)
      simpa [this] using hy
    let J : X →L[ℝ] StrongDual ℝ (StrongDual ℝ X) :=
      NormedSpace.inclusionInDoubleDual ℝ X
    let Q : Submodule ℝ (StrongDual ℝ (StrongDual ℝ X)) := ⨆ n, F n
    have hzQ : WeakDual.toStrongDual z ∈ Q := by
      apply Submodule.mem_iSup_of_mem 0
      exact Submodule.subset_span (Set.mem_insert _ _)
    have hdiffQ (n : ℕ) :
        WeakDual.toStrongDual z - J ((toWeakSpace ℝ X).symm (u n)) ∈ Q := by
      apply Submodule.mem_iSup_of_mem (n + 1)
      apply Submodule.subset_span
      apply Set.mem_insert_iff.mpr
      right
      exact ⟨u n, hu_points n, rfl⟩
    have hJ_range (n : ℕ) : J ((toWeakSpace ℝ X).symm (u n)) ∈ Q := by
      have := Q.sub_mem hzQ (hdiffQ n)
      simpa only [sub_sub_cancel] using this
    have hJ_span (y : X)
        (hy : y ∈ Submodule.span ℝ (Set.range fun n ↦
          (toWeakSpace ℝ X).symm (u n))) : J y ∈ Q := by
      have hle : Submodule.span ℝ (Set.range fun n ↦
          (toWeakSpace ℝ X).symm (u n)) ≤ Q.comap J.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨n, rfl⟩
        exact hJ_range n
      exact hle hy
    have hJx_closure : J x ∈ closure (Q : Set (StrongDual ℝ (StrongDual ℝ X))) := by
      apply closure_mono (Set.image_subset_iff.mpr hJ_span)
      exact image_closure_subset_closure_image J.continuous ⟨x, hx_span, rfl⟩
    set y : StrongDual ℝ (StrongDual ℝ X) := WeakDual.toStrongDual z - J x with hy_def
    have hy_closure : y ∈ closure (Q : Set (StrongDual ℝ (StrongDual ℝ X))) := by
      change y ∈ Q.topologicalClosure
      exact Q.topologicalClosure.sub_mem (Q.le_topologicalClosure hzQ) hJx_closure
    have hy_zero : y = 0 := by
      by_contra hy_ne
      have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
      obtain ⟨w, hwQ, hyw⟩ := Metric.mem_closure_iff.mp hy_closure (‖y‖ / 4) (by positivity)
      obtain ⟨n, hwn⟩ :=
        (Submodule.mem_iSup_of_directed F hF_mono.directed_le).mp hwQ
      obtain ⟨f, hfq, hwf⟩ := hF_norming n w hwn
      have hyf : y f = 0 := by
        rw [hy_def]
        dsimp only [J]
        rw [sub_apply, NormedSpace.dual_def,
          hcanonical_eval (n + 1) f hfq, sub_self]
      have hwf_le : ‖w f‖ ≤ ‖w - y‖ := by
        calc
          ‖w f‖ = ‖(w - y) f‖ := by rw [sub_apply, hyf, sub_zero]
          _ ≤ ‖w - y‖ * ‖f‖ := (w - y).le_opNorm f
          _ ≤ ‖w - y‖ * 1 := mul_le_mul_of_nonneg_left
            ((q (n + 1)).norm_functionals f hfq).le (norm_nonneg _)
          _ = ‖w - y‖ := mul_one _
      have hwy : ‖w - y‖ < ‖y‖ / 4 := by
        simpa only [dist_eq_norm, norm_sub_rev] using hyw
      have hy_tri : ‖y‖ ≤ ‖y - w‖ + ‖w‖ := by
        calc
          ‖y‖ = ‖(y - w) + w‖ := congrArg norm (sub_add_cancel y w).symm
          _ ≤ ‖y - w‖ + ‖w‖ := norm_add_le _ _
      have hy_norm : ‖J x - WeakDual.toStrongDual z‖ = ‖y‖ := by
        rw [hy_def, norm_sub_rev]
      have hyw_norm : ‖y - w‖ = ‖w - y‖ := norm_sub_rev _ _
      nlinarith [hy_tri, hy_norm, hyw_norm]
    refine ⟨xw, hxw, ?_⟩
    have hzx : WeakDual.toStrongDual z = J x := by
      rw [hy_def] at hy_zero
      exact sub_eq_zero.mp hy_zero
    apply DFunLike.ext _ _
    intro f
    dsimp only [e]
    calc
      NormedSpace.inclusionInDoubleDualWeak ℝ X xw f =
          f ((toWeakSpace ℝ X).symm xw) :=
        NormedSpace.inclusionInDoubleDualWeak_apply_apply ℝ X xw f
      _ = f x := rfl
      _ = z f := by
        simpa only [J, NormedSpace.dual_def, WeakDual.toStrongDual_apply] using
          DFunLike.congr_fun hzx.symm f
  have hs_closed : IsClosed s := by
    have := he_closed.preimage e.continuous
    rw [Set.preimage_image_eq _
      (NormedSpace.isEmbedding_inclusionInDoubleDualWeak ℝ X).injective] at this
    exact this
  rw [← hs_closed.closure_eq]
  exact NormedSpace.isCompact_closure_of_isBounded ℝ X s hb (by
    rw [he_closed.closure_eq]
    simpa only [e] using Set.image_subset_range e s)

private lemma isSeqCompact_of_isCompact
    {s : Set (WeakSpace ℝ X)} (hs : IsCompact s) : IsSeqCompact s := by
  classical
  intro u hu
  let P : Submodule ℝ X := Submodule.span ℝ
    (Set.range fun n ↦ (toWeakSpace ℝ X).symm (u n))
  let Y : Submodule ℝ X := P.topologicalClosure
  have hY_separable : TopologicalSpace.IsSeparable (Y : Set X) := by
    apply TopologicalSpace.IsSeparable.closure
    apply TopologicalSpace.IsSeparable.span
    exact Set.countable_range _ |>.isSeparable
  let : TopologicalSpace.SeparableSpace Y := hY_separable.separableSpace
  let K : Set (WeakSpace ℝ X) := s ∩ toWeakSpace ℝ X '' (Y : Set X)
  have hY_weak_closed : IsClosed (toWeakSpace ℝ X '' (Y : Set X)) := by
    change IsClosed (toWeakSpace ℝ X '' closure (P : Set X))
    rw [(Submodule.convex P).toWeakSpace_closure ℝ]
    exact isClosed_closure
  have hK_compact : IsCompact K := hs.inter_right hY_weak_closed
  choose f hf using fun n ↦ exists_dual_vector'' ℝ (TopologicalSpace.denseSeq Y n : X)
  let g : ℕ → K → ℝ := fun n x ↦ f n ((toWeakSpace ℝ X).symm x.1)
  have hg_cont (n : ℕ) : Continuous (g n) := by
    exact (WeakBilin.eval_continuous (topDualPairing ℝ X).flip (f n)).comp
      continuous_subtype_val
  have hg_sep : ∀ x y : K, x ≠ y → ∃ n, g n x ≠ g n y := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy' : (toWeakSpace ℝ X).symm x ≠ (toWeakSpace ℝ X).symm y := by
      intro h
      apply hxy
      apply Subtype.ext
      exact (toWeakSpace ℝ X).symm.injective h
    have hxY : (toWeakSpace ℝ X).symm x ∈ Y := by
      obtain ⟨z, hz, hzx⟩ := hx.2
      simpa only [(toWeakSpace ℝ X).injective.eq_iff] using hzx ▸ hz
    have hyY : (toWeakSpace ℝ X).symm y ∈ Y := by
      obtain ⟨z, hz, hzy⟩ := hy.2
      simpa only [(toWeakSpace ℝ X).injective.eq_iff] using hzy ▸ hz
    let d : Y := ⟨(toWeakSpace ℝ X).symm x - (toWeakSpace ℝ X).symm y,
      Y.sub_mem hxY hyY⟩
    have hd_ne : d ≠ 0 := by
      exact Subtype.coe_ne_coe.mp (sub_ne_zero.mpr hxy')
    have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq Y).exists_dist_lt d
      (ε := ‖d‖ / 4) (div_pos hd_pos (by norm_num))
    refine ⟨n, ?_⟩
    intro heq
    have hfd : f n (d : X) = 0 := by
      simpa only [g, d, map_sub, sub_eq_zero] using heq
    have hdn_le : ‖(TopologicalSpace.denseSeq Y n : X)‖ ≤
        ‖(TopologicalSpace.denseSeq Y n : X) - d‖ := by
      have heval_norm : ‖f n (TopologicalSpace.denseSeq Y n : X)‖ =
          ‖(TopologicalSpace.denseSeq Y n : X)‖ := by
        rw [(hf n).2]
        simp
      rw [← heval_norm, ← sub_zero (f n (TopologicalSpace.denseSeq Y n : X)), ← hfd,
        ← map_sub]
      exact ((f n).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hf n).1)
    have hdist : ‖(TopologicalSpace.denseSeq Y n : X) - d‖ < ‖d‖ / 4 := by
      simpa only [dist_eq_norm, norm_sub_rev, ← Submodule.norm_coe, Submodule.coe_sub] using hn
    have hd_tri : ‖d‖ ≤ ‖d - TopologicalSpace.denseSeq Y n‖ +
        ‖(TopologicalSpace.denseSeq Y n : X)‖ := by
      simpa only [sub_add_cancel, ← Submodule.norm_coe, Submodule.coe_sub] using
        norm_add_le (d - TopologicalSpace.denseSeq Y n) (TopologicalSpace.denseSeq Y n)
    have hsub_norm : ‖d - TopologicalSpace.denseSeq Y n‖ =
        ‖(TopologicalSpace.denseSeq Y n : X) - d‖ := by
      change ‖(d : X) - (TopologicalSpace.denseSeq Y n : X)‖ = _
      exact norm_sub_rev _ _
    nlinarith [hd_tri, hsub_norm]
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
  let : TopologicalSpace.MetrizableSpace K :=
    Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
      g hg_cont hg_sep
  let v : ℕ → K := fun n ↦ ⟨u n, hu n, ⟨(toWeakSpace ℝ X).symm (u n),
    P.le_topologicalClosure (Submodule.subset_span ⟨n, rfl⟩),
    (toWeakSpace ℝ X).apply_symm_apply _⟩⟩
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq v
  exact ⟨a.1, a.2.1, φ, hφ, continuous_subtype_val.tendsto a |>.comp hlim⟩

/-- **Eberlein--Smulian theorem**: compactness and sequential compactness agree for subsets of a
normed space equipped with its weak topology. -/
theorem isCompact_iff_isSeqCompact {s : Set (WeakSpace ℝ X)} :
    IsCompact s ↔ IsSeqCompact s :=
  ⟨isSeqCompact_of_isCompact, isCompact_of_isSeqCompact⟩

end WeakSpace
