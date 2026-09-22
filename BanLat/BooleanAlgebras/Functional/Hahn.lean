/-
Authors: Jesús Illescas-Fiorito
-/

import BanLat.BooleanAlgebras.Functional.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Hahn decomposition for Boolean-algebra functionals

This file proves the **Hahn decomposition theorem:**

for any pair `(μ, ν)` of finite countably additive functionals on a `σ`-complete Boolean
algebra `B` there exists a *Hahn decomposition*, that is, an element `p ∈ B`
such that:
* if `b ≤ p`, then `μ(b) ≤ ν(b)`.
* if `b ⟂ p`, then `ν(b) ≤ μ(b)`.
-/

open Filter Topology
open scoped ENNReal

universe u

namespace CountablyAdditiveFunctional

variable {B : Type u} [SigmaCompleteBooleanAlgebra B]

/-- `p ∈ B` is a Hahn decomposition for `(μ, ν)` if `b ≤ p → μ(b) ≤ ν(b)` and
`b ⟂ p → ν(b) ≤ μ(b)`. -/
structure IsHahnDecomposition
    (μ ν : CountablyAdditiveFunctional B) (p : B) : Prop where
  le_on : ∀ ⦃b : B⦄, b ≤ p → μ b ≤ ν b
  ge_on_compl : ∀ ⦃b : B⦄, Disjoint b p → ν b ≤ μ b

/-- If `p` is a Hahn decomposition for `(μ, ν)`, `pᶜ` is a Hahn decomposition
for `(ν, μ)`. -/
theorem IsHahnDecomposition.compl {μ ν : CountablyAdditiveFunctional B} {p : B}
    (h : IsHahnDecomposition μ ν p) :
    IsHahnDecomposition ν μ pᶜ := by
  constructor
  · intro b hb
    exact h.ge_on_compl (le_compl_iff_disjoint_right.mp hb)
  · intro b hb
    exact h.le_on (disjoint_compl_right_iff.mp hb)

/-- For any finite non-negative countably additive functionals `(μ, ν)`, there exists
`p ∈ B` such that `ν(b)-μ(b) ≤ ν(p)-μ(p)` for all `b ∈ B`. -/
private lemma exists_forall_toReal_sub_le
    (μ ν : CountablyAdditiveFunctional B) (hμ : μ.IsFinite) (hν : ν.IsFinite) :
    ∃ p : B, ∀ b : B,
      (ν b).toReal - (μ b).toReal ≤ (ν p).toReal - (μ p).toReal := by
  let d : B → ℝ := fun b ↦ (ν b).toReal - (μ b).toReal
  let c : Set ℝ := Set.range d
  let γ : ℝ := sSup c
  have d_split (a b : B) : d a = d (a \ b) + d (a ⊓ b) := by
    dsimp only [d]
    rw [← ν.map_sdiff_add_inf a b, ← μ.map_sdiff_add_inf a b,
      ENNReal.toReal_add (ν.ne_top hν _) (ν.ne_top hν _),
      ENNReal.toReal_add (μ.ne_top hμ _) (μ.ne_top hμ _)]
    ring
  have d_iSup (a : ℕ → B) (ha : Monotone a) :
      Tendsto (fun n ↦ d (a n)) atTop (𝓝 (d (⨆ n, a n))) := by
    refine Tendsto.sub ?_ ?_
    · exact (ENNReal.tendsto_toReal (ν.ne_top hν _)).comp (ν.tendsto_map_iSup ha)
    · exact (ENNReal.tendsto_toReal (μ.ne_top hμ _)).comp (μ.tendsto_map_iSup ha)
  have d_iInf (a : ℕ → B) (ha : Antitone a) :
      Tendsto (fun n ↦ d (a n)) atTop
        (𝓝 (d (SigmaCompleteBooleanAlgebra.iInfNat a))) := by
    have hvalue (ρ : CountablyAdditiveFunctional B) (hρ : ρ.IsFinite) (b : B) :
        (ρ b).toReal = (ρ ⊤).toReal - (ρ bᶜ).toReal := by
      have h := congrArg ENNReal.toReal (ρ.map_sup (disjoint_compl_right : Disjoint b bᶜ))
      rw [sup_compl_eq_top, ENNReal.toReal_add (ρ.ne_top hρ b) (ρ.ne_top hρ bᶜ)] at h
      linarith
    have ht (ρ : CountablyAdditiveFunctional B) (hρ : ρ.IsFinite) :
        Tendsto (fun n ↦ (ρ (a n)).toReal) atTop
          (𝓝 (ρ (SigmaCompleteBooleanAlgebra.iInfNat a)).toReal) := by
      have hcomp : Monotone (fun n ↦ (a n)ᶜ) := by
        intro n m hnm
        exact compl_le_compl (ha hnm)
      have hc := ρ.tendsto_map_iSup hcomp
      have hcr := (ENNReal.tendsto_toReal (ρ.ne_top hρ _)).comp hc
      have hconst : Tendsto (fun _ : ℕ ↦ (ρ ⊤).toReal) atTop (𝓝 (ρ ⊤).toReal) :=
        tendsto_const_nhds
      rw [hvalue ρ hρ, SigmaCompleteBooleanAlgebra.compl_iInfNat]
      simpa only [Function.comp_apply, ← hvalue ρ hρ] using hconst.sub hcr
    exact (ht ν hν).sub (ht μ hμ)
  have bdd_c : BddAbove c := by
    use (ν ⊤).toReal
    rintro _ ⟨b, rfl⟩
    exact (sub_le_self _ ENNReal.toReal_nonneg).trans <|
      (ENNReal.toReal_le_toReal (ν.ne_top hν b) (ν.ne_top hν ⊤)).2
        (ν.monotone le_top)
  have c_nonempty : c.Nonempty := Set.range_nonempty d
  have d_le_γ (b : B) : d b ≤ γ := le_csSup bdd_c ⟨b, rfl⟩
  have hnear (n : ℕ) : ∃ b : B, γ - (1 / 2) ^ n < d b := by
    have hlt : γ - (1 / 2) ^ n < γ := sub_lt_self γ (by positivity)
    rcases exists_lt_of_lt_csSup c_nonempty hlt with ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨b, hb⟩
  rcases Classical.axiom_of_choice hnear with ⟨e, he⟩
  let f : ℕ → ℕ → B := fun n m ↦ (Finset.Ico n (m + 1)).inf e
  have f_le_f {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) : f a d ≤ f b c := by
    apply Finset.le_inf
    intro i hi
    apply Finset.inf_le
    exact Finset.Ico_subset_Ico hab (Nat.succ_le_succ hcd) hi
  have f_succ (n m : ℕ) (hnm : n ≤ m) :
      f n (m + 1) = f n m ⊓ e (m + 1) := by
    have h : n ≤ m + 1 := le_of_lt (Nat.succ_le_succ hnm)
    simp_rw [f, ← Finset.insert_Ico_right_eq_Ico_add_one h, Finset.inf_insert,
      inf_comm]
  have le_d_f (m n : ℕ) (hmn : m ≤ n) :
      γ - 2 * (1 / 2) ^ m + (1 / 2) ^ n ≤ d (f m n) := by
    induction n, hmn using Nat.le_induction with
    | base =>
        simp only [f, Nat.Ico_succ_singleton, Finset.inf_singleton]
        have hm := he m
        linarith
    | succ n hmn ih =>
        refine le_of_add_le_add_left (a := γ) ?_
        calc
          γ + (γ - 2 * (1 / 2) ^ m + (1 / 2) ^ (n + 1)) =
              γ + (γ - 2 * (1 / 2) ^ m + ((1 / 2) ^ n - (1 / 2) ^ (n + 1))) := by
            rw [pow_succ, mul_one_div, _root_.sub_half]
          _ = γ - (1 / 2) ^ (n + 1) +
              (γ - 2 * (1 / 2) ^ m + (1 / 2) ^ n) := by ring
          _ ≤ d (e (n + 1)) + d (f m n) := add_le_add (le_of_lt <| he _) ih
          _ ≤ d (e (n + 1)) + d (f m n \ e (n + 1)) + d (f m (n + 1)) := by
            rw [f_succ _ _ hmn, d_split (f m n) (e (n + 1)), add_assoc]
          _ = d (e (n + 1) ⊔ f m n) + d (f m (n + 1)) := by
            rw [d_split (e (n + 1) ⊔ f m n) (e (n + 1))]
            have hinf : (e (n + 1) ⊔ f m n) ⊓ e (n + 1) = e (n + 1) :=
              inf_eq_right.mpr le_sup_left
            rw [sup_sdiff_left_self, hinf]
            ring
          _ ≤ γ + d (f m (n + 1)) := add_le_add (d_le_γ _) le_rfl
  let r : ℕ → B := fun m ↦ SigmaCompleteBooleanAlgebra.iInfNat (f m)
  let p : B := ⨆ m, r m
  have hr_mono : Monotone r := by
    intro m n hmn
    apply SigmaCompleteBooleanAlgebra.le_iInfNat
    intro k
    exact (SigmaCompleteBooleanAlgebra.iInfNat_le (f m) k).trans
      (f_le_f hmn le_rfl)
  have γ_le_d_p : γ ≤ d p := by
    have hγ : Tendsto (fun m : ℕ ↦ γ - 2 * (1 / 2) ^ m) atTop (𝓝 γ) := by
      suffices Tendsto (fun m : ℕ ↦ γ - 2 * (1 / 2) ^ m) atTop (𝓝 (γ - 2 * 0)) by
        simpa only [mul_zero, sub_zero]
      exact tendsto_const_nhds.sub <|
        tendsto_const_nhds.mul <|
          tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hd : Tendsto (fun m ↦ d (r m)) atTop (𝓝 (d p)) := by
      exact d_iSup r hr_mono
    refine le_of_tendsto_of_tendsto' hγ hd fun m ↦ ?_
    have hm : Tendsto (fun n ↦ d (f m n)) atTop (𝓝 (d (r m))) := by
      apply d_iInf
      intro n k hnk
      exact f_le_f le_rfl hnk
    refine ge_of_tendsto hm (eventually_atTop.2 ⟨m, fun n hmn ↦ ?_⟩)
    exact le_trans (le_add_of_le_of_nonneg le_rfl (pow_nonneg (by positivity) _))
      (le_d_f m n hmn)
  refine ⟨p, fun b ↦ ?_⟩
  exact (d_le_γ b).trans γ_le_d_p

/-- For any finite non-negative countably additive functionals `(μ, ν)` there
exists a Hahn decomposition. -/
theorem exists_isHahnDecomposition
    (μ ν : CountablyAdditiveFunctional B) (hμ : μ.IsFinite) (hν : ν.IsFinite) :
    ∃ p : B, IsHahnDecomposition μ ν p := by
  let d : B → ℝ := fun b ↦ (ν b).toReal - (μ b).toReal
  have d_split (a b : B) : d a = d (a \ b) + d (a ⊓ b) := by
    dsimp only [d]
    rw [← ν.map_sdiff_add_inf a b, ← μ.map_sdiff_add_inf a b,
      ENNReal.toReal_add (ν.ne_top hν _) (ν.ne_top hν _),
      ENNReal.toReal_add (μ.ne_top hμ _) (μ.ne_top hμ _)]
    ring
  rcases exists_forall_toReal_sub_le μ ν hμ hν with ⟨p, hp⟩
  have d_max (b : B) : d b ≤ d p := hp b
  refine ⟨p, ?_, ?_⟩
  · intro b hb
    have hd_nonneg : 0 ≤ d b := by
      apply (add_le_add_iff_left (d p)).mp
      calc
        d p + 0 ≤ d p := by simp
        _ = d (p \ b) + d b := by rw [d_split p b, inf_eq_right.mpr hb]
        _ ≤ d p + d b := add_le_add (d_max _) le_rfl
    exact (ENNReal.toReal_le_toReal (μ.ne_top hμ b) (ν.ne_top hν b)).mp
      (by simpa only [d, sub_nonneg] using hd_nonneg)
  · intro b hb
    have hd_nonpos : d b ≤ 0 := by
      apply (add_le_add_iff_left (d p)).mp
      calc
        d p + d b = d (p ⊔ b) := by
          rw [d_split (p ⊔ b) p, sup_sdiff_left_self, hb.sdiff_eq_left,
            inf_eq_right.mpr le_sup_left]
          ring
        _ ≤ d p := d_max _
        _ = d p + 0 := by simp
    exact (ENNReal.toReal_le_toReal (ν.ne_top hν b) (μ.ne_top hμ b)).mp
      (by simpa only [d, sub_nonpos] using hd_nonpos)

end CountablyAdditiveFunctional
