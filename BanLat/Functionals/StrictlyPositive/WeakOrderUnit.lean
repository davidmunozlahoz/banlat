/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Operators.StrictlyPositive
import BanLat.Substructures.Band.Generated

/-!
# Weak order units and strictly positive functionals

If the order dual of `X` separates points, every weak order unit of the order dual
is a strictly positive functional on `X`. Under the same assumption, any vector
`v ≥ 0` satisfying `f v > 0` for every nonzero positive order-bounded functional `f`
is a weak order unit of `X`.
-/

namespace OrderDualSpace

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- If a weak order unit `f` of the order dual vanishes at a nonnegative vector `x`,
then every positive order-bounded functional `g` also vanishes at `x`. -/
private lemma apply_eq_zero_of_weakOrderUnit {f g : OrderDualSpace X}
    (hf : WeakOrderUnit f) (hg : 0 ≤ g) {x : X} (hx : 0 ≤ x) (hfx : f x = 0) :
    g x = 0 := by
  let : IsVLArchimedean (OrderDualSpace X) :=
    IsVLArchimedean_of_sigmaConditionallyCompleteLattice
  have hmem : g ∈ Band.generated ({f} : Set (OrderDualSpace X)) := by
    rw [(weakOrderUnit_iff_generated_singleton_eq_top hf.1).mp hf]
    trivial
  have hlub := (Band.mem_generated_singleton_iff_isLUB_inf_nsmul hf.1 hg).mp hmem
  have hmono : Monotone (fun n : ℕ ↦ g ⊓ n • f) := by
    intro m n hmn
    exact inf_le_inf_left g (nsmul_le_nsmul_left hf.1 hmn)
  obtain ⟨q, hq, hqx⟩ := OrderBoundedHom.isLUB_of_directedOn
    (Set.range_nonempty (fun n : ℕ ↦ g ⊓ n • f)) hmono.directed_le.directedOn_range
    ⟨g, by rintro _ ⟨n, rfl⟩; exact inf_le_left⟩
  have heq : q = g := hq.unique hlub
  rw [heq] at hqx
  apply le_antisymm ((hqx hx).2 ?_) (nonneg_iff.mp hg x hx)
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  have h := le_iff.mp (inf_le_right : g ⊓ n • f ≤ n • f) x hx
  change (g ⊓ n • f) x ≤ n • f x at h
  simpa only [hfx, smul_zero] using h

/-- Let `X` be a vector lattice whose order dual separates points.
If `f : OrderDualSpace X` is a weak order unit, then `f x > 0` for every `x > 0` in `X`. -/
theorem strictlyPositive_of_weakOrderUnit (hsep : SeparatesPoints X)
    {f : OrderDualSpace X} (hf : WeakOrderUnit f) : StrictlyPositive f.toLinearMap := by
  intro x hx
  by_contra! h
  have hfx : f x = 0 := le_antisymm h (nonneg_iff.mp hf.1 x hx.le)
  apply hx.ne'
  apply hsep x
  intro g
  have hp := apply_eq_zero_of_weakOrderUnit hf (posPart_nonneg g) hx.le hfx
  have hn := apply_eq_zero_of_weakOrderUnit hf (negPart_nonneg g) hx.le hfx
  calc g x = (g⁺ - g⁻) x :=
        congrArg (fun k : OrderDualSpace X ↦ k x) (posPart_sub_negPart g).symm
    _ = 0 := by change g⁺ x - g⁻ x = 0; rw [hp, hn, sub_self]

/-- If the order dual of `X` separates points, then for every `x > 0` in `X`
there exists a positive order-bounded functional `f` such that `f x > 0`. -/
private lemma exists_positive_apply_pos (hsep : SeparatesPoints X) {x : X}
    (hx : 0 < x) : ∃ f : OrderDualSpace X, 0 ≤ f ∧ 0 < f x := by
  have h : ¬ ∀ f : OrderDualSpace X, f x = 0 := fun h ↦ hx.ne' (hsep x h)
  push Not at h
  obtain ⟨f, hf⟩ := h
  refine ⟨|f|, abs_nonneg f, (abs_pos.mpr hf).trans_le ?_⟩
  exact (isLUB_abs_apply (φ := f) hx.le).1 ⟨x, (abs_of_nonneg hx.le).le, rfl⟩

/-- If the order dual separates points, a positive vector on which every nonzero
positive order-bounded functional is strictly positive is a weak order unit. -/
theorem weakOrderUnit_of_forall_apply_pos (hsep : SeparatesPoints X)
    {v : X} (hv : 0 ≤ v)
    (h : ∀ f : OrderDualSpace X, 0 ≤ f → f ≠ 0 → 0 < f v) : WeakOrderUnit v := by
  refine ⟨hv, fun x hxv ↦ ?_⟩
  by_contra hx
  have hxpos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x)
    (fun hzero ↦ hx ((abs_eq_zero_iff_zero x).mp hzero.symm))
  obtain ⟨f, hf, hfx⟩ := exists_positive_apply_pos hsep hxpos
  obtain ⟨g, hg, _, hgu, hgv⟩ :=
    OrderBoundedHom.exists_positive_fragment hf (abs_nonneg x)
  have hg_ne : g ≠ 0 := by
    intro hzero
    have hz : g |x| = 0 := by rw [hzero]; rfl
    exact hfx.ne' (hgu.symm.trans hz)
  exact (h g hg hg_ne).ne' (hgv v hv
    (by simpa only [IsVLDisjoint, abs_abs, inf_comm] using hxv))

end OrderDualSpace
