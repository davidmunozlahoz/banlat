/-
Authors: Raúl Enrique Pariente-Martín
-/

import BanLat.Basic
import BanLat.Operators.Positive
import BanLat.Substructures.Sublattice
import Mathlib.LinearAlgebra.LinearPMap

/-!
# Hahn–Banach theorem for vector lattices

The Hahn–Banach theorem for vector lattices, also known as the Hahn–Banach–Kantorovich theorem,
extends a linear map from a linear subspace of a real vector space to the whole space,
preserving domination by a sublinear map into a Dedekind complete real vector lattice.
Here sublinearity means subadditivity and homogeneity for positive real scalars; Dedekind
completeness is expressed by `ConditionallyCompleteLattice` on the codomain.
-/

open Set Submodule

variable {E Z : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup Z] [ConditionallyCompleteLattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]

/-- Choose the image of a new vector `a` when extending `f` linearly beyond its domain.
The extension defined by `S (y + λ • a) = f y + λ • z` remains dominated by `p`
provided that `f y - p (y - a) ≤ z ≤ p (w + a) - f w` for all `y, w` in the
domain of `f`. Subadditivity of `p` and domination of `f` make these bounds compatible;
Dedekind completeness then supplies such a `z`. -/
private lemma exists_extension_value (f : E →ₗ.[ℝ] Z) (p : E → Z)
    (hp : ∀ x y, p (x + y) ≤ p x + p y)
    (hf : ∀ x : f.domain, f x ≤ p x) (a : E) :
    ∃ z, (∀ y : f.domain, f y - p (y - a) ≤ z) ∧
      ∀ y : f.domain, z ≤ p (y + a) - f y := by
  obtain ⟨z, hz₁, hz₂⟩ := exists_between_of_forall_le
    (s := Set.range fun y : f.domain ↦ f y - p (y - a))
    (t := Set.range fun y : f.domain ↦ p (y + a) - f y)
    (range_nonempty _) (range_nonempty _) (by
      rintro _ ⟨y, rfl⟩ _ ⟨w, rfl⟩
      change f y - p (y - a) ≤ p (w + a) - f w
      rw [le_sub_iff_add_le, sub_add_eq_add_sub, sub_le_iff_le_add,
        add_comm (p (w + a))]
      calc f y + f w = f (y + w) := (f.map_add y w).symm
        _ ≤ p ((y : E) + w) := hf (y + w)
        _ = p (((y : E) - a) + (w + a)) := by congr 1; abel
        _ ≤ p (y - a) + p (w + a) := hp _ _)
  exact ⟨z, fun y ↦ hz₁ (mem_range_self y), fun y ↦ hz₂ (mem_range_self y)⟩

/-- If `f y + z ≤ p (y + a)` for every `y` in the domain of `f`, then
`f y + r • z ≤ p (y + r • a)` for every such `y` and every positive real `r`,
provided that `p` is positively homogeneous. -/
private lemma extension_bound_pos (f : E →ₗ.[ℝ] Z) (p : E → Z)
    (hp : ∀ (r : ℝ), 0 < r → ∀ x, p (r • x) = r • p x)
    (a : E) (z : Z) (hz : ∀ y : f.domain, f y + z ≤ p (y + a))
    (y : f.domain) {r : ℝ} (hr : 0 < r) :
    f y + r • z ≤ p ((y : E) + r • a) := by
  have h := smul_le_smul_of_nonneg_left (hz (r⁻¹ • y)) hr.le
  rw [← hp r hr] at h
  simpa [smul_add, f.map_smul, smul_smul, hr.ne'] using h

/-- If `p` is positively homogeneous and dominates `f` on its domain, any `z` satisfying
`f w - p (w - a) ≤ z ≤ p (w + a) - f w` for every `w` in that domain also satisfies
`f y + r • z ≤ p (y + r • a)` for every domain element `y` and every real `r`. -/
private lemma extension_bound (f : E →ₗ.[ℝ] Z) (p : E → Z)
    (hp : ∀ (r : ℝ), 0 < r → ∀ x, p (r • x) = r • p x)
    (hf : ∀ y : f.domain, f y ≤ p y) (a : E) (z : Z)
    (hl : ∀ y : f.domain, f y - p (y - a) ≤ z)
    (hu : ∀ y : f.domain, z ≤ p (y + a) - f y)
    (y : f.domain) (r : ℝ) : f y + r • z ≤ p ((y : E) + r • a) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · have hz : ∀ y : f.domain, f y + -z ≤ p ((y : E) + -a) := by
      intro y
      simpa [sub_eq_add_neg, add_comm] using (sub_le_comm.mp (hl y))
    simpa using extension_bound_pos f p hp (-a) (-z) hz y (neg_pos.mpr hr)
  · simpa using hf y
  · exact extension_bound_pos f p hp a z
      (fun y ↦ by simpa [add_comm] using le_sub_iff_add_le.mp (hu y)) y hr

/-- Enlarge a proper domain `F` to `F + ℝa`, with `a ∉ F`, while preserving domination by `p`.
The extension has the form `g (y + r • a) = f y + r • z`, with `z` chosen between the
lower and upper candidates in `exists_extension_value`. -/
private lemma extension_step (f : E →ₗ.[ℝ] Z) (p : E → Z)
    (hp_smul : ∀ (r : ℝ), 0 < r → ∀ x, p (r • x) = r • p x)
    (hp_add : ∀ x y, p (x + y) ≤ p x + p y)
    (hf : ∀ x : f.domain, f x ≤ p x) (hdom : f.domain ≠ ⊤) :
    ∃ g : E →ₗ.[ℝ] Z, f < g ∧ ∀ x : g.domain, g x ≤ p x := by
  obtain ⟨a, -, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hdom)
  obtain ⟨z, hl, hu⟩ := exists_extension_value f p hp_add hf a
  refine ⟨f.supSpanSingleton a z ha, ?_, ?_⟩
  · refine lt_iff_le_not_ge.mpr ⟨f.left_le_sup _ _, fun h ↦ ?_⟩
    have hd := LinearPMap.domain_mono.monotone h
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, span_le,
      singleton_subset_iff] at hd
    exact ha hd.2
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := mem_sup.mp hx
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hw
    rw [LinearPMap.supSpanSingleton_apply_mk]
    exact extension_bound f p hp_smul hf a z hl hu ⟨y, hy⟩ r

/-- Every nonempty chain of partial linear maps, ordered by extension and dominated by `p`
on their respective domains, admits a common linear extension that is also dominated by `p`
on its domain. -/
private lemma dominated_chain_upper_bound (p : E → Z)
    (c : Set (E →ₗ.[ℝ] Z)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hp : ∀ f ∈ c, ∀ x : f.domain, f x ≤ p x) :
    ∃ g : E →ₗ.[ℝ] Z, (∀ x : g.domain, g x ≤ p x) ∧ ∀ f ∈ c, f ≤ g := by
  refine ⟨LinearPMap.sSup c hc.directedOn, ?_, fun _ hf ↦ LinearPMap.le_sSup _ hf⟩
  rintro ⟨x, hx⟩
  obtain ⟨f, hfc, hxf⟩ := (LinearPMap.mem_domain_sSup_iff hne hc.directedOn).mp hx
  simpa only [LinearPMap.sSup_apply hc.directedOn hfc ⟨x, hxf⟩] using hp f hfc ⟨x, hxf⟩

/-- Zorn's lemma gives a maximal dominated partial linear extension of `f`.
Its domain is the whole space: otherwise `extension_step` would produce a strictly larger
dominated extension, contradicting maximality. -/
private lemma exists_dominated_top (f : E →ₗ.[ℝ] Z) (p : E → Z)
    (hp_smul : ∀ (r : ℝ), 0 < r → ∀ x, p (r • x) = r • p x)
    (hp_add : ∀ x y, p (x + y) ≤ p x + p y)
    (hf : ∀ x : f.domain, f x ≤ p x) :
    ∃ g ≥ f, g.domain = ⊤ ∧ ∀ x : g.domain, g x ≤ p x := by
  let s := {g : E →ₗ.[ℝ] Z | ∀ x : g.domain, g x ≤ p x}
  have hc : ∀ c, c ⊆ s → IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hchain y hy
    exact dominated_chain_upper_bound p c hchain ⟨y, hy⟩ hcs
  obtain ⟨g, hfg, hg, hmax⟩ := zorn_le_nonempty₀ s hc f hf
  refine ⟨g, hfg, ?_, hg⟩
  by_contra hdom
  obtain ⟨q, hgq, hq⟩ := extension_step g p hp_smul hp_add hg hdom
  exact hgq.not_ge (hmax hq hgq.le)

/-- **Hahn–Banach theorem for vector lattices (Hahn–Banach–Kantorovich theorem)**: a linear map
on a linear subspace of a real vector space, dominated by a sublinear map into a Dedekind
complete real vector lattice, has a linear extension to the whole space under the same bound. -/
theorem LinearMap.exists_extension_of_le_sublinear
    (F : Submodule ℝ E) (T : F →ₗ[ℝ] Z) (p : E → Z)
    (hp_smul : ∀ (r : ℝ), 0 < r → ∀ x, p (r • x) = r • p x)
    (hp_add : ∀ x y, p (x + y) ≤ p x + p y)
    (hT : ∀ y : F, T y ≤ p y) :
    ∃ S : E →ₗ[ℝ] Z, (∀ y : F, S y = T y) ∧ ∀ x, S x ≤ p x := by
  obtain ⟨⟨G, g⟩, ⟨_, hTg⟩, rfl : G = ⊤, hg⟩ :=
    exists_dominated_top (⟨F, T⟩ : E →ₗ.[ℝ] Z) p hp_smul hp_add hT
  refine ⟨g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial), ?_, ?_⟩
  · exact fun y ↦ (hTg rfl).symm
  · exact fun x ↦ hg ⟨x, trivial⟩

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
/-- If positive linear operators `S : Y → Z` and `T : X → Z` satisfy
`S y ≤ T y` for every positive `y ∈ Y`, then `S` admits a linear extension
`R : X → Z` satisfying `R x ≤ T (x⁺)` for every `x ∈ X`. -/
private lemma exists_extension_le_posPart (Y : VectorSublattice X)
    (T : X →ₗ[ℝ] Z) (S : Y →ₗ[ℝ] Z) (hT : Positive T) (hS : Positive S)
    (hST : ∀ y : Y, 0 ≤ y → S y ≤ T y) :
    ∃ R : X →ₗ[ℝ] Z, (∀ y : Y, R y = S y) ∧ ∀ x, R x ≤ T x⁺ := by
  apply LinearMap.exists_extension_of_le_sublinear Y.toSubmodule S (fun x ↦ T x⁺)
  · intro r hr x
    rw [posPart_smul_nonneg hr.le, map_smul]
  · intro x y
    exact ((Positive.monotone_iff.mpr hT) (posPart_add_le x y)).trans_eq (T.map_add _ _)
  · intro y
    let z : Y := y
    exact ((Positive.monotone_iff.mpr hS) (le_posPart z)).trans
      (hST z⁺ (posPart_nonneg z))

/-- **Hahn–Banach theorem for operators.** Let `Y` be a vector sublattice of `X` and
`Z` a Dedekind complete vector lattice. If positive linear operators `S : Y → Z` and
`T : X → Z` satisfy `S y ≤ T y` for every positive `y ∈ Y`, then `S` extends to
a linear operator `R : X → Z` satisfying `0 ≤ R x ≤ T x` for every positive `x ∈ X`. -/
theorem VectorSublattice.exists_positive_extension_le (Y : VectorSublattice X)
    (T : X →ₗ[ℝ] Z) (S : Y →ₗ[ℝ] Z) (hT : Positive T) (hS : Positive S)
    (hST : ∀ y : Y, 0 ≤ y → S y ≤ T y) :
    ∃ R : X →ₗ[ℝ] Z, 0 ≤ R ∧ R ≤ T ∧ ∀ y : Y, R y = S y := by
  obtain ⟨R, hext, hR⟩ := exists_extension_le_posPart Y T S hT hS hST
  refine ⟨R, Positive.zero_le_iff.mpr ?_, Positive.le_iff.mpr ?_, hext⟩
  · intro x hx
    have h := hR (-x)
    simpa only [map_neg, posPart_eq_zero.mpr (neg_nonpos.mpr hx), map_zero,
      neg_nonpos] using h
  · intro x hx
    simpa only [posPart_of_nonneg hx] using hR x
