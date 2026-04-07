import BanLat.Dual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Convex.Cone.Dual

/-!
# The bidual of a Banach lattice

The **bidual** `BidualSpace X` of a Banach lattice `X` is the norm dual of its
norm dual. Iterating the construction from `BanLat.Dual` shows that `X**` is
itself a Banach lattice. The canonical evaluation map `X → X**`, which embeds
every normed space into its bidual, is in the lattice setting an isometric
vector lattice homomorphism: it preserves not only the norm but also the
lattice operations `⊔`, `⊓`, and `|·|`. In particular, every Banach lattice
sits inside its bidual as a vector sublattice.
-/

noncomputable section

/-- The **bidual** of a Banach lattice: the norm dual of its norm dual. -/
abbrev BidualSpace (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] : Type _ :=
  NormDualSpace (NormDualSpace X)

namespace BidualSpace

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]

/-- The bidual of a Banach lattice is itself a Banach lattice. -/
example : BanachLattice (BidualSpace X) := inferInstance

/-! ### The canonical embedding `X → X**` -/

/-- The canonical evaluation embedding of a Banach lattice into its bidual,
sending `x` to the functional `φ ↦ φ x`. -/
def inclusion : X →L[ℝ] BidualSpace X :=
  NormedSpace.inclusionInDoubleDual ℝ X

@[simp]
theorem inclusion_apply (x : X) (φ : NormDualSpace X) :
    inclusion x φ = φ x := rfl

/-- The canonical embedding into the bidual is a linear isometry. -/
def inclusionLi : X →ₗᵢ[ℝ] BidualSpace X :=
  NormedSpace.inclusionInDoubleDualLi ℝ

@[simp]
theorem inclusionLi_apply (x : X) (φ : NormDualSpace X) :
    inclusionLi x φ = φ x := rfl

/-- The canonical embedding into the bidual preserves the norm. -/
theorem norm_inclusion (x : X) : ‖(inclusion (X := X)) x‖ = ‖x‖ :=
  (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ).norm_map x

/-! ### Order properties of the canonical embedding -/

/-- The canonical embedding into the bidual is positive: it sends positive
elements of `X` to positive elements of `X**`. -/
theorem inclusion_nonneg {x : X} (hx : 0 ≤ x) : 0 ≤ inclusion x := by
  change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace (inclusion x)
  intro φ hφ
  change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace φ at hφ
  have := hφ x hx
  simpa using this

/-- If every positive functional on `X` is non-negative on `x`, then `x ≥ 0`.
This is the Hahn–Banach separation: the closed positive cone of a normed
vector lattice equals the set of points sent to `[0, ∞)` by every positive
continuous functional. -/
private theorem nonneg_of_forall_dual_nonneg {x : X}
    (h : ∀ φ : NormDualSpace X, 0 ≤ φ → 0 ≤ φ x) : 0 ≤ x := by
  by_contra hx
  obtain ⟨f, hf_pos, hf_neg⟩ :=
    (ProperCone.positive ℝ X).hyperplane_separation_point hx
  have hfp : (0 : NormDualSpace X) ≤ f := by
    change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace f
    intro y hy
    have := hf_pos y hy
    simpa using this
  exact absurd (h f hfp) (not_le.mpr hf_neg)

/-- The canonical embedding into the bidual is an order embedding:
`inclusion x ≤ inclusion y` iff `x ≤ y`. -/
theorem inclusion_le_inclusion_iff {x y : X} :
    inclusion x ≤ inclusion y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← sub_nonneg]
    refine nonneg_of_forall_dual_nonneg fun φ hφ => ?_
    have hxy : φ x ≤ φ y := by
      change NormDualSpace.toOrderDualSpace (inclusion x) ≤
        NormDualSpace.toOrderDualSpace (inclusion y) at h
      have := h φ hφ
      simpa using this
    rw [φ.map_sub]; linarith
  · rw [← sub_nonneg] at h ⊢
    have h1 := inclusion_nonneg h
    rwa [(inclusion (X := X)).map_sub] at h1

/-- The canonical embedding into the bidual is injective. -/
theorem inclusion_injective : Function.Injective (inclusion (X := X)) :=
  (NormedSpace.inclusionInDoubleDualLi (E := X) ℝ).injective

/-! ### Lattice homomorphism property -/

/-- The canonical embedding into the bidual preserves the positive part.
This is the key non-trivial step in showing it is a vector lattice
homomorphism: it relies on the dual Riesz–Kantorovich formula
`φ z⁺ = sup {g z : 0 ≤ g ≤ φ}`. -/
private theorem inclusion_posPart (z : X) :
    inclusion z⁺ = (inclusion z)⁺ := by
  refine le_antisymm ?_ ?_
  · -- (≤) inclusion z⁺ ≤ (inclusion z)⁺: test against positive ψ ∈ NormDualSpace X
    change NormDualSpace.toOrderDualSpace (inclusion z⁺) ≤
      NormDualSpace.toOrderDualSpace ((inclusion z)⁺)
    intro ψ hψ
    change NormDualSpace.toOrderDualSpace 0 ≤ NormDualSpace.toOrderDualSpace ψ at hψ
    -- Dual Riesz–Kantorovich: ψ z⁺ = sup {g z : 0 ≤ g ≤ ψ in OrderDualSpace X}
    have hψOD : (0 : OrderDualSpace X) ≤ NormDualSpace.toOrderDualSpace ψ := hψ
    have hdual := OrderBoundedHom.isLUB_apply_posPart hψOD z
    -- Primal Riesz–Kantorovich applied at OrderBoundedHom (NormDualSpace X) ℝ:
    -- (toOrderDualSpace (inclusion z))⁺ ψ = sup {ψ' z : 0 ≤ ψ' ≤ ψ in NormDualSpace X}
    have hprimal := OrderBoundedHom.isLUB_posPart_apply
      (f := NormDualSpace.toOrderDualSpace (inclusion z)) (x := ψ) hψ
    refine hdual.2 ?_
    rintro _ ⟨g, hg_nn, hg_le, rfl⟩
    -- For each g in OrderDualSpace X with 0 ≤ g ≤ ψ, lift to ψ' := ofOrderDualSpace g
    refine hprimal.1 ⟨NormDualSpace.ofOrderDualSpace g, ?_, ?_, rfl⟩
    · change NormDualSpace.toOrderDualSpace 0 ≤
        NormDualSpace.toOrderDualSpace (NormDualSpace.ofOrderDualSpace g)
      exact hg_nn
    · change NormDualSpace.toOrderDualSpace (NormDualSpace.ofOrderDualSpace g) ≤
        NormDualSpace.toOrderDualSpace ψ
      exact hg_le
  · -- (≥) (inclusion z)⁺ ≤ inclusion z⁺: from positivity of `inclusion`
    rw [posPart_def]
    exact sup_le (inclusion_le_inclusion_iff.mpr le_sup_left)
      (inclusion_nonneg (posPart_nonneg z))

/-- The canonical embedding into the bidual preserves the negative part. -/
private theorem inclusion_negPart (z : X) :
    inclusion z⁻ = (inclusion z)⁻ := by
  rw [show z⁻ = (-z)⁺ from (posPart_neg z).symm, inclusion_posPart, map_neg,
    posPart_neg]

/-- The canonical embedding into the bidual preserves the modulus. -/
theorem inclusion_abs (x : X) : inclusion (|x|) = |inclusion x| := by
  rw [← posPart_add_negPart x, map_add, inclusion_posPart, inclusion_negPart,
    posPart_add_negPart]

/-- The canonical embedding into the bidual preserves binary suprema. -/
theorem inclusion_sup (x y : X) :
    inclusion (x ⊔ y) = inclusion x ⊔ inclusion y := by
  rw [sup_eq_add_posPart_sub, map_add, inclusion_posPart, map_sub,
    ← sup_eq_add_posPart_sub]

/-- The canonical embedding into the bidual preserves binary infima. -/
theorem inclusion_inf (x y : X) :
    inclusion (x ⊓ y) = inclusion x ⊓ inclusion y := by
  rw [inf_eq_sub_posPart_sub, map_sub, inclusion_posPart, map_sub,
    ← inf_eq_sub_posPart_sub]

/-- The canonical embedding into the bidual, bundled as a vector lattice
homomorphism. -/
def inclusionVecLatHom : VecLatHom X (BidualSpace X) where
  toFun := inclusion
  map_add' := (inclusion (X := X)).map_add
  map_smul' := (inclusion (X := X)).map_smul
  map_sup' := inclusion_sup
  map_inf' := inclusion_inf

@[simp]
theorem inclusionVecLatHom_apply (x : X) (φ : NormDualSpace X) :
    inclusionVecLatHom x φ = φ x := rfl

end BidualSpace

end
