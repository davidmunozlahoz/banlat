import BanLat.ALSpace
import BanLat.AMSpace
import BanLat.Operators.Hom
import BanLat.OrderDense
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Products of vector, normed and Banach lattices

Given a family `(X i)` of vector lattices, the product `∀ i, X i` carries a
pointwise vector lattice structure. When each `X i` is a normed (resp. Banach)
lattice and the index set is finite, the ℓ^p product `PiLp p X` is again a
normed (resp. Banach) lattice for `1 ≤ p ≤ ∞`. Moreover, the ℓ^∞ product of
AM-spaces is an AM-space, and the ℓ^1 product of AL-spaces is an AL-space.
-/

open scoped ENNReal

/-! ### Pointwise product -/

namespace Pi

variable {ι : Type*} {X : ι → Type*}
  [∀ i, AddCommGroup (X i)] [∀ i, Lattice (X i)] [∀ i, IsOrderedAddMonoid (X i)]
  [∀ i, VectorLattice (X i)]

/-- The pointwise product of a family of vector lattices is a vector lattice.
The lattice operations and absolute value are computed pointwise (see
`Pi.sup_apply`, `Pi.inf_apply`, `Pi.abs_apply` in Mathlib). -/
instance instVectorLattice : VectorLattice (∀ i, X i) := ⟨⟩

end Pi

/-! ### ℓ^p product

For a finite index set `ι` and `1 ≤ p ≤ ∞`, the ℓ^p product of normed vector
lattices is again a normed vector lattice, and Banachness is preserved. The
order structure is pointwise; only the norm depends on `p`.
-/

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : ι → Type*}

section Order

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

/-- Pointwise `≤` on `PiLp p X`. -/
instance instLE : LE (PiLp p X) where
  le x y := ∀ i, x i ≤ y i

/-- Pointwise `<` on `PiLp p X`. -/
instance instLT : LT (PiLp p X) where
  lt x y := WithLp.ofLp x < WithLp.ofLp y

/-- Pointwise `⊔` on `PiLp p X`. -/
instance instMax : Max (PiLp p X) where
  max x y := WithLp.toLp p (fun i => x i ⊔ y i)

/-- Pointwise `⊓` on `PiLp p X`. -/
instance instMin : Min (PiLp p X) where
  min x y := WithLp.toLp p (fun i => x i ⊓ y i)

/-- Pointwise lattice structure on `PiLp p X`. -/
instance instLattice : Lattice (PiLp p X) :=
  Function.Injective.lattice (β := ∀ i, X i) WithLp.ofLp (WithLp.ofLp_injective p)
    Iff.rfl Iff.rfl (fun _ _ => rfl) (fun _ _ => rfl)

/-- The order on `PiLp p X` is compatible with addition. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (PiLp p X) :=
  Function.Injective.isOrderedAddMonoid (β := PiLp p X) (α := ∀ i, X i)
    WithLp.ofLp (fun _ _ => rfl) Iff.rfl

/-- The ℓ^p norm is solid: `|x| ≤ |y|` implies `‖x‖ ≤ ‖y‖`. -/
instance instHasSolidNorm [∀ i, HasSolidNorm (X i)] : HasSolidNorm (PiLp p X) where
  solid := fun x y h => by
    -- pointwise bound on norms via the solid norm of each factor
    have hpt : ∀ i, ‖x i‖ ≤ ‖y i‖ := fun i =>
      HasSolidNorm.solid (α := X i) (h i)
    rcases eq_or_ne p ∞ with hp | hp
    · subst hp
      simp only [PiLp.norm_eq_ciSup]
      exact ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) hpt
    · have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
      have hpos : 0 < p.toReal := by
        have := ENNReal.toReal_lt_toReal (by norm_num) hp |>.mpr
          (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) h1)
        simpa using this
      simp only [PiLp.norm_eq_sum hpos]
      gcongr with i
      exact hpt i

end Order

/-! #### Vector and Banach lattice structure -/

variable [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
  [∀ i, IsOrderedAddMonoid (X i)]

instance instPosSMulMono [∀ i, NormedVectorLattice (X i)] :
    PosSMulMono ℝ (PiLp p X) where
  smul_le_smul_of_nonneg_left := by
    intro a ha b₁ b₂ hb i
    exact smul_le_smul_of_nonneg_left (hb i) ha

/-- The ℓ^p product of normed vector lattices is a vector lattice. -/
instance instVectorLattice [∀ i, NormedVectorLattice (X i)] :
    VectorLattice (PiLp p X) := ⟨⟩

/-- The ℓ^p product of normed vector lattices is a normed vector lattice. -/
instance instNormedVectorLattice [∀ i, NormedVectorLattice (X i)] :
    NormedVectorLattice (PiLp p X) where

/-- The ℓ^p product of Banach lattices is a Banach lattice. -/
instance instBanachLattice [∀ i, BanachLattice (X i)] :
    BanachLattice (PiLp p X) where

/-! #### AM- and AL-space structures -/

/-- The ℓ^∞ product of AM-spaces is an AM-space. -/
instance instAMSpaceTop [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
    [∀ i, IsOrderedAddMonoid (X i)] [∀ i, AMSpace (X i)] :
    AMSpace (PiLp ∞ X) where
  norm_sup_eq_max_of_nonneg := by
    intro x y hx hy
    simp only [PiLp.norm_eq_ciSup]
    have hpt : ∀ i, ‖(x ⊔ y).ofLp i‖ = max ‖x.ofLp i‖ ‖y.ofLp i‖ := fun i =>
      AMSpace.norm_sup_eq_max_of_nonneg (X := X i) (hx i) (hy i)
    cases isEmpty_or_nonempty ι
    · simp
    · change ⨆ i, ‖(x ⊔ y).ofLp i‖ = (⨆ i, ‖x.ofLp i‖) ⊔ (⨆ i, ‖y.ofLp i‖)
      simp_rw [hpt]
      have hbx : BddAbove (Set.range fun i => ‖x.ofLp i‖) :=
        Set.Finite.bddAbove (Set.finite_range _)
      have hby : BddAbove (Set.range fun i => ‖y.ofLp i‖) :=
        Set.Finite.bddAbove (Set.finite_range _)
      refine le_antisymm
        (ciSup_le fun i => sup_le_sup (le_ciSup hbx i) (le_ciSup hby i))
        (sup_le
          (ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) fun _ => le_sup_left)
          (ciSup_mono (Set.Finite.bddAbove (Set.finite_range _)) fun _ => le_sup_right))

/-- The ℓ^1 product of AL-spaces is an AL-space. -/
instance instALSpaceOne [∀ i, NormedAddCommGroup (X i)] [∀ i, Lattice (X i)]
    [∀ i, IsOrderedAddMonoid (X i)] [∀ i, ALSpace (X i)] :
    ALSpace (PiLp 1 X) where
  norm_add_eq_of_nonneg := by
    intro x y hx hy
    simp only [PiLp.norm_eq_of_L1]
    have hpt : ∀ i, ‖(x + y).ofLp i‖ = ‖x.ofLp i‖ + ‖y.ofLp i‖ := fun i =>
      ALSpace.norm_add_eq_of_nonneg (X := X i) (hx i) (hy i)
    simp_rw [hpt, Finset.sum_add_distrib]

end PiLp

/-! ### Decomposition Lemma: embeddings into products

The Decomposition Lemma in `BanLat/Band.lean` says that, under PPP and with a
maximal disjoint family `Λ ⊆ X₊`, every `x ∈ X₊` is the supremum of its
principal band projections `(Pₐ x)_{a ∈ Λ}`. Below we record the two
consequences phrased in terms of products: an order dense lattice embedding of
`X` into the product `(a : Λ) → ↥(principalBand a)`, and an embedding of an
arbitrary vector lattice with PPP into a product of vector lattices with weak
units. -/

universe u

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-- A band projection vanishes on its disjoint complement. -/
private lemma bandProjection_eq_zero_of_mem_disjointComplement
    (P : ProjectionBand X) {x : X}
    (hx : x ∈ disjointComplement (P : Set X)) :
    P.bandProjection x = 0 := by
  have h0_mem : (0 : X) ∈ P := P.toBand.toOrderIdeal.toSubmodule.zero_mem
  have hdec₁ : x = P.bandProjection x + (x - P.bandProjection x) := by abel
  have hdec₂ : x = 0 + x := (zero_add x).symm
  exact (P.decomposition_unique (P.bandProjection_mem x)
    (P.id_sub_bandProjection_mem x) h0_mem hx hdec₁ hdec₂).1

/-- A band projection is the identity on the band itself. -/
private lemma bandProjection_of_mem_eq_self (P : ProjectionBand X) {x : X}
    (hx : x ∈ P) : P.bandProjection x = x := by
  have h0_mem : (0 : X) ∈ disjointComplement (P : Set X) :=
    (Band.disjointComplementOrderIdeal (P : Set X)).toSubmodule.zero_mem
  have hdec₁ : x = P.bandProjection x + (x - P.bandProjection x) := by abel
  have hdec₂ : x = x + 0 := (add_zero x).symm
  exact (P.decomposition_unique (P.bandProjection_mem x)
    (P.id_sub_bandProjection_mem x) hx h0_mem hdec₁ hdec₂).1

/-- The principal bands generated by two disjoint elements are themselves
mutually disjoint as subsets of `X`. -/
private lemma principalBand_subset_disjointComplement
    {a b : X} (hab : IsVLDisjoint a b) :
    (Band.principalBand a : Set X)
      ⊆ disjointComplement (Band.principalBand b : Set X) := by
  -- principalBand b ⊆ {a}ᵈ
  have h₁ : (Band.principalBand b : Set X) ⊆ ({a} : Set X)ᵈ := by
    refine Band.bandGenerated_le (B := Band.disjointComplementBand ({a} : Set X)) ?_
    intro y hy; rcases hy with rfl
    intro c hc; rcases hc with rfl
    exact isVLDisjoint_comm.mp hab
  -- so a ⊥ everything in principalBand b
  have ha_mem : a ∈ disjointComplement (Band.principalBand b : Set X) := by
    intro y hy
    exact isVLDisjoint_comm.mp (h₁ hy a (Set.mem_singleton _))
  -- principalBand a ⊆ disjointComplement (principalBand b)
  refine Band.bandGenerated_le
    (B := Band.disjointComplementBand (Band.principalBand b : Set X)) ?_
  intro y hy; rcases hy with rfl; exact ha_mem

open Band in
/-- Let `X` have PPP and let `Λ` be a maximal disjoint family in `X₊`. The map
`T : X → (a : Λ) → ↥(principalBand a)` defined by `T x a = Pₐ x` is an
injective vector lattice homomorphism with order dense range. -/
theorem exists_orderDense_lattice_embedding_of_isMaximalDisjoint
    [HasPrincipalProjectionProperty X] {Λ : Set X} (hΛ : IsMaximalDisjoint Λ) :
    ∃ T : VecLatHom X ((a : Λ) → ↥(Band.principalBand (a : X)).toSubmodule),
      Function.Injective T ∧ IsOrderDense (Set.range T) := by
  classical
  -- The underlying function: package each component of `Pₐ x` in the band.
  set f : X → ((a : Λ) → ↥(Band.principalBand (a : X)).toSubmodule) := fun x a =>
    ⟨principalBandProjection (a : X) x, by
      change _ ∈ (Band.principalBand (a : X) : Set X)
      rw [← principalProjectionBand_coe (a : X)]
      exact (principalProjectionBand (a : X)).bandProjection_mem x⟩ with hf_def
  have hf_lin : IsLinearMap ℝ f := by
    refine ⟨?_, ?_⟩
    · intro x y; funext a
      apply Subtype.ext
      change principalBandProjection (a : X) (x + y) = _
      rw [map_add]; rfl
    · intro r x; funext a
      apply Subtype.ext
      change principalBandProjection (a : X) (r • x) = _
      rw [map_smul]; rfl
  have hf_sup : ∀ x y : X, f (x ⊔ y) = f x ⊔ f y := by
    intro x y; funext a
    apply Subtype.ext
    have hvl := (principalProjectionBand (a : X)).bandProjection_isVecLatHom
    change (principalProjectionBand (a : X)).bandProjection.toFun (x ⊔ y) = _
    rw [hvl.map_sup' x y]; rfl
  have hf_inf : ∀ x y : X, f (x ⊓ y) = f x ⊓ f y := by
    intro x y; funext a
    apply Subtype.ext
    have hvl := (principalProjectionBand (a : X)).bandProjection_isVecLatHom
    change (principalProjectionBand (a : X)).bandProjection.toFun (x ⊓ y) = _
    rw [hvl.map_inf' x y]; rfl
  let T : VecLatHom X ((a : Λ) → ↥(Band.principalBand (a : X)).toSubmodule) :=
    IsVecLatHom.mk' f
      { toIsLinearMap := hf_lin
        map_sup' := hf_sup
        map_inf' := hf_inf }
  -- Each `principalBandProjection a` as a `VecLatHom` (used for `map_abs`).
  let Pa : Λ → VecLatHom X X := fun a =>
    IsVecLatHom.mk' _
      (principalProjectionBand (a : X)).bandProjection_isVecLatHom
  refine ⟨T, ?_, ?_⟩
  · -- Injectivity via `IsLUB` of the projections of `|x - y|`.
    intro x y hxy
    have hpw : ∀ a : Λ, principalBandProjection (a : X) x =
        principalBandProjection (a : X) y := fun a =>
      congrArg (fun g => (g a).val) hxy
    have hsub : ∀ a : Λ, principalBandProjection (a : X) (x - y) = 0 := by
      intro a; rw [map_sub, hpw a, sub_self]
    have hLUB := isLUB_principalBandProjection_of_isMaximalDisjoint hΛ
      (x := |x - y|) (abs_nonneg _)
    have hub : (0 : X) ∈ upperBounds
        (Set.range fun a : Λ => principalBandProjection (a : X) |x - y|) := by
      rintro _ ⟨a, rfl⟩
      change principalBandProjection (a : X) |x - y| ≤ 0
      have h1 : principalBandProjection (a : X) |x - y| =
          |principalBandProjection (a : X) (x - y)| := (Pa a).map_abs (x - y)
      rw [h1, hsub a, abs_zero]
    have hle : |x - y| ≤ 0 := hLUB.2 hub
    have h₁ : x - y ≤ 0 := le_trans (le_abs_self _) hle
    have h₂ : 0 ≤ x - y := neg_nonpos.mp (le_trans (neg_le_abs _) hle)
    exact sub_eq_zero.mp (le_antisymm h₁ h₂)
  · -- Order density: pick a coordinate where `g` is positive and use that
    -- element as the witness.
    intro g hg
    have hgnn : 0 ≤ g := hg.le
    have hgne : g ≠ 0 := hg.ne'
    have hexists : ∃ a : Λ, g a ≠ 0 := by
      by_contra hcontra; push_neg at hcontra
      apply hgne; funext a; exact hcontra a
    obtain ⟨a₀, hga0⟩ := hexists
    have hga0_pos : 0 < g a₀ := lt_of_le_of_ne (hgnn a₀) (Ne.symm hga0)
    set y : X := (g a₀ : X) with hy_def
    have hy_pos : (0 : X) < y := hga0_pos
    have hy_mem : y ∈ Band.principalBand (a₀ : X) := (g a₀).property
    have hy_nn : (0 : X) ≤ y := hy_pos.le
    have hPmem : y ∈ principalProjectionBand (a₀ : X) := by
      change y ∈ ((principalProjectionBand (a₀ : X) : ProjectionBand X) : Set X)
      rw [principalProjectionBand_coe]; exact hy_mem
    have hPa0_y : principalBandProjection (a₀ : X) y = y :=
      bandProjection_of_mem_eq_self (principalProjectionBand (a₀ : X)) hPmem
    refine ⟨T y, ⟨y, rfl⟩, ?_, ?_⟩
    · -- `0 < T y`: nonneg coordinatewise, and nonzero at `a₀`.
      refine lt_of_le_of_ne ?_ ?_
      · intro a
        change (0 : X) ≤ principalBandProjection (a : X) y
        exact (principalProjectionBand (a : X)).bandProjection_nonneg hy_nn
      · intro hT0
        have h1 : (T y) a₀ =
            (0 : (a : Λ) → ↥(Band.principalBand (a : X)).toSubmodule) a₀ := by
          rw [← hT0]
        have h2 : principalBandProjection (a₀ : X) y = 0 := congrArg Subtype.val h1
        rw [hPa0_y] at h2
        exact (ne_of_gt hy_pos) h2
    · -- `T y ≤ g`: at `a₀` they agree; at other coordinates `T y` is `0`.
      intro a
      change principalBandProjection (a : X) y ≤ (g a).val
      by_cases hab : (a : X) = (a₀ : X)
      · have hex : a = a₀ := Subtype.ext hab
        subst hex
        rw [hPa0_y]
      · have hne : (a : X) ≠ (a₀ : X) := hab
        have hdset := hΛ.prop.2
        have hdisj : IsVLDisjoint (a₀ : X) (a : X) :=
          hdset a₀.property a.property (fun h => hne h.symm)
        have hy_in_dC : y ∈ disjointComplement (Band.principalBand (a : X) : Set X) :=
          principalBand_subset_disjointComplement hdisj hy_mem
        have hy_in_dC' : y ∈ disjointComplement
            ((principalProjectionBand (a : X) : ProjectionBand X) : Set X) := by
          rw [principalProjectionBand_coe]; exact hy_in_dC
        have h0 : principalBandProjection (a : X) y = 0 :=
          bandProjection_eq_zero_of_mem_disjointComplement
            (principalProjectionBand (a : X)) hy_in_dC'
        rw [h0]
        exact hgnn a

/-- Every vector lattice with the principal projection property embeds as an
order dense sublattice into a direct product of vector lattices each carrying
a weak order unit. The factors are the principal bands generated by a maximal
disjoint family. -/
theorem exists_orderDense_embedding_into_orderComplete_with_weakOrderUnit
    [HasPrincipalProjectionProperty X] [IsOrderComplete X] [IsVLArchimedean X] :
    ∃ (ι : Type u) (Y : ι → Type u)
      (_ : ∀ i, AddCommGroup (Y i)) (_ : ∀ i, Lattice (Y i))
      (_ : ∀ i, IsOrderedAddMonoid (Y i)) (_ : ∀ i, VectorLattice (Y i))
      (_ : ∀ i, IsOrderComplete (Y i)),
      (∀ i, ∃ e : Y i, IsWeakOrderUnit e) ∧
      ∃ T : VecLatHom X (∀ i, Y i),
        Function.Injective T ∧ IsOrderDense (Set.range T) := by
  obtain ⟨Λ, hΛ⟩ := exists_isMaximalDisjoint X
  refine ⟨↥Λ, fun a => ↥(Band.principalBand (a : X)).toSubmodule,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, ?_, ?_⟩
  · -- Each principal band carries `a` itself as a weak order unit.
    intro a
    have ha_pos : (0 : X) < (a : X) := hΛ.prop.1 (a : X) a.property
    have ha_nn : (0 : X) ≤ (a : X) := ha_pos.le
    have ha_mem : (a : X) ∈ Band.principalBand (a : X) :=
      Band.subset_bandGenerated _ (Set.mem_singleton _)
    refine ⟨⟨(a : X), ha_mem⟩, ?_, ?_⟩
    · change (0 : X) ≤ (a : X)
      exact ha_nn
    · intro x hx
      apply Subtype.ext
      change x.val = (0 : X)
      have hx' : IsVLDisjoint x.val (a : X) := by
        have h := congrArg Subtype.val hx
        change |x.val| ⊓ |(a : X)| = 0 at h
        exact h
      exact isWeakOrderUnit_principalBand_self ha_nn x.val x.property hx'
  · exact exists_orderDense_lattice_embedding_of_isMaximalDisjoint hΛ
