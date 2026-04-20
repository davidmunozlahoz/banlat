import BanLat.Examples.CofK
import BanLat.Examples.SignedMeasure
import BanLat.Preliminaries.Baire
import BanLat.Sublattice

/-!
# The Banach lattice `M(K)` of regular signed Borel measures

For a compact Hausdorff space `K`, the classical space `M(K)` is the space of
**regular** signed Borel measures on `K`, equipped with the total-variation
norm. It is identified here as the closed sublattice of
`MeasureTheory.SignedMeasure K` cut out by the regularity predicate
`SignedMeasure.IsRegular`.

The first main result is that `M(K)` is Banach-lattice isometrically isomorphic
to the space `@SignedMeasure K (baire K)` of finite signed measures on the Baire
σ-algebra, via the unique regular Borel extension (`BaireMeasure.borelExtension`
from `BanLat.Preliminaries.Baire`). Since `SignedMeasure` on any measurable
space carries a canonical Banach-lattice structure (developed in
`BanLat.Examples.SignedMeasure`), all structural properties — AL-space, atoms,
principal bands — transfer to `M(K)` through this isomorphism.

The second main result is the **Riesz–Markov–Kakutani representation theorem**:
`M(K)` is Banach-lattice isometrically isomorphic to the norm dual `C(K, ℝ)*`,
assembling the duality results from `BanLat.Examples.CofK`.
-/

open MeasureTheory Set

/-! ### Closedness of the regularity predicate in the TV norm -/

namespace MeasureTheory.SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
/-- The real-valued Jordan positive parts of `u` and `v` differ on any measurable set by at
most `‖u - v‖`, using that `posPart` is a 1-Lipschitz lattice operation. -/
private lemma toReal_posPart_sub_le_norm_of_signed {u v : SignedMeasure K}
    {E : Set K} (hE : MeasurableSet E) :
    |(u.toJordanDecomposition.posPart E).toReal -
        (v.toJordanDecomposition.posPart E).toReal| ≤ ‖u - v‖ := by
  have h_u_eval : u.posPart E = (u.toJordanDecomposition.posPart E).toReal := by
    change u.toJordanDecomposition.posPart.toSignedMeasure E = _
    rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def]
  have h_v_eval : v.posPart E = (v.toJordanDecomposition.posPart E).toReal := by
    change v.toJordanDecomposition.posPart.toSignedMeasure E = _
    rw [Measure.toSignedMeasure_apply_measurable hE, measureReal_def]
  have h_eq_u : u ⊔ 0 = u.posPart := by rw [max_def, sub_zero, zero_add]
  have h_eq_v : v ⊔ 0 = v.posPart := by rw [max_def, sub_zero, zero_add]
  rw [← h_u_eval, ← h_v_eval, show u.posPart E - v.posPart E = (u.posPart - v.posPart) E from
      (VectorMeasure.sub_apply _ _ _).symm]
  calc |(u.posPart - v.posPart) E|
      ≤ ((u.posPart - v.posPart).totalVariation Set.univ).toReal :=
        abs_apply_le_totalVariation_univ _ hE
    _ = ‖u.posPart - v.posPart‖ := (norm_def _).symm
    _ = ‖u ⊔ 0 - v ⊔ 0‖ := by rw [h_eq_u, h_eq_v]
    _ ≤ ‖u - v‖ := norm_sup_sub_sup_le_norm u v 0

/-- The set of regular signed measures is closed in the total-variation
norm. -/
theorem isClosed_isRegular :
    IsClosed {s : SignedMeasure K | IsRegular s} := by
  refine isSeqClosed_iff_isClosed.mp fun {sₙ s} hsₙ hlim => ?_
  have key : ∀ {t : SignedMeasure K} {tₙ : ℕ → SignedMeasure K},
      (∀ n, (tₙ n).toJordanDecomposition.posPart.Regular) →
      Filter.Tendsto tₙ Filter.atTop (nhds t) →
      t.toJordanDecomposition.posPart.Regular := by
    intro t tₙ htₙ hlim'
    apply Measure.Regular.of_uniform_approx
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim' ε hε
    have hN' : ‖tₙ N - t‖ < ε := by
      have := hN N le_rfl; rwa [dist_eq_norm] at this
    refine ⟨(tₙ N).toJordanDecomposition.posPart, inferInstance, htₙ N, ?_⟩
    intro E hE
    exact lt_of_le_of_lt (toReal_posPart_sub_le_norm_of_signed hE) hN'
  have hpos := key (fun n => (hsₙ n).posPart_regular) hlim
  have hlim_neg : Filter.Tendsto (fun n => -(sₙ n)) Filter.atTop (nhds (-s)) := hlim.neg
  have hneg : s.toJordanDecomposition.negPart.Regular := by
    have h := key (fun n => by rw [toJordanDecomposition_neg]; exact (hsₙ n).negPart_regular)
      hlim_neg
    rw [toJordanDecomposition_neg] at h; exact h
  haveI := hpos; haveI := hneg
  change (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).Regular
  infer_instance

/-! ### `M(K)` as a closed vector sublattice -/

/-- The submodule of regular signed measures. -/
def regularSubmodule : Submodule ℝ (SignedMeasure K) where
  carrier := {s | IsRegular s}
  add_mem' := IsRegular.add
  zero_mem' := IsRegular.zero
  smul_mem' := IsRegular.smul

/-- The vector sublattice of regular signed measures. -/
noncomputable def regularSublattice : VectorSublattice (SignedMeasure K) :=
  VectorSublattice.ofAbsClosed regularSubmodule fun _ hs => IsRegular.abs hs

/-- `M(K)` — the Banach lattice of regular signed Borel measures on `K`. -/
abbrev _root_.MofK (K : Type*) [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] : Type _ :=
  ↥(regularSublattice (K := K)).toSubmodule

/-- Membership in the regular sublattice is regularity. -/
theorem mem_regularSublattice_iff {s : SignedMeasure K} :
    s ∈ regularSublattice (K := K) ↔ IsRegular s := Iff.rfl

/-- `M(K)` is closed as a subset of `SignedMeasure K`. -/
theorem isClosed_MofK :
    IsClosed (regularSublattice (K := K) : Set (SignedMeasure K)) :=
  isClosed_isRegular

/-- `M(K)` is a Banach lattice. -/
noncomputable instance instBanachLatticeMofK : BanachLattice (MofK K) :=
  VectorSublattice.instBanachLatticeSubtype _ isClosed_MofK

end MeasureTheory.SignedMeasure

/-! ### Isomorphism with signed Baire measures -/

section BaireEquiv

open MeasureTheory MeasureTheory.SignedMeasure BaireMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [Nonempty K]

private noncomputable instance instNACG_BaireSM :
    NormedAddCommGroup (@SignedMeasure K (baire K)) := by
  letI : MeasurableSpace K := baire K; infer_instance

private noncomputable instance instModule_BaireSM :
    Module ℝ (@SignedMeasure K (baire K)) := by
  letI : MeasurableSpace K := baire K; infer_instance

private noncomputable instance instLattice_BaireSM :
    Lattice (@SignedMeasure K (baire K)) := by
  letI : MeasurableSpace K := baire K; infer_instance

private noncomputable instance instIOAM_BaireSM :
    IsOrderedAddMonoid (@SignedMeasure K (baire K)) := by
  letI : MeasurableSpace K := baire K; infer_instance

private noncomputable instance instBL_BaireSM :
    BanachLattice (@SignedMeasure K (baire K)) := by
  letI : MeasurableSpace K := baire K; infer_instance

private noncomputable instance instAL_BaireSM :
    ALSpace (@SignedMeasure K (baire K)) := by
  letI : MeasurableSpace K := baire K; infer_instance

/-- `M(K)` is isometrically isomorphic as a Banach lattice to the space of
finite signed measures on the Baire σ-algebra of `K`. The forward map is
restriction to Baire-measurable sets; the inverse is the unique regular Borel
extension. -/
noncomputable def MofK.baireEquiv :
    BanachLatEquiv (MofK K) (@SignedMeasure K (baire K)) := by
  have hmeas := BorelSpace.measurable_eq (α := K)
  subst hmeas
  letI : MeasurableSpace K := borel K
  set hle : baire K ≤ borel K := baire_le_borel (α := K) with hle_def
  -- Forward: μ ↦ μ.trim hle
  let fwd : SignedMeasure K → @SignedMeasure K (baire K) := fun μ => μ.trim hle
  -- Inverse: s ↦ borelExtension s
  let invf : @SignedMeasure K (baire K) → SignedMeasure K := fun s => borelExtension s
  -- Apply-on-Baire agreement
  have fwd_apply : ∀ (μ : SignedMeasure K) {t : Set K},
      @MeasurableSet K (baire K) t → fwd μ t = μ t :=
    fun _ _ ht => VectorMeasure.trim_measurableSet_eq hle ht
  have invf_apply : ∀ (s : @SignedMeasure K (baire K)) {t : Set K},
      @MeasurableSet K (baire K) t → invf s t = s t :=
    fun s _ ht => borelExtension_apply s ht
  have invf_regular : ∀ s : @SignedMeasure K (baire K), (invf s).IsRegular :=
    fun s => borelExtension_regular s
  -- Left/right inverse
  have left_inv : ∀ (μ : SignedMeasure K), μ.IsRegular → invf (fwd μ) = μ := fun μ hμ =>
    (borelExtension_unique (fwd μ) μ hμ (fun _ ht => (fwd_apply μ ht).symm)).symm
  have right_inv : ∀ s : @SignedMeasure K (baire K), fwd (invf s) = s := fun s => by
    refine VectorMeasure.ext fun t ht => ?_
    rw [fwd_apply (invf s) ht, invf_apply s ht]
  -- Linearity of fwd
  have fwd_add : ∀ μ ν : SignedMeasure K, fwd (μ + ν) = fwd μ + fwd ν := fun μ ν => by
    refine VectorMeasure.ext fun t ht => ?_
    rw [fwd_apply _ ht, VectorMeasure.add_apply, VectorMeasure.add_apply,
        fwd_apply _ ht, fwd_apply _ ht]
  have fwd_smul : ∀ (c : ℝ) (μ : SignedMeasure K), fwd (c • μ) = c • fwd μ := fun c μ => by
    refine VectorMeasure.ext fun t ht => ?_
    rw [fwd_apply _ ht, VectorMeasure.smul_apply, VectorMeasure.smul_apply, fwd_apply _ ht]
  have fwd_neg : ∀ (μ : SignedMeasure K), fwd (-μ) = -fwd μ := fun μ => by
    refine VectorMeasure.ext fun t ht => ?_
    rw [fwd_apply _ ht, VectorMeasure.neg_apply, VectorMeasure.neg_apply, fwd_apply _ ht]
  have fwd_sub : ∀ μ ν : SignedMeasure K, fwd (μ - ν) = fwd μ - fwd ν := fun μ ν => by
    rw [sub_eq_add_neg, sub_eq_add_neg, fwd_add, fwd_neg]
  -- Positivity preservation
  have fwd_nonneg : ∀ {μ : SignedMeasure K}, 0 ≤ μ → 0 ≤ fwd μ := fun {μ} hμ t ht => by
    rw [VectorMeasure.zero_apply, fwd_apply _ ht]
    have := hμ t (hle t ht)
    rwa [VectorMeasure.zero_apply] at this
  have invf_nonneg : ∀ {s : @SignedMeasure K (baire K)}, 0 ≤ s → 0 ≤ invf s :=
    fun hs => borelExtension_nonneg hs
  have fwd_nonneg_iff : ∀ {μ : SignedMeasure K}, μ.IsRegular → (0 ≤ fwd μ ↔ 0 ≤ μ) := by
    intro μ hμ
    refine ⟨fun h => ?_, fwd_nonneg⟩
    have h' := invf_nonneg h
    rwa [left_inv μ hμ] at h'
  -- Order preservation biconditional
  have fwd_le_iff : ∀ {μ ν : SignedMeasure K}, μ.IsRegular → ν.IsRegular →
      (fwd μ ≤ fwd ν ↔ μ ≤ ν) := by
    intros μ ν hμ hν
    constructor
    · intro h
      have h1 : 0 ≤ fwd (ν - μ) := by rw [fwd_sub]; exact sub_nonneg.mpr h
      exact sub_nonneg.mp ((fwd_nonneg_iff (SignedMeasure.IsRegular.sub hν hμ)).mp h1)
    · intro h
      have h1 : 0 ≤ fwd (ν - μ) := fwd_nonneg (sub_nonneg.mpr h)
      rw [fwd_sub] at h1
      exact sub_nonneg.mp h1
  -- Norm preservation
  have norm_le_fwd : ∀ (μ : SignedMeasure K), μ.IsRegular → ‖μ‖ ≤ ‖fwd μ‖ := fun μ hμ => by
    calc ‖μ‖ = ‖invf (fwd μ)‖ := by rw [left_inv μ hμ]
      _ = ‖borelExtension (fwd μ)‖ := rfl
      _ ≤ ‖fwd μ‖ := borelExtension_norm_le (fwd μ)
  have norm_fwd_nn : ∀ (s : SignedMeasure K), 0 ≤ s → ‖fwd s‖ = ‖s‖ := fun s hs => by
    have hfwd_nn : (0 : @SignedMeasure K (baire K)) ≤ fwd s := fwd_nonneg hs
    have h1 : ‖fwd s‖ = ((fwd s : @SignedMeasure K (baire K)) Set.univ : ℝ) :=
      @SignedMeasure.norm_of_nonneg K (baire K) (fwd s) hfwd_nn
    have h2 : ‖s‖ = (s Set.univ : ℝ) := SignedMeasure.norm_of_nonneg hs
    rw [h1, h2]
    exact fwd_apply s (@MeasurableSet.univ K (baire K))
  have norm_fwd_le : ∀ (μ : SignedMeasure K), ‖fwd μ‖ ≤ ‖μ‖ := fun μ => by
    set P := μ.toJordanDecomposition.posPart with hP_def
    set N := μ.toJordanDecomposition.negPart with hN_def
    have hμ_eq : μ = P.toSignedMeasure - N.toSignedMeasure :=
      (SignedMeasure.toSignedMeasure_toJordanDecomposition μ).symm
    have hP_nn : (0 : SignedMeasure K) ≤ P.toSignedMeasure := Measure.zero_le_toSignedMeasure _
    have hN_nn : (0 : SignedMeasure K) ≤ N.toSignedMeasure := Measure.zero_le_toSignedMeasure _
    have h_sum : ‖P.toSignedMeasure‖ + ‖N.toSignedMeasure‖ = ‖μ‖ := by
      rw [SignedMeasure.norm_of_nonneg hP_nn, SignedMeasure.norm_of_nonneg hN_nn,
          Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
          Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
          SignedMeasure.norm_def μ]
      unfold SignedMeasure.totalVariation
      rw [Measure.add_apply, measureReal_def, measureReal_def,
          ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have hfwd_eq : fwd μ = fwd P.toSignedMeasure - fwd N.toSignedMeasure := by
      conv_lhs => rw [hμ_eq]
      exact fwd_sub P.toSignedMeasure N.toSignedMeasure
    calc ‖fwd μ‖
        = ‖fwd P.toSignedMeasure - fwd N.toSignedMeasure‖ := by rw [hfwd_eq]
      _ ≤ ‖fwd P.toSignedMeasure‖ + ‖fwd N.toSignedMeasure‖ := norm_sub_le _ _
      _ = ‖P.toSignedMeasure‖ + ‖N.toSignedMeasure‖ := by
          rw [norm_fwd_nn _ hP_nn, norm_fwd_nn _ hN_nn]
      _ = ‖μ‖ := h_sum
  have norm_eq : ∀ (μ : MofK K), ‖fwd μ.val‖ = ‖μ.val‖ := fun μ =>
    le_antisymm (norm_fwd_le μ.val) (norm_le_fwd μ.val μ.property)
  have sup_reg : ∀ {μ ν : SignedMeasure K}, μ.IsRegular → ν.IsRegular →
      (μ ⊔ ν).IsRegular := fun hμ hν => regularSublattice.sup_mem hμ hν
  have inf_reg : ∀ {μ ν : SignedMeasure K}, μ.IsRegular → ν.IsRegular →
      (μ ⊓ ν).IsRegular := fun hμ hν => regularSublattice.inf_mem hμ hν
  have fwd_sup : ∀ (μ ν : SignedMeasure K), μ.IsRegular → ν.IsRegular →
      fwd (μ ⊔ ν) = fwd μ ⊔ fwd ν := fun μ ν hμ hν => by
    have hsup_reg : (μ ⊔ ν).IsRegular := sup_reg hμ hν
    apply le_antisymm
    · have hz_reg : (invf (fwd μ ⊔ fwd ν)).IsRegular := invf_regular _
      have hz_eq : fwd (invf (fwd μ ⊔ fwd ν)) = fwd μ ⊔ fwd ν := right_inv _
      have hμ_le : μ ≤ invf (fwd μ ⊔ fwd ν) := by
        apply (fwd_le_iff hμ hz_reg).mp
        rw [hz_eq]; exact le_sup_left
      have hν_le : ν ≤ invf (fwd μ ⊔ fwd ν) := by
        apply (fwd_le_iff hν hz_reg).mp
        rw [hz_eq]; exact le_sup_right
      have h := (fwd_le_iff hsup_reg hz_reg).mpr (sup_le hμ_le hν_le)
      rwa [hz_eq] at h
    · exact sup_le ((fwd_le_iff hμ hsup_reg).mpr le_sup_left)
                   ((fwd_le_iff hν hsup_reg).mpr le_sup_right)
  have fwd_inf : ∀ (μ ν : SignedMeasure K), μ.IsRegular → ν.IsRegular →
      fwd (μ ⊓ ν) = fwd μ ⊓ fwd ν := fun μ ν hμ hν => by
    have hinf_reg : (μ ⊓ ν).IsRegular := inf_reg hμ hν
    apply le_antisymm
    · exact le_inf ((fwd_le_iff hinf_reg hμ).mpr inf_le_left)
                   ((fwd_le_iff hinf_reg hν).mpr inf_le_right)
    · have hz_reg : (invf (fwd μ ⊓ fwd ν)).IsRegular := invf_regular _
      have hz_eq : fwd (invf (fwd μ ⊓ fwd ν)) = fwd μ ⊓ fwd ν := right_inv _
      have hle_μ : invf (fwd μ ⊓ fwd ν) ≤ μ := by
        apply (fwd_le_iff hz_reg hμ).mp
        rw [hz_eq]; exact inf_le_left
      have hle_ν : invf (fwd μ ⊓ fwd ν) ≤ ν := by
        apply (fwd_le_iff hz_reg hν).mp
        rw [hz_eq]; exact inf_le_right
      have h := (fwd_le_iff hz_reg hinf_reg).mpr (le_inf hle_μ hle_ν)
      rwa [hz_eq] at h
  -- Assemble the BanachLatEquiv
  exact {
    toLinearIsometryEquiv :=
      { toFun := fun μ => fwd μ.val
        invFun := fun s => ⟨invf s, invf_regular s⟩
        map_add' := fun μ ν => fwd_add μ.val ν.val
        map_smul' := fun c μ => fwd_smul c μ.val
        left_inv := fun μ => Subtype.ext (left_inv μ.val μ.property)
        right_inv := right_inv
        norm_map' := norm_eq }
    map_sup' := fun μ ν => fwd_sup μ.val ν.val μ.property ν.property
    map_inf' := fun μ ν => fwd_inf μ.val ν.val μ.property ν.property }

end BaireEquiv

/-! ### Riesz representation: `M(K) ≃ C(K, ℝ)*` -/

section Riesz

open MeasureTheory MeasureTheory.SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [Nonempty K]

/-- The linear equivalence underlying the Riesz–Markov–Kakutani isomorphism. -/
private noncomputable def rieszLinearEquiv :
    MofK K ≃ₗ[ℝ] NormDualSpace C(K, ℝ) where
  toFun μ := signedMeasureFunctional μ.val
  invFun φ := ⟨rieszSignedMeasure φ, rieszSignedMeasure_isRegular φ⟩
  left_inv μ :=
    Subtype.ext (rieszSignedMeasure_signedMeasureFunctional μ.property)
  right_inv := signedMeasureFunctional_rieszSignedMeasure
  map_add' μ ν := signedMeasureFunctional_add μ.val ν.val
  map_smul' c μ := signedMeasureFunctional_smul c μ.val

/-- **Riesz–Markov–Kakutani representation theorem** for `C(K, ℝ)`. -/
noncomputable def rieszEquiv :
    BanachLatEquiv (MofK K) (NormDualSpace C(K, ℝ)) where
  toLinearIsometryEquiv :=
    { rieszLinearEquiv with
      norm_map' := fun μ => norm_signedMeasureFunctional μ.property }
  map_sup' μ ν := signedMeasureFunctional_sup μ.property ν.property
  map_inf' μ ν := signedMeasureFunctional_inf μ.property ν.property

@[simp]
theorem rieszEquiv_apply (μ : MofK K) (f : C(K, ℝ)) :
    rieszEquiv μ f = signedMeasureIntegral μ.val f :=
  signedMeasureFunctional_apply μ.val f

/-- The Riesz isomorphism preserves positivity. -/
theorem rieszEquiv_nonneg_iff {μ : MofK K} :
    0 ≤ (rieszEquiv : BanachLatEquiv (MofK K) _) μ ↔ 0 ≤ μ :=
  signedMeasureFunctional_nonneg_iff μ.property

end Riesz

/-! ### AL-space structure on `M(K)` -/

noncomputable instance MeasureTheory.SignedMeasure.instALSpaceMofK
    {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] : ALSpace (MofK K) where
  norm_add_eq_of_nonneg {x y} hx hy := by
    change ‖x.val + y.val‖ = ‖x.val‖ + ‖y.val‖
    exact ALSpace.norm_add_eq_of_nonneg hx hy

/-! ### Atoms and Dirac deltas in `M(K)` -/

section Atoms

open MeasureTheory MeasureTheory.SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [Nonempty K]
  [@MeasurableSingletonClass K (baire K)]

noncomputable def MofK.dirac (x : K) : MofK K :=
  MofK.baireEquiv.toLinearIsometryEquiv.symm
    (@SignedMeasure.dirac K (baire K) x)

set_option maxHeartbeats 400000 in
-- transferring positivity through `baireEquiv.symm` is unification-heavy
omit [@MeasurableSingletonClass K (baire K)] in
theorem MofK.zero_le_dirac (x : K) : 0 ≤ MofK.dirac x := by
  have hδ : (0 : @SignedMeasure K (baire K)) ≤ @SignedMeasure.dirac K (baire K) x :=
    @SignedMeasure.zero_le_dirac K (baire K) x
  let φ : MofK K ≃ₗᵢ[ℝ] @SignedMeasure K (baire K) :=
    MofK.baireEquiv.toLinearIsometryEquiv
  change 0 ≤ φ.symm (@SignedMeasure.dirac K (baire K) x)
  have h0 : φ.symm 0 = 0 := φ.symm.map_zero
  have hφsup : ∀ (a b : MofK K), φ (a ⊔ b) = φ a ⊔ φ b := MofK.baireEquiv.map_sup'
  have hsup : φ.symm (0 ⊔ @SignedMeasure.dirac K (baire K) x) =
      φ.symm 0 ⊔ φ.symm (@SignedMeasure.dirac K (baire K) x) := by
    apply φ.injective
    rw [φ.apply_symm_apply, hφsup, φ.apply_symm_apply, φ.apply_symm_apply]
  rw [sup_eq_right.mpr hδ, h0] at hsup
  exact le_sup_left.trans hsup.symm.le

omit [@MeasurableSingletonClass K (baire K)] in
theorem MofK.norm_dirac (x : K) : ‖MofK.dirac x‖ = 1 := by
  change ‖MofK.baireEquiv.toLinearIsometryEquiv.symm _‖ = 1
  rw [LinearIsometryEquiv.norm_map]
  exact @SignedMeasure.norm_dirac K (baire K) x

omit [@MeasurableSingletonClass K (baire K)] in
theorem MofK.dirac_ne_zero (x : K) : MofK.dirac x ≠ 0 := by
  rw [ne_eq, ← norm_eq_zero, MofK.norm_dirac]; exact one_ne_zero

set_option maxHeartbeats 400000 in
-- transferring lattice-disjointness through `baireEquiv.symm` is unification-heavy
theorem MofK.isVLDisjoint_dirac_of_ne {x y : K} (h : x ≠ y) :
    IsVLDisjoint (MofK.dirac x) (MofK.dirac y) := by
  have hB : IsVLDisjoint (@SignedMeasure.dirac K (baire K) x)
      (@SignedMeasure.dirac K (baire K) y) :=
    @SignedMeasure.isVLDisjoint_dirac_of_ne K (baire K) _ x y h
  let φ : MofK K ≃ₗᵢ[ℝ] @SignedMeasure K (baire K) :=
    MofK.baireEquiv.toLinearIsometryEquiv
  have hφsup_fwd : ∀ (a b : MofK K), φ (a ⊔ b) = φ a ⊔ φ b := MofK.baireEquiv.map_sup'
  have hφinf_fwd : ∀ (a b : MofK K), φ (a ⊓ b) = φ a ⊓ φ b := MofK.baireEquiv.map_inf'
  have hφsup : ∀ (a b : @SignedMeasure K (baire K)),
      φ.symm (a ⊔ b) = φ.symm a ⊔ φ.symm b := fun a b => by
    apply φ.injective
    rw [φ.apply_symm_apply, hφsup_fwd, φ.apply_symm_apply, φ.apply_symm_apply]
  have hφabs : ∀ (a : @SignedMeasure K (baire K)), φ.symm (|a|) = |φ.symm a| := fun a => by
    change φ.symm (a ⊔ -a) = _
    rw [hφsup]
    change φ.symm a ⊔ φ.symm (-a) = φ.symm a ⊔ -φ.symm a
    rw [map_neg]
  have hφinf : ∀ (a b : @SignedMeasure K (baire K)),
      φ.symm (a ⊓ b) = φ.symm a ⊓ φ.symm b := fun a b => by
    apply φ.injective
    rw [φ.apply_symm_apply, hφinf_fwd, φ.apply_symm_apply, φ.apply_symm_apply]
  change |MofK.dirac x| ⊓ |MofK.dirac y| = 0
  change |φ.symm (@SignedMeasure.dirac K (baire K) x)| ⊓
    |φ.symm (@SignedMeasure.dirac K (baire K) y)| = 0
  rw [← hφabs, ← hφabs, ← hφinf,
      show |@SignedMeasure.dirac K (baire K) x| ⊓
        |@SignedMeasure.dirac K (baire K) y| = 0 from hB]
  exact φ.symm.map_zero

set_option maxHeartbeats 400000 in
-- transferring atom property through `baireEquiv` is unification-heavy
theorem MofK.isVLAtom_dirac (x : K) : IsVLAtom (MofK.dirac x) := by
  refine ⟨lt_of_le_of_ne (MofK.zero_le_dirac x) (Ne.symm (MofK.dirac_ne_zero x)), ?_⟩
  let φ : MofK K ≃ₗᵢ[ℝ] @SignedMeasure K (baire K) :=
    MofK.baireEquiv.toLinearIsometryEquiv
  have hδ : IsVLAtom (@SignedMeasure.dirac K (baire K) x) :=
    @SignedMeasure.isVLAtom_dirac K (baire K) _ x
  have hφ_sup : ∀ a b : MofK K, φ (a ⊔ b) = φ a ⊔ φ b := MofK.baireEquiv.map_sup'
  have hφ_le : ∀ {a b : MofK K}, φ a ≤ φ b ↔ a ≤ b := by
    intros a b
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have heq : φ a ⊔ φ b = φ b := sup_eq_right.mpr h
      rw [← hφ_sup] at heq
      exact sup_eq_right.mp (φ.injective heq)
    · rw [show b = a ⊔ b from (sup_eq_right.mpr h).symm, hφ_sup]
      exact le_sup_left
  intro y hy0 hyd
  have h_eq : φ (MofK.dirac x) = @SignedMeasure.dirac K (baire K) x := φ.apply_symm_apply _
  have hφ0 : (φ (0 : MofK K) : @SignedMeasure K (baire K)) = 0 := φ.map_zero
  have hφy_nn : (0 : @SignedMeasure K (baire K)) ≤ φ y := hφ0 ▸ hφ_le.mpr hy0
  have hφy_le : φ y ≤ @SignedMeasure.dirac K (baire K) x := h_eq ▸ hφ_le.mpr hyd
  obtain ⟨c, hc⟩ := hδ.2 (φ y) hφy_nn hφy_le
  refine ⟨c, ?_⟩
  have h1 : y = φ.symm (φ y) := (φ.symm_apply_apply y).symm
  rw [h1, hc, map_smul]
  rfl

theorem MofK.isVLAtom_smul_dirac {c : ℝ} (hc : 0 < c) (x : K) :
    IsVLAtom (c • MofK.dirac x) :=
  MofK.isVLAtom_dirac x |>.smul hc

/-- **Atoms of `M(K)` are exactly the positive multiples of Dirac deltas.** A
regular signed Borel measure on `K` is a vector-lattice atom of `M(K)` iff it
is a strictly positive scalar multiple of some Dirac delta `δ_x`. -/
theorem MofK.isVLAtom_iff_exists_smul_dirac (s : MofK K) :
    IsVLAtom s ↔ ∃ (c : ℝ) (x : K), 0 < c ∧ s = c • MofK.dirac x :=
  sorry

end Atoms

/-! ### Principal bands and `L¹` in `M(K)` -/

section PrincipalBands

open MeasureTheory MeasureTheory.SignedMeasure BaireMeasure

universe u

variable {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [Nonempty K]

/-- Transfer of principal bands by a Banach lattice equivalence, for non-negative
elements. -/
private lemma principalBand_image_mem_of_bLE
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    [IsOrderContinuousNorm A]
    (φ : BanachLatEquiv A B)
    {a z : A} (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hmem : z ∈ Band.principalBand a) :
    φ z ∈ Band.principalBand (φ a) := by
  set T : A →L[ℝ] B := φ.toContinuousLinearEquiv.toContinuousLinearMap
  have hsup : ∀ x y : A, T (x ⊔ y) = T x ⊔ T y := φ.map_sup'
  have hinf : ∀ x y : A, T (x ⊓ y) = T x ⊓ T y := φ.map_inf'
  have hTa_nn : 0 ≤ T a := by
    have heq : T a = T a ⊔ 0 := by
      rw [← map_zero T, ← hsup, sup_of_le_left ha]
    exact le_sup_right.trans heq.symm.le
  have hTz_nn : 0 ≤ T z := by
    have heq : T z = T z ⊔ 0 := by
      rw [← map_zero T, ← hsup, sup_of_le_left hz]
    exact le_sup_right.trans heq.symm.le
  have hlub : IsLUB (Set.range (fun n : ℕ => z ⊓ n • a)) z :=
    (Band.mem_principalBand_iff_isLUB ha hz).mp hmem
  set u : ℕ → A := fun n => z ⊓ n • a
  have hu_mono : Monotone u := fun m n hmn =>
    inf_le_inf_left z (nsmul_le_nsmul_left ha hmn)
  have hu_bdd : BddAbove (Set.range u) :=
    ⟨z, by rintro _ ⟨n, rfl⟩; exact inf_le_left⟩
  obtain ⟨z', hz'_lub, htend⟩ :=
    BanachLattice.tendsto_of_monotone_bddAbove hu_mono hu_bdd
  have hz'_eq : z' = z := IsLUB.unique hz'_lub hlub
  rw [hz'_eq] at htend
  have hTtend : Filter.Tendsto (fun n => T (u n)) Filter.atTop (nhds (T z)) :=
    T.continuous.tendsto z |>.comp htend
  have hT_u : ∀ n, T (u n) = T z ⊓ n • T a := fun n => by
    change T (z ⊓ n • a) = T z ⊓ n • T a
    rw [hinf z (n • a), map_nsmul T n a]
  have hTu_mem : ∀ n, T (u n) ∈ (Band.principalBand (T a) : Set B) := fun n => by
    rw [hT_u n]
    apply Band.principal_le_principalBand
    refine ⟨n, n.cast_nonneg, ?_⟩
    have h_nn : 0 ≤ T z ⊓ n • T a := le_inf hTz_nn (nsmul_nonneg hTa_nn n)
    rw [abs_of_nonneg h_nn, abs_of_nonneg hTa_nn, Nat.cast_smul_eq_nsmul]
    exact inf_le_right
  exact (Band.isClosed_coe _).mem_of_tendsto hTtend
    (Filter.Eventually.of_forall hTu_mem)

/-- Transfer of principal bands by a Banach lattice equivalence. -/
private lemma principalBand_image_mem_of_bLE_general
    {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [Lattice A] [Lattice B]
    [IsOrderedAddMonoid A] [IsOrderedAddMonoid B]
    [BanachLattice A] [BanachLattice B]
    [IsOrderContinuousNorm A]
    (φ : BanachLatEquiv A B)
    {a z : A} (ha : 0 ≤ a) (hmem : z ∈ Band.principalBand a) :
    φ z ∈ Band.principalBand (φ a) := by
  have habs : |z| ∈ Band.principalBand a := (Band.principalBand a).abs_mem hmem
  have hp_nn : 0 ≤ z⁺ := posPart_nonneg z
  have hn_nn : 0 ≤ z⁻ := negPart_nonneg z
  have hp_le : z⁺ ≤ |z| := by
    rw [← posPart_add_negPart z]; exact le_add_of_nonneg_right hn_nn
  have hn_le : z⁻ ≤ |z| := by
    rw [← posPart_add_negPart z]; exact le_add_of_nonneg_left hp_nn
  have hp_mem : z⁺ ∈ Band.principalBand a :=
    (Band.principalBand a).solid habs hp_nn hp_le
  have hn_mem : z⁻ ∈ Band.principalBand a :=
    (Band.principalBand a).solid habs hn_nn hn_le
  have hφp : φ z⁺ ∈ Band.principalBand (φ a) :=
    principalBand_image_mem_of_bLE φ ha hp_nn hp_mem
  have hφn : φ z⁻ ∈ Band.principalBand (φ a) :=
    principalBand_image_mem_of_bLE φ ha hn_nn hn_mem
  have hdecomp : φ z = φ z⁺ - φ z⁻ := by
    have h : (z⁺ - z⁻ : A) = z := posPart_sub_negPart z
    conv_lhs => rw [← h]
    change φ.toLinearIsometryEquiv (z⁺ - z⁻) = _
    exact map_sub _ _ _
  rw [hdecomp]
  exact (Band.principalBand (φ a)).toSubmodule.sub_mem hφp hφn

/-- The symmetric map of `MofK.baireEquiv` viewed as a Banach-lattice
equivalence. -/
private noncomputable def MofK.baireEquiv_symm :
    BanachLatEquiv (@SignedMeasure K (baire K)) (MofK K) := by
  set φ : BanachLatEquiv (MofK K) (@SignedMeasure K (baire K)) := MofK.baireEquiv
  have hsymm_sup : ∀ (b c : @SignedMeasure K (baire K)),
      φ.toLinearIsometryEquiv.symm (b ⊔ c) =
        φ.toLinearIsometryEquiv.symm b ⊔ φ.toLinearIsometryEquiv.symm c := by
    intro b c
    apply φ.toLinearIsometryEquiv.injective
    have h1 : φ (φ.toLinearIsometryEquiv.symm b ⊔ φ.toLinearIsometryEquiv.symm c) =
        φ (φ.toLinearIsometryEquiv.symm b) ⊔ φ (φ.toLinearIsometryEquiv.symm c) :=
      φ.map_sup' _ _
    rw [φ.toLinearIsometryEquiv.apply_symm_apply]
    change b ⊔ c = φ (φ.toLinearIsometryEquiv.symm b ⊔ φ.toLinearIsometryEquiv.symm c)
    rw [h1]
    change b ⊔ c = φ.toLinearIsometryEquiv (φ.toLinearIsometryEquiv.symm b) ⊔
      φ.toLinearIsometryEquiv (φ.toLinearIsometryEquiv.symm c)
    rw [φ.toLinearIsometryEquiv.apply_symm_apply,
        φ.toLinearIsometryEquiv.apply_symm_apply]
  have hsymm_inf : ∀ (b c : @SignedMeasure K (baire K)),
      φ.toLinearIsometryEquiv.symm (b ⊓ c) =
        φ.toLinearIsometryEquiv.symm b ⊓ φ.toLinearIsometryEquiv.symm c := by
    intro b c
    apply φ.toLinearIsometryEquiv.injective
    have h1 : φ (φ.toLinearIsometryEquiv.symm b ⊓ φ.toLinearIsometryEquiv.symm c) =
        φ (φ.toLinearIsometryEquiv.symm b) ⊓ φ (φ.toLinearIsometryEquiv.symm c) :=
      φ.map_inf' _ _
    rw [φ.toLinearIsometryEquiv.apply_symm_apply]
    change b ⊓ c = φ (φ.toLinearIsometryEquiv.symm b ⊓ φ.toLinearIsometryEquiv.symm c)
    rw [h1]
    change b ⊓ c = φ.toLinearIsometryEquiv (φ.toLinearIsometryEquiv.symm b) ⊓
      φ.toLinearIsometryEquiv (φ.toLinearIsometryEquiv.symm c)
    rw [φ.toLinearIsometryEquiv.apply_symm_apply,
        φ.toLinearIsometryEquiv.apply_symm_apply]
  exact
    { toLinearIsometryEquiv := φ.toLinearIsometryEquiv.symm
      map_sup' := hsymm_sup
      map_inf' := hsymm_inf }

/-- `baireEquiv` restricts to a Banach-lattice equivalence between principal
bands. -/
private noncomputable def MofK.principalBand_baireEquiv {μ : MofK K} (hμ : 0 ≤ μ) :
    BanachLatEquiv ↥(Band.principalBand μ).toSubmodule
      ↥(Band.principalBand (MofK.baireEquiv μ)).toSubmodule := by
  set φ : BanachLatEquiv (MofK K) (@SignedMeasure K (baire K)) := MofK.baireEquiv
  let φs : BanachLatEquiv (@SignedMeasure K (baire K)) (MofK K) := MofK.baireEquiv_symm
  have hμ' : (0 : @SignedMeasure K (baire K)) ≤ φ μ := by
    have h0 : φ (0 : MofK K) = 0 := φ.toLinearIsometryEquiv.map_zero
    have hs : φ (0 ⊔ μ) = φ 0 ⊔ φ μ := φ.map_sup' 0 μ
    rw [sup_eq_right.mpr hμ, h0] at hs
    exact le_sup_left.trans hs.symm.le
  have hφsymm_μ : φs (φ μ) = μ :=
    φ.toLinearIsometryEquiv.symm_apply_apply μ
  have hmem_fwd : ∀ {v : MofK K}, v ∈ Band.principalBand μ →
      φ v ∈ Band.principalBand (φ μ) :=
    fun hv => principalBand_image_mem_of_bLE_general φ hμ hv
  have hmem_bwd : ∀ {w : @SignedMeasure K (baire K)},
      w ∈ Band.principalBand (φ μ) →
      φs w ∈ Band.principalBand μ := by
    intro w hw
    have h := principalBand_image_mem_of_bLE_general φs hμ' hw
    rwa [hφsymm_μ] at h
  refine
    { toLinearIsometryEquiv :=
        { toFun := fun v => ⟨φ v.val, hmem_fwd v.property⟩
          invFun := fun w => ⟨φs w.val, hmem_bwd w.property⟩
          map_add' := fun v w => Subtype.ext (by
            change φ.toLinearIsometryEquiv (v.val + w.val) =
              φ.toLinearIsometryEquiv v.val + φ.toLinearIsometryEquiv w.val
            exact map_add _ _ _)
          map_smul' := fun c v => Subtype.ext (by
            change φ.toLinearIsometryEquiv (c • v.val) =
              c • φ.toLinearIsometryEquiv v.val
            exact map_smul _ _ _)
          left_inv := fun v => Subtype.ext
            (φ.toLinearIsometryEquiv.symm_apply_apply _)
          right_inv := fun w => Subtype.ext
            (φ.toLinearIsometryEquiv.apply_symm_apply _)
          norm_map' := fun v => φ.toLinearIsometryEquiv.norm_map _ }
      map_sup' := fun v w => Subtype.ext (φ.map_sup' _ _)
      map_inf' := fun v w => Subtype.ext (φ.map_inf' _ _) }

theorem MofK.exists_principalBand_banachLatEquivL1 {μ : MofK K} (hμ : 0 ≤ μ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (ν : Measure Ω) (_ : IsFiniteMeasure ν),
      Nonempty (BanachLatEquiv ↥(Band.principalBand μ).toSubmodule (Lp ℝ 1 ν)) := by
  set φ : BanachLatEquiv (MofK K) (@SignedMeasure K (baire K)) := MofK.baireEquiv
  have hμ' : (0 : @SignedMeasure K (baire K)) ≤ φ μ := by
    have h0 : φ (0 : MofK K) = 0 := φ.toLinearIsometryEquiv.map_zero
    have hs : φ (0 ⊔ μ) = φ 0 ⊔ φ μ := φ.map_sup' 0 μ
    rw [sup_eq_right.mpr hμ, h0] at hs
    exact le_sup_left.trans hs.symm.le
  let β : BanachLatEquiv ↥(Band.principalBand μ).toSubmodule
      ↥(Band.principalBand (φ μ)).toSubmodule := MofK.principalBand_baireEquiv hμ
  -- Extract posPart and finiteness from the Jordan decomposition of φ μ on baire K
  let jd := @MeasureTheory.SignedMeasure.toJordanDecomposition K (baire K) (φ μ)
  haveI hpos_fin : @MeasureTheory.IsFiniteMeasure K (baire K)
      (@MeasureTheory.JordanDecomposition.posPart K (baire K) jd) :=
    @MeasureTheory.JordanDecomposition.posPart_finite K (baire K) jd
  let γ := @MeasureTheory.SignedMeasure.principalBandBanachLatEquivL1 K (baire K) (φ μ) hμ'
  have h_sup : ∀ v w : ↥(Band.principalBand μ).toSubmodule,
      γ (β (v ⊔ w)) = γ (β v) ⊔ γ (β w) := fun v w => by
    have h1 : β (v ⊔ w) = β v ⊔ β w := β.map_sup' v w
    have h2 : γ (β v ⊔ β w) = γ (β v) ⊔ γ (β w) := γ.map_sup' _ _
    rw [h1, h2]
  have h_inf : ∀ v w : ↥(Band.principalBand μ).toSubmodule,
      γ (β (v ⊓ w)) = γ (β v) ⊓ γ (β w) := fun v w => by
    have h1 : β (v ⊓ w) = β v ⊓ β w := β.map_inf' v w
    have h2 : γ (β v ⊓ β w) = γ (β v) ⊓ γ (β w) := γ.map_inf' _ _
    rw [h1, h2]
  let ψ := ({ toLinearIsometryEquiv := β.toLinearIsometryEquiv.trans γ.toLinearIsometryEquiv
              map_sup' := h_sup
              map_inf' := h_inf } : BanachLatEquiv _ _)
  exact ⟨_, _, _, hpos_fin, ⟨ψ⟩⟩

end PrincipalBands

/-! ### Discrete + continuous decomposition

By `BanLat.Atom`, every Archimedean vector lattice splits formally into an
**atomic part** (the band generated by all atoms) and a **continuous part**
(the disjoint complement of the atoms). For `M(K)` these abstract bands
admit concrete descriptions:

* an element of the **continuous part** is a measure that vanishes on every
  singleton;
* an element of the **atomic part** is a norm-convergent countable series of
  weighted Dirac masses, supported on pairwise distinct points.

Combining these characterisations with the abstract decomposition yields the
classical fact that every regular signed Borel measure on `K` is the sum of a
countable sum of Diracs and a continuous measure. -/

section Decomposition

open MeasureTheory MeasureTheory.SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [Nonempty K]
  [@MeasurableSingletonClass K (baire K)]

/-- Subset monotonicity for non-negative signed measures. -/
private lemma signedMeasure_apply_le_apply_of_subset {α : Type*} [MeasurableSpace α]
    {s : SignedMeasure α} (hs : 0 ≤ s) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) : s A ≤ s B := by
  have hBdiffA : MeasurableSet (B \ A) := hB.diff hA
  have h_diff_nn : 0 ≤ s (B \ A) := by
    have := hs _ hBdiffA; rwa [VectorMeasure.zero_apply] at this
  have h_disj : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  have h_union : A ∪ (B \ A) = B := Set.union_diff_cancel hAB
  have h_add : s A + s (B \ A) = s B := by
    rw [← VectorMeasure.of_union h_disj hA hBdiffA, h_union]
  linarith

/-- For a non-negative signed measure `s`, the lattice inf with a Dirac
vanishes iff `s` itself vanishes on the singleton. -/
private lemma signedMeasure_inf_dirac_eq_zero_iff
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {s : SignedMeasure α} (hs : 0 ≤ s) (x : α) :
    s ⊓ SignedMeasure.dirac x = 0 ↔ s ({x} : Set α) = 0 := by
  have hxset : MeasurableSet ({x} : Set α) := measurableSet_singleton x
  have hsx_nn : 0 ≤ s ({x} : Set α) := by
    have := hs _ hxset; rwa [VectorMeasure.zero_apply] at this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- (⇒): build `c • dirac_x ≤ s ⊓ dirac_x = 0` and evaluate at `{x}`.
    set c : ℝ := min (s ({x} : Set α)) 1 with hc_def
    have hc_nn : 0 ≤ c := le_min hsx_nn (by norm_num)
    have hcd_le_s : c • SignedMeasure.dirac x ≤ s := by
      intro B hB
      rw [VectorMeasure.smul_apply, smul_eq_mul]
      by_cases hxB : x ∈ B
      · rw [SignedMeasure.dirac_apply_of_mem hB hxB, mul_one]
        calc c ≤ s ({x} : Set α) := min_le_left _ _
          _ ≤ s B := signedMeasure_apply_le_apply_of_subset hs hxset hB
              (Set.singleton_subset_iff.mpr hxB)
      · rw [SignedMeasure.dirac_apply_of_notMem hB hxB, mul_zero]
        have := hs B hB; rwa [VectorMeasure.zero_apply] at this
    have hcd_le_d : c • SignedMeasure.dirac x ≤ SignedMeasure.dirac x := by
      intro B hB
      rw [VectorMeasure.smul_apply, smul_eq_mul]
      by_cases hxB : x ∈ B
      · rw [SignedMeasure.dirac_apply_of_mem hB hxB, mul_one]; exact min_le_right _ _
      · rw [SignedMeasure.dirac_apply_of_notMem hB hxB, mul_zero]
    have hcd_le_inf : c • SignedMeasure.dirac x ≤ s ⊓ SignedMeasure.dirac x :=
      le_inf hcd_le_s hcd_le_d
    rw [h] at hcd_le_inf
    have h_at_x := hcd_le_inf {x} hxset
    rw [VectorMeasure.smul_apply, smul_eq_mul,
        SignedMeasure.dirac_apply_of_mem hxset (Set.mem_singleton x), mul_one,
        VectorMeasure.zero_apply] at h_at_x
    have hc_zero : c = 0 := le_antisymm h_at_x hc_nn
    rw [hc_def] at hc_zero
    rcases min_eq_iff.mp hc_zero with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exfalso; linarith
  · -- (⇐): split every measurable set on `{x}` and use `s ⊓ dirac_x ≤ s, dirac_x`.
    refine VectorMeasure.ext fun B hB => ?_
    rw [VectorMeasure.zero_apply]
    have hinf_nn : (0 : SignedMeasure α) ≤ s ⊓ SignedMeasure.dirac x :=
      le_inf hs (SignedMeasure.zero_le_dirac x)
    have hinf_le_d : s ⊓ SignedMeasure.dirac x ≤ SignedMeasure.dirac x := inf_le_right
    have hinf_le_s : s ⊓ SignedMeasure.dirac x ≤ s := inf_le_left
    have hBdiff : MeasurableSet (B \ {x}) := hB.diff hxset
    have hBint : MeasurableSet (B ∩ {x}) := hB.inter hxset
    have h_disj : Disjoint (B ∩ {x}) (B \ {x}) := by
      apply Set.disjoint_left.mpr
      rintro a ⟨_, ha⟩ ⟨_, ha'⟩; exact ha' ha
    have h_cup : (B ∩ {x}) ∪ (B \ {x}) = B := Set.inter_union_diff B {x}
    have h_split : (s ⊓ SignedMeasure.dirac x) (B ∩ {x}) +
        (s ⊓ SignedMeasure.dirac x) (B \ {x}) = (s ⊓ SignedMeasure.dirac x) B := by
      rw [← VectorMeasure.of_union h_disj hBint hBdiff, h_cup]
    have h_diff_zero : (s ⊓ SignedMeasure.dirac x) (B \ {x}) = 0 := by
      have h_ub := hinf_le_d _ hBdiff
      have hxnotMem : x ∉ B \ {x} := by simp
      rw [SignedMeasure.dirac_apply_of_notMem hBdiff hxnotMem] at h_ub
      have h_lb := hinf_nn _ hBdiff
      rw [VectorMeasure.zero_apply] at h_lb
      linarith
    have h_int_zero : (s ⊓ SignedMeasure.dirac x) (B ∩ {x}) = 0 := by
      by_cases hxB : x ∈ B
      · have h_eq : B ∩ {x} = {x} := by
          ext y
          refine ⟨fun ⟨_, hy⟩ => hy, fun hy => ?_⟩
          rw [Set.mem_singleton_iff] at hy
          exact ⟨hy ▸ hxB, by rw [hy]; rfl⟩
        rw [h_eq]
        have h_ub := hinf_le_s _ hxset
        rw [h] at h_ub
        have h_lb := hinf_nn _ hxset
        rw [VectorMeasure.zero_apply] at h_lb
        linarith
      · have h_eq : B ∩ {x} = ∅ := by
          ext y
          refine ⟨fun ⟨hy1, hy2⟩ => ?_, fun h => h.elim⟩
          rw [Set.mem_singleton_iff] at hy2
          exact hxB (hy2 ▸ hy1)
        rw [h_eq]; exact (s ⊓ SignedMeasure.dirac x).empty
    rw [← h_split, h_diff_zero, h_int_zero, add_zero]

/-- A measure `μ ∈ M(K)` is **continuous** (or *atomless*, *diffuse*) when the
total-variation modulus of its Baire restriction vanishes on every singleton.
This is the standard atomlessness condition. -/
def MofK.IsContinuous (μ : MofK K) : Prop :=
  ∀ x : K, (|MofK.baireEquiv μ| : @SignedMeasure K (baire K))
    ({x} : Set K) = 0

omit [@MeasurableSingletonClass K (baire K)] in
private lemma MofK.baireEquiv_abs (μ : MofK K) :
    MofK.baireEquiv (|μ|) = |MofK.baireEquiv μ| := by
  set φ : MofK K ≃ₗᵢ[ℝ] @SignedMeasure K (baire K) :=
    MofK.baireEquiv.toLinearIsometryEquiv
  show φ (μ ⊔ -μ) = φ μ ⊔ -φ μ
  have hsup : φ (μ ⊔ -μ) = φ μ ⊔ φ (-μ) := MofK.baireEquiv.map_sup' _ _
  rw [hsup, map_neg]

omit [@MeasurableSingletonClass K (baire K)] in
private lemma MofK.baireEquiv_dirac (x : K) :
    MofK.baireEquiv (MofK.dirac x) = (@SignedMeasure.dirac K (baire K) x) :=
  (MofK.baireEquiv (K := K)).toLinearIsometryEquiv.apply_symm_apply _

private lemma MofK.isVLDisjoint_dirac_iff_baire_singleton_zero (μ : MofK K) (x : K) :
    IsVLDisjoint μ (MofK.dirac x) ↔
      (|MofK.baireEquiv μ| : @SignedMeasure K (baire K)) ({x} : Set K) = 0 := by
  let φ : MofK K ≃ₗᵢ[ℝ] @SignedMeasure K (baire K) :=
    MofK.baireEquiv.toLinearIsometryEquiv
  have habs_dx : (|MofK.dirac x| : MofK K) = MofK.dirac x :=
    abs_of_nonneg (MofK.zero_le_dirac x)
  have hφμ_nn : (0 : @SignedMeasure K (baire K)) ≤ |φ μ| := abs_nonneg _
  have hφ_inf : ∀ a b : MofK K, φ (a ⊓ b) = φ a ⊓ φ b := MofK.baireEquiv.map_inf'
  have hφ_zero : φ (0 : MofK K) = 0 := φ.map_zero
  have hφ_abs : φ (|μ|) = |φ μ| := MofK.baireEquiv_abs μ
  have hφ_dirac : φ (MofK.dirac x) = (@SignedMeasure.dirac K (baire K) x) :=
    φ.apply_symm_apply _
  have hkey : IsVLDisjoint μ (MofK.dirac x) ↔
      (|φ μ| : @SignedMeasure K (baire K)) ⊓
        (@SignedMeasure.dirac K (baire K) x) = 0 := by
    constructor
    · intro h
      have h1 : (|μ| ⊓ MofK.dirac x : MofK K) = 0 := by
        have hh : |μ| ⊓ |MofK.dirac x| = 0 := h
        rwa [habs_dx] at hh
      have h2 : φ (|μ| ⊓ MofK.dirac x) = φ (0 : MofK K) := by rw [h1]
      rw [hφ_inf, hφ_abs, hφ_dirac, hφ_zero] at h2
      exact h2
    · intro h
      show |μ| ⊓ |MofK.dirac x| = 0
      rw [habs_dx]
      apply φ.injective
      rw [hφ_inf, hφ_abs, hφ_dirac, hφ_zero]
      exact h
  refine Iff.trans hkey ?_
  exact @signedMeasure_inf_dirac_eq_zero_iff K (baire K) inferInstance _ hφμ_nn x

/-- **Continuous band of `M(K)`.** A measure belongs to the continuous part of
`M(K)` exactly when it is continuous in the sense of `MofK.IsContinuous`. -/
theorem MofK.mem_continuousPart_iff (μ : MofK K) :
    μ ∈ continuousPart (MofK K) ↔ MofK.IsContinuous μ := by
  refine ⟨fun hμ x => ?_, fun hμ a hatom => ?_⟩
  · -- (⇒): MofK.dirac x is an atom, so μ ⟂ dirac x; convert via the helper.
    have hdisj : IsVLDisjoint μ (MofK.dirac x) := hμ _ (MofK.isVLAtom_dirac x)
    exact (MofK.isVLDisjoint_dirac_iff_baire_singleton_zero μ x).mp hdisj
  · -- (⇐): use atom characterization to write a = c • dirac y, reduce to dirac y.
    obtain ⟨c, y, hc, ha⟩ := (MofK.isVLAtom_iff_exists_smul_dirac a).mp hatom
    have h : IsVLDisjoint μ (MofK.dirac y) :=
      (MofK.isVLDisjoint_dirac_iff_baire_singleton_zero μ y).mpr (hμ y)
    have habs_d : (|MofK.dirac y| : MofK K) = MofK.dirac y :=
      abs_of_nonneg (MofK.zero_le_dirac y)
    have hcd_nn : (0 : MofK K) ≤ c • MofK.dirac y :=
      smul_nonneg hc.le (MofK.zero_le_dirac y)
    have hh : |μ| ⊓ MofK.dirac y = 0 := by
      have hh' : |μ| ⊓ |MofK.dirac y| = 0 := h
      rwa [habs_d] at hh'
    have hd_disj_μ : MofK.dirac y ⊓ |μ| = 0 := by rw [inf_comm]; exact hh
    have hcd_disj : (c • MofK.dirac y) ⊓ |μ| = 0 :=
      disjoint_smul (MofK.dirac y) (|μ|) c hc.le hd_disj_μ
    show |μ| ⊓ |a| = 0
    rw [ha, abs_of_nonneg hcd_nn, inf_comm]; exact hcd_disj

/-- **Discrete (atomic) band of `M(K)`.** A measure belongs to the atomic
part of `M(K)` exactly when it is a norm-convergent countable sum of weighted
Dirac masses, supported on pairwise distinct points. -/
theorem MofK.mem_atomicPart_iff (μ : MofK K) :
    μ ∈ atomicPart (MofK K) ↔
      ∃ (ι : Type) (_ : Countable ι) (c : ι → ℝ) (x : ι → K),
        Function.Injective x ∧
        Summable (fun n : ι => c n • MofK.dirac (x n)) ∧
        μ = ∑' n : ι, c n • MofK.dirac (x n) :=
  sorry

/-- **Discrete + continuous decomposition in `M(K)`.** Every regular signed
Borel measure on `K` decomposes as the sum of a norm-convergent countable
series of weighted Dirac deltas, supported on pairwise distinct points, and a
continuous measure. -/
theorem MofK.exists_discrete_continuous_decomposition (μ : MofK K) :
    ∃ (ι : Type) (_ : Countable ι) (c : ι → ℝ) (x : ι → K) (ν : MofK K),
      Function.Injective x ∧
      MofK.IsContinuous ν ∧
      Summable (fun n : ι => c n • MofK.dirac (x n)) ∧
      μ = (∑' n : ι, c n • MofK.dirac (x n)) + ν := by
  -- `M(K)` has the projection property since it is order continuous (AL-space)
  -- hence order complete; so `atomicPart (MofK K)` is a projection band.
  obtain ⟨P, hP⟩ :=
    HasProjectionProperty.exists_projectionBand (atomicPart (MofK K))
  -- Decompose μ into atomic + continuous parts.
  obtain ⟨a, c_part, ha_mem, hc_mem, hμ_eq⟩ := P.decomposition μ
  have ha_mem' : a ∈ atomicPart (MofK K) := by
    have : a ∈ (P : Set (MofK K)) := ha_mem
    rwa [hP] at this
  have hc_mem' : c_part ∈ continuousPart (MofK K) := by
    intro b hb
    have hb_in_P : b ∈ (P : Set (MofK K)) := by
      rw [hP]; exact isVLAtom.mem_atomicPart hb
    exact hc_mem b hb_in_P
  -- Use the atomic-band classification to express `a` as a Dirac series.
  obtain ⟨ι, hι, coef, pts, hinj, hsumm, ha_sum⟩ :=
    (MofK.mem_atomicPart_iff a).mp ha_mem'
  refine ⟨ι, hι, coef, pts, c_part, hinj, ?_, hsumm, ?_⟩
  · exact (MofK.mem_continuousPart_iff c_part).mp hc_mem'
  · rw [← ha_sum]; exact hμ_eq

end Decomposition
