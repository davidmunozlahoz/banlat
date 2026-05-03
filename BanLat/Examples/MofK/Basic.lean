import BanLat.Preliminaries.Regularity
import BanLat.Examples.SignedMeasure.Basic
import BanLat.Substructures.Sublattice

/-!
# The Banach lattice `M(K)` of regular signed Borel measures

For a compact Hausdorff space `K` with its Borel σ-algebra, the classical space
`M(K)` is the space of **regular** signed Borel measures on `K`, equipped with
the total-variation norm. It is identified here as the closed vector
sublattice of `MeasureTheory.SignedMeasure K` consisting of those signed
measures satisfying the regularity predicate
`MeasureTheory.SignedMeasure.IsRegular`.

The vector-space and linear-order structure of regular signed measures is
already established in `BanLat.Preliminaries.Regularity`. This file packages
those facts as a `VectorSublattice` of `SignedMeasure K`, shows that this
sublattice is closed in the total-variation norm, and concludes that `M(K)`
is a Banach lattice via `VectorSublattice.instBanachLatticeSubtype`.
-/

open MeasureTheory Set

namespace MeasureTheory.SignedMeasure

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-! ### Regularity is preserved by the modulus

The vector-lattice modulus `|s|` of a signed measure equals `s.posPart +
s.negPart`. Both summands are regular when `s` is regular, so `|s|` is
regular as well. -/

/-- The modulus of a regular signed measure is regular. -/
theorem IsRegular.abs {s : SignedMeasure K} (hs : s.IsRegular) :
    (|s|).IsRegular := by
  haveI := hs.posPart_regular
  haveI := hs.negPart_regular
  set μ := s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart
  let j : JordanDecomposition K :=
    ⟨μ, 0, Measure.MutuallySingular.zero_right⟩
  have habs : |s| = j.toSignedMeasure := by
    rw [SignedMeasure.abs_eq_posPart_add_negPart]
    change s.toJordanDecomposition.posPart.toSignedMeasure +
        s.toJordanDecomposition.negPart.toSignedMeasure = j.toSignedMeasure
    change _ = j.posPart.toSignedMeasure - j.negPart.toSignedMeasure
    change _ = μ.toSignedMeasure - (0 : Measure K).toSignedMeasure
    rw [Measure.toSignedMeasure_zero, sub_zero, ← Measure.toSignedMeasure_add]
  have habs_jd : |s|.toJordanDecomposition = j :=
    SignedMeasure.toJordanDecomposition_eq habs
  change |s|.totalVariation.Regular
  rw [SignedMeasure.totalVariation, habs_jd]
  change (μ + 0).Regular
  rw [add_zero]
  infer_instance

/-! ### `M(K)` as a closed vector sublattice -/

/-- The submodule of regular signed measures inside `SignedMeasure K`. -/
def regularSubmodule : Submodule ℝ (SignedMeasure K) where
  carrier := {s | s.IsRegular}
  add_mem' := IsRegular.add
  zero_mem' := IsRegular.zero
  smul_mem' := IsRegular.smul

/-- The vector sublattice of regular signed measures inside `SignedMeasure K`. -/
noncomputable def regularSignedMeasureSublattice : VectorSublattice (SignedMeasure K) :=
  VectorSublattice.ofAbsClosed regularSubmodule fun _ hs => IsRegular.abs hs

/-- Membership in the vector sublattice of regular signed measures is regularity. -/
theorem mem_regularSignedMeasureSublattice_iff {s : SignedMeasure K} :
    s ∈ regularSignedMeasureSublattice (K := K) ↔ s.IsRegular := Iff.rfl

/-! ### Closedness of regularity in the total-variation norm

Closedness uses two ingredients: regularity of a finite measure can be checked
via uniform approximation by regular measures
(`MeasureTheory.Measure.Regular.of_uniform_approx`), and the Jordan positive
part is `1`-Lipschitz with respect to the total-variation norm, since
`s.posPart = s ⊔ 0` and lattice operations are non-expansive. -/

omit [TopologicalSpace K] [T2Space K] [CompactSpace K] [BorelSpace K] in
/-- The real-valued Jordan positive parts of `u` and `v` differ on any measurable
set by at most `‖u - v‖`. -/
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
  have h_eq_u : u ⊔ 0 = u.posPart := by
    rw [max_def, sub_zero, zero_add]
  have h_eq_v : v ⊔ 0 = v.posPart := by
    rw [max_def, sub_zero, zero_add]
  rw [← h_u_eval, ← h_v_eval,
    show u.posPart E - v.posPart E = (u.posPart - v.posPart) E from
      (VectorMeasure.sub_apply _ _ _).symm]
  calc
    |(u.posPart - v.posPart) E|
      ≤ ((u.posPart - v.posPart).totalVariation Set.univ).toReal :=
        abs_apply_le_totalVariation_univ _ hE
    _ = ‖u.posPart - v.posPart‖ := (norm_def _).symm
    _ = ‖u ⊔ 0 - v ⊔ 0‖ := by rw [h_eq_u, h_eq_v]
    _ ≤ ‖u - v‖ := norm_sup_sub_sup_le_norm u v 0

/-- The set of regular signed measures is closed in the total-variation
norm. -/
theorem isClosed_isRegular :
    IsClosed {s : SignedMeasure K | s.IsRegular} := by
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
      have := hN N le_rfl
      rwa [dist_eq_norm] at this
    refine ⟨(tₙ N).toJordanDecomposition.posPart, inferInstance, htₙ N, ?_⟩
    intro E hE
    exact lt_of_le_of_lt (toReal_posPart_sub_le_norm_of_signed hE) hN'
  have hpos := key (fun n => (hsₙ n).posPart_regular) hlim
  have hlim_neg : Filter.Tendsto (fun n => -(sₙ n)) Filter.atTop (nhds (-s)) := hlim.neg
  have hneg : s.toJordanDecomposition.negPart.Regular := by
    have h := key
      (fun n => by
        rw [toJordanDecomposition_neg]
        exact (hsₙ n).negPart_regular)
      hlim_neg
    rw [toJordanDecomposition_neg] at h
    exact h
  haveI := hpos
  haveI := hneg
  change (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).Regular
  infer_instance

/-- `M(K)` is closed as a subset of `SignedMeasure K`. -/
theorem isClosed_regularSignedMeasureSublattice :
    IsClosed (regularSignedMeasureSublattice (K := K) : Set (SignedMeasure K)) :=
  isClosed_isRegular

end MeasureTheory.SignedMeasure

/-! ### `M(K)` and its Banach lattice structure -/

open MeasureTheory.SignedMeasure in
/-- `M(K)` — the Banach lattice of regular signed Borel measures on a compact
Hausdorff space `K`. -/
abbrev MofK (K : Type*) [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] : Type _ :=
  ↥(regularSignedMeasureSublattice (K := K)).toSubmodule

namespace MofK

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- `M(K)` is a Banach lattice. -/
noncomputable instance instBanachLattice : BanachLattice (MofK K) :=
  VectorSublattice.instBanachLatticeSubtype _
    MeasureTheory.SignedMeasure.isClosed_regularSignedMeasureSublattice

end MofK
