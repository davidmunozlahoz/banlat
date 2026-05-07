import BanLat.OrderContinuous.MeyerNieberg
import BanLat.OrderContinuous.Decomposition

/-!
# Ando's theorem

A Banach lattice has an order continuous norm iff every norm-closed order
ideal is a band; in that case every norm-closed ideal is a projection band.
-/

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

namespace BanachLattice

variable [BanachLattice X]

/-- In an order continuous Banach lattice, every norm-closed order ideal is
a band. -/
theorem band_of_isClosed_orderIdeal [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ B : Band X, (B : Set X) = (J : Set X) := by
  refine ⟨Band.ofPosDirectedSSupMem J ?_, rfl⟩
  intro S hS hpos hdir hne x hx
  -- Index by `↥S` as a directed nonempty preorder.
  haveI : Nonempty ↥S := hne.to_subtype
  haveI : IsDirected ↥S (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.val a.2 b.val b.2
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  -- Antitone net `u s = x - s`, nonneg, with `IsGLB 0` since `x = sup S`.
  let u : ↥S → X := fun s => x - s.val
  have hu_anti : Antitone u := fun a b h =>
    sub_le_sub_left (show a.val ≤ b.val from h) x
  have hu_nn : ∀ s, 0 ≤ u s := fun s => sub_nonneg.mpr (hx.1 s.2)
  have hu_glb : IsGLB (Set.range u) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨s, rfl⟩; exact hu_nn s
    · intro w hw
      have hub : ∀ y ∈ S, y ≤ x - w := fun y hy =>
        le_sub_comm.mp (hw ⟨⟨y, hy⟩, rfl⟩)
      have h := hx.2 hub
      rwa [le_sub_iff_add_le, add_comm, add_le_iff_nonpos_left] at h
  -- Order continuity gives `u → 0`, hence the inclusion `s ↦ s.val → x`.
  have htend := IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero
    hu_anti hu_nn hu_glb
  have hval_tend : Filter.Tendsto (fun s : ↥S => s.val) Filter.atTop (nhds x) := by
    have h1 : Filter.Tendsto (fun s : ↥S => x - u s) Filter.atTop (nhds (x - 0)) :=
      tendsto_const_nhds.sub htend
    simpa [u, sub_sub_cancel] using h1
  -- `J` is closed and contains each `s.val`, so `x ∈ J`.
  exact hcl.mem_of_tendsto hval_tend (Filter.Eventually.of_forall (fun s => hS s.2))

omit [BanachLattice X] in
private lemma isVLDisjoint_finset_sum_right {ι : Type*} {s : Finset ι}
    {x : X} {f : ι → X}
    (h : ∀ i ∈ s, IsVLDisjoint x (f i)) : IsVLDisjoint x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isVLDisjoint_zero_right x
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (h a (Finset.mem_insert_self a s)).add_right ?_
      exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [BanachLattice X] in
private lemma le_of_le_add_of_isVLDisjoint {y p q : X}
    (hy0 : 0 ≤ y) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hy : y ≤ p + q) (hyq : IsVLDisjoint y q) : y ≤ p := by
  have hyq_inf : y ⊓ q = 0 := inf_eq_zero_of_isVLDisjoint hy0 hq0 hyq
  calc
    y = y ⊓ (p + q) := (inf_eq_left.mpr hy).symm
    _ ≤ y ⊓ p + y ⊓ q :=
      inf_le_inf_add_inf_of_nonneg y p q hy0 hp0 hq0
    _ = y ⊓ p := by rw [hyq_inf, add_zero]
    _ ≤ p := inf_le_right

omit [BanachLattice X] in
private lemma le_abs_sub_of_le_of_isVLDisjoint {y p z : X}
    (hy0 : 0 ≤ y) (hyp : y ≤ p) (hyz : IsVLDisjoint y z) :
    y ≤ |p - z| := by
  have hyz_inf : y ⊓ |z| = 0 := by
    have := hyz
    rwa [IsVLDisjoint, abs_of_nonneg hy0] at this
  have hp_le : p ≤ |p - z| + |z| := by
    calc
      p = (p - z) + z := by abel
      _ ≤ |p - z| + |z| := add_le_add (le_abs_self _) (le_abs_self _)
  have hy_le_sum : y ≤ |p - z| + |z| := hyp.trans hp_le
  calc
    y = y ⊓ (|p - z| + |z|) := (inf_eq_left.mpr hy_le_sum).symm
    _ ≤ y ⊓ |p - z| + y ⊓ |z| :=
      inf_le_inf_add_inf_of_nonneg y |p - z| |z| hy0 (abs_nonneg _) (abs_nonneg _)
    _ = y ⊓ |p - z| := by rw [hyz_inf, add_zero]
    _ ≤ |p - z| := inf_le_right

private theorem projectionBand_of_isClosed_orderIdeal_of_forall_isBand
    (h : ∀ J : OrderIdeal X, IsClosed (J : Set X) →
      ∃ B : Band X, (B : Set X) = (J : Set X))
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ P : ProjectionBand X, (P : Set X) = (J : Set X) := by
  -- `Jᵈ` as an order ideal.
  let Jd : OrderIdeal X := (Band.disjointComplement ((J : Set X))).toOrderIdeal
  have hJd_set : ((Jd : Set X)) = ((J : Set X))ᵈ := rfl
  -- `Jᵈ` is closed.
  have hJd_cl : IsClosed ((Jd : Set X)) := by
    rw [hJd_set]; exact isClosed_disjointComplement ((J : Set X))
  -- `J + Jᵈ` is a closed order ideal.
  have hSum_cl : IsClosed ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) :=
    (ClosedOrderIdeal.sup
      { toOrderIdeal := J, isClosed' := hcl }
      { toOrderIdeal := Jd, isClosed' := hJd_cl }).isClosed'
  -- ...hence a band.
  obtain ⟨BSum, hBSum⟩ := h (OrderIdeal.sum J Jd) hSum_cl
  -- Inclusions: `J ⊆ J + Jᵈ` and `Jᵈ ⊆ J + Jᵈ` (at the set level).
  have hJ_sub : ((J : Set X)) ⊆ ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) := by
    intro a ha
    exact Submodule.mem_sup.mpr ⟨a, ha, 0, Submodule.zero_mem _, by simp⟩
  have hJd_sub : ((Jd : Set X)) ⊆ ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) := by
    intro a ha
    exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, a, ha, by simp⟩
  -- `(J + Jᵈ)ᵈ ⊆ {0}`.
  have hSumd_zero : (((OrderIdeal.sum J Jd : OrderIdeal X) : Set X))ᵈ ⊆ ({0} : Set X) := by
    intro x hx
    have hxJ : x ∈ ((J : Set X))ᵈ := disjointComplement_anti hJ_sub hx
    have hxJd : x ∈ ((Jd : Set X))ᵈ := disjointComplement_anti hJd_sub hx
    rw [hJd_set] at hxJd
    exact disjointComplement_inter_eq_zero ((J : Set X))ᵈ ⟨hxJ, hxJd⟩
  -- Since `BSum = J + Jᵈ` as sets, and `BSum` is a band, `BSumᵈᵈ = BSum`.
  have hBSum_dd : (((BSum : Set X))ᵈ)ᵈ = ((BSum : Set X)) :=
    Band.eq_disjointComplement_disjointComplement BSum
  -- `{0}ᵈ = X`.
  have hzero_d : (({0} : Set X))ᵈ = (Set.univ : Set X) := by
    ext x
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    unfold IsVLDisjoint
    simp
  -- Chain: `BSum = BSumᵈᵈ ⊇ ({0})ᵈ = X` (using `BSumᵈ ⊆ {0}`).
  have hBSum_top : ((BSum : Set X)) = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← hBSum_dd]
    have : (((BSum : Set X))ᵈ) ⊆ ({0} : Set X) := by
      rw [hBSum]; exact hSumd_zero
    calc (Set.univ : Set X)
        = (({0} : Set X))ᵈ := hzero_d.symm
      _ ⊆ (((BSum : Set X))ᵈ)ᵈ := disjointComplement_anti this
  -- Transfer: `J + Jᵈ = X` as sets.
  have hSum_top : ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) = Set.univ := by
    rw [← hBSum]; exact hBSum_top
  -- Apply the decomposition characterisation.
  refine (ProjectionBand.projectionBand_iff_add_disjointComplement J).mpr (fun x => ?_)
  have hxmem : x ∈ ((OrderIdeal.sum J Jd : OrderIdeal X) : Set X) := by
    rw [hSum_top]; exact Set.mem_univ _
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxmem
  refine ⟨a, b, ha, ?_, hab.symm⟩
  exact (show b ∈ ((J : Set X))ᵈ by rw [← hJd_set]; exact hb)

/-- A Banach lattice in which every norm-closed ideal is a band has an order
continuous norm.

**Proof sketch.** By Meyer-Nieberg's characterisation, it suffices to show
that every order-bounded disjoint sequence converges to zero in norm. Given
such a sequence `(uₙ) ⊆ [0, w]`, let `J` be the closed ideal generated by
`{uₙ}`. By hypothesis `J` is a band; the closed-sum lemma makes `J + Jᵈ`
closed, hence a band, hence `(J + Jᵈ)ᵈᵈ = J + Jᵈ`; combined with `(J + Jᵈ)ᵈ ⊆
Jᵈ ∩ Jᵈᵈ = {0}` one gets `J + Jᵈ = X`, so `J` is a projection band. Denoting
by `P` the band projection, `Pw ∈ J` is norm-approximated by `v` with `|v| ≤
∑_{k ≤ N} λ_k uₖ`; for `n > N`, disjointness gives `v ⊥ uₙ` and `uₙ ≤ |Pw −
v|`, whence `‖uₙ‖ < ε`.

The inner argument uses the closed ideal generated by the sequence together
with the explicit finite positive-combination description of generated
ideals. -/
theorem isOrderContinuousNorm_of_isClosed_ideal_isBand
    (h : ∀ J : OrderIdeal X, IsClosed (J : Set X) →
      ∃ B : Band X, (B : Set X) = (J : Set X)) :
    IsOrderContinuousNorm X := by
  -- Reduce to Meyer-Nieberg: every order-bounded disjoint sequence in a
  -- Banach lattice must converge to zero in norm.
  refine isOrderContinuousNorm_of_disjoint_tendsto_zero (fun {u} hd hbd => ?_)
  classical
  let v : ℕ → X := fun n => |u n|
  have hv_disj : Pairwise fun i j => IsVLDisjoint (v i) (v j) := by
    intro i j hij
    simpa [v, IsVLDisjoint, abs_abs] using hd hij
  obtain ⟨w, hw⟩ := hbd
  have hw0 : 0 ≤ w := (abs_nonneg (u 0)).trans (hw ⟨0, rfl⟩)
  let G : OrderIdeal X := OrderIdeal.generated (Set.range v)
  let J : OrderIdeal X := OrderIdeal.topologicalClosure G
  have hJ_closed : IsClosed (J : Set X) := by
    change IsClosed ((G.toSubmodule.topologicalClosure : Submodule ℝ X) : Set X)
    exact Submodule.isClosed_topologicalClosure G.toSubmodule
  obtain ⟨P, hP⟩ := projectionBand_of_isClosed_orderIdeal_of_forall_isBand h J hJ_closed
  let p : X := P.bandProjection w
  let q : X := w - p
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact Positive.zero_le_iff.mp P.bandProjection_nonneg w hw0
  have hq0 : 0 ≤ q := by
    have hp_le_w : p ≤ w := by
      dsimp [p]
      exact Positive.le_iff.mp P.bandProjection_le_id w hw0
    exact sub_nonneg.mpr hp_le_w
  have hw_decomp : w = p + q := by
    dsimp [q]; abel
  have hpJ : p ∈ (J : Set X) := by
    rw [← hP]
    exact P.bandProjection_mem w
  have hp_closure : p ∈ closure (G.toSubmodule : Set X) := by
    have hpJ' : p ∈ ((G.toSubmodule.topologicalClosure : Submodule ℝ X) : Set X) := by
      simpa [J, OrderIdeal.topologicalClosure_toSubmodule] using hpJ
    rwa [Submodule.topologicalClosure_coe] at hpJ'
  have hv_mem_J : ∀ n, v n ∈ (J : Set X) := by
    intro n
    have hvG : v n ∈ (G : Set X) := OrderIdeal.subset_generated _ ⟨n, rfl⟩
    change v n ∈ G.toSubmodule.topologicalClosure
    exact G.toSubmodule.le_topologicalClosure hvG
  have hv_le_p : ∀ n, v n ≤ p := by
    intro n
    have hvP : v n ∈ (P : Set X) := by
      rw [hP]; exact hv_mem_J n
    have hqP : q ∈ disjointComplement (P : Set X) := by
      dsimp [q, p]
      exact P.id_sub_bandProjection_mem w
    have hvq : IsVLDisjoint (v n) q := isVLDisjoint_comm.mp (hqP (v n) hvP)
    have hvw : v n ≤ p + q := by
      rw [← hw_decomp]
      exact hw ⟨n, rfl⟩
    exact le_of_le_add_of_isVLDisjoint (abs_nonneg _) hp0 hq0 hvw hvq
  have hv_tend : Filter.Tendsto v Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨y, hyG, hy_norm⟩ : ∃ y ∈ (G : Set X), ‖p - y‖ < ε := by
      rcases Metric.mem_closure_iff.mp hp_closure ε hε with ⟨y, hy_mem, hy_dist⟩
      exact ⟨y, hy_mem, by rwa [dist_eq_norm] at hy_dist⟩
    obtain ⟨t, c, hts, hc, hy_le⟩ := OrderIdeal.mem_generated_iff.mp hyG
    let idx : X → ℕ := fun z =>
      if hz : z ∈ t then (Set.mem_range.mp (hts z hz)).choose else 0
    have hidx : ∀ z ∈ t, v (idx z) = z := by
      intro z hz
      dsimp [idx]
      rw [dif_pos hz]
      exact (Set.mem_range.mp (hts z hz)).choose_spec
    refine Filter.eventually_atTop.mpr ⟨t.sup idx + 1, fun n hn => ?_⟩
    have hdis_sum : IsVLDisjoint (v n) (∑ z ∈ t, c z • |z|) := by
      apply isVLDisjoint_finset_sum_right
      intro z hz
      have hidx_lt : idx z < n := by
        exact Nat.lt_of_le_of_lt (Finset.le_sup (f := idx) hz) (by omega)
      have hdis_z : IsVLDisjoint (v n) z := by
        rw [← hidx z hz]
        exact hv_disj (by omega)
      have hdis_abs : IsVLDisjoint (v n) |z| := by
        simpa [IsVLDisjoint, abs_abs] using hdis_z
      exact hdis_abs.smul_right (c z)
    have hsum_nonneg : 0 ≤ ∑ z ∈ t, c z • |z| :=
      Finset.sum_nonneg fun z hz => smul_nonneg (hc z hz) (abs_nonneg z)
    have hy_le_abs : |y| ≤ |((∑ z ∈ t, c z • |z|) : X)| := by
      rwa [abs_of_nonneg hsum_nonneg]
    have hvy : IsVLDisjoint (v n) y := hdis_sum.mono_right hy_le_abs
    have hv_abs_le : v n ≤ |p - y| :=
      le_abs_sub_of_le_of_isVLDisjoint (abs_nonneg _) (hv_le_p n) hvy
    have hnorm_le : ‖v n‖ ≤ ‖p - y‖ := by
      rw [← norm_abs_eq_norm (p - y)]
      exact norm_le_norm_of_abs_le_abs (by simpa [v, abs_abs] using hv_abs_le)
    rw [dist_zero_right]
    exact lt_of_le_of_lt hnorm_le hy_norm
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := Metric.tendsto_nhds.mp hv_tend ε hε
  filter_upwards [hev] with n hn
  rw [dist_zero_right] at hn ⊢
  simpa [v, norm_abs_eq_norm] using hn

/-- **Ando's theorem**: a Banach lattice has an order continuous norm iff
every norm-closed ideal is a band. -/
theorem isOrderContinuousNorm_iff_isClosed_ideal_isBand :
    IsOrderContinuousNorm X ↔
      (∀ J : OrderIdeal X, IsClosed (J : Set X) →
        ∃ B : Band X, (B : Set X) = (J : Set X)) :=
  ⟨fun _ => band_of_isClosed_orderIdeal,
   fun h => isOrderContinuousNorm_of_isClosed_ideal_isBand h⟩

/-- In an order continuous Banach lattice, every norm-closed ideal is a
projection band. -/
theorem projectionBand_of_isClosed_orderIdeal
    [IsOrderContinuousNorm X]
    (J : OrderIdeal X) (hcl : IsClosed (J : Set X)) :
    ∃ P : ProjectionBand X, (P : Set X) = (J : Set X) :=
  projectionBand_of_isClosed_orderIdeal_of_forall_isBand
    (fun J hcl => band_of_isClosed_orderIdeal J hcl) J hcl

end BanachLattice
