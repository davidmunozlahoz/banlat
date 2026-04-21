import BanLat.Operators.Hom

/-!
# Positive operators

A linear map between vector lattices is **positive** if it sends non-negative elements to
non-negative elements. For linear maps, positivity is equivalent to monotonicity. A positive
operator satisfies `|f x| ≤ f |x|`, and every positive operator from a Banach lattice to a
normed vector lattice is automatically continuous. As a corollary, every vector lattice
isomorphism between Banach lattices is a Banach space isomorphism.
-/

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]

/-- A linear map is *positive* if it sends non-negative elements to non-negative elements. -/
def Positive (f : X →ₗ[ℝ] Y) : Prop :=
  ∀ x : X, 0 ≤ x → 0 ≤ f x

namespace Positive

/-- For a linear map between vector lattices, monotonicity and positivity are equivalent. -/
theorem monotone_iff {f : X →ₗ[ℝ] Y} : Monotone f ↔ Positive f := by
  constructor
  · intro hm x hx
    simpa [map_zero] using hm hx
  · intro hp a b hab
    have h : 0 ≤ f (b - a) := hp (b - a) (sub_nonneg.mpr hab)
    rwa [map_sub, sub_nonneg] at h

/-- A positive operator satisfies `|f x| ≤ f |x|`. -/
theorem abs_le_map_abs {f : X →ₗ[ℝ] Y} (hf : Positive f) (x : X) : |f x| ≤ f |x| := by
  rw [abs]
  apply sup_le
  · exact (monotone_iff.mpr hf) (by rw [abs]; exact le_sup_left)
  · have h : f (-x) ≤ f |x| := (monotone_iff.mpr hf) (by rw [abs]; exact le_sup_right)
    rwa [map_neg] at h

section ExtensionLemma

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}

omit [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y] [IsVLArchimedean Y] in
private lemma tau_zero
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y) :
    τ 0 = 0 := by
  have h := hτ_add 0 0 le_rfl le_rfl
  rw [add_zero] at h
  exact (add_left_cancel (show τ 0 + 0 = τ 0 + τ 0 from by
    rw [add_zero]; exact h)).symm

omit [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice X]
  [VectorLattice Y] [IsVLArchimedean Y] in
private lemma tau_nsmul
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    (n : ℕ) {x : X} (hx : 0 ≤ x) :
    τ (n • x) = n • τ x := by
  induction n with
  | zero => simp [tau_zero hτ_add]
  | succ n ih =>
    rw [succ_nsmul, hτ_add _ _ (nsmul_nonneg hx n) hx, ih, succ_nsmul]

omit [VectorLattice X] [VectorLattice Y] [IsVLArchimedean Y] in
private lemma tau_mono
    (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    {a b : X} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a ≤ b) :
    τ a ≤ τ b := by
  have hd : 0 ≤ b - a := sub_nonneg.mpr hab
  have : τ b = τ a + τ (b - a) := by
    rw [← hτ_add a (b - a) ha hd]; congr 1; abel
  rw [this]
  exact le_add_of_nonneg_right (hτ_nn _ hd)

private lemma tau_real_smul
    (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    {r : ℝ} (hr : 0 ≤ r) {x : X} (hx : 0 ≤ x) :
    τ (r • x) = r • τ x := by
  set d := τ (r • x) - r • τ x with hd_def
  suffices hd : d = 0 from sub_eq_zero.mp hd
  rw [← abs_eq_zero_iff_zero]
  apply IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
    (y := τ x) (abs_nonneg d)
  intro m
  set k := Nat.floor ((m : ℝ) * r)
  have hmr : 0 ≤ (m : ℝ) * r := mul_nonneg (Nat.cast_nonneg m) hr
  have hk_le : (k : ℝ) ≤ (m : ℝ) * r := Nat.floor_le hmr
  have hmr_lt : (m : ℝ) * r < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmrx : m • (r • x) = ((m : ℝ) * r) • x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  -- m • τ(r•x) and m • (r • τ x) both lie in [k • τ x, (k+1) • τ x]
  have hlo : k • τ x ≤ m • τ (r • x) := by
    rw [← tau_nsmul hτ_add m (smul_nonneg hr hx),
        ← tau_nsmul hτ_add k hx]
    exact tau_mono hτ_nn hτ_add (nsmul_nonneg hx k)
      (nsmul_nonneg (smul_nonneg hr hx) m) <| by
      rw [hmrx, ← Nat.cast_smul_eq_nsmul ℝ k x]
      exact smul_le_smul_of_nonneg_right hk_le hx
  have hhi : m • τ (r • x) ≤ (k + 1) • τ x := by
    rw [← tau_nsmul hτ_add m (smul_nonneg hr hx),
        ← tau_nsmul hτ_add (k + 1) hx]
    exact tau_mono hτ_nn hτ_add
      (nsmul_nonneg (smul_nonneg hr hx) m)
      (nsmul_nonneg hx (k + 1)) <| by
      rw [hmrx, ← Nat.cast_smul_eq_nsmul ℝ (k + 1) x]
      exact smul_le_smul_of_nonneg_right (by push_cast; exact hmr_lt.le) hx
  have hlo' : k • τ x ≤ m • (r • τ x) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    exact smul_le_smul_of_nonneg_right hk_le (hτ_nn _ hx)
  have hhi' : m • (r • τ x) ≤ (k + 1) • τ x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ m (r • τ x),
      ← Nat.cast_smul_eq_nsmul ℝ (k + 1) (τ x), smul_smul]
    exact smul_le_smul_of_nonneg_right (by push_cast; exact hmr_lt.le)
      (hτ_nn _ hx)
  -- Both values lie in an interval of width τ x, so |m•d| ≤ τ x
  have h1 : m • τ (r • x) - m • (r • τ x) ≤ τ x :=
    calc m • τ (r • x) - m • (r • τ x)
        ≤ (k + 1) • τ x - k • τ x := sub_le_sub hhi hlo'
      _ = τ x := by rw [add_nsmul, one_nsmul, add_sub_cancel_left]
  have h2 : m • (r • τ x) - m • τ (r • x) ≤ τ x :=
    calc m • (r • τ x) - m • τ (r • x)
        ≤ (k + 1) • τ x - k • τ x := sub_le_sub hhi' hlo
      _ = τ x := by rw [add_nsmul, one_nsmul, add_sub_cancel_left]
  -- Convert to m • |d| ≤ τ x
  have habs : |m • τ (r • x) - m • (r • τ x)| ≤ τ x :=
    sup_le h1 (show -(m • τ (r • x) - m • (r • τ x)) ≤ τ x by rwa [neg_sub])
  have hmd : m • τ (r • x) - m • (r • τ x) = m • d := by
    rw [← smul_sub]
  rw [hmd] at habs
  rw [← Nat.cast_smul_eq_nsmul ℝ m d] at habs
  rw [abs_smul' d (↑m : ℝ), abs_of_nonneg (Nat.cast_nonneg m)] at habs
  rwa [Nat.cast_smul_eq_nsmul ℝ m |d|] at habs

private lemma posPart_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (x : X) :
    (r • x)⁺ = r • x⁺ := by
  change (r • x) ⊔ 0 = r • (x ⊔ 0)
  rw [← smul_zero r, ← nonneg_smul_sup x 0 r hr, smul_zero]

private lemma negPart_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (x : X) :
    (r • x)⁻ = r • x⁻ := by
  change (-(r • x)) ⊔ 0 = r • ((-x) ⊔ 0)
  rw [← smul_neg, ← smul_zero r, ← nonneg_smul_sup (-x) 0 r hr, smul_zero]

omit [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] in
private lemma extFun_add
    (_hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    (x y : X) :
    τ (x + y)⁺ - τ (x + y)⁻ = (τ x⁺ - τ x⁻) + (τ y⁺ - τ y⁻) := by
  have hid : (x + y)⁺ + x⁻ + y⁻ = (x + y)⁻ + x⁺ + y⁺ := by
    have l1 : (x + y)⁺ = x + y + (x + y)⁻ :=
      eq_add_of_sub_eq (posPart_sub_negPart _)
    have l2 : x⁺ = x + x⁻ := eq_add_of_sub_eq (posPart_sub_negPart x)
    have l3 : y⁺ = y + y⁻ := eq_add_of_sub_eq (posPart_sub_negPart y)
    rw [l1, l2, l3]; abel
  have hlhs : τ ((x + y)⁺ + x⁻ + y⁻) =
      τ (x + y)⁺ + τ x⁻ + τ y⁻ := by
    rw [hτ_add _ _ (add_nonneg (posPart_nonneg _) (negPart_nonneg _))
        (negPart_nonneg _),
      hτ_add _ _ (posPart_nonneg _) (negPart_nonneg _)]
  have hrhs : τ ((x + y)⁻ + x⁺ + y⁺) =
      τ (x + y)⁻ + τ x⁺ + τ y⁺ := by
    rw [hτ_add _ _ (add_nonneg (negPart_nonneg _) (posPart_nonneg _))
        (posPart_nonneg _),
      hτ_add _ _ (negPart_nonneg _) (posPart_nonneg _)]
  have key := hlhs.symm.trans ((congrArg τ hid).trans hrhs)
  calc τ (x + y)⁺ - τ (x + y)⁻
      = τ (x + y)⁺ + τ x⁻ + τ y⁻ - τ x⁻ - τ y⁻ - τ (x + y)⁻ := by
        abel
    _ = τ (x + y)⁻ + τ x⁺ + τ y⁺ - τ x⁻ - τ y⁻ - τ (x + y)⁻ := by
        rw [key]
    _ = τ x⁺ - τ x⁻ + (τ y⁺ - τ y⁻) := by abel

private lemma extFun_smul
    (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
    (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
    (r : ℝ) (x : X) :
    τ (r • x)⁺ - τ (r • x)⁻ = r • (τ x⁺ - τ x⁻) := by
  by_cases hr : 0 ≤ r
  · rw [posPart_smul_nonneg hr, negPart_smul_nonneg hr,
      tau_real_smul hτ_nn hτ_add hr (posPart_nonneg _),
      tau_real_smul hτ_nn hτ_add hr (negPart_nonneg _), smul_sub]
  · push_neg at hr
    have hnr : 0 ≤ -r := le_of_lt (neg_pos.mpr hr)
    have hrx : r • x = -((-r) • x) := by rw [neg_smul, neg_neg]
    have hp : (r • x)⁺ = (-r) • x⁻ := by
      rw [hrx, posPart_neg, negPart_smul_nonneg hnr]
    have hn : (r • x)⁻ = (-r) • x⁺ := by
      rw [hrx, negPart_neg, posPart_smul_nonneg hnr]
    rw [hp, hn,
      tau_real_smul hτ_nn hτ_add hnr (negPart_nonneg _),
      tau_real_smul hτ_nn hτ_add hnr (posPart_nonneg _)]
    rw [← smul_sub (-r) (τ x⁻) (τ x⁺),
      show τ x⁻ - τ x⁺ = -(τ x⁺ - τ x⁻) from (neg_sub _ _).symm,
      smul_neg, neg_smul, neg_neg]

variable
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)

/-- **Extension Lemma**: an additive map on the positive cone of a vector lattice
extends to a unique positive linear operator when the codomain is Archimedean.
The extension satisfies `T x = τ x⁺ − τ x⁻`. -/
noncomputable def extension : X →ₗ[ℝ] Y :=
  { toFun := fun x => τ x⁺ - τ x⁻
    map_add' := extFun_add hτ_nn hτ_add
    map_smul' := fun r x => by
      simp only [RingHom.id_apply]
      exact extFun_smul hτ_nn hτ_add r x }

@[simp]
theorem extension_apply (x : X) :
    extension hτ_nn hτ_add x = τ x⁺ - τ x⁻ := rfl

theorem extension_nonneg {x : X} (hx : 0 ≤ x) :
    extension hτ_nn hτ_add x = τ x := by
  rw [extension_apply, posPart_of_nonneg hx, negPart_of_nonneg hx,
    tau_zero hτ_add, sub_zero]

theorem extension_positive : Positive (extension hτ_nn hτ_add) :=
  fun x hx => by
    rw [extension_nonneg hτ_nn hτ_add hx]; exact hτ_nn _ hx

/-- The positive linear extension is the unique positive operator
extending τ on nonneg elements. -/
theorem extension_unique {f : X →ₗ[ℝ] Y} (_hf : Positive f)
    (hext : ∀ x, 0 ≤ x → f x = τ x) :
    f = extension hτ_nn hτ_add := by
  ext x
  simp only [extension_apply]
  rw [← hext _ (posPart_nonneg _), ← hext _ (negPart_nonneg _), ← map_sub]
  congr 1; exact (posPart_sub_negPart x).symm

/-- An additive bijection between positive cones extends to a vector lattice
isomorphism when the codomain is Archimedean. -/
noncomputable def extensionEquiv
    (hτ_inj : ∀ x y, 0 ≤ x → 0 ≤ y → τ x = τ y → x = y)
    (hτ_surj : ∀ y, 0 ≤ y → ∃ x, 0 ≤ x ∧ τ x = y) :
    VecLatEquiv X Y := by
  set T := extension hτ_nn hτ_add
  have hT_inj : Function.Injective T := by
    intro a b hab
    have h : T (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab
    rw [extension_apply] at h
    have heq : (a - b)⁺ = (a - b)⁻ :=
      hτ_inj _ _ (posPart_nonneg _) (negPart_nonneg _) (sub_eq_zero.mp h)
    have hsub := posPart_sub_negPart (a - b)
    rw [heq, sub_self] at hsub
    exact sub_eq_zero.mp hsub.symm
  have hT_surj : Function.Surjective T := by
    intro y
    obtain ⟨a, ha, haτ⟩ := hτ_surj y⁺ (posPart_nonneg y)
    obtain ⟨b, hb, hbτ⟩ := hτ_surj y⁻ (negPart_nonneg y)
    exact ⟨a - b, by
      rw [map_sub, extension_nonneg hτ_nn hτ_add ha,
        extension_nonneg hτ_nn hτ_add hb, haτ, hbτ,
        posPart_sub_negPart]⟩
  -- T is order-reflecting: 0 ≤ Tx → 0 ≤ x
  have hT_bipos : ∀ x, 0 ≤ T x → 0 ≤ x := by
    intro x hTx
    rw [extension_apply] at hTx
    have hτle : τ x⁻ ≤ τ x⁺ := sub_nonneg.mp hTx
    obtain ⟨c, hc, hcτ⟩ := hτ_surj _ hTx
    have hsum : τ (x⁻ + c) = τ x⁺ := by
      rw [hτ_add _ _ (negPart_nonneg _) hc, hcτ, add_sub_cancel]
    have heq : x⁻ + c = x⁺ :=
      hτ_inj _ _ (add_nonneg (negPart_nonneg _) hc) (posPart_nonneg _) hsum
    have hle : x⁻ ≤ x⁺ := heq ▸ le_add_of_nonneg_right hc
    have : x⁻ = 0 := (inf_eq_left.mpr hle).symm.trans
      ((inf_comm x⁻ x⁺).trans (posPart_inf_negPart_eq_zero x))
    rw [← posPart_sub_negPart x, this, sub_zero]
    exact posPart_nonneg _
  -- T⁻¹ is monotone (from bipositivity + positivity)
  have hT_inv_mono : ∀ a b, T a ≤ T b → a ≤ b := by
    intro a b hab
    have : 0 ≤ T (b - a) := by rw [map_sub]; exact sub_nonneg.mpr hab
    exact sub_nonneg.mp (hT_bipos _ this)
  have hT_mono : Monotone T := monotone_iff.mpr (extension_positive hτ_nn hτ_add)
  -- T preserves ⊔
  have hT_sup : ∀ a b, T (a ⊔ b) = T a ⊔ T b := by
    intro a b
    apply le_antisymm
    · obtain ⟨c, hc⟩ := hT_surj (T a ⊔ T b)
      have hca : a ≤ c := hT_inv_mono _ _ (hc ▸ le_sup_left)
      have hcb : b ≤ c := hT_inv_mono _ _ (hc ▸ le_sup_right)
      rw [← hc]; exact hT_mono (sup_le hca hcb)
    · exact sup_le (hT_mono le_sup_left) (hT_mono le_sup_right)
  -- T preserves ⊓
  have hT_inf : ∀ a b, T (a ⊓ b) = T a ⊓ T b := by
    intro a b
    apply le_antisymm
    · exact le_inf (hT_mono inf_le_left) (hT_mono inf_le_right)
    · obtain ⟨c, hc⟩ := hT_surj (T a ⊓ T b)
      have hca : c ≤ a := hT_inv_mono _ _ (hc ▸ inf_le_left)
      have hcb : c ≤ b := hT_inv_mono _ _ (hc ▸ inf_le_right)
      rw [← hc]; exact hT_mono (le_inf hca hcb)
  exact
    { (LinearEquiv.ofBijective T ⟨hT_inj, hT_surj⟩) with
      map_sup' := hT_sup
      map_inf' := hT_inf }

end ExtensionLemma

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]

private lemma norm_map_le_of_abs_le {f : X →ₗ[ℝ] Y} (hf : Positive f)
    {x y : X} (h : |x| ≤ y) : ‖f x‖ ≤ ‖f y‖ :=
  norm_le_norm_of_abs_le_abs <|
    (abs_le_map_abs hf x).trans <|
    ((monotone_iff.mpr hf) h).trans (le_abs_self _)

/-- Every positive linear operator from a Banach lattice to a normed vector lattice
is continuous. -/
theorem continuous {f : X →ₗ[ℝ] Y} (hf : Positive f) : Continuous f := by
  by_contra hcont
  have hunb : ∀ C : ℝ, ∃ x : X, C * ‖x‖ < ‖f x‖ := by
    by_contra h; push_neg at h; obtain ⟨C, hC⟩ := h
    exact hcont (continuous_of_linear_of_bound f.map_add f.map_smul hC)
  -- For each n, find xₙ with ‖xₙ‖ ≤ (1/2)ⁿ and n < ‖f xₙ‖
  have hseq : ∀ n : ℕ, ∃ x : X, ‖x‖ ≤ (1 / 2 : ℝ) ^ n ∧ (n : ℝ) < ‖f x‖ := by
    intro n
    obtain ⟨z, hz⟩ := hunb ((n : ℝ) * (2 : ℝ) ^ n)
    have hznz : z ≠ 0 := by intro h; simp [h] at hz
    refine ⟨((2 : ℝ) ^ n * ‖z‖)⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      simp [one_div, mul_comm]
    · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      rw [lt_inv_mul_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * ‖z‖)]
      linarith [mul_comm ((n : ℝ) * (2 : ℝ) ^ n) ‖z‖]
  choose x hxn hxf using hseq
  have habs : Summable (fun n => |x n|) :=
    .of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ n)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      (fun n => by rw [norm_abs_eq_norm]; exact hxn n)
  set y := ∑' n, |x n|
  have hle : ∀ n, |x n| ≤ y := fun n => habs.le_tsum n (fun j _ => abs_nonneg _)
  obtain ⟨N, hN⟩ := exists_nat_gt ‖f y‖
  exact absurd (lt_of_lt_of_le (hxf N) (norm_map_le_of_abs_le hf (hle N)))
    (not_lt.mpr hN.le)

end Positive

namespace VecLatEquiv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [BanachLattice Y]

/-- A vector lattice isomorphism between Banach lattices extends to a continuous linear
equivalence. -/
noncomputable def toContinuousLinearEquiv (e : VecLatEquiv X Y) : X ≃L[ℝ] Y :=
  ContinuousLinearEquiv.mk e.toLinearEquiv
    (Positive.continuous (Positive.monotone_iff.mp e.toVecLatHom.monotone))
    (Positive.continuous (Positive.monotone_iff.mp e.symm.toVecLatHom.monotone))

end VecLatEquiv
