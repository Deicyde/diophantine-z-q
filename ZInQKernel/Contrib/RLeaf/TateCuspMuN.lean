import ZInQKernel.Contrib.RLeaf.TateCuspGlue
import ZInQKernel.Contrib.RLeaf.IgusaLocal
import ZInQKernel.Contrib.TauCeti.Backport.AlgebraicGeometry.EllipticCurve.TateCurve.Homomorphism
import ZInQKernel.Contrib.TauCeti.Backport.RingTheory.HahnSeries.Map

/-!
# t40-tate: the cusp `μ_N` of the Tate curve

Over `L' = K((t))`, `K = ℚ(ζ_N)`, the Tate curve `E_t` has the points `P(ζ^m)` (Tate's
uniformization of the roots of unity), and the coefficientwise action of `Gal(K/ℚ)` on `L'` is
continuous and commutes with the Tate coordinates, so it permutes the `x`-coordinates of the
generators of `⟨P(ζ)⟩` transitively. Transported to `E_j` over `\overline{L'}` (with `j ↦ j(E_t)`)
this gives the cusp statement `TateMuN` of task t40-igusa.
-/

noncomputable section

namespace ZInQ.RLeaf.TateCuspMuN

open MonoidWithZeroHom.ValueGroup₀ WithZeroMulInt TauCeti
open scoped WithZero
open LeafModCurves

/-! ### `K((t))` as a complete normed field -/

/-- The `t`-adic valuation of `K((t))` has rank one (normalized by `|t| = 1/2`). -/
@[reducible] def rankOneK (K : Type*) [Field K] :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).RankOne where
  hom' := (toNNReal (two_ne_zero)).comp embedding
  strictMono' := (toNNReal_strictMono one_lt_two).comp embedding_strictMono
  exists_val_nontrivial := ⟨HahnSeries.single 1 1, by
    rw [LaurentSeries.valuation_single_zpow]
    exact ⟨WithZero.exp_ne_zero, by
      rw [Ne, ← WithZero.exp_zero, WithZero.exp_inj]; omega⟩⟩

attribute [local instance] rankOneK

open scoped Valued

instance (K : Type*) [Field K] : CompleteSpace (LaurentSeries K) :=
  LaurentSeries.instLaurentSeriesComplete

theorem norm_eq (K : Type*) [Field K] (x : LaurentSeries K) :
    ‖x‖ = (toNNReal (two_ne_zero) (Valued.v x) : ℝ) := by
  rw [Valued.toNormedField.norm_def]
  show ((toNNReal _).comp embedding (Valued.v.restrict x) : ℝ) = _
  rw [MonoidWithZeroHom.comp_apply]
  congr 2
  exact embedding_restrict₀ x

/-- Two elements of `ℤᵐ⁰` with the same bounds `≤ exp (-D)` are equal. -/
theorem eq_of_forall_le_exp_iff {a b : ℤᵐ⁰}
    (h : ∀ D : ℤ, a ≤ WithZero.exp (-D) ↔ b ≤ WithZero.exp (-D)) : a = b := by
  have key : ∀ a b : ℤᵐ⁰, (∀ D : ℤ, a ≤ WithZero.exp (-D) → b ≤ WithZero.exp (-D)) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · subst ha
      by_contra hb
      have hb0 : b ≠ 0 := by rintro rfl; exact hb le_rfl
      have h1 := h (-(WithZero.log b) + 1) zero_le
      have h2 : WithZero.exp (WithZero.log b) ≤ WithZero.exp (-(-(WithZero.log b) + 1)) := by
        rwa [WithZero.exp_log hb0]
      rw [WithZero.exp_le_exp] at h2
      omega
    · have := h (-(WithZero.log a)) (by rw [neg_neg, WithZero.exp_log ha])
      rwa [neg_neg, WithZero.exp_log ha] at this
  exact le_antisymm (key b a fun D => (h D).mpr) (key a b fun D => (h D).mp)

/-- The coefficientwise image along an injective field map preserves the valuation. -/
theorem valuation_mapRingHom {K K' : Type*} [Field K] [Field K'] (f : K →+* K')
    (x : LaurentSeries K) :
    Valued.v (HahnSeries.mapRingHom f x : LaurentSeries K') = Valued.v x := by
  refine eq_of_forall_le_exp_iff fun D => ?_
  rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  rw [HahnSeries.coeff_mapRingHom, map_eq_zero_iff f f.injective]

theorem norm_mapRingHom {K K' : Type*} [Field K] [Field K'] (f : K →+* K')
    (x : LaurentSeries K) :
    ‖(HahnSeries.mapRingHom f x : LaurentSeries K')‖ = ‖x‖ := by
  rw [norm_eq, norm_eq, valuation_mapRingHom]

instance {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    RingHomIsometric (HahnSeries.mapRingHom f : LaurentSeries K →+* LaurentSeries K') :=
  ⟨fun {x} => norm_mapRingHom f x⟩

theorem continuous_mapRingHom {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    Continuous (HahnSeries.mapRingHom f : LaurentSeries K →+* LaurentSeries K') :=
  AddMonoidHomClass.continuous_of_bound _ 1 fun x => by rw [one_mul, norm_mapRingHom]

/-! ### The uniformizer and the roots of unity -/

/-- The uniformizer `t` of `K((t))` as a unit. -/
def tK (K : Type*) [Field K] : (LaurentSeries K)ˣ := Units.mk0 (HahnSeries.single 1 1) (by simp)

theorem valuation_tK_zpow (K : Type*) [Field K] (k : ℤ) :
    Valued.v (((tK K ^ k : (LaurentSeries K)ˣ)) : LaurentSeries K) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  change Valued.v (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ^ k = _
  rw [LaurentSeries.valuation_single_zpow, ← WithZero.exp_zsmul]
  simp

theorem norm_tK_lt_one (K : Type*) [Field K] : ‖((tK K : (LaurentSeries K)ˣ) : LaurentSeries K)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have := valuation_tK_zpow K 1
  rw [zpow_one] at this
  rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem mapRingHom_tK {K K' : Type*} [Field K] [Field K'] (f : K →+* K') :
    Units.map (HahnSeries.mapRingHom f : LaurentSeries K →+* LaurentSeries K').toMonoidHom (tK K) =
      tK K' := by
  ext n
  simp only [tK, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Units.val_mk0,
    HahnSeries.coeff_mapRingHom, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem valuation_C {K : Type*} [Field K] {a : K} (ha : a ≠ 0) :
    Valued.v (HahnSeries.C a : LaurentSeries K) = 1 := by
  have h1 : ∀ b : K, Valued.v (HahnSeries.C b : LaurentSeries K) ≤ 1 := fun b =>
    (LaurentSeries.val_le_one_iff_eq_coe K _).mpr ⟨PowerSeries.C b, HahnSeries.ofPowerSeries_C (Γ := ℤ) b⟩
  have h2 : Valued.v (HahnSeries.C a : LaurentSeries K) * Valued.v (HahnSeries.C a⁻¹ : LaurentSeries K) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  refine le_antisymm (h1 a) ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_one_of_lt_of_le hlt (h1 a⁻¹)
  rw [h2] at this
  exact lt_irrefl _ this

/-! ### Generic transport lemmas -/

/-- Points along an equality of curves. -/
def castEquiv {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := h ▸ AddEquiv.refl _

theorem xCoord_castEquiv {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    (h : W₁ = W₂) (P : W₁.toAffine.Point) : xCoord (castEquiv h P) = xCoord P := by
  subst h; rfl

theorem xCoord_addEquivVariableChange {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (P : (C • W).toAffine.Point) (hP : P ≠ 0) :
    xCoord (WeierstrassCurve.Affine.Point.addEquivVariableChange W C P) =
      (C.u : F) ^ 2 * xCoord P + C.r := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · show xCoord (WeierstrassCurve.Affine.Point.equivVariableChange W C (.some x y h)) = _
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]; rfl

theorem xCoord_tate {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (u : Kˣ)
    (hne : tateUniformizationHom q hq (Additive.ofMul (u : Kˣ ⧸ Subgroup.zpowers q)) ≠ 0) :
    xCoord (tateUniformizationHom q hq (Additive.ofMul (u : Kˣ ⧸ Subgroup.zpowers q))) =
      tateUniformizationX q u := by
  have h1 : (u : Kˣ ⧸ Subgroup.zpowers q) ≠ 1 := fun h => hne (by
    rw [tateUniformizationHom_apply, toMul_ofMul, h, tateUniformization_one])
  rw [tateUniformizationHom_apply, toMul_ofMul, tateUniformization_of_ne_one q hq h1]
  rfl

theorem tate_ofMul_pow {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (y : Kˣ) (m : ℕ) :
    tateUniformizationHom q hq (Additive.ofMul ((y ^ m : Kˣ) : Kˣ ⧸ Subgroup.zpowers q)) =
      m • tateUniformizationHom q hq (Additive.ofMul (y : Kˣ ⧸ Subgroup.zpowers q)) := by
  rw [QuotientGroup.mk_pow, ofMul_pow, map_nsmul]

theorem ne_zero_of_addOrderOf_map {A B : Type*} [AddCommGroup A] [AddCommGroup B] (Φ : A →+ B)
    (x : A) {N : ℕ} (hN : 2 ≤ N) (h : addOrderOf (Φ x) = N) : x ≠ 0 := by
  rintro rfl
  rw [map_zero, addOrderOf_zero] at h
  omega

theorem nsmul_map_eq {A B C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C']
    (Φ : B →+ C') (t : A →+ B) (x y : A) (m : ℕ) (h : t y = m • t x) :
    m • Φ (t x) = Φ (t y) := by
  rw [← map_nsmul, h]

theorem tateCurveAt_congr {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {q q' : Kˣ} (h : q = q') (hq : ‖(q : K)‖ < 1) (hq' : ‖(q' : K)‖ < 1) :
    tateCurveAt q hq = tateCurveAt q' hq' := by
  subst h; rfl

/-- The `x`-coordinate transformation between a curve and `E_j` over a common field is defined
over `ℚ((t))` (copy of the computation in `TateCuspGlue`). -/
theorem uR_mem {Ω : Type*} [Field Ω] [CharZero Ω] (ι : LaurentSeries ℚ →+* Ω)
    {W : WeierstrassCurve (LaurentSeries ℚ)} [W.IsElliptic]
    (hj : W.j ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ)) (T : WeierstrassCurve Ω)
    {x4 x6 x2 : LaurentSeries ℚ} (hT4 : T.c₄ = ι x4) (hT6 : T.c₆ = ι x6) (hT2 : T.b₂ = ι x2)
    (C : WeierstrassCurve.VariableChange Ω) (hC : C • T = W.map ι) :
    ((C.u : Ω) ^ 2 ∈ ι.fieldRange) ∧ C.r ∈ ι.fieldRange := by
  have hιR : ∀ z, ι z ∈ ι.fieldRange := fun z => ⟨z, rfl⟩
  have h4 := congrArg WeierstrassCurve.c₄ hC
  have h6 := congrArg WeierstrassCurve.c₆ hC
  have h2 := congrArg WeierstrassCurve.b₂ hC
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄ W ι] at h4
  rw [WeierstrassCurve.variableChange_c₆, WeierstrassCurve.map_c₆ W ι] at h6
  rw [WeierstrassCurve.variableChange_b₂, WeierstrassCurve.map_b₂ W ι] at h2
  set a : Ω := ((C.u⁻¹ : Ωˣ) : Ω) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hc4 : ι W.c₄ ≠ 0 := (map_ne_zero ι).mpr (TateCuspGlue.c₄_ne_zero hj)
  have hc6 : ι W.c₆ ≠ 0 := (map_ne_zero ι).mpr (TateCuspGlue.c₆_ne_zero hj)
  have hT4' : T.c₄ ≠ 0 := fun h0 => hc4 (by rw [← h4, h0, mul_zero])
  have hT6' : T.c₆ ≠ 0 := fun h0 => hc6 (by rw [← h6, h0, mul_zero])
  have ha2 : a ^ 2 = ι W.c₆ * T.c₄ / (ι W.c₄ * T.c₆) := by
    rw [← h4, ← h6]; field_simp
  have ha2R : a ^ 2 ∈ ι.fieldRange := by
    rw [ha2, hT4, hT6]
    exact div_mem (mul_mem (hιR _) (hιR _)) (mul_mem (hιR _) (hιR _))
  refine ⟨?_, ?_⟩
  · have : ((C.u : Ωˣ) : Ω) ^ 2 = (a ^ 2)⁻¹ := by
      rw [ha, Units.val_inv_eq_inv_val, inv_pow, inv_inv]
    rw [this]; exact inv_mem ha2R
  · have : C.r = (ι W.b₂ / a ^ 2 - T.b₂) / 12 := by
      rw [← h2]; field_simp; ring
    rw [this, hT2]
    exact div_mem (sub_mem (div_mem (hιR _) ha2R) (hιR _)) ⟨12, map_ofNat ι 12⟩

theorem exists_nat_zsmul_eq {G : Type*} [AddCommGroup G] (Q : G) {N : ℕ} (hQ : addOrderOf Q = N)
    (hN : 0 < N) (k : ℤ) : ∃ m : ℕ, m < N ∧ k • Q = m • Q := by
  have hNQ : N • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hk0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg k (by exact_mod_cast hN.ne')
  have hkN : k % (N : ℤ) < N := Int.emod_lt_of_pos k (by exact_mod_cast hN)
  refine ⟨(k % (N : ℤ)).toNat, by omega, ?_⟩
  have hmk : (((k % (N : ℤ)).toNat : ℕ) : ℤ) = k % (N : ℤ) := Int.toNat_of_nonneg hk0
  have h1 : ((N : ℤ) * (k / N)) • Q = 0 := by
    rw [mul_comm, ← smul_smul, natCast_zsmul, hNQ, zsmul_zero]
  conv_lhs => rw [← Int.mul_ediv_add_emod k N]
  rw [add_zsmul, h1, zero_add]
  conv_lhs => rw [← hmk]
  rw [natCast_zsmul]

theorem coprime_of_addOrderOf_nsmul {G : Type*} [AddCommGroup G] (Q : G) {N : ℕ}
    (hQ : addOrderOf Q = N) (hN : 2 ≤ N) (m : ℕ) (hm : addOrderOf (m • Q) = N) :
    Nat.Coprime m N := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_nsmul, addOrderOf_zero] at hm
    omega
  rw [addOrderOf_nsmul' _ hm0, hQ] at hm
  rcases (Nat.div_eq_self.mp hm) with h | h
  · omega
  · rw [Nat.coprime_comm]; exact h

/-! ### The Tate curve over `ℚ((t))` and its `j`-invariant -/

/-- `E_t` over `ℚ((t))`. -/
def WL : WeierstrassCurve (LaurentSeries ℚ) := tateCurveAt (tK ℚ) (norm_tK_lt_one ℚ)

instance : WL.IsElliptic := by unfold WL; infer_instance

theorem WL_j_not_mem : WL.j ∉ Set.range (HahnSeries.ofPowerSeries ℤ ℚ) := by
  rintro ⟨F, hF⟩
  have h1 : Valued.v WL.j ≤ 1 := (LaurentSeries.val_le_one_iff_eq_coe ℚ _).mpr ⟨F, hF⟩
  rw [← Valued.toNormedField.norm_le_one_iff] at h1
  unfold WL at h1
  rw [norm_tateCurveAt_j] at h1
  have hq := norm_tK_lt_one ℚ
  have hpos : 0 < ‖((tK ℚ : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ)‖ :=
    norm_pos_iff.mpr (Units.ne_zero _)
  have := (one_lt_inv₀ hpos).mpr hq
  linarith

/-- `ℚ(j) → ℚ((t))`, `j ↦ j(E_t)`. -/
def phiL : Qj →+* LaurentSeries ℚ := TateCuspGlue.phi WL.j WL_j_not_mem

/-! ### The cusp over an arbitrary complete extension `F` of `ℚ((t))`

Everything is stated for a complete non-archimedean normed field `F` with an isometric
embedding `incl : ℚ((t)) → F`, so that all structures on `F` come from `[NormedField F]` (and
the kernel never compares two instance paths on a concrete field). -/

section Generic

variable (F : Type) [NormedField F] [CompleteSpace F] [IsUltrametricDist F] [CharZero F]
  [DecidableEq F] (incl : LaurentSeries ℚ →+* F) [RingHomIsometric incl]

/-- `Ω = \overline{F}`, a copy of `AlgebraicClosure F` remembering `incl` (so that its
`ℚ(j)`-algebra structure `j ↦ j(E_t)` can be an instance). -/
def ΩF (_incl : LaurentSeries ℚ →+* F) : Type := AlgebraicClosure F

instance : Field (ΩF F incl) := inferInstanceAs (Field (AlgebraicClosure F))
instance : IsAlgClosed (ΩF F incl) := inferInstanceAs (IsAlgClosed (AlgebraicClosure F))
instance : Algebra F (ΩF F incl) := inferInstanceAs (Algebra F (AlgebraicClosure F))
instance : IsAlgClosure F (ΩF F incl) := inferInstanceAs (IsAlgClosure F (AlgebraicClosure F))
instance : Module.IsTorsionFree F (ΩF F incl) :=
  inferInstanceAs (Module.IsTorsionFree F (AlgebraicClosure F))
instance : CharZero (ΩF F incl) :=
  charZero_of_injective_algebraMap (algebraMap F (ΩF F incl)).injective
noncomputable instance : DecidableEq (ΩF F incl) := Classical.decEq _

/-- `ℚ((t)) → Ω`. -/
abbrev ιF : LaurentSeries ℚ →+* ΩF F incl := (algebraMap F (ΩF F incl)).comp incl

/-- `Ω` as a `ℚ(j)`-algebra through `j ↦ j(E_t)`. -/
instance algQjΩF : Algebra Qj (ΩF F incl) := ((ιF F incl).comp phiL).toAlgebra

/-- The parameter `q = t` in `F`. -/
def qF : Fˣ := Units.map (incl : LaurentSeries ℚ →* F) (tK ℚ)

theorem norm_qF : ‖((qF F incl : Fˣ) : F)‖ < 1 := by
  rw [qF, Units.coe_map, MonoidHom.coe_ofClass, RingHomIsometric.norm_map]
  exact norm_tK_lt_one ℚ

theorem WL_map_incl : WL.map incl = tateCurveAt (qF F incl) (norm_qF F incl) := by
  unfold WL
  exact map_tateCurveAt incl (tK ℚ) _

theorem algebraMap_Qj_ΩF (a : Qj) : algebraMap Qj (ΩF F incl) a = ιF F incl (phiL a) := rfl

theorem ΩF_c₄ : (Ej.baseChange (ΩF F incl)).c₄ = ιF F incl (phiL Ej.c₄) := by
  show (Ej.map (algebraMap Qj (ΩF F incl))).c₄ = _
  rw [WeierstrassCurve.map_c₄, algebraMap_Qj_ΩF]

theorem ΩF_c₆ : (Ej.baseChange (ΩF F incl)).c₆ = ιF F incl (phiL Ej.c₆) := by
  show (Ej.map (algebraMap Qj (ΩF F incl))).c₆ = _
  rw [WeierstrassCurve.map_c₆, algebraMap_Qj_ΩF]

theorem ΩF_b₂ : (Ej.baseChange (ΩF F incl)).b₂ = ιF F incl (phiL Ej.b₂) := by
  show (Ej.map (algebraMap Qj (ΩF F incl))).b₂ = _
  rw [WeierstrassCurve.map_b₂, algebraMap_Qj_ΩF]

instance : (Ej.baseChange (ΩF F incl)).IsElliptic := inferInstanceAs ((Ej.map _).IsElliptic)

theorem ΩF_j : (Ej.baseChange (ΩF F incl)).j = (WL.map (ιF F incl)).j := by
  rw [WeierstrassCurve.map_j]
  show (Ej.map (algebraMap Qj (ΩF F incl))).j = _
  rw [WeierstrassCurve.map_j, Ej_j, algebraMap_Qj_ΩF, phiL, TateCuspGlue.phi_X]

/-- The automorphism of `Ω` extending a ring automorphism `σ` of `F` that fixes `ℚ((t))`; it
fixes `ℚ(j)`. -/
def tauF (σ : F ≃+* F) (hσ : ∀ z, σ (incl z) = incl z) : ΩF F incl ≃ₐ[Qj] ΩF F incl :=
  AlgEquiv.ofRingEquiv (f := IsAlgClosure.equivOfEquiv (ΩF F incl) (ΩF F incl) σ) fun a => by
    simp only [algebraMap_Qj_ΩF, ιF, RingHom.comp_apply]
    rw [IsAlgClosure.equivOfEquiv_algebraMap, hσ]

theorem tauF_algebraMap (σ : F ≃+* F) (hσ : ∀ z, σ (incl z) = incl z) (s : F) :
    tauF F incl σ hσ (algebraMap F (ΩF F incl) s) = algebraMap F (ΩF F incl) (σ s) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ s

theorem tauF_ιF (σ : F ≃+* F) (hσ : ∀ z, σ (incl z) = incl z) (z : LaurentSeries ℚ) :
    tauF F incl σ hσ (ιF F incl z) = ιF F incl z := by
  simp only [ιF, RingHom.comp_apply]
  rw [tauF_algebraMap, hσ]


/-- The transport of points from a curve `E` over `F` with `E = W ⊗ F` to a curve `T` over `Ω`
with `C • T = W ⊗ Ω`. -/
def PhiF (W : WeierstrassCurve (LaurentSeries ℚ)) (E : WeierstrassCurve F)
    (hW : W.map incl = E) (T : WeierstrassCurve (ΩF F incl))
    (C : WeierstrassCurve.VariableChange (ΩF F incl)) (hC : C • T = W.map (ιF F incl)) :
    E.toAffine.Point →+ T.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.addEquivVariableChange T C).toAddMonoidHom.comp
    ((castEquiv hC.symm).toAddMonoidHom.comp
      ((castEquiv (W.map_map incl (algebraMap F (ΩF F incl)))).toAddMonoidHom.comp
        ((AddMonoidHom.mk'
          (WeierstrassCurve.Affine.Point.mapAlong (algebraMap F (ΩF F incl))
            (algebraMap F (ΩF F incl)).injective)
          (WeierstrassCurve.Affine.Point.mapAlong_add _ _)).comp
          (castEquiv hW.symm).toAddMonoidHom)))

theorem PhiF_injective (W : WeierstrassCurve (LaurentSeries ℚ)) (E : WeierstrassCurve F)
    (hW : W.map incl = E) (T : WeierstrassCurve (ΩF F incl))
    (C : WeierstrassCurve.VariableChange (ΩF F incl)) (hC : C • T = W.map (ιF F incl)) :
    Function.Injective (PhiF F incl W E hW T C hC) := fun a b h =>
  (castEquiv hW.symm).injective (WeierstrassCurve.Affine.Point.mapAlong_injective
    (algebraMap F (ΩF F incl)) (algebraMap F (ΩF F incl)).injective
    ((castEquiv (W.map_map incl (algebraMap F (ΩF F incl)))).injective
      ((castEquiv hC.symm).injective
      ((WeierstrassCurve.Affine.Point.addEquivVariableChange T C).injective h))))

theorem xCoord_PhiF (W : WeierstrassCurve (LaurentSeries ℚ)) (E : WeierstrassCurve F)
    (hW : W.map incl = E) (T : WeierstrassCurve (ΩF F incl))
    (C : WeierstrassCurve.VariableChange (ΩF F incl)) (hC : C • T = W.map (ιF F incl))
    (P : E.toAffine.Point) (hP : P ≠ 0) :
    xCoord (PhiF F incl W E hW T C hC P) =
      (C.u : ΩF F incl) ^ 2 * algebraMap F (ΩF F incl) (xCoord P) + C.r := by
  set X := (castEquiv hC.symm) ((castEquiv (W.map_map incl (algebraMap F (ΩF F incl))))
        (WeierstrassCurve.Affine.Point.mapAlong (algebraMap F (ΩF F incl))
            (algebraMap F (ΩF F incl)).injective (castEquiv hW.symm P))) with hX
  have hX0 : X ≠ 0 := by
    intro h0
    apply hP
    apply PhiF_injective F incl W E hW T C hC
    show WeierstrassCurve.Affine.Point.addEquivVariableChange T C X = _
    rw [h0, map_zero, map_zero]
  show xCoord (WeierstrassCurve.Affine.Point.addEquivVariableChange T C X) = _
  rw [xCoord_addEquivVariableChange _ _ _ hX0, hX, xCoord_castEquiv, xCoord_castEquiv,
    TateCuspGlue.xCoord_mapAlong, xCoord_castEquiv]

/-- The Galois-type input: `σ` with `σ(u) = u^m`. -/
theorem sigma_X (σ : F ≃+* F) (hσc : Continuous σ) (hσ : ∀ z, σ (incl z) = incl z) (u : Fˣ)
    (m : ℕ) (hu : Units.map (σ : F →* F) u = u ^ m) :
    σ (tateUniformizationX (qF F incl) u) = tateUniformizationX (qF F incl) (u ^ m) := by
  have h := map_tateUniformizationX (σ : F →+* F) hσc (qF F incl) u (norm_qF F incl)
  have hq : Units.map ((σ : F →+* F) : F →* F) (qF F incl) = qF F incl := by
    ext; simp [qF, hσ]
  have hu' : Units.map ((σ : F →+* F) : F →* F) u = u ^ m := hu
  rw [hq, hu'] at h
  exact h

/-- **The cusp `μ_N` over `Ω = \overline{F}`.** -/
theorem tateMuNAt_of_unit (N : ℕ) (hN : 2 ≤ N) (u : Fˣ)
    (hu : orderOf (u : Fˣ ⧸ Subgroup.zpowers (qF F incl)) = N)
    (hgal : ∀ m : ℕ, m < N → Nat.Coprime m N → ∃ σ : F ≃+* F, Continuous σ ∧
      (∀ z, σ (incl z) = incl z) ∧ Units.map (σ : F →* F) u = u ^ m) :
    TateMuNAt N (ΩF F incl) := by
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ (ΩF_j F incl)
  obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩ :=
    uR_mem (ιF F incl) WL_j_not_mem _ (ΩF_c₄ F incl) (ΩF_c₆ F incl) (ΩF_b₂ F incl) C hC
  have hq := norm_qF F incl
  have hΦ := PhiF_injective F incl WL _ (WL_map_incl F incl) _ C hC
  have htate : Function.Injective (tateUniformizationHom (qF F incl) hq) :=
    tateUniformizationHom_injective _ hq
  have hQ₀ : addOrderOf (PhiF F incl WL _ (WL_map_incl F incl) _ C hC
      (tateUniformizationHom (qF F incl) hq
        (Additive.ofMul (u : Fˣ ⧸ Subgroup.zpowers (qF F incl))))) = N := by
    have hx₀ : addOrderOf (Additive.ofMul (u : Fˣ ⧸ Subgroup.zpowers (qF F incl))) = N := by
      rw [addOrderOf_ofMul_eq_orderOf, hu]
    rw [addOrderOf_injective _ hΦ]
    exact (addOrderOf_injective _ htate _).trans hx₀
  refine ⟨_, hQ₀, fun R hR hRo => ?_⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
  obtain ⟨m, hmN, hkm⟩ := exists_nat_zsmul_eq _ hQ₀ (by omega) k
  rw [hkm] at hRo ⊢
  have hcop := coprime_of_addOrderOf_nsmul _ hQ₀ hN m hRo
  obtain ⟨σ, hσc, hσ, hσu⟩ := hgal m hmN hcop
  refine ⟨tauF F incl σ hσ, ?_⟩
  have hEq := nsmul_map_eq (PhiF F incl WL _ (WL_map_incl F incl) _ C hC)
    (tateUniformizationHom (qF F incl) hq)
    (Additive.ofMul (u : Fˣ ⧸ Subgroup.zpowers (qF F incl)))
    (Additive.ofMul ((u ^ m : Fˣ) : Fˣ ⧸ Subgroup.zpowers (qF F incl))) m
    (tate_ofMul_pow (qF F incl) hq u m)
  rw [hEq] at hRo ⊢
  have hNz : ∀ y, addOrderOf (PhiF F incl WL _ (WL_map_incl F incl) _ C hC
      (tateUniformizationHom (qF F incl) hq y)) = N →
      tateUniformizationHom (qF F incl) hq y ≠ 0 := fun y hy =>
    ne_zero_of_addOrderOf_map (PhiF F incl WL _ (WL_map_incl F incl) _ C hC) _ hN hy
  rw [xCoord_PhiF F incl WL _ (WL_map_incl F incl) _ C hC _ (hNz _ hQ₀),
    xCoord_PhiF F incl WL _ (WL_map_incl F incl) _ C hC _ (hNz _ hRo),
    xCoord_tate _ hq _ (hNz _ hQ₀), xCoord_tate _ hq _ (hNz _ hRo), ← hα, ← hβ,
    map_add, map_mul, tauF_ιF, tauF_ιF, tauF_algebraMap, sigma_X F incl σ hσc hσ u m hσu]

end Generic

/-! ### Specialization: `F = K((t))` -/

section Laurent

variable (K : Type) [Field K] [CharZero K]

noncomputable instance : DecidableEq (LaurentSeries K) := Classical.decEq _

instance : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries K)).injective

/-- `ℚ((t)) → K((t))`. -/
def inclK : LaurentSeries ℚ →+* LaurentSeries K := HahnSeries.mapRingHom (algebraMap ℚ K)

instance : RingHomIsometric (inclK K) :=
  inferInstanceAs (RingHomIsometric (HahnSeries.mapRingHom (Γ := ℤ) (algebraMap ℚ K)))

theorem qF_inclK : qF (LaurentSeries K) (inclK K) = tK K := by
  ext n
  simp only [qF, tK, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, inclK,
    HahnSeries.coeff_mapRingHom, HahnSeries.coeff_single]
  split_ifs <;> simp

/-- A nonzero `ζ ∈ K` as a unit of `K((t))`. -/
def uζ (ζ : K) (hζ0 : ζ ≠ 0) : (LaurentSeries K)ˣ := Units.mk0 (HahnSeries.C ζ) (HahnSeries.C_ne_zero hζ0)

theorem orderOf_uζ (ζ : K) (hζ0 : ζ ≠ 0) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) :
    orderOf ((uζ K ζ hζ0 : (LaurentSeries K)ˣ) :
      (LaurentSeries K)ˣ ⧸ Subgroup.zpowers (qF (LaurentSeries K) (inclK K))) = N := by
  rw [qF_inclK]
  have hpow : ∀ m : ℕ, ((uζ K ζ hζ0 ^ m : (LaurentSeries K)ˣ) : LaurentSeries K) =
      HahnSeries.C (ζ ^ m) := fun m => by
    rw [Units.val_pow_eq_pow_val, map_pow]; rfl
  rw [orderOf_eq_iff hN]
  refine ⟨?_, fun m hm hm0 h => ?_⟩
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : uζ K ζ hζ0 ^ N = 1 := by
      ext; rw [hpow, hζ.pow_eq_one, map_one, Units.val_one]
    rw [this]; exact one_mem _
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    have hv := congrArg (fun u : (LaurentSeries K)ˣ => Valued.v (u : LaurentSeries K)) hk
    simp only [valuation_tK_zpow, hpow] at hv
    rw [valuation_C (pow_ne_zero _ hζ0)] at hv
    have hk0 : k = 0 := by
      rw [← WithZero.exp_zero, WithZero.exp_inj] at hv; omega
    rw [hk0, zpow_zero] at hk
    have h1 : HahnSeries.C (ζ ^ m) = (HahnSeries.C (1 : K) : LaurentSeries K) := by
      rw [← hpow, ← hk, map_one]; rfl
    have h2 := HahnSeries.C_injective h1
    exact absurd (Nat.le_of_dvd hm0 (hζ.dvd_of_pow_eq_one m h2)) (by omega)

/-- The coefficientwise action of a ring automorphism `g` of `K` on `K((t))`. -/
def sigmaK (g : K ≃+* K) : LaurentSeries K ≃+* LaurentSeries K :=
  RingEquiv.ofRingHom (HahnSeries.mapRingHom (g : K →+* K))
    (HahnSeries.mapRingHom (g.symm : K →+* K))
    (by rw [← HahnSeries.mapRingHom_comp]; ext x n; simp [HahnSeries.coeff_mapRingHom])
    (by rw [← HahnSeries.mapRingHom_comp]; ext x n; simp [HahnSeries.coeff_mapRingHom])

theorem sigmaK_inclK (g : K ≃+* K) (z : LaurentSeries ℚ) :
    sigmaK K g (inclK K z) = inclK K z := by
  show HahnSeries.mapRingHom (g : K →+* K) (HahnSeries.mapRingHom _ z) = _
  ext n
  simp [inclK, HahnSeries.coeff_mapRingHom, RingHom.map_rat_algebraMap]

theorem continuous_sigmaK (g : K ≃+* K) : Continuous (sigmaK K g) :=
  continuous_mapRingHom (g : K →+* K)

theorem sigmaK_uζ (g : K ≃+* K) (ζ : K) (hζ0 : ζ ≠ 0) (m : ℕ) (hg : g ζ = ζ ^ m) :
    Units.map (sigmaK K g : LaurentSeries K →* LaurentSeries K) (uζ K ζ hζ0) =
      uζ K ζ hζ0 ^ m := by
  ext n
  rw [Units.coe_map, Units.val_pow_eq_pow_val, MonoidHom.coe_ofClass]
  show HahnSeries.coeff (HahnSeries.mapRingHom (g : K →+* K) (HahnSeries.C _)) n = _
  rw [HahnSeries.coeff_mapRingHom, uζ, Units.val_mk0, ← map_pow, HahnSeries.C_apply,
    HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp [hg]

/-- **The cusp `μ_N` over `\overline{K((t))}`.** -/
theorem tateMuNAt_of_root (N : ℕ) (hN : 2 ≤ N) (ζ : K) (hζ : IsPrimitiveRoot ζ N)
    (hgal : ∀ m : ℕ, m < N → Nat.Coprime m N → ∃ g : K ≃+* K, g ζ = ζ ^ m) :
    TateMuNAt N (ΩF (LaurentSeries K) (inclK K)) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  exact tateMuNAt_of_unit (LaurentSeries K) (inclK K) N hN (uζ K ζ hζ0)
    (orderOf_uζ K ζ hζ0 N (by omega) hζ) fun m hmN hcop => by
      obtain ⟨g, hg⟩ := hgal m hmN hcop
      exact ⟨sigmaK K g, continuous_sigmaK K g, sigmaK_inclK K g, sigmaK_uζ K g ζ hζ0 m hg⟩

end Laurent

/-! ### The cyclotomic field `ℚ(ζ_N)` -/

section Cyclotomic

variable (N : ℕ) [NeZero N]

abbrev KN := CyclotomicField N ℚ

instance : IsCyclotomicExtension {N} ℚ (KN N) := CyclotomicField.isCyclotomicExtension N ℚ

/-- The Galois element `ζ ↦ ζ^m` of `ℚ(ζ_N)`. -/
def galN (m : ℕ) (hcop : Nat.Coprime m N) : KN N ≃ₐ[ℚ] KN N :=
  (IsCyclotomicExtension.autEquivPow (KN N)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))).symm (ZMod.unitOfCoprime m hcop)

theorem galN_zeta (m : ℕ) (hcop : Nat.Coprime m N) (hmN : m < N) :
    galN N m hcop (IsCyclotomicExtension.zeta N ℚ (KN N)) =
      IsCyclotomicExtension.zeta N ℚ (KN N) ^ m := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (KN N)
  have h1 := hζ.autToPow_spec ℚ (galN N m hcop)
  have h2 : (IsCyclotomicExtension.autEquivPow (KN N)
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))) (galN N m hcop) =
        ZMod.unitOfCoprime m hcop :=
    MulEquiv.apply_symm_apply _ _
  rw [IsCyclotomicExtension.autEquivPow_apply] at h2
  have h3 : ((hζ.autToPow ℚ (galN N m hcop) : (ZMod N)ˣ) : ZMod N) = (m : ZMod N) := by
    rw [← ZMod.coe_unitOfCoprime m hcop, ← h2]; rfl
  rw [← h1, h3, ZMod.val_natCast, Nat.mod_eq_of_lt hmN]


end Cyclotomic

/-- **`TateMuN` (task t40-igusa) is proved.** -/
theorem _root_.ZInQ.RLeaf.tateMuN : TateMuN := by
  refine tateMuN_of_at fun N hN => ?_
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨Kbar, inferInstance, inferInstance, inferInstance, inferInstance, 0, addOrderOf_zero,
      fun R hR _ => ⟨AlgEquiv.refl, ?_⟩⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
    rw [zsmul_zero]; rfl
  · haveI : NeZero N := ⟨hN.ne'⟩
    exact ⟨ΩF (LaurentSeries (KN N)) (inclK (KN N)), inferInstance, inferInstance,
      inferInstance, _,
      tateMuNAt_of_root (KN N) N (by omega) _ (IsCyclotomicExtension.zeta_spec N ℚ (KN N))
        fun m hmN hcop => ⟨(galN N m hcop).toRingEquiv, galN_zeta N m hcop hmN⟩⟩

end ZInQ.RLeaf.TateCuspMuN

#print axioms ZInQ.RLeaf.tateMuN
