import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
import ZInQKernel.Contrib.OneProof.HeegnerPointRationalCd.Used
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero

/-!
# heegner-32: the points of the parametrization of `C_d` as twisted sums of points of `X₀(32)`

For `d ≡ 5 (mod 8)` squarefree, `g = gaussD d` (`g² = d`), `L` a period lattice of `C_d : y² = x³ − d²x` and
`τ ∈ ℍ`:

`weierPt C_d L (2 Φ_d(τ)) = S_{λg}(Z(τ)) + S_{λ̄g}(Z(τ))`,  `Z(τ) = Σ_{a mod d} (a/d) · (x(τ + a/d), y(τ + a/d))`,

where `(x, y)` is x0-32's eta-quotient parametrization `ZInQ.Contrib.TYZGenus.X0.phiC` of `X₀(32) = 32a1 : y² = x³ + 4x`,
`λ = (1 + i)/2`, and `S_μ(x, y) = (μ²x, μ³y)` maps `32a1` to `C_d` when `4μ⁴ = −d²`.
-/

noncomputable section

open UpperHalfPlane Complex WeierstrassCurve Filter Topology
open scoped WeierstrassCurve.Affine

namespace ZInQ.Heegner32

open ZInQ.GZWeil (eichlerCd gaussD scalePP mem_scalePP g₂_scalePP g₃_scalePP isPeriodLattice_cd_iff)
open ZInQ.GZTheta (jacobiChar)
open ZInQ.Contrib.TYZDecomp.CurveA (curveA)

/-! ## §1. Additivity of `weierPt` for short Weierstrass curves (from the uniformization theorem) -/

theorem fun_add_of_eq (L : PeriodPair) {W : WeierstrassCurve ℂ} (h : L.weierstrassCurve = W)
    (F : ℂ → W.toAffine.Point) (hF0 : ∀ z ∈ L.lattice, F z = 0)
    (hF1 : ∀ z ∉ L.lattice, ∃ hns, F z = .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) hns)
    (z w : ℂ) : F (z + w) = F z + F w := by
  subst h
  have hD := L.discriminant_ne_zero
  have hF : F = L.toPoint hD := by
    funext u
    by_cases hu : u ∈ L.lattice
    · rw [hF0 u hu, L.toPoint_of_mem hD hu]
    · obtain ⟨hns, e⟩ := hF1 u hu
      rw [e, L.toPoint_of_notMem hD hu]
  rw [hF]
  exact (L.isUniformization_toPoint hD).1 z w

theorem short_b₂ (A : ℚ) : ((shortCurve A)⁄ℂ).b₂ = 0 := by
  simp [WeierstrassCurve.b₂, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

theorem short_a₁ (A : ℚ) : ((shortCurve A)⁄ℂ).a₁ = 0 := by
  simp [shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

theorem short_a₃ (A : ℚ) : ((shortCurve A)⁄ℂ).a₃ = 0 := by
  simp [shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

/-- For a period lattice of `y² = x³ + Ax`, the curve of `L` is `E⁄ℂ`. -/
theorem weierstrassCurve_eq_short {A : ℚ} {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) : L.weierstrassCurve = (shortCurve A)⁄ℂ := by
  obtain ⟨h2, h3⟩ := hL
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.baseChange, WeierstrassCurve.map, shortCurve] at h2 h3
  push_cast at h2 h3
  ext <;> simp [PeriodPair.weierstrassCurve, shortCurve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, h2, h3] <;> ring

/-- **`weierPt E L` is additive** for `E : y² = x³ + Ax` (the uniformization theorem, vendored). -/
theorem weierPt_short_add {A : ℚ} [(shortCurve A).IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) (z w : ℂ) :
    ZInQ.GZHL3.weierPt (shortCurve A) L (z + w) =
      ZInQ.GZHL3.weierPt (shortCurve A) L z + ZInQ.GZHL3.weierPt (shortCurve A) L w := by
  refine fun_add_of_eq L (weierstrassCurve_eq_short hL) _ (fun u hu => ?_) (fun u hu => ?_) z w
  · exact ZInQ.GZHeegner.weierPt_eq_zero _ L hu
  · rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hu]
    have hns := ZInQ.GZHL3.weierPt_some (shortCurve A) hL hu
    simp only [short_b₂, short_a₁, short_a₃, zero_div, sub_zero, zero_mul] at hns ⊢
    exact ⟨hns, by first | rfl | trivial⟩

/-- `weierPt E L` as an additive map. -/
def weierHom {A : ℚ} [(shortCurve A).IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) : ℂ →+ ((shortCurve A)⁄ℂ).toAffine.Point :=
  AddMonoidHom.mk' (ZInQ.GZHL3.weierPt (shortCurve A) L) (weierPt_short_add hL)

theorem weierHom_apply {A : ℚ} [(shortCurve A).IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve A) L) (z : ℂ) :
    weierHom hL z = ZInQ.GZHL3.weierPt (shortCurve A) L z := rfl

/-! ## §2. Scaling of lattices and the maps `S_μ` -/

theorem isScale_scalePP (L : PeriodPair) {μ : ℂ} (hμ : μ ≠ 0) : T5Glue.IsScale (scalePP L μ hμ) L μ := by
  refine ⟨hμ, ?_⟩
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
  rw [mem_scalePP]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

instance (d : ℕ) [NeZero d] : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic :=
  ZInQ.GZDecomp.shortCurve_cd_isElliptic (NeZero.ne d)

instance : (shortCurve (4 : ℚ)).IsElliptic := shortCurve_isElliptic (by norm_num)

/-- `S_μ(x, y) = (μ²x, μ³y)` from `32a1 : y² = x³ + 4x` to `C_d : y² = x³ − d²x`, for `4μ⁴ = −d²`. -/
def sMap (d : ℕ) [NeZero d] (μ : ℂ) (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) :
    ZInQ.Contrib.TYZGenus.X0.PtAC → ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).toAffine.Point
  | .zero => 0
  | .some x y h => .some (μ ^ 2 * x) (μ ^ 3 * y) (by
      rw [← Affine.equation_iff_nonsingular]
      have he := (Affine.equation_iff_nonsingular.mpr h)
      rw [Affine.equation_iff] at he ⊢
      simp only [ZInQ.Contrib.TYZGenus.X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        map_zero, zero_mul, add_zero, map_neg, map_pow, map_natCast, map_ofNat] at he ⊢
      push_cast at he ⊢
      linear_combination μ ^ 6 * he + μ ^ 2 * x * hμ)

instance : curveA.IsElliptic := by unfold curveA; exact shortCurve_isElliptic (by norm_num)

theorem sMap_zero (d : ℕ) [NeZero d] (μ : ℂ) (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) : sMap d μ hμ 0 = 0 := rfl

theorem isPeriodLattice_scale {d : ℕ} [NeZero d] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {μ : ℂ} (hμ0 : μ ≠ 0)
    (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) :
    ZInQ.GZHL3.IsPeriodLattice curveA (scalePP L μ hμ0) := by
  obtain ⟨h2, h3⟩ := (isPeriodLattice_cd_iff d L).1 hL
  have hd2 : (d : ℂ) ^ 2 = -4 * μ ^ 4 := by linear_combination hμ
  have hμ4 : μ ^ 4 ≠ 0 := pow_ne_zero 4 hμ0
  refine ⟨?_, ?_⟩
  · rw [g₂_scalePP, h2, hd2]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveA, shortCurve,
      WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]
    push_cast
    field_simp
    ring
  · rw [g₃_scalePP, h3]
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      curveA, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]
    push_cast
    ring

/-- **Scaling.** `weierPt C_d L z = S_μ(weierPt 32a1 (μL) (μz))`. -/
theorem weierPt_scale {d : ℕ} [NeZero d] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {μ : ℂ} (hμ0 : μ ≠ 0)
    (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) (z : ℂ) :
    ZInQ.GZHL3.weierPt (shortCurve (-(d : ℚ) ^ 2)) L z =
      sMap d μ hμ (ZInQ.GZHL3.weierPt curveA (scalePP L μ hμ0) (μ * z)) := by
  have hs := isScale_scalePP L hμ0
  have hL' := isPeriodLattice_scale hL hμ0 hμ
  by_cases hz : z ∈ L.lattice
  · have hz' : μ * z ∈ (scalePP L μ hμ0).lattice := hs.mul_mem hz
    rw [ZInQ.GZHeegner.weierPt_eq_zero _ L hz, ZInQ.GZHeegner.weierPt_eq_zero _ _ hz', sMap_zero]
  · have hz' : μ * z ∉ (scalePP L μ hμ0).lattice := by
      rw [hs.mem_iff, inv_mul_cancel_left₀ hμ0]; exact hz
    rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hz, ZInQ.GZHeegner.weierPt_eq_some _ hL' hz']
    simp only [sMap, Affine.Point.some.injEq]
    have hw := hs.weierstrassP z
    have hw' := hs.derivWeierstrassP z
    have e1 : ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).b₂ = 0 := short_b₂ _
    have e2 : ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).a₁ = 0 := short_a₁ _
    have e3 : ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).a₃ = 0 := short_a₃ _
    have f1 : (curveA⁄ℂ).b₂ = 0 := short_b₂ 4
    have f2 : (curveA⁄ℂ).a₁ = 0 := short_a₁ 4
    have f3 : (curveA⁄ℂ).a₃ = 0 := short_a₃ 4
    rw [e1, e2, e3, f1, f2, f3, hw, hw']
    constructor <;> field_simp <;> ring

/-! ## §3. `x0-32`'s parametrization is `℘` of a lattice of `32a1` at `Φ₁ + c₀` -/

/-- For a period lattice `L` of `32a1`, `(x(σ), y(σ)) = weierPt 32a1 L (Φ₁(σ) + c₀)` on `ℍ`. -/
theorem exists_c0 {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice curveA L) :
    ∃ c₀ : ℂ, ∀ σ : ℍ, ZInQ.GZHL3.weierPt curveA L (eichlerCd 1 σ + c₀) = ZInQ.Contrib.TYZGenus.X0.phiC σ := by
  have hg2 : L.g₂ = -16 := by
    rw [hL.1]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveA, shortCurve,
      WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]
    push_cast; ring
  have hg3 : L.g₃ = 0 := by
    rw [hL.2]
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      curveA, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]
    push_cast; ring
  set τ0 : ℍ := UpperHalfPlane.I
  obtain ⟨z1, hz1, hx1⟩ := ZInQ.GZWeil.weierstrassP_surjective L (ZInQ.Contrib.TYZGenus.X0.xC τ0)
  have hrel := ZInQ.GZWeil.relation_A L hg2 hg3 hz1
  have heqτ := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ0
  obtain ⟨z0, hz0, hx, hy⟩ : ∃ z0, z0 ∉ L.lattice ∧ L.weierstrassP z0 = ZInQ.Contrib.TYZGenus.X0.xC τ0 ∧
      L.derivWeierstrassP z0 = 2 * ZInQ.Contrib.TYZGenus.X0.yC τ0 := by
    have hsq : (L.derivWeierstrassP z1 - 2 * ZInQ.Contrib.TYZGenus.X0.yC τ0) * (L.derivWeierstrassP z1 + 2 * ZInQ.Contrib.TYZGenus.X0.yC τ0) = 0 := by
      rw [hx1] at hrel
      linear_combination hrel - 4 * heqτ
    rcases mul_eq_zero.mp hsq with h | h
    · exact ⟨z1, hz1, hx1, by linear_combination h⟩
    · refine ⟨-z1, fun h' => hz1 (by simpa using neg_mem h'), by rw [L.weierstrassP_neg, hx1], ?_⟩
      rw [L.derivWeierstrassP_neg]; linear_combination -h
  set c0 := z0 - eichlerCd 1 τ0 with hc0
  refine ⟨c0, fun σ => ?_⟩
  have hD := ZInQ.GZWeil.etaModelDifferential
  have hG := fun {s : ℂ} (hs : 0 < s.im) => ZInQ.GZWeil.global_eq L hg2 hg3 hD τ0 hz0 hx hy hs
  obtain ⟨hnot, hxeq⟩ := hG σ.im_pos
  -- `℘'(Φ₁(σ) + c₀) = 2 y(σ)`, by differentiating `℘(Φ₁ + c₀) = x` near `σ`
  have hcomp : HasDerivAt (L.weierstrassP ∘ fun s => eichlerCd 1 s + c0)
      (L.derivWeierstrassP (eichlerCd 1 σ + c0) * (2 * Real.pi * Complex.I * ZInQ.Contrib.TYZGenus.X0.fC σ)) σ :=
    (ZInQ.GZWeil.hasDerivAt_wp L hnot).comp (σ : ℂ)
      ((ZInQ.GZWeil.hasDerivAt_eichlerCd_one σ.im_pos).add_const c0)
  have hev : ZInQ.Contrib.TYZGenus.X0.xC =ᶠ[𝓝 (σ : ℂ)] (L.weierstrassP ∘ fun s => eichlerCd 1 s + c0) := by
    filter_upwards [ZInQ.GZWeil.U_open.mem_nhds σ.im_pos] with s hs
    exact (hG hs).2.symm
  have hxd := hcomp.congr_of_eventuallyEq hev
  have huniq := hxd.unique (hD σ)
  have hf : (2 * Real.pi * Complex.I * ZInQ.Contrib.TYZGenus.X0.fC σ : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) (ZInQ.Contrib.TYZGenus.X0.fC_ne_zero σ)
    exact_mod_cast Real.pi_ne_zero
  have hyeq : L.derivWeierstrassP (eichlerCd 1 σ + c0) = 2 * ZInQ.Contrib.TYZGenus.X0.yC σ := by
    apply mul_right_cancel₀ hf
    linear_combination huniq
  rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hnot]
  have hns : ZInQ.Contrib.TYZGenus.X0.curveAC.toAffine.Nonsingular (ZInQ.Contrib.TYZGenus.X0.xC σ) (ZInQ.Contrib.TYZGenus.X0.yC σ) := by
    have h := ZInQ.GZHL3.weierPt_some curveA hL hnot
    have e1 : (curveA⁄ℂ).b₂ = 0 := short_b₂ 4
    have e2 : (curveA⁄ℂ).a₁ = 0 := short_a₁ 4
    have e3 : (curveA⁄ℂ).a₃ = 0 := short_a₃ 4
    rw [e1, e2, e3, hxeq, hyeq] at h
    convert h using 1 <;> ring
  unfold ZInQ.Contrib.TYZGenus.X0.phiC
  rw [dif_pos hns]
  simp only [Affine.Point.some.injEq]
  have e1 : (curveA⁄ℂ).b₂ = 0 := short_b₂ 4
  have e2 : (curveA⁄ℂ).a₁ = 0 := short_a₁ 4
  have e3 : (curveA⁄ℂ).a₃ = 0 := short_a₃ 4
  rw [e1, e2, e3, hxeq, hyeq]
  constructor <;> ring

/-! ## §4. The twisted sum `Z(τ)` and the main identity -/

/-- `τ + a/d ∈ ℍ`. -/
def shiftH (d : ℕ) [NeZero d] (τ : ℍ) (a : ZMod d) : ℍ :=
  ⟨(τ : ℂ) + (a.val : ℂ) / d, by
    have : ((a.val : ℂ) / d).im = 0 := by
      rw [show ((a.val : ℂ) / d) = (((a.val : ℝ) / d : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    rw [Complex.add_im, this, add_zero]; exact τ.im_pos⟩

theorem coe_shiftH (d : ℕ) [NeZero d] (τ : ℍ) (a : ZMod d) :
    ((shiftH d τ a : ℍ) : ℂ) = (τ : ℂ) + (a.val : ℂ) / d := rfl

/-- **The twisted sum** `Z(τ) = Σ_{a mod d} (a/d) · (x(τ + a/d), y(τ + a/d)) ∈ 32a1(ℂ)`. -/
def zTw (d : ℕ) [NeZero d] (τ : ℍ) : ZInQ.Contrib.TYZGenus.X0.PtAC :=
  ∑ a : ZMod d, (jacobiSym (a.val : ℤ) d) • ZInQ.Contrib.TYZGenus.X0.phiC (shiftH d τ a)

theorem jacobiChar_apply (d : ℕ) [NeZero d] (a : ZMod d) :
    jacobiChar d a = ((jacobiSym (a.val : ℤ) d : ℤ) : ℂ) := rfl

theorem jacobiChar_ne_one {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1) :
    jacobiChar d ≠ 1 := by
  intro h
  have hp := ZInQ.GZWeil.jacobiChar_isPrimitive (d := d) (Nat.odd_iff.mpr (by omega)) hsq
  rw [h] at hp
  have := hp
  unfold DirichletCharacter.IsPrimitive at this
  rw [DirichletCharacter.conductor_one] at this
  exact hd1 this.symm

theorem sum_jacobiChar {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1) :
    ∑ a : ZMod d, jacobiChar d a = 0 :=
  MulChar.sum_eq_zero_of_ne_one (jacobiChar_ne_one hd4 hsq hd1)

/-- `Σ_a (a/d) Φ₁(τ + a/d) = g Φ_d(τ)` (gz-weil's twist formula and Gauss sum). -/
theorem sum_char_eichler {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (τ : ℍ) :
    ∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) =
      gaussD d * eichlerCd d τ := by
  have hg := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  have hT := ZInQ.GZWeil.twist_formula d τ.im_pos
  simp_rw [ZInQ.GZWeil.dft_jacobiChar hd4 hsq] at hT
  have hg2 := ZInQ.GZWeil.gaussD_sq hd4 hsq
  apply mul_left_cancel₀ hg
  rw [Finset.mul_sum]
  have : ∑ a : ZMod d, gaussD d * (jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ)) =
      ∑ a : ZMod d, jacobiChar d a * gaussD d * eichlerCd 1 ((τ : ℂ) + (a.val : ℂ) / d) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_shiftH]; ring
  rw [this, ← hT, ← hg2]; ring

/-- `weierPt 32a1 L' (Σ_a (a/d) Φ₁(τ + a/d)) = Z(τ)` for a period lattice `L'` of `32a1`. -/
theorem weierPt_sum_eq_zTw {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1)
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice curveA L) (τ : ℍ) :
    ZInQ.GZHL3.weierPt curveA L
      (∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ)) = zTw d τ := by
  obtain ⟨c0, hc0⟩ := exists_c0 hL
  have hsum : ∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) =
      ∑ a : ZMod d, (jacobiSym (a.val : ℤ) d) • (eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) + c0) := by
    have h0 : ∑ a : ZMod d, jacobiChar d a * c0 = 0 := by
      rw [← Finset.sum_mul, sum_jacobiChar hd4 hsq hd1, zero_mul]
    rw [← add_zero (∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ)), ← h0,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [zsmul_eq_mul, ← jacobiChar_apply]; ring
  rw [hsum]
  have hL4 : ZInQ.GZHL3.IsPeriodLattice (shortCurve 4) L := hL
  show weierHom hL4 _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_zsmul, weierHom_apply]
  exact congrArg (fun P => jacobiSym (a.val : ℤ) d • P) (hc0 (shiftH d τ a))

/-- `λ = (1 + i)/2`, `λ̄ = (1 − i)/2`. -/
def lam : ℂ := (1 + Complex.I) / 2
def lamb : ℂ := (1 - Complex.I) / 2

theorem lam_pow_four : lam ^ 4 = -1 / 4 := by
  unfold lam
  ring_nf; rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; simp,
    Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring

theorem lamb_pow_four : lamb ^ 4 = -1 / 4 := by
  unfold lamb
  ring_nf; rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; simp,
    Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring

theorem lam_mul_lamb : lam * lamb = 1 / 2 := by
  unfold lam lamb
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-1 / 4 : ℂ) * hI

theorem lam_ne_zero : lam ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [lam] at this

theorem lamb_ne_zero : lamb ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [lamb] at this

theorem mu_pow {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) {l : ℂ}
    (hl : l ^ 4 = -1 / 4) : 4 * (l * gaussD d) ^ 4 = -(d : ℂ) ^ 2 := by
  have hg2 := ZInQ.GZWeil.gaussD_sq hd4 hsq
  rw [mul_pow, hl, show gaussD d ^ 4 = (gaussD d ^ 2) ^ 2 by ring, hg2]; ring

/-- **The parametrization of `C_d` at `2Φ_d(τ)` as a twisted sum on `X₀(32)`.** -/
theorem weierPt_two_eichlerCd {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (hd1 : d ≠ 1)
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) (τ : ℍ) :
    ZInQ.GZHL3.weierPt (shortCurve (-(d : ℚ) ^ 2)) L (2 * eichlerCd d τ) =
      sMap d (lam * gaussD d) (mu_pow hd4 hsq lam_pow_four) (zTw d τ) +
        sMap d (lamb * gaussD d) (mu_pow hd4 hsq lamb_pow_four) (zTw d τ) := by
  have hg := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  set w := ∑ a : ZMod d, jacobiChar d a * eichlerCd 1 ((shiftH d τ a : ℍ) : ℂ) with hw
  have hwg : w = gaussD d * eichlerCd d τ := sum_char_eichler hd4 hsq τ
  have h1 : lam * gaussD d ≠ 0 := mul_ne_zero lam_ne_zero hg
  have h2 : lamb * gaussD d ≠ 0 := mul_ne_zero lamb_ne_zero hg
  have hsplit : 2 * eichlerCd d τ = 2 * lamb / gaussD d * w + 2 * lam / gaussD d * w := by
    rw [hwg, show lam = 1 - lamb by unfold lam lamb; ring]
    field_simp
    ring
  rw [hsplit, weierPt_short_add hL,
    weierPt_scale hL h1 (mu_pow hd4 hsq lam_pow_four) (2 * lamb / gaussD d * w),
    weierPt_scale hL h2 (mu_pow hd4 hsq lamb_pow_four) (2 * lam / gaussD d * w)]
  have e1 : lam * gaussD d * (2 * lamb / gaussD d * w) = w := by
    field_simp; linear_combination (2 * w) * lam_mul_lamb
  have e2 : lamb * gaussD d * (2 * lam / gaussD d * w) = w := by
    field_simp; linear_combination (2 * w) * lam_mul_lamb
  rw [e1, e2, weierPt_sum_eq_zTw hd4 hsq hd1 (isPeriodLattice_scale hL h1 (mu_pow hd4 hsq lam_pow_four)),
    weierPt_sum_eq_zTw hd4 hsq hd1 (isPeriodLattice_scale hL h2 (mu_pow hd4 hsq lamb_pow_four))]

/-! ## §5. Galois conjugation of the maps `S_μ` -/

theorem sMap_congr {d : ℕ} [NeZero d] {μ μ' : ℂ} (h : μ = μ') (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2)
    (hμ' : 4 * μ' ^ 4 = -(d : ℂ) ^ 2) : sMap d μ hμ = sMap d μ' hμ' := by
  subst h; rfl

theorem sigma_hmu {d : ℕ} [NeZero d] (σ : ℂ ≃+* ℂ) {μ : ℂ} (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2) :
    4 * (σ μ) ^ 4 = -(d : ℂ) ^ 2 := by
  have h := congrArg σ hμ
  simpa [map_mul, map_pow, map_neg, map_natCast, map_ofNat] using h

/-- `σ ∘ S_μ = S_{σμ} ∘ σ`. -/
theorem map_sMap {d : ℕ} [NeZero d] (σ : ℂ ≃+* ℂ) {μ : ℂ} (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2)
    (P : ZInQ.Contrib.TYZGenus.X0.PtAC) :
    Affine.Point.map (ZInQ.GZHeegner.sigA σ) (sMap d μ hμ P) =
      sMap d (σ μ) (sigma_hmu σ hμ) (Affine.Point.map (ZInQ.GZHeegner.sigA σ) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [sMap, Affine.Point.map_some, Affine.Point.some.injEq]
    simp [ZInQ.GZHeegner.sigA, map_mul, map_pow]

/-- `S_{−μ} = S_μ ∘ (−1)`. -/
theorem sMap_neg {d : ℕ} [NeZero d] {μ : ℂ} (hμ : 4 * μ ^ 4 = -(d : ℂ) ^ 2)
    (hμ' : 4 * (-μ) ^ 4 = -(d : ℂ) ^ 2) (P : ZInQ.Contrib.TYZGenus.X0.PtAC) :
    sMap d (-μ) hμ' P = sMap d μ hμ (-P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]
    simp only [sMap, Affine.Point.some.injEq]
    simp only [Affine.negY, curveA, shortCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      map_zero, zero_mul, sub_zero]
    constructor <;> ring

/-- `Ψ(P) = S_{λg}(P) + S_{λ̄g}(P)`. -/
def psiMap (d : ℕ) [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (P : ZInQ.Contrib.TYZGenus.X0.PtAC) :
    ((shortCurve (-(d : ℚ) ^ 2))⁄ℂ).toAffine.Point :=
  sMap d (lam * gaussD d) (mu_pow hd4 hsq lam_pow_four) P +
    sMap d (lamb * gaussD d) (mu_pow hd4 hsq lamb_pow_four) P

theorem sigma_I (σ : ℂ ≃+* ℂ) : σ Complex.I = Complex.I ∨ σ Complex.I = -Complex.I := by
  have h : (σ Complex.I - Complex.I) * (σ Complex.I + Complex.I) = 0 := by
    have : σ Complex.I ^ 2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, map_one]
    linear_combination this - Complex.I_sq
  rcases mul_eq_zero.mp h with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem sigma_gauss {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (σ : ℂ ≃+* ℂ) :
    σ (gaussD d) = gaussD d ∨ σ (gaussD d) = -gaussD d := by
  have hg2 := ZInQ.GZWeil.gaussD_sq hd4 hsq
  have h : (σ (gaussD d) - gaussD d) * (σ (gaussD d) + gaussD d) = 0 := by
    have : σ (gaussD d) ^ 2 = gaussD d ^ 2 := by rw [← map_pow, hg2, map_natCast]
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · left; linear_combination h
  · right; linear_combination h

theorem sigma_lam (σ : ℂ ≃+* ℂ) (h : σ Complex.I = Complex.I) : σ lam = lam ∧ σ lamb = lamb := by
  unfold lam lamb
  constructor <;> simp [map_div₀, map_add, map_sub, h, map_ofNat]

theorem sigma_lam' (σ : ℂ ≃+* ℂ) (h : σ Complex.I = -Complex.I) : σ lam = lamb ∧ σ lamb = lam := by
  unfold lam lamb
  constructor <;> simp [map_div₀, map_add, map_sub, h, sub_eq_add_neg, map_ofNat]

/-- **`σ ∘ Ψ = Ψ ∘ (±σ)`**, the sign being `σ(g)/g`. -/
theorem map_psiMap {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (σ : ℂ ≃+* ℂ)
    (P : ZInQ.Contrib.TYZGenus.X0.PtAC) :
    Affine.Point.map (ZInQ.GZHeegner.sigA σ) (psiMap d hd4 hsq P) =
      psiMap d hd4 hsq (if σ (gaussD d) = gaussD d then
        Affine.Point.map (ZInQ.GZHeegner.sigA σ) P else -Affine.Point.map (ZInQ.GZHeegner.sigA σ) P) := by
  unfold psiMap
  rw [map_add, map_sMap, map_sMap]
  set Pσ := Affine.Point.map (ZInQ.GZHeegner.sigA σ) P
  have hg0 := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  have ha := mu_pow hd4 hsq lam_pow_four
  have hb := mu_pow hd4 hsq lamb_pow_four
  have hn1 : 4 * (-(lam * gaussD d)) ^ 4 = -(d : ℂ) ^ 2 := by
    rw [neg_pow, show ((-1 : ℂ)) ^ 4 = 1 by norm_num, one_mul]; exact ha
  have hn2 : 4 * (-(lamb * gaussD d)) ^ 4 = -(d : ℂ) ^ 2 := by
    rw [neg_pow, show ((-1 : ℂ)) ^ 4 = 1 by norm_num, one_mul]; exact hb
  rcases sigma_gauss hd4 hsq σ with hg | hg
  · rw [if_pos hg]
    rcases sigma_I σ with hI | hI
    · obtain ⟨h1, h2⟩ := sigma_lam σ hI
      rw [sMap_congr (μ := σ (lam * gaussD d)) (μ' := lam * gaussD d) (by rw [map_mul, h1, hg])
          (sigma_hmu σ ha) ha,
        sMap_congr (μ := σ (lamb * gaussD d)) (μ' := lamb * gaussD d) (by rw [map_mul, h2, hg])
          (sigma_hmu σ hb) hb]
    · obtain ⟨h1, h2⟩ := sigma_lam' σ hI
      rw [sMap_congr (μ := σ (lam * gaussD d)) (μ' := lamb * gaussD d) (by rw [map_mul, h1, hg])
          (sigma_hmu σ ha) hb,
        sMap_congr (μ := σ (lamb * gaussD d)) (μ' := lam * gaussD d) (by rw [map_mul, h2, hg])
          (sigma_hmu σ hb) ha, add_comm]
  · have hne : σ (gaussD d) ≠ gaussD d := by
      rw [hg]; intro h; exact hg0 (by linear_combination -h / 2)
    rw [if_neg hne]
    rcases sigma_I σ with hI | hI
    · obtain ⟨h1, h2⟩ := sigma_lam σ hI
      rw [sMap_congr (μ := σ (lam * gaussD d)) (μ' := -(lam * gaussD d)) (by rw [map_mul, h1, hg]; ring)
          (sigma_hmu σ ha) hn1,
        sMap_congr (μ := σ (lamb * gaussD d)) (μ' := -(lamb * gaussD d)) (by rw [map_mul, h2, hg]; ring)
          (sigma_hmu σ hb) hn2, sMap_neg ha hn1, sMap_neg hb hn2]
    · obtain ⟨h1, h2⟩ := sigma_lam' σ hI
      rw [sMap_congr (μ := σ (lam * gaussD d)) (μ' := -(lamb * gaussD d)) (by rw [map_mul, h1, hg]; ring)
          (sigma_hmu σ ha) hn2,
        sMap_congr (μ := σ (lamb * gaussD d)) (μ' := -(lam * gaussD d)) (by rw [map_mul, h2, hg]; ring)
          (sigma_hmu σ hb) hn1, sMap_neg ha hn1, sMap_neg hb hn2, add_comm]

/-! ## §6. The Galois statement on `X₀(32)` and the even-`c` Heegner point -/

open ZInQ.GZDecomp (IsOddImagFundDisc HeegnerHyp)
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.Shimura
  ZInQ.Contrib.TYZDecomp.CurveA

/-- **(GLUE: Shimura reciprocity on `X₀(32)` at conductor-`d` Heegner points, twisted by `(·/d)`.)**
For `d ≡ 5 (mod 8)` squarefree, `K = ℚ(√−m)` (`m ≡ 3 (mod 4)` squarefree, `m > 4`) satisfying the Heegner
hypothesis for `32 d²`, a complete set `S` of Heegner representatives of level `32 d²`, discriminant `−m` and
residue `β`, and `σ ∈ Aut(ℂ/K)`: there is a permutation `π` of `S` with
`σ(Z(τ_Q)) = ε_σ · Z(τ_{π Q})`, `ε_σ = σ(g)/g ∈ {±1}`, `g = gaussD d` (`g² = d`), where
`Z(τ) = Σ_{a mod d} (a/d) · (x(τ + a/d), y(τ + a/d))` (`zTw`, x0-32's eta-quotient parametrization `ZInQ.Contrib.TYZGenus.X0.phiC`).

Why it holds (not proved here). For `Q = [A, B, C] ∈ S` and `(a, d) = 1`, `τ_Q + a/d` is the Heegner point of
the form `[Ad, (B − 2Aa/d)d, ·]` of level `32` and discriminant `−m d²` (conductor `d`), and the
`φ(d)` such points are the conductor-`d` sublattices of `⟨1/d, τ_Q⟩` other than `⟨1, τ_Q⟩`, `⟨1/d, dτ_Q⟩`.
By `X0ModuliUsed`'s eta route (`shimuraReciprocityPic` from `hCM` and `ThetaWeierstrass8`, both proved),
`σ` moves `(x, y)(τ_Q + a/d)` to `(x, y)` at the image lattice pair under `Art⁻¹`; the image of the family of
`Q` is the family of the Dirichlet composite `π Q`, with `a ↦ a'`, `(a'/d) = χ_gen(σ)(a/d)`, where `χ_gen` is
the genus character of `K(√d)/K` (`d ≡ 1 mod 4`, every `p ∣ d` split in `K`); and `σ(g)/g = χ_gen(σ)`.
These three steps (conductor-`d` composition, the genus character, Chebotarev in the ring class field of
conductor `d`) are elementary algebraic number theory; no canonical model of `X₀(32 d²)` is used. -/
def TwistTransportCd : Prop :=
  ∀ (d : ℕ) [NeZero d], d % 8 = 5 → Squarefree d →
  ∀ (m : ℕ) [NeZero m], Squarefree m → m % 4 = 3 → 4 < m → HeegnerHyp (32 * d ^ 2) (-(m : ℤ)) →
  ∀ (β : ℤ) (S : Finset (HeegnerForm (32 * d ^ 2) (-(m : ℤ)))),
    ZInQ.GZHL3.IsHeegnerReps (32 * d ^ 2) (-(m : ℤ)) β S →
  ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) →
  ∃ π : HeegnerForm (32 * d ^ 2) (-(m : ℤ)) → HeegnerForm (32 * d ^ 2) (-(m : ℤ)),
    Set.MapsTo π S S ∧ Set.InjOn π S ∧
    ∀ Q ∈ S, Affine.Point.map (ZInQ.GZHeegner.sigA σ) (zTw d Q.tauH) =
      (if σ (gaussD d) = gaussD d then zTw d (π Q).tauH else -zTw d (π Q).tauH)

/-- **`HeegnerPointRationalAt` restricted to even `c`** (`c ∈ 2ℤ`). -/
def HeegnerPointRationalAtEven (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : HeckeRing.GL2.Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), ZInQ.GZHL3.IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℚ), ZInQ.GZHL3.IsPeriodLattice E L → c ≠ 0 → (∃ k : ℤ, c = 2 * k) →
      ZInQ.GZHL3.PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
      ∃ y : (E⁄K).toAffine.Point, Affine.Point.map ι y = ZInQ.GZHL3.heegnerC E L f c S

/-- **The corrected (even-`c`) form of `GZHL3.HeegnerPointRationalCd`.** -/
def HeegnerPointRationalCdEven : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → HeegnerPointRationalAtEven (shortCurve (-(d : ℚ) ^ 2))

theorem heegnerPointRationalCdEven_of (h : ZInQ.GZHL3.HeegnerPointRationalCd) :
    HeegnerPointRationalCdEven := by
  intro d hd hsq N _ f hχ hf D β hD hD4 hH hβ S hS L c hL hc _ hP K _ _ _ hK δ hδ ι hι
  exact h d hd hsq N f hχ hf D β hD hD4 hH hβ S hS L c hL hc hP K hK δ hδ ι hι

/-- **The even-`c` Heegner point of `C_d` from the Galois statement on `X₀(32)`.** -/
theorem heegnerPointRationalCdEven_of_twist (hT : TwistTransportCd) : HeegnerPointRationalCdEven := by
  intro d hd hsq N _ f hχ hcoeff D β hDf hD4 hHH hβ S hS L c hL hc hc2 hPer K _ _ _ hK2 δ hδ ι hι
  obtain ⟨k, hk⟩ := hc2
  have : NeZero d := ⟨by omega⟩
  have hd4 : d % 4 = 1 := by omega
  have hd1 : d ≠ 1 := by omega
  have hN := ZInQ.GZStatements.level_eq_of_coeff_cd hd4 hsq f hχ hcoeff
  subst hN
  obtain ⟨hD0, hD1, hDsq⟩ := hDf
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, D = -(m : ℤ) := ⟨D.natAbs, by omega⟩
  have : NeZero m := ⟨by omega⟩
  have hmsq : Squarefree m := Int.squarefree_natCast.1 (ZInQ.GZHeegner.squarefree_neg_iff.1 hDsq)
  have hm3 : m % 4 = 3 := by omega
  have hm4 : 4 < m := by omega
  have hHC : ZInQ.GZHL3.heegnerC (shortCurve (-(d : ℚ) ^ 2)) L f c S =
      ∑ Q ∈ S, k • psiMap d hd4 hsq (zTw d Q.tauH) := by
    unfold ZInQ.GZHL3.heegnerC
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [ZInQ.GZWeil.eichler_eq_eichlerCd hd4 hsq f hcoeff, hk]
    have e : ((2 * k : ℤ) : ℚ) = (2 * (k : ℚ)) := by push_cast; ring
    have e2 : (((2 * (k : ℚ)) : ℚ) : ℂ) * eichlerCd d (Q.tauH : ℂ) = k • (2 * eichlerCd d (Q.tauH : ℂ)) := by
      rw [zsmul_eq_mul]; push_cast; ring
    rw [show ((2 * (k : ℚ) : ℚ) : ℂ) = (((2 * (k : ℚ)) : ℚ) : ℂ) from rfl, e2, ← weierHom_apply hL,
      map_zsmul, weierHom_apply, weierPt_two_eichlerCd hd4 hsq hd1 hL]
    rfl
  have hfix : ∀ σ : ℂ ≃+* ℂ, (∀ q : QNeg m, σ (kappa m q) = kappa m q) →
      Affine.Point.map (ZInQ.GZHeegner.sigA σ) (ZInQ.GZHL3.heegnerC (shortCurve (-(d : ℚ) ^ 2)) L f c S) =
        ZInQ.GZHL3.heegnerC (shortCurve (-(d : ℚ) ^ 2)) L f c S := by
    intro σ hσ
    obtain ⟨π, hπS, hπinj, hπZ⟩ := hT d hd hsq m hmsq hm3 hm4 hHH β S hS σ hσ
    rw [hHC, map_sum]
    have key : ∀ Q ∈ S, Affine.Point.map (ZInQ.GZHeegner.sigA σ) (k • psiMap d hd4 hsq (zTw d Q.tauH)) =
        k • psiMap d hd4 hsq (zTw d (π Q).tauH) := by
      intro Q hQ
      rw [map_zsmul, map_psiMap, hπZ Q hQ]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl key]
    refine Finset.sum_nbij π hπS hπinj ?_ (fun _ _ => rfl)
    intro R hR
    obtain ⟨Q, hQ, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun Q _ => π Q) (fun Q hQ => hπS hQ)
      (fun a₁ a₂ ha₁ ha₂ h => hπinj ha₁ ha₂ h) le_rfl R hR
    exact ⟨Q, hQ, h.symm⟩
  exact exists_point_of_fixed _ _ hfix K δ hδ ι hι

/-! ## §7. The even form suffices for the chain -/

/-- From any `c` with `c Λ_f ⊆ L`, the even integer `2·num(c)` has the same property. -/
theorem periodsIn_two_num {N : ℕ} [NeZero N] {f : HeckeRing.GL2.Newform N 2} {c : ℚ} {L : PeriodPair}
    (h : ZInQ.GZHL3.PeriodsIn f c L) : ZInQ.GZHL3.PeriodsIn f ((2 * c.num : ℤ) : ℚ) L := by
  intro γ hγ τ
  have h1 := h γ hγ τ
  have e : (((2 * c.num : ℤ) : ℚ) : ℂ) = ((2 * c.den : ℕ) : ℂ) * (c : ℂ) := by
    have : ((2 * c.num : ℤ) : ℚ) = (2 * c.den : ℕ) * c := by
      push_cast; rw [mul_assoc, Rat.den_mul_eq_num]
    rw [this]; push_cast; ring
  rw [e, mul_assoc]
  have := Submodule.smul_mem L.lattice (((2 * c.den : ℕ) : ℤ)) h1
  rwa [zsmul_eq_mul, Int.cast_natCast] at this

section Chain

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp ZInQ.GZHL3
open scoped WeierstrassCurve.Affine Modular MatrixGroups

/-- gz-weil's `heegner_at_of_lattice` with `HeegnerPointRationalAt` replaced by its even-`c` form: the
constant `c` of the parametrization is replaced by `2·num(c)` (`periodsIn_two_num`). -/
theorem heegner_at_even (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hLat : ∃ L : PeriodPair, IsPeriodLattice E L)
    (hES : EichlerShimuraParamAt E) (hHP : HeegnerPointRationalAtEven E)
    (hGZ : GrossZagierFormulaAt E) (hGC : GrossConjugationAt E) :
    ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K], Module.finrank ℚ K = 2 →
      (∃ δ : K, δ ^ 2 = algebraMap ℚ K D) →
      ∃ y : (E⁄K).Point, ¬IsOfFinAddOrder y ∧
        ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y) := by
  intro N _ f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1 K _ _ instAlg hK2 ⟨δ, hδ⟩
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain rfl : instAlg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have : FiniteDimensional ℚ K := Module.finite_of_finrank_eq_succ hK2
  have : NumberField K := ⟨⟩
  have hδ' : δ ^ 2 = (D : K) := by rw [hδ]; simp
  obtain ⟨β, hβ⟩ := ZInQ.GZStatements.exists_sq_mod_four_mul_of_heegnerHyp (NeZero.ne N) hDisc hHeeg
  obtain ⟨S, hS⟩ := heegnerRepsExist N D β hDisc hβ
  obtain ⟨L, hL⟩ := hLat
  obtain ⟨c₁, hc₁, hcL₁⟩ := hES N f hχ hf L hL
  set c : ℚ := ((2 * c₁.num : ℤ) : ℚ) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]; exact_mod_cast mul_ne_zero two_ne_zero (Rat.num_ne_zero.mpr hc₁)
  have hcL : PeriodsIn f c L := periodsIn_two_num hcL₁
  have hc2 : ∃ k : ℤ, c = 2 * k := ⟨c₁.num, by rw [hcdef]; push_cast; ring⟩
  obtain ⟨ι, hι⟩ := exists_embedding hDisc.1 δ hδ'
  obtain ⟨y, hy⟩ := hHP N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hc2 hcL K hK2 δ hδ' ι hι
  refine ⟨y, ?_, ?_⟩
  · obtain ⟨κ, -, hκ⟩ := hGZ N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι
      hι y hy F G hF hG
    intro htors
    rw [WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_of_isOfFinAddOrder htors,
      Complex.ofReal_zero, mul_zero] at hκ
    exact deriv_mul_ne_zero hF.1 hG.1 h1 hG1 hκ
  · intro σ
    have hσ2 : (σ δ - δ) * (σ δ + δ) = 0 := by
      have : σ δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ', map_intCast]
      linear_combination this
    rcases mul_eq_zero.mp hσ2 with h | h
    · have hnr : δ ∉ Set.range (algebraMap ℚ K) := by
        rintro ⟨q, rfl⟩
        have hq : q ^ 2 = (D : ℚ) := by
          apply (algebraMap ℚ K).injective
          rw [map_pow, hδ', map_intCast]
        have : (D : ℚ) < 0 := by exact_mod_cast hDisc.1
        nlinarith [sq_nonneg q]
      have := algEquiv_eq_one_of_fix hK2 hnr σ (sub_eq_zero.mp h)
      subst this
      rw [map_one_apply, sub_self]
      exact IsOfFinAddOrder.zero
    · have hw : rootNumber f hχ = -1 := signOfSimpleZero N f hχ F hF h1
      exact (hGC N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι hι y hy σ
        (eq_neg_of_add_eq_zero_left h)).2 hw

/-- **`GZStatements.GrossZagierHeegnerCd` from the even-`c` Heegner point, the Gross–Zagier formula and
Gross's conjugation relation** (gz-weil's chain, with `HeegnerPointRationalCd` weakened to even `c`). -/
theorem grossZagierHeegnerCd_of_even (hHP : HeegnerPointRationalCdEven)
    (hGZ : GrossZagierFormulaCd) (hGC : GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd := by
  intro d hd hsq
  have : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic := shortCurve_cd_isElliptic (by omega)
  exact heegner_at_even _ (ZInQ.GZWeil.exists_isPeriodLattice_cd (by omega))
    (ZInQ.GZWeil.shimuraCMParamCd_proved d hd hsq) (hHP d hd hsq) (hGZ d hd hsq) (hGC d hd hsq)

/-- **`GrossZagierHeegnerCd` from the Galois statement `TwistTransportCd` on `X₀(32)` and the two printed
Gross–Zagier statements** (no canonical model of `X₀(32 d²)`). -/
theorem grossZagierHeegnerCd_of_twist (hT : TwistTransportCd)
    (hGZ : GrossZagierFormulaCd) (hGC : GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_even (heegnerPointRationalCdEven_of_twist hT) hGZ hGC

end Chain

end ZInQ.Heegner32
