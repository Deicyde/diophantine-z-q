import ZInQKernel.Contrib.OneProof.TYZThm33Curve
import ZInQKernel.Contrib.OneProof.AdelicX0.CMPoints

/-!
# h33-g5: TYZ Theorem 3.3 with TYZ's adelic CM points `P_n = [h, 1] ∈ X_U(ℂ)`

Task h33-g5 (2026-11-17). Report: `docs/research/h33-g5.md`; scratch and log: `scratch/h33-g5/`.

The h33 leaf of h33-d1 (`H33D1.TYZThm33CurveSome`) reads TYZ's CM points `P_n` on the adelic curve
`X_U` as the points `τ_n` of `ℍ`. This file states the leaf with TYZ's points as printed and proves
the step G5 in Lean:

* `IsShPointAt N ι P x`: the `ℂ`-point `x` of the model `X` of `X₀(N)` is the point
  `P ∈ X_{U₀(N)}(ℂ)° = GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(N))` (TYZ L1518–1520): `x` is at every `τ ∈ ℍ`
  with `[τ, 1] = P`. Every `P` is some `[τ, 1]` (`toSh_surjective`, strong approximation), and the
  `τ` with `[τ, 1] = P` form one `Γ₀(N)`-orbit (`toSh_eq_toSh_iff`); since `IsPointAt` is
  `Γ₀(N)`-invariant (`isPointAt_smul_iff`), `IsShPointAt N ι [τ, 1] x ↔ IsPointAt N ι τ x`
  (`isShPointAt_toSh_iff`).
* The leaf `TYZThm33AdelicSome`: as h33-d1's, with the hypothesis on `w` stated at TYZ's
  `f₀(P_n)`, `P_n = [h, 1] ∈ X_U(ℂ)` with `h` the fixed point of TYZ's embedding `K_n → M₂(ℚ)`
  (`AdelicX0.tyzP5`, `tyzP7`), `f₀ : X_U → X_{U₀(32)}` the projection.
* `tyzThm33CurveSome_of_adelic` and `tyzThm33AdelicSome_of_curveSome`: the two leaves are
  equivalent in Lean (`P_n ↦ τ_n` is `AdelicX0.f0_tyzP5`, `f0_tyzP7`).
* `tyzThm33_of_adelic (hCM) : TYZThm33AdelicSome → TYZSplit.TYZThm33`, the binder `h33`.
* G7: TYZ's model `2y² = x³ + x` and the kernel's `y² = x³ + 4x` (`tyzToA`, §4).

No `sorry`, no `axiom`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Topology
open scoped WeierstrassCurve.Affine Manifold

namespace ZInQ.H33G5

open ZInQ.GZSch ZInQ.GZAlg ZInQ.GZDict2 ZInQ.AdelicX0 ZInQ.H33D1
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.TYZSplit
  ZInQ.Contrib.TYZGenus.H33Dict ZInQ.Contrib.TYZGenus.CMBridge

/-! ## §1. Points of `X_{U₀(N)}(ℂ)°` on a model of `X₀(N)` -/

/-- **`x : Spec ℂ ⟶ X` is the point `P ∈ GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U₀(N))`** of TYZ's complex
uniformization of `X_{U₀(N)}` (Period7.tex L1518–1520, cusps omitted), for a model `(X, ι)` of
`X₀(N)`: `x` is the point `τ` (hgz-steps' `IsPointAt`) for every `τ ∈ ℍ` with `[τ, 1] = P`. Such
`τ` exist (`toSh_surjective`) and form one `Γ₀(N)`-orbit (`toSh_eq_toSh_iff`). -/
def IsShPointAt (N : ℕ) [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    (ι : X.functionField ≃+* X0Field N) (P : Sh (U0 N)) (x : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∀ τ : ℍ, toSh (U0 N) τ = P → IsPointAt N ι τ x

theorem isPointAt_of_isShPointAt {N : ℕ} [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    {ι : X.functionField ≃+* X0Field N} {τ : ℍ} {x : Spec (CommRingCat.of ℂ) ⟶ X}
    (h : IsShPointAt N ι (toSh (U0 N) τ) x) : IsPointAt N ι τ x := h τ rfl

/-! ## §2. The leaf -/

/-- **The statement of TYZ Theorem 3.3 on one model `(X, ι)` of `X₀(32)`, with TYZ's adelic CM
points.** As `H33D1.TYZ33Body`, with `w n = i₀(f₀(P_n))` for the `ℂ`-points `x` of `X` that are the
point `f₀(P_n) ∈ X_{U₀(32)}(ℂ)`, `P_n = [h, 1] ∈ X_U(ℂ)` TYZ's CM point. -/
def TYZ33BodyAd (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Spec (CommRingCat.of ℚ))
    (ι : X.functionField ≃+* X0Field 32) : Prop :=
  ∀ i₀ : X ⟶ ESch curveA, IsIso i₀ → i₀ ≫ toSpecQ curveA = sX →
  (∀ p : X, IsCuspInfty 32 ι p → i₀ p = ptO curveA) →
  ∀ w : ℕ → PtA,
    (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
      IsShPointAt 32 ι (shMap UTYZ_le (tyzP5 n hn)) x →
        toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) →
    (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → ∀ x : Spec (CommRingCat.of ℂ) ⟶ X,
      IsShPointAt 32 ι (shMap UTYZ_le (tyzP7 n hn)) x →
        toC (w n) = ZInQ.GZSch.ptOf curveA (x ≫ i₀)) →
    TYZThm33EpsAfter (zOfLift w)

/-- **Leaf TYZ-3.3 (adelic form, one model): Tian–Yuan–Zhang Theorem 3.3 for TYZ's isomorphism of
curves `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ` and TYZ's CM points `P_n = [h, 1] ∈ X_U(ℂ)`, for
`n ≡ 5, 7 (mod 8)`.**

Source: Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*,
arXiv:1411.4728v1, Theorem 3.3 (Period7.tex L1296–1311), with §3.1: `A ≅ (X₀(32), ∞)`, "Fix an
identification `i₀`" (L1173–1174); `U₀(32)`, `U` (L1179–1185); `f₀ : X_U → X₀(32)` (L1187);
`f_n = f₀ − f₀∘[i]` (`n ≡ 5`), `f_n = i₀` (`n ≡ 7`) (L1195–1198); the embeddings `K_n → M₂(ℚ)`
(L1225–1229); `P_n = [h, 1] ∈ X_U(ℂ)`, `h` the fixed point of `K_n^×` in `ℍ` (L1236–1240); the
complex uniformization `GL₂(ℚ)₊ \ (ℍ ∪ ℙ¹(ℚ)) × GL₂(𝔸_f)/U₀(32)` (L1518–1520). Journal version:
Asian J. Math. 21 (2017), NOT checked.

The objects are those of `H33D1.TYZThm33CurveSome` (a normal proper model `(X, ι)` of `X₀(32)`,
`A = ESch curveA`, `i₀` an isomorphism of `ℚ`-schemes with `i₀(∞) = O`), except the CM points:
* `X_U(ℂ)° = Sh UTYZ` and `X_{U₀(32)}(ℂ)° = Sh (U0 32)` are the double coset spaces
  `GL₂(ℚ)⁺ \ (ℍ × GL₂(𝔸_f)/U)` (`AdelicX0.Sh`, `𝔸_f` Mathlib's `FiniteAdeleRing ℤ ℚ`);
* `P_n = tyzP5 n` (`n ≡ 5`), `tyzP7 n` (`n ≡ 7`, `δ = tyzDelta n`): `[h, 1]` with `h` the fixed
  point in `ℍ` of TYZ's image of `√−n`;
* `f₀(P_n) = shMap UTYZ_le P_n`, and the `ℂ`-points of `X` at it are `IsShPointAt 32 ι (f₀ P_n)`.

Readings left (not Lean): G2 (TYZ's `X_{U₀(32)}` over `ℚ` is the model `(X, ι)`: its function field
is `ℚ(j, j₃₂) ⊂ ℚ((q))` with `∞` the place `ord_q`, and its `ℂ`-points are `Sh (U0 32)` through
`IsPointAt`; see the report), the identification `X_U ≅ X₀(32)_{ℚ(i)}` with `f_n` (G5's second half,
used only through `zOfLift`), the sign of `[i]` (G6, h33-sign), the model `y² = x³ + 4x` (G7, §4),
the weakenings of h33-dict. -/
def TYZThm33AdelicSome : Prop :=
  ∃ (X : Scheme.{0}) (_ : IsIntegral X) (sX : X ⟶ Spec (CommRingCat.of ℚ)), IsProper sX ∧
    ZInQ.Contrib.CurvesG.IsNormalScheme X ∧ topologicalKrullDim X = 1 ∧
    ∃ ι : X.functionField ≃+* X0Field 32, TYZ33BodyAd X sX ι

/-! ## §3. The bridge -/

/-- **`P_n ↦ τ_n`**: the adelic body implies h33-d1's body. -/
theorem tyz33Body_of_ad {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (CommRingCat.of ℚ)}
    {ι : X.functionField ≃+* X0Field 32} (h : TYZ33BodyAd X sX ι) : H33D1.TYZ33Body X sX ι := by
  intro i₀ hi hs hc w h5 h7
  refine h i₀ hi hs hc w (fun n hn hsq x hx => h5 n hn hsq x ?_) (fun n hn hsq x hx => h7 n hn hsq x ?_)
  · rw [f0_tyzP5] at hx; exact isPointAt_of_isShPointAt hx
  · rw [f0_tyzP7] at hx; exact isPointAt_of_isShPointAt hx

/-- **The adelic leaf implies h33-d1's leaf.** -/
theorem tyzThm33CurveSome_of_adelic (h : TYZThm33AdelicSome) : H33D1.TYZThm33CurveSome := by
  obtain ⟨X, hX, sX, hp, hN, hd, ι, hb⟩ := h
  exact ⟨X, hX, sX, hp, hN, hd, ι, tyz33Body_of_ad hb⟩

/-- **The contribution: `TYZThm33AdelicSome` discharges the binder `h33` of `frozenTarget`**
(given `hCM`, an existing binder, through `HCMDict.shimuraMainCM_of_printed`). -/
theorem tyzThm33_of_adelic (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33AdelicSome) : TYZThm33 :=
  H33D1.tyzThm33_of_curveSome hCM (tyzThm33CurveSome_of_adelic h)

/-! ## §3b. `IsPointAt` is `Γ₀(N)`-invariant; the two leaves are equivalent -/

/-- `(j(τ), j(Nτ))` is `Γ₀(N)`-invariant (Gamma0QExp's `jf_smul`, `jN_smul_of_mem`). -/
theorem pt2_smul {N : ℕ} [NeZero N] {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (w : ℍ) : pt2 N (σ • w) = pt2 N w := by
  have h1 : jFun (σ • w) = jFun w := ZInQ.Gamma0QExp.jf_smul σ w
  have h2 : jFun (scaleN N (σ • w)) = jFun (scaleN N w) :=
    ZInQ.Gamma0QExp.jN_smul_of_mem N hσ w
  ext i
  fin_cases i
  · exact h1
  · exact h2

/-- Every `P(j, j_N)/Q(j, j_N)` is `Γ₀(N)`-invariant. -/
theorem ratFn_smul {N : ℕ} [NeZero N] {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (P Q : MvPolynomial (Fin 2) ℚ) (w : ℍ) :
    ratFn N P Q (σ • w) = ratFn N P Q w := by
  simp only [ratFn, polyFn, pt2_smul hσ w]

/-- **Limits at `σ τ` of a `σ`-invariant function are limits at `τ`** (the Möbius map of `σ` is a
local homeomorphism at `τ`). -/
theorem tendsto_of_smul_invariant {F : ℍ → ℂ} (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hF : ∀ w : ℍ, F (σ • w) = F w) (τ : ℍ) {L : Filter ℂ}
    (h : Tendsto (F ∘ ofComplex) (𝓝[≠] ((σ • τ : ℍ) : ℂ)) L) :
    Tendsto (F ∘ ofComplex) (𝓝[≠] (τ : ℂ)) L := by
  set a : ℂ := ((σ 0 0 : ℤ) : ℂ); set b : ℂ := ((σ 0 1 : ℤ) : ℂ)
  set c : ℂ := ((σ 1 0 : ℤ) : ℂ); set d : ℂ := ((σ 1 1 : ℤ) : ℂ)
  set m : ℂ → ℂ := fun z => (a * z + b) / (c * z + d)
  have hdet : a * d - b * c = 1 := by
    have := σ.det_coe
    rw [Matrix.det_fin_two] at this
    simp only [a, b, c, d]; exact_mod_cast this
  have hcoe : ∀ w : ℍ, ((σ • w : ℍ) : ℂ) = m w := fun w => by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [m, a, b, c, d]
  have hden : c * (τ : ℂ) + d ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (σ : GL (Fin 2) ℝ) τ
    simpa [UpperHalfPlane.denom, c, d] using this
  have hcont : ContinuousAt m (τ : ℂ) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hden
  have hev : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im ∧ c * z + d ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
    have h2 : ∀ᶠ z in 𝓝 (τ : ℂ), c * z + d ≠ 0 :=
      ContinuousAt.eventually_ne (by fun_prop) hden
    exact h1.and h2
  have hm : Tendsto m (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((σ • τ : ℍ) : ℂ)) := by
    rw [hcoe]
    refine tendsto_nhdsWithin_iff.mpr ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hne
    intro heq
    apply hne
    have heq' : m z = m τ := heq
    simp only [m] at heq'
    rw [div_eq_div_iff hz.2 hden] at heq'
    have : (a * d - b * c) * (z - τ) = 0 := by linear_combination heq'
    rw [hdet, one_mul, sub_eq_zero] at this
    exact this
  refine (h.comp hm).congr' ?_
  filter_upwards [nhdsWithin_le_nhds hev] with z hz
  simp only [Function.comp_apply]
  have hz' : ofComplex z = ⟨z, hz.1⟩ := ofComplex_apply_of_im_pos hz.1
  have hmz : ofComplex (m z) = σ • (⟨z, hz.1⟩ : ℍ) := by
    have him : 0 < (m z).im := by
      have := (σ • (⟨z, hz.1⟩ : ℍ)).im_pos
      rwa [UpperHalfPlane.im, hcoe] at this
    rw [ofComplex_apply_of_im_pos him]
    exact UpperHalfPlane.ext (by rw [hcoe])
  rw [hmz, hF, hz']

/-- **`IsPointAt` is `Γ₀(N)`-invariant**: `x` is the point `σ τ` iff it is the point `τ`. -/
theorem isPointAt_smul_iff {N : ℕ} [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    {ι : X.functionField ≃+* X0Field N} {σ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    IsPointAt N ι (σ • τ) x ↔ IsPointAt N ι τ x := by
  constructor
  · intro h s P Q hr
    exact tendsto_of_smul_invariant σ (ratFn_smul hσ P Q) τ (h s P Q hr)
  · intro h s P Q hr
    have hσ' : σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := inv_mem hσ
    have e : σ⁻¹ • σ • τ = τ := inv_smul_smul σ τ
    exact tendsto_of_smul_invariant σ⁻¹ (ratFn_smul hσ' P Q) (σ • τ) (by rw [e]; exact h s P Q hr)

/-- **`x` is the point `[τ, 1]` of `X_{U₀(N)}(ℂ)°` iff `x` is the point `τ`.** -/
theorem isShPointAt_toSh_iff {N : ℕ} [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    {ι : X.functionField ≃+* X0Field N} (τ : ℍ) (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    IsShPointAt N ι (toSh (U0 N) τ) x ↔ IsPointAt N ι τ x := by
  refine ⟨isPointAt_of_isShPointAt, fun h τ' hτ' => ?_⟩
  obtain ⟨σ, hσ, rfl⟩ := (toSh_eq_toSh_iff (NeZero.ne N) τ' τ).mp hτ'
  exact (isPointAt_smul_iff hσ τ' x).mp h

/-- **`IsShPointAt` in existential form**: `x` is the point `P` iff it is the point `τ` for some
(equivalently every) `τ` with `[τ, 1] = P`; such `τ` exist by strong approximation. -/
theorem isShPointAt_iff_exists {N : ℕ} [NeZero N] {X : Scheme.{0}} [IsIntegral X]
    {ι : X.functionField ≃+* X0Field N} (P : Sh (U0 N)) (x : Spec (CommRingCat.of ℂ) ⟶ X) :
    IsShPointAt N ι P x ↔ ∃ τ : ℍ, toSh (U0 N) τ = P ∧ IsPointAt N ι τ x := by
  obtain ⟨τ, rfl⟩ := toSh_surjective (NeZero.ne N) P
  refine ⟨fun h => ⟨τ, rfl, isPointAt_of_isShPointAt h⟩, ?_⟩
  rintro ⟨τ', hτ', h⟩
  rw [← hτ']
  exact (isShPointAt_toSh_iff τ' x).mpr h

/-- **h33-d1's body implies the adelic body**: the two leaves are equivalent. -/
theorem tyz33BodyAd_of_body {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (CommRingCat.of ℚ)}
    {ι : X.functionField ≃+* X0Field 32} (h : H33D1.TYZ33Body X sX ι) : TYZ33BodyAd X sX ι := by
  intro i₀ hi hs hc w h5 h7
  refine h i₀ hi hs hc w (fun n hn hsq x hx => h5 n hn hsq x ?_)
    (fun n hn hsq x hx => h7 n hn hsq x ?_)
  · rw [f0_tyzP5]; exact (isShPointAt_toSh_iff _ x).mpr hx
  · rw [f0_tyzP7]; exact (isShPointAt_toSh_iff _ x).mpr hx

theorem tyzThm33AdelicSome_of_curveSome (h : H33D1.TYZThm33CurveSome) : TYZThm33AdelicSome := by
  obtain ⟨X, hX, sX, hp, hN, hd, ι, hb⟩ := h
  exact ⟨X, hX, sX, hp, hN, hd, ι, tyz33BodyAd_of_body hb⟩

/-- **The adelic leaf and h33-d1's leaf are equivalent.** -/
theorem tyzThm33AdelicSome_iff : TYZThm33AdelicSome ↔ H33D1.TYZThm33CurveSome :=
  ⟨tyzThm33CurveSome_of_adelic, tyzThm33AdelicSome_of_curveSome⟩

/-! ## §4. G7: TYZ's model `2y² = x³ + x` and the kernel's `y² = x³ + 4x` -/

/-- **TYZ's `A : 2y² = x³ + x`** (Period7.tex L1172), its points over `ℚ̄`: the point `O` at infinity
or an affine solution. -/
inductive TYZPt where
  | zero : TYZPt
  | some (x y : Qbar) (h : 2 * y ^ 2 = x ^ 3 + x) : TYZPt

theorem curveAbar_Δ : curveAbar.Δ = -4096 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  norm_num

theorem curveAbar_nonsingular_iff {X Y : Qbar} :
    curveAbar.toAffine.Nonsingular X Y ↔ Y ^ 2 = X ^ 3 + 4 * X := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (by rw [curveAbar_Δ]; norm_num), WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  constructor <;> intro h <;> linear_combination h

theorem tyz_nonsingular {x y : Qbar} (h : 2 * y ^ 2 = x ^ 3 + x) :
    curveAbar.toAffine.Nonsingular (2 * x) (4 * y) :=
  curveAbar_nonsingular_iff.mpr (by linear_combination 8 * h)

theorem tyz_of_nonsingular {X Y : Qbar} (h : curveAbar.toAffine.Nonsingular X Y) :
    2 * (Y / 4) ^ 2 = (X / 2) ^ 3 + X / 2 := by
  have := curveAbar_nonsingular_iff.mp h
  linear_combination (1 / 8 : Qbar) * this

/-- **G7: the model change `(x, y) ↦ (2x, 4y)`, `O ↦ O`**, from TYZ's `2y² = x³ + x` to the kernel's
`A : y² = x³ + 4x` (`8(2y² − x³ − x) = (4y)² − (2x)³ − 4·2x`). -/
def tyzToA : TYZPt → PtA
  | .zero => .zero
  | .some x y h => .some (2 * x) (4 * y) (tyz_nonsingular h)

/-- The inverse `(X, Y) ↦ (X/2, Y/4)`. -/
def aToTyz : PtA → TYZPt
  | .zero => .zero
  | .some X Y h => .some (X / 2) (Y / 4) (tyz_of_nonsingular h)

/-- **The model change is a bijection `A_TYZ(ℚ̄) ≃ A(ℚ̄)`.** -/
def tyzEquiv : TYZPt ≃ PtA where
  toFun := tyzToA
  invFun := aToTyz
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      show TYZPt.some (2 * x / 2) (4 * y / 4) _ = TYZPt.some x y h
      congr 1 <;> ring
  right_inv P := by
    cases P with
    | zero => rfl
    | some X Y h =>
      show WeierstrassCurve.Affine.Point.some (2 * (X / 2)) (4 * (Y / 4)) _ = .some X Y h
      congr 1 <;> ring

/-- TYZ's `[i] : (x, y) ↦ (−x, iy)` on `2y² = x³ + x` (the same `i = iQ` as the kernel's `iPt`). -/
def iTYZ : TYZPt → TYZPt
  | .zero => .zero
  | .some x y h => .some (-x) (iQ * y) (by linear_combination y ^ 2 * 2 * iQ_sq - h)

/-- **The model change commutes with `[i]`.** -/
theorem tyzToA_iTYZ (P : TYZPt) : tyzToA (iTYZ P) = iPt (tyzToA P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    show WeierstrassCurve.Affine.Point.some (2 * -x) (4 * (iQ * y)) _ =
      .some (-(2 * x)) (iQ * (4 * y)) _
    congr 1 <;> ring

/-- TYZ's `−(x, y) = (x, −y)`. -/
def negTYZ : TYZPt → TYZPt
  | .zero => .zero
  | .some x y h => .some x (-y) (by linear_combination h)

/-- **The model change commutes with negation.** -/
theorem tyzToA_neg (P : TYZPt) : tyzToA (negTYZ P) = -tyzToA P := by
  cases P with
  | zero => rfl
  | some x y h =>
    show WeierstrassCurve.Affine.Point.some (2 * x) (4 * -y) _ = -(.some (2 * x) (4 * y) _)
    rw [WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    have h1 : curveAbar.a₁ = 0 := curveAbar_a₁
    have h3 : curveAbar.a₃ = 0 := curveAbar_a₃
    simp only [WeierstrassCurve.Affine.negY]
    simp only [curveAbar, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] at h1 h3 ⊢
    rw [h1, h3]; ring

/-- **The model change maps lines to lines** (so the chord-and-tangent laws with origin `O`
correspond): three affine points are collinear iff their images are. -/
theorem collinear_tyzToA (x₁ y₁ x₂ y₂ x₃ y₃ : Qbar) :
    (2 * x₂ - 2 * x₁) * (4 * y₃ - 4 * y₁) = (2 * x₃ - 2 * x₁) * (4 * y₂ - 4 * y₁) ↔
      (x₂ - x₁) * (y₃ - y₁) = (x₃ - x₁) * (y₂ - y₁) := by
  constructor
  · intro h
    have h8 : (8 : Qbar) * ((x₂ - x₁) * (y₃ - y₁) - (x₃ - x₁) * (y₂ - y₁)) = 0 := by
      linear_combination h
    have := (mul_eq_zero.mp h8).resolve_left (by norm_num)
    linear_combination this
  · intro h; linear_combination 8 * h

/-- Vertical lines (the lines through `O`) correspond. -/
theorem vertical_tyzToA (x₁ x₂ : Qbar) : 2 * x₁ = 2 * x₂ ↔ x₁ = x₂ := by
  constructor
  · intro h; have := congrArg (· / 2) h; simpa using this
  · intro h; rw [h]

end ZInQ.H33G5
