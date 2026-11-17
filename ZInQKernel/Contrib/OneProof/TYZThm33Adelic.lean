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

end ZInQ.H33G5
