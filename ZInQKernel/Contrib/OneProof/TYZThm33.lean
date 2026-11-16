import ZInQKernel.OneProof.TYZSplit
import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8

/-!
# h33-dict: the top hypothesis `h33` (TYZ Theorem 3.3) from its printed form

Original reduction by the project contributor at revision
`d489fc13f1eadba5ca95d61b8f455cd2b0e7c402` (2026-11-16), reused with its proof declarations unchanged.
Source: https://github.com/Deicyde/diophantine-z-q/blob/d489fc13f1eadba5ca95d61b8f455cd2b0e7c402/ZInQKernel/Contrib/OneProof/TYZThm33.lean
Original report: `docs/research/h33-dict.md` at that revision. The conditional export `CloudB3SC7H33.h33_proof`
is new. Comment-only provenance and source-reading updates are recorded in
`ZInQKernel/Contrib/CloudB3SC7H33/SOURCE_REUSE.md`.

`ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33` (the argument `h33` of `ZInQ.OneProof.frozenTarget`) states TYZ
Theorem 3.3 over the kernel's CM points `TYZ35.basePt`, built on x0-32's eta-quotient model `X0.phiC`, with
`ε` chosen before the representatives `Φ`. The 11-16 dictionary pass rated it a consequence for two reasons:
(1) TYZ build `z_n` from an algebraic identification `i₀ : X₀(32) → A`, not from the eta model; (2) choosing
`ε` before `Φ` needs TYZ Prop. 3.2(4). This file proves

  `tyzThm33_of_printed (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33Printed) : TYZSplit.TYZThm33`

where `TYZThm33Printed` (§1) is TYZ Theorem 3.3 over an arbitrary identification `i₀ : (X₀(32), ∞) ≅ (A, O)`
over `ℚ` (encoded by its pullbacks in `ℚ(X₀(32))`, `IsX0Identification`), with `ε` chosen after `Φ` and `χ`,
and `hCM` is the printed main theorem of complex multiplication, already a hypothesis of `frozenTarget`.
The implementation-level reduction steps below are proved. Interpreting `IsX0Identification` as an
algebraic pointed isomorphism, and the inherited modular-curve/component dictionary, remain standard
source interpretation rather than Lean scheme-equivalence theorems:

* §2 TYZ Prop. 3.2(4) in the form the uniformization uses (`TYZProp324Used`: two lifts of the same
  `t ∈ Cl_n` move `z_n` to points differing by torsion), from the CM inputs that `hCM` gives through the
  proved theta identity (hx-used, theta-wp8): the kernel's glue KER for `n ≡ 5`, `z_n ∈ A(H_n)` for `n ≡ 7`;
* §3 `ε` can be chosen before `Φ` (`tyzThm33_of_epsAfter`);
* §4 the eta model `(x, y)` is an identification: `x, y ∈ ℚ(X₀(32))` and the curve equation (kernel),
  `x` unbounded at `∞` (x0-32), and, new here, `x = O(e^{4π Im τ})` at `∞` and `x` bounded at every cusp
  `γ∞` with `32 ∤ c` (Ligozat's orders, from an exact form of tyz-cm's Hermite decomposition and the
  `SL₂(ℤ)`-invariance of `|η|⁴ Im`): `isX0Identification_eta`;
* §5 the CM points: `toC (heegnerPt Q) = phiC τ_Q` (from `hCM`), so `basePt` is `zOfLift` of the
  Heegner points of the eta model.

No `sorry`, no `axiom`.
-/

noncomputable section

set_option maxRecDepth 8000

namespace ZInQ.Contrib.TYZGenus.H33Dict

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.PropN NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Rank5b
  ZInQ.Contrib.TYZGenus.CMBridge ZInQ.Contrib.TYZGenus.TYZ35 ZInQ.Contrib.TYZDecomp
  ZInQ.RouteK.Redei ZInQ.Literature ZInQ.Contrib.TYZGenus.TYZSplit

/-! # §1. The leaf -/

/-! ## §1.1 Theorem 3.3 for a family of CM points, `ε` chosen after `Φ` and `χ` -/

/-- `P_χ = Σ_{t ∈ Φ} χ(t) z_n^t` for an arbitrary family `z` of CM points (`PchiG` is `PchiGWith basePt`). -/
def PchiGWith (z : ℕ → PtA) (n : ℕ) [NeZero n] (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) : PtA :=
  ∑ t : ClG n, ((χ t : ℤˣ) : ℤ) • galPt (φ t) (z n)

theorem pchiGWith_basePt {n : ℕ} [NeZero n] (φ : ClG n → GalQ) (χ : ClG n →* ℤˣ) :
    PchiGWith basePt n φ χ = PchiG n φ χ := rfl

/-- **TYZ's class of `ε(d₀, d₁)`** (L1308–1309): `±i` on `(d₀, d₁) ≡ (5, 3) (mod 8)`, `±1` otherwise. -/
def EpsClass (d₀ d₁ : ℕ) (e : GaussianInt) : Prop :=
  (d₀ % 8 = 5 ∧ d₁ % 8 = 3 → e = gi ∨ e = -gi) ∧ (¬ (d₀ % 8 = 5 ∧ d₁ % 8 = 3) → e = 1 ∨ e = -1)

/-- **TYZ Theorem 3.3 for a family `z` of CM points, in the printed quantifier order**: as
`TYZSplit.TYZThm33` (with `basePt` replaced by `z`), except that `ε(d₀, d₁)` is chosen after the set of
representatives `Φ` and the character `χ` (TYZ fix `Φ` at L1279 before stating the theorem, so their
`ε(d₀, d₁)` may a priori depend on `Φ`). -/
def TYZThm33EpsAfter (z : ℕ → PtA) : Prop :=
  ∀ ℓ : ℕ → ℤ, (∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((ℓ m : ℂ)) ^ 2 = lcalSq m) →
  ∃ (Q : ℕ → PtA) (m : ℕ → ℕ),
    (∀ d, 0 < m d) ∧ (∀ d, InMinus d (Q d)) ∧
    (∀ d : ℕ, Squarefree d → (d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) →
      (¬ ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC d) F ∧ analyticOrderAt F 1 ≤ 1) →
        IsOfFinAddOrder (Q d)) ∧
    ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
      ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ,
        (¬ IsOfFinAddOrder (PchiGWith z n φ χ) →
          ∃ d₀ d₁ : ℕ, d₀ * d₁ = n ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
            (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair n d₁ χ) ∧
        ∀ d₀ d₁ : ℕ, d₀ * d₁ = n → (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) →
          (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) → IsChiPair n d₁ χ →
          ∃ ε : GaussianInt, EpsClass d₀ d₁ ε ∧
            IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiGWith z n φ χ -
              (ε * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀)

/-! ## §1.2 TYZ's identification `i₀ : (X₀(32), ∞) ≅ (A, O)`, over Mathlib's upper half plane -/

open WeierstrassCurve.Affine in
open Classical in
/-- The point `(X(τ), Y(τ)) ∈ A(ℂ)` (`0` if it is not on `A`; never the case under the curve equation). -/
def ptOf (X Y : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : X0.PtAC :=
  if h : X0.curveAC.toAffine.Nonsingular (X τ) (Y τ) then .some (X τ) (Y τ) h else 0

theorem ptOf_eta (τ : UpperHalfPlane) :
    ptOf (fun τ => X0.xC τ) (fun τ => X0.yC τ) τ = X0.phiC τ := rfl

/-- **`(X, Y) = (x ∘ i₀, y ∘ i₀)` for an isomorphism `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ`** (TYZ L1173–1174),
`A : y² = x³ + 4x` (`ℚ`-isomorphic to TYZ's `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`). Over `ℂ`,
`X₀(32)(ℂ) = Γ₀(32)\ℍ ∪ {cusps}` and a morphism `i₀` is given by the pullbacks `X = x∘i₀`, `Y = y∘i₀` of the
coordinate functions, which are elements of `ℚ(X₀(32))`; the conditions say:
* `X, Y ∈ ℚ(X₀(32))`, regular on `ℍ` (`IsRatModFn 32`: `Γ₀(32)`-invariant, meromorphic at the cusps, rational
  `q`-expansion at `∞`): `i₀` is a morphism over `ℚ` with `i₀⁻¹(O) ⊆ {cusps}`;
* `Y² = X³ + 4X`: `i₀` lands on `A`;
* `X` is unbounded at `∞`: `i₀(∞) = O`;
* `X = O(e^{4π Im τ})` at `∞` (a pole of order at most `2` in `q`, `∞` having width `1`) and `X` is bounded at
  every other cusp `γ∞` (`γ ∈ SL₂(ℤ)`, `32 ∤ c`; the cusps `γ∞` with `32 ∣ c` are exactly those
  `Γ₀(32)`-equivalent to `∞`): `X` has degree at most `2` on `X₀(32)`, and `deg X = deg i₀ · deg x = 2 deg i₀`,
  so `deg i₀ = 1` (and `deg X = 2`), i.e. `i₀` is an isomorphism.
Conversely every isomorphism `i₀ : (X₀(32), ∞) ≅ (A, O)` over `ℚ` has these pullbacks (`x` has a single
double pole at `O`, `q` is a local parameter at `∞`). So the predicate is exactly TYZ's normalization. -/
def IsX0Identification (X Y : UpperHalfPlane → ℂ) : Prop :=
  Shimura.IsRatModFn 32 X ∧ Shimura.IsRatModFn 32 Y ∧ (∀ τ, Y τ ^ 2 = X τ ^ 3 + 4 * X τ) ∧
    ¬ UpperHalfPlane.IsBoundedAtImInfty X ∧
    (X =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (4 * Real.pi * τ.im)) ∧
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ¬ (32 : ℤ) ∣ γ 1 0 →
      UpperHalfPlane.IsBoundedAtImInfty (fun τ => X (γ • τ))

/-- TYZ's `z_n = f_n(P_n)` from the points `w n = i₀(P_n) ∈ A(ℚ̄)`: `f_n = f₀ − f₀∘[i]`, i.e.
`z_n = (1 − [i]) i₀(P_n)`, for `n ≡ 5 (mod 8)`; `f_n = i₀`, `z_n = i₀(P_n)`, otherwise (TYZ L1195–1198). -/
def zOfLift (w : ℕ → PtA) (n : ℕ) : PtA := if n % 8 = 5 then w n - iPt (w n) else w n

/-- **Leaf TYZ-3.3 (printed form): Tian–Yuan–Zhang Theorem 3.3 ("Gross–Zagier formula"), for TYZ's
identification `i₀ : (X₀(32), ∞) ≅ (A, O)`, for `n ≡ 5, 7 (mod 8)`.**

Source: Tian–Yuan–Zhang, *Genus periods, genus points and congruent number problem*, arXiv:1411.4728v1,
Theorem 3.3 (`\label{GZ}`, Period7.tex L1299–1311), with the set-up of §3.1: `A : 2y² = x³ + x` identified
with `(X₀(32), ∞)` (L1173–1174), `f_n = f₀ − f₀∘[i]` for `n ≡ 5`, `f_n = i₀` for `n ≡ 7` (L1195–1198), the
embeddings of `K_n` with fixed points `P_n` (L1203–1205, L1245–1252), `Cl_n = Gal(H_n/K_n)`, `Cl'_n`, `σ`
(L1263–1265), "fix a set `Φ` of representatives" and `P_χ` (L1279–1284), `𝒫(n)` (L1288–1295), `h₂` (L992).
Journal: *Asian J. Math.* 21 (2017) 721–774, Theorem 3.3, printed p. 739; setup pp. 736–739,
sign and Corollary 3.9 p. 744, proof pp. 749–751, explicit Theorem A.9 p. 769. Exact arXiv v1 and
the authors' typeset journal copy were opened and compared on 2026-11-16 (AI-READ):
https://arxiv.org/pdf/1411.4728v1 and https://web.math.princeton.edu/~shouwu/publications/cn.pdf .
The original d489fc13 report relied on the previous arXiv readings in tyz-split and h33-sign and did not
make this journal comparison. Those reports and the original proof history remain preserved.
The analytic-to-algebraic interpretation of `IsX0Identification` is the standard q-expansion/degree
argument in its docstring, not a Lean theorem constructing a scheme isomorphism. No human-reading
flag is cleared by this AI-READ comparison. See `CloudB3SC7H33/SOURCE_AUDIT.md`.

The statement: for every identification `i₀` (pullbacks `X = x∘i₀`, `Y = y∘i₀`, `IsX0Identification`),
every family `w` of algebraic points with `w(n) = i₀(P_n)` in `A(ℂ)` (so `z_n = f_n(P_n) = zOfLift w n`),
every sign choice `ℓ` of `𝓛` on classes 1, 3, there are `𝒫(d) = Q d / m d` such that for every positive
squarefree `n ≡ 5, 7 (mod 8)`, every `Φ` and every `χ : Cl_n → {±1}`:
* `P_χ` non-torsion only if `χ = χ_{d₀,d₁}`, `n = d₀d₁`, `0 < d₀ ≡ 5, 6, 7`, `0 < d₁ ≡ 1, 2, 3 (mod 8)`;
* then `P_χ = ε(d₀,d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` in `A(ℚ̄) ⊗ ℚ` for some `ε(d₀,d₁)` in TYZ's class.

Encoding (a reading of the printed display, never stronger):
* `i₀`: any isomorphism `(X₀(32), ∞) ≅ (A, O)` over `ℚ`, through its pullbacks (`IsX0Identification` is
  exactly this class, see its docstring); TYZ fix one, and there are two (`Aut_ℚ(A, O) = ±1`), so the
  statement for all of them is the printed one. `A` is the kernel's `y² = x³ + 4x`, `ℚ`-isomorphic to TYZ's
  `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`, compatibly with `[i]`. The kernel's eta model `phiC` is one such
  `i₀` (proved: `isX0Identification_eta`), and nothing about `phiC` is assumed by the leaf.
* `w n ∈ A(ℚ̄)` with `toC (w n) = i₀(τ_n)`: the leaf is vacuous for a family that is not algebraic, never
  false (TYZ's `z_n ∈ A(H'_n)` is algebraic). `P_n` is the CM point `τ_n` of the kernel's Heegner form
  `tyzForm n` (`[16(n+1), −8, 1]`, `n ≡ 5`) resp. `tyzForm7 n` (`n ≡ 7`), the fixed points of TYZ's
  embeddings (h33-sign `Iso.lean`), read on `X₀(32)` through `X_U ≅ X₀(32)_{ℚ(i)}` (L1191–1193).
* `z_n = (1 − [i]) i₀(P_n)` for `n ≡ 5` (TYZ's `f₀ − f₀∘[i]` on the component of `P_n`; the sign of `[i]`
  is fixed by TYZ's text, `α = −i` at L1564–1566, and by TYZ Thm 3.6(1) in Lean: h33-sign), `i₀(P_n)` for
  `n ≡ 7`. In the proof of the Hecke-action proposition for `n ≡ 5` the cusps `[∞,1]`, `[0]` lie on the
  component of `P_n` (about L1238, L1519, L1551), and with this sign `f₀∘[1 − i]` is `ϖ`-invariant up to
  2-torsion (about L1584–1589), as Prop. 3.1 and the proof of Thm 3.3 need. With the other sign the lifts do
  not commute with `[i]`, the contributing and excluded characters swap, and the leaf would be false, not
  weaker (statement review of tyz-split; h33-sign).
* `A(H'_n(i)) ⊗ ℚ ⊂ A(ℚ̄) ⊗ ℚ`; a vector of `A(ℚ̄) ⊗ ℚ` is `Q/m`, and equality in it is "the difference of the
  cleared multiples is torsion"; `ℤ[i]` acts through `iPt`.
* `ε(d₀,d₁)` is chosen after `Φ` and `χ` (`TYZThm33EpsAfter`): TYZ fix `Φ` before the theorem. Its class
  (`EpsClass`) is printed at L1308–1309.
* `𝒫(d) = Q d / m d` with `Q d ∈ A(K_d)^-` and `Q d` torsion when `ord_{s=1} L(E_d, s) > 1` (then
  `𝓛(d) = 0`, L338–345, and `𝒫(d) = 0`, L1295); the value of the coefficient `2^{−1−ρ(d)}𝓛(d)` is
  forgotten (it needs Néron–Tate regulators): weaker than the print.
* `𝓛(d₁)` is defined up to sign (L364); `ℓ` is any integer choice with `ℓ(d₁)² = 𝓛(d₁)²` (`lcalSq`), the sign
  absorbed in `ε`. Non-vacuity: the hypothesis on `ℓ` is satisfiable only if every `𝓛(m)²` (`m ≡ 1, 3`) is
  an integer square, i.e. together with TYZ Thm 1.1 (`TYZThm11Integral`); otherwise the leaf (and the row,
  through `IsTYZLcal`) is vacuously true. The hypotheses on `(X, Y, w)` are satisfiable given `hCM`
  (`tyzThm33Printed_hyps_satisfiable`).
* Only `n ≡ 5, 7` (TYZ: `n ≡ 5, 6, 7`); then `d₀, d₁` are odd, so the classes `6, 2` do not occur (they are
  kept in the statement as printed). `h₂` is defined in TYZ §2 (L992) and reused in §3 (L2354). `Φ` by lifts to `Gal(ℚ̄/ℚ)` (`IsPhi`), `χ` a character of `Cl_n`,
  `χ_{d₀,d₁}` by its radicand (`IsChiPair`), `h₂ = log₂ [Cl_n : Cl_n²]` (`h2G`), as in `TYZSplit.TYZThm33`. -/
def TYZThm33Printed : Prop :=
  ∀ X Y : UpperHalfPlane → ℂ, IsX0Identification X Y → ∀ w : ℕ → PtA,
    (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → toC (w n) = ptOf X Y (tyzForm n hn).tauH) →
    (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → toC (w n) = ptOf X Y (tyzForm7 n hn).tauH) →
    TYZThm33EpsAfter (zOfLift w)

/-! # §2. Glue: TYZ Proposition 3.2(4), used form, from the CM inputs (proved) -/

/-! ## §2.1 The CM inputs from `hCM` -/

/-- The CM inputs of the TYZ chain (algebraicity, field of definition, Shimura reciprocity on `Pic`) from
the printed main theorem of CM `hCM` and the proved theta identity (theta-wp8, hx-used). -/
theorem cmInputs (hCM : T5Glue.ShimuraMainCM) : X0ModuliUsed.CMInputs :=
  X0ModuliUsed.cmInputs_of (X0EtaRoute.srAt_x ThetaWP8.xEtaWeierstrass hCM)
    (X0EtaRoute.srAt_y ThetaWP8.xEtaWeierstrass hCM)

/-- `Gal(H_{n,4}/H_n)` moves `z_n` only by `ℤτ(1)` (glue KER of the kernel), from the CM inputs. -/
theorem kerFix (h : X0ModuliUsed.CMInputs) : T321.KerFixesZnMod :=
  T321.kerFixesZnMod
    (ZInQ.Contrib.TYZGenus.Shimura.tyzSigmaFixesZn_of h.pic ZInQ.Contrib.TYZGenus.Shimura.etaModelFricke)
    (T321.tyzThm36OneFive_of h.pic h.alg T321.wNegatesI) (X0ModuliUsed.znOverH4_of_field h.field)

/-! ## §2.2 Restrictions to `H_n` -/

section General

variable {K : Type} [Field K] [NumberField K]

/-- If the Artin symbol of `c ∈ Pic O` fixes the Hilbert class field, then `c ↦ 1` in `Cl(K)` (stated for a
general `K`: at `K = ℚ(√−n)` the rewrite by `restrict_ringClassArtinEquiv` times out in the kernel). -/
theorem picToMax_eq_one_of_fix (O : NumberFieldOrder K) (c : Pic O)
    (h : ∀ x : ringClassField (maximalNumberFieldOrder K),
      ringClassArtinEquiv O c (IntermediateField.inclusion (ringClassField_maximal_le O) x) =
        IntermediateField.inclusion (ringClassField_maximal_le O) x) :
    picToMax O c = 1 := by
  apply (ringClassArtinEquiv (maximalNumberFieldOrder K)).injective
  rw [map_one]
  ext x
  have e := h x
  rw [← restrictNormalHom_inclusion_apply, restrict_ringClassArtinEquiv] at e
  have e' := (IntermediateField.inclusion (ringClassField_maximal_le O)).injective e
  rw [e']
  rfl

end General

section Restr

variable {n : ℕ} [NeZero n]

theorem restricts_inv_mul {ρ ρ' : GalQ} {t : ClG n} (h : Restricts n ρ t) (h' : Restricts n ρ' t) :
    Restricts n (ρ'⁻¹ * ρ) 1 := by
  intro x
  rw [AlgEquiv.mul_apply, h x, ← h' x]
  simp

theorem restricts_agree {ρ ρ' : GalQ} {t : ClG n} (h : Restricts n ρ t) (h' : Restricts n ρ' t) :
    ∀ x ∈ hilbertBar n, ρ x = ρ' x := by
  intro x hx
  rw [hilbertBar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := h ⟨y, hy⟩
  have h2 := h' ⟨y, hy⟩
  change ρ (embed n y) = ρ' (embed n y)
  exact h1.trans h2.symm

/-- **An automorphism acting trivially on `H_n` and as `a ∈ Pic(𝒪_{n,4})` on `H_{n,4}` has `a ↦ 1` in
`Cl(K_n)`** (compatibility of the Artin maps, ring-class's `restrict_ringClassArtinEquiv`). -/
theorem picToMax_eq_one {σ : GalQ} (h1 : Restricts n σ 1) {a : Pic (O4 n)} (ha : ActsAsArtin4 σ n a) :
    picToMax (O4 n) a = 1 := by
  have hle := ringClassField_maximal_le (O4 n)
  refine picToMax_eq_one_of_fix (O4 n) a fun x => ?_
  have hc : ((IntermediateField.inclusion hle x : H4 n) : SeparableClosure (QNeg n)) =
      ((x : hilbertField n) : SeparableClosure (QNeg n)) := IntermediateField.coe_inclusion hle x
  have e1 := ha (IntermediateField.inclusion hle x)
  have e2 : σ (embed n ((x : hilbertField n) : SeparableClosure (QNeg n))) =
      embed n ((x : hilbertField n) : SeparableClosure (QNeg n)) := by
    rw [h1 x, AlgEquiv.one_apply]
  rw [hc] at e1
  apply Subtype.ext
  rw [hc]
  exact (embed n).injective (e1.symm.trans e2)

end Restr

/-! ## §2.3 TYZ Proposition 3.2(4), used form -/

theorem tauG_two_eq : tauG 2 = pt00 := by
  rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul, ptT_add_self]

theorem tauG_two_tors : IsOfFinAddOrder (tauG 2) :=
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, by rw [two_nsmul, tauG_two_eq, pt00_add_self]⟩

/-- **TYZ Proposition 3.2(4), the form the uniformization of `ε` uses**: for squarefree `n ≡ 5, 7 (mod 8)`
two lifts `ρ, ρ' ∈ Gal(ℚ̄/ℚ)` of the same `t ∈ Cl_n = Gal(H_n/K_n)` move `z_n` (`TYZ35.basePt n`) to
points that differ by a torsion point. TYZ Prop. 3.2(4) (`CM point1`, arXiv:1411.4728v1 about L1261, as
quoted in tyz-split.md and in the docstring of `TYZSplit.IsPhi`: `2z_n ∈ A(H_n)`) gives it at once; here it
is proved from the CM inputs: `Gal(H_{n,4}/H_n)` moves `z_n` by `ℤτ(1)` for `n ≡ 5` (kernel glue KER, from
Shimura reciprocity, TYZ Thm 3.6(1) in Lean and `z_n ∈ A(H_{n,4})`), and `z_n ∈ A(H_n)` for `n ≡ 7`. -/
def TYZProp324Used : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) → ∀ (t : ClG n) (ρ ρ' : GalQ),
    Restricts n ρ t → Restricts n ρ' t → IsOfFinAddOrder (galPt ρ (basePt n) - galPt ρ' (basePt n))

theorem tyzProp324Used_of (h : X0ModuliUsed.CMInputs) : TYZProp324Used := by
  intro n hn0 hsq hn8 t ρ ρ' hρ hρ'
  rcases hn8 with h5 | h7
  · have hb : basePt n = tyzZn n := by simp [basePt, h5]
    rw [hb]
    have hσ := restricts_inv_mul hρ hρ'
    have hω : (ρ'⁻¹ * ρ) (T321.omegaBar n) = T321.omegaBar n :=
      restricts_fix_sqrt_negn hσ T321.omegaBar_sq
    obtain ⟨a, ha⟩ := T321.exists_acts4_of_fix hω
    have hpa := picToMax_eq_one hσ ha
    obtain ⟨j, hj⟩ := kerFix h n hn0 h5 hsq a hpa _ ha
    have hρe : ρ = ρ' * (ρ'⁻¹ * ρ) := by group
    have : galPt ρ (tyzZn n) - galPt ρ' (tyzZn n) = j • tauG 2 := by
      conv_lhs => rw [hρe, galPt_mul, hj, map_add, map_zsmul, T321.galPt_tauG_two]
      abel
    rw [this]
    exact tauG_two_tors.zsmul
  · have hb : basePt n = tyzZ7 n := by
      have : n % 8 ≠ 5 := by omega
      simp [basePt, this]
    rw [hb]
    have hz := cmFieldOfDefinition7_of h.field n h7 hsq
    rw [galPt_congr (restricts_agree hρ hρ') hz, sub_self]
    exact IsOfFinAddOrder.zero


/-! # §3. Glue: `ε` before `Φ` (proved) -/

/-- Modulo torsion `P_χ` does not depend on `Φ` (from TYZ Prop. 3.2(4), used form). -/
theorem pchi_sub_tors (h324 : TYZProp324Used) {n : ℕ} [NeZero n] (hsq : Squarefree n)
    (hn8 : n % 8 = 5 ∨ n % 8 = 7) {φ φ' : ClG n → GalQ} (hφ : IsPhi n φ) (hφ' : IsPhi n φ')
    (χ : ClG n →* ℤˣ) : IsOfFinAddOrder (PchiGWith basePt n φ χ - PchiGWith basePt n φ' χ) := by
  unfold PchiGWith
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_induction _ IsOfFinAddOrder (fun a b ha hb => ha.add hb) IsOfFinAddOrder.zero
    (fun t _ => ?_)
  rw [← zsmul_sub]
  exact (h324 n inferInstance hsq hn8 t _ _ (hφ t) (hφ' t)).zsmul

theorem gsmul_sub (c : GaussianInt) (P R : PtA) : c • (P - R) = c • P - c • R := smul_sub c P R

theorem natCast_gsmul_tors (k : ℕ) {P : PtA} (h : IsOfFinAddOrder P) :
    IsOfFinAddOrder ((k : GaussianInt) • P) := by
  rw [Nat.cast_smul_eq_nsmul GaussianInt k P]
  exact h.nsmul

theorem radTYZ_ne_zero {n d₁ : ℕ} (h : d₁ ≠ 0) : radTYZ n d₁ ≠ 0 := by
  unfold radTYZ
  split_ifs <;> omega

/-- **`ε` can be chosen before `Φ`**: TYZ Theorem 3.3 in the printed quantifier order for the kernel's
`z_n`, with TYZ Prop. 3.2(4) (used form), gives the kernel's `TYZSplit.TYZThm33`. -/
theorem tyzThm33_of_epsAfter (h324 : TYZProp324Used) (h : TYZThm33EpsAfter basePt) : TYZThm33 := by
  classical
  intro ℓ hℓ
  obtain ⟨Q, m, hm, hQ, htors, hmain⟩ := h ℓ hℓ
  have key : ∀ d₀ d₁ : ℕ, ∃ e : GaussianInt, EpsClass d₀ d₁ e ∧
      ∀ (n : ℕ) (_ : NeZero n), d₀ * d₁ = n → Squarefree n → (n % 8 = 5 ∨ n % 8 = 7) →
        (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) → (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) →
        ∀ φ : ClG n → GalQ, IsPhi n φ → ∀ χ : ClG n →* ℤˣ, IsChiPair n d₁ χ →
          IsOfFinAddOrder ((m d₀ : GaussianInt) • PchiG n φ χ -
            (e * 2 ^ h2G n * (ℓ d₁ : GaussianInt)) • Q d₀) := by
    intro d₀ d₁
    by_cases H : ∃ (_ : NeZero (d₀ * d₁)) (χ : ClG (d₀ * d₁) →* ℤˣ), Squarefree (d₀ * d₁) ∧
        ((d₀ * d₁) % 8 = 5 ∨ (d₀ * d₁) % 8 = 7) ∧ (d₀ % 8 = 5 ∨ d₀ % 8 = 6 ∨ d₀ % 8 = 7) ∧
        (d₁ % 8 = 1 ∨ d₁ % 8 = 2 ∨ d₁ % 8 = 3) ∧ IsChiPair (d₀ * d₁) d₁ χ
    · obtain ⟨hnz, χ₀, hsq, hn8, h0, h1, hχ₀⟩ := H
      choose φ₀ hφ₀ using fun t : ClG (d₀ * d₁) => exists_restricts t
      obtain ⟨e, he, het⟩ := (hmain (d₀ * d₁) hnz hsq hn8 φ₀ hφ₀ χ₀).2 d₀ d₁ rfl h0 h1 hχ₀
      refine ⟨e, he, ?_⟩
      rintro n hnz' rfl - - - - φ hφ χ hχ
      have hd₁ : d₁ ≠ 0 := right_ne_zero_of_mul hnz.out
      have hχe : χ = χ₀ := isExtChar_unique (radTYZ_ne_zero hd₁) hχ hχ₀
      subst hχe
      have hdiff := natCast_gsmul_tors (m d₀) (pchi_sub_tors h324 hsq hn8 hφ hφ₀ χ)
      have e1 : (m d₀ : GaussianInt) • PchiG (d₀ * d₁) φ χ -
          (e * 2 ^ h2G (d₀ * d₁) * (ℓ d₁ : GaussianInt)) • Q d₀ =
          (m d₀ : GaussianInt) • (PchiGWith basePt (d₀ * d₁) φ χ - PchiGWith basePt (d₀ * d₁) φ₀ χ) +
          ((m d₀ : GaussianInt) • PchiGWith basePt (d₀ * d₁) φ₀ χ -
            (e * 2 ^ h2G (d₀ * d₁) * (ℓ d₁ : GaussianInt)) • Q d₀) := by
        rw [gsmul_sub, pchiGWith_basePt]
        abel
      rw [e1]
      exact hdiff.add het
    · refine ⟨if d₀ % 8 = 5 ∧ d₁ % 8 = 3 then gi else 1, ?_, ?_⟩
      · constructor <;> intro hc <;> simp [hc]
      · rintro n hnz rfl hsq hn8 h0 h1 φ hφ χ hχ
        exact absurd ⟨hnz, χ, hsq, hn8, h0, h1, hχ⟩ H
  choose ε hε hεt using key
  refine ⟨Q, m, ε, hm, hQ, fun d₀ d₁ _ _ => hε d₀ d₁, htors, ?_⟩
  intro n hnz hsq hn8 φ hφ χ
  exact ⟨(hmain n hnz hsq hn8 φ hφ χ).1,
    fun d₀ d₁ hd h0 h1 hχ => hεt d₀ d₁ n hnz hd hsq hn8 h0 h1 φ hφ χ hχ⟩

/-! # §4. Glue: the eta model of x0-32 is an identification `(X₀(32), ∞) ≅ (A, O)` (proved) -/

/-! ## §4.1 Pole orders of x0-32's `x` at the cusps of `Γ₀(32)` (Ligozat's orders, proved) -/

section Cusp

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- `gcd(δ, c)` for the lower-left entry `c` of `γ`. -/
abbrev gδ (δ : ℕ) (γ : SL(2, ℤ)) : ℕ := Nat.gcd δ (γ 1 0).natAbs

/-- `Shimura.exists_smul_decomp` with the exact imaginary part: `δ·γτ = γ'w`, `δ·Im w = gcd(δ, c)²·Im τ`. -/
theorem exists_smul_decomp_exact {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ (γ' : SL(2, ℤ)) (w : UpperHalfPlane), (δ : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) =
      ((γ' • w : UpperHalfPlane) : ℂ) ∧ w.im * δ = ((gδ δ γ : ℕ) : ℝ) ^ 2 * τ.im := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨p, u, s, v, g, t, e, hB, hp, hpt, hs, hst, hg0, he0, hge⟩ :=
    Shimura.exists_hermite (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) δ hdet (by exact_mod_cast hδ)
  have hgval : g = ((gδ δ γ : ℕ) : ℤ) := by
    have h1 : Int.gcd p s = 1 := Int.isCoprime_iff_gcd_eq_one.1 ⟨v, -u, by linear_combination hB⟩
    have h2 : Int.gcd (γ 0 0) (γ 1 0) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.1 ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩
    have h3 : Int.gcd ((δ : ℤ) * γ 0 0) (γ 1 0) = Int.gcd (p * g) (s * g) := by rw [hp, hs]
    rw [Int.gcd_mul_right, h1, one_mul] at h3
    have h4 : Int.gcd ((δ : ℤ) * γ 0 0) (γ 1 0) = Nat.gcd δ (γ 1 0).natAbs := by
      show Nat.gcd ((δ : ℤ) * γ 0 0).natAbs (γ 1 0).natAbs = _
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.Coprime.gcd_mul_right_cancel δ h2
    rw [h3] at h4
    rw [gδ, ← h4, Int.natAbs_of_nonneg hg0.le]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have heR : (0 : ℝ) < e := by exact_mod_cast he0
  have hgeR : (g : ℝ) * e = δ := by exact_mod_cast hge
  have hwim : 0 < (((g : ℂ) * τ + t) / e).im := by
    have : (((g : ℂ) * τ + t) / e).im = g * τ.im / e := by
      rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
      simp
    rw [this]; have := τ.im_pos; positivity
  let w : UpperHalfPlane := ⟨((g : ℂ) * τ + t) / e, hwim⟩
  have hwim' : w.im = g * τ.im / e := by
    show (((g : ℂ) * τ + t) / e).im = _
    rw [show (e : ℂ) = ((e : ℝ) : ℂ) by simp, Complex.div_ofReal_im]
    simp
  let γ' : SL(2, ℤ) := ⟨!![p, u; s, v], by rw [Matrix.det_fin_two_of]; exact hB⟩
  refine ⟨γ', w, ?_, ?_⟩
  · rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [γ', Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      algebraMap_int_eq, eq_intCast]
    have hden : ((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
      have := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
      simpa [ModularGroup.denom_apply] using this
    have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    have h1 : ((p : ℝ) : ℂ) * (w : ℂ) + ((u : ℝ) : ℂ) =
        δ * (((γ 0 0 : ℝ) : ℂ) * τ + ((γ 0 1 : ℝ) : ℂ)) / e := by
      show ((p : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((u : ℝ) : ℂ) = _
      field_simp
      have hp' : (p : ℂ) * g = δ * γ 0 0 := by exact_mod_cast hp
      have hpt' : (p : ℂ) * t + u * e = δ * γ 0 1 := by exact_mod_cast hpt
      push_cast
      linear_combination (τ : ℂ) * hp' + hpt'
    have h2 : ((s : ℝ) : ℂ) * (w : ℂ) + ((v : ℝ) : ℂ) =
        (((γ 1 0 : ℝ) : ℂ) * τ + ((γ 1 1 : ℝ) : ℂ)) / e := by
      show ((s : ℝ) : ℂ) * (((g : ℂ) * τ + t) / e) + ((v : ℝ) : ℂ) = _
      field_simp
      have hs' : (s : ℂ) * g = γ 1 0 := by exact_mod_cast hs
      have hst' : (s : ℂ) * t + v * e = γ 1 1 := by exact_mod_cast hst
      push_cast
      linear_combination (τ : ℂ) * hs' + hst'
    rw [h1, h2]
    field_simp
  · have hg' : (g : ℝ) = ((gδ δ γ : ℕ) : ℝ) := by rw [hgval]; push_cast; rfl
    rw [hwim', ← hgeR, ← hg']
    field_simp

/-- `|η(δγτ)|⁴·δ·Im(γτ) = H(w)` with `δ·Im w = gcd(δ, c)²·Im τ`. -/
theorem etaD_norm_exact {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ∃ w : UpperHalfPlane, ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) =
      Shimura.Hinv w ∧ w.im * δ = ((gδ δ γ : ℕ) : ℝ) ^ 2 * τ.im := by
  obtain ⟨γ', w, hw, h1⟩ := exists_smul_decomp_exact hδ γ τ
  refine ⟨w, ?_, h1⟩
  rw [← Shimura.Hinv_smul γ' w]
  unfold Shimura.Hinv X0.etaD
  rw [hw]
  congr 1
  have := congrArg Complex.im hw
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero] at this
  exact this

/-- `H(w) = e^{−π Im w/3}·P(w)·Im w` with `m ≤ P(w) ≤ M` for `Im w ≥ 1` (`P = |∏(1 − qⁿ)|⁴`). -/
theorem Hinv_exact :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ w : UpperHalfPlane, 1 ≤ w.im → ∃ P : ℝ, m ≤ P ∧ P ≤ M ∧
      Shimura.Hinv w = Real.exp (-(Real.pi * w.im / 3)) * P * w.im := by
  obtain ⟨m, M, hm, hM, hb⟩ := Shimura.exists_prodF_bounds
  refine ⟨m ^ 4, M ^ 4, by positivity, by positivity, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := hb _ (Shimura.norm_q_le w hw)
  refine ⟨‖X0.prodF (cexp (2 * Real.pi * I * (w : ℂ)))‖ ^ 4, pow_le_pow_left₀ hm.le h1 4,
    pow_le_pow_left₀ (norm_nonneg _) h2 4, ?_⟩
  unfold Shimura.Hinv
  rw [Shimura.eta_eq_prodF, norm_mul, mul_pow, Shimura.norm_qParam24_pow4]

/-- The exponent `32·S(c) = 32g₂² + 2g₁₆² − 8g₄² − 2g₃₂²` of `|x(γτ) − 2|⁴` (Ligozat's order formula). -/
def expS (γ : SL(2, ℤ)) : ℝ :=
  32 * ((gδ 2 γ : ℕ) : ℝ) ^ 2 + 2 * ((gδ 16 γ : ℕ) : ℝ) ^ 2 - 8 * ((gδ 4 γ : ℕ) : ℝ) ^ 2 -
    2 * ((gδ 32 γ : ℕ) : ℝ) ^ 2


theorem gratio_le {a b c d : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 2) (hb : 0 ≤ b) (hb2 : b ≤ 16)
    (hc : 1 ≤ c) (hd : 1 ≤ d) : ((a ^ 2) ^ 2 * b ^ 2) / (c ^ 2 * (d ^ 2) ^ 2) ≤ 4096 := by
  have a1 : (a ^ 2) ^ 2 ≤ 16 := by
    have := pow_le_pow_left₀ ha ha2 4
    calc (a ^ 2) ^ 2 = a ^ 4 := by ring
      _ ≤ 2 ^ 4 := this
      _ = 16 := by norm_num
  have a2 : b ^ 2 ≤ 256 := by
    have := pow_le_pow_left₀ hb hb2 2
    calc b ^ 2 ≤ 16 ^ 2 := this
      _ = 256 := by norm_num
  have hn : (a ^ 2) ^ 2 * b ^ 2 ≤ 4096 :=
    (mul_le_mul a1 a2 (by positivity) (by norm_num)).trans (by norm_num)
  have h1 : 1 ≤ c ^ 2 * (d ^ 2) ^ 2 := by
    have e1 : 1 ≤ c ^ 2 := one_le_pow₀ hc
    have e2 : 1 ≤ (d ^ 2) ^ 2 := one_le_pow₀ (one_le_pow₀ hd)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c ^ 2 * (d ^ 2) ^ 2 := mul_le_mul e1 e2 zero_le_one (by positivity)
  calc ((a ^ 2) ^ 2 * b ^ 2) / (c ^ 2 * (d ^ 2) ^ 2) ≤ ((a ^ 2) ^ 2 * b ^ 2) / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos h1
    _ ≤ 4096 := by rw [div_one]; exact hn

/-- **`|x(γτ) − 2|⁴ ≤ K·e^{−π Im τ·S(γ)/96}`** for `Im τ ≥ 32`, uniformly in `γ ∈ SL₂(ℤ)` (`S = expS γ`). -/
theorem xC_sub_two_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), 32 ≤ τ.im →
    ‖X0.xC ((γ • τ : UpperHalfPlane) : ℂ) - 2‖ ^ 4 ≤
      K * Real.exp (-(Real.pi * τ.im * expS γ / 96)) := by
  obtain ⟨m, M, hm, hM, hb⟩ := Hinv_exact
  refine ⟨64 * M ^ 3 / m ^ 3 * 64 * 4096, by positivity, fun γ τ hτ => ?_⟩
  have hT0 : 0 < τ.im := τ.im_pos
  set T := τ.im with hT
  have data : ∀ δ : ℕ, 0 < δ → δ ≤ 32 → ∃ P : ℝ, m ≤ P ∧ P ≤ M ∧
      ‖X0.etaD δ ((γ • τ : UpperHalfPlane) : ℂ)‖ ^ 4 * (δ * (γ • τ).im) =
        Real.exp (-(Real.pi * (((gδ δ γ : ℕ) : ℝ) ^ 2 * T / δ) / 3)) * P *
          (((gδ δ γ : ℕ) : ℝ) ^ 2 * T / δ) := by
    intro δ hδ hδ32
    obtain ⟨w, hw, hwim⟩ := etaD_norm_exact hδ γ τ
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    have hwim' : w.im = ((gδ δ γ : ℕ) : ℝ) ^ 2 * T / δ := by
      rw [eq_div_iff hδR.ne']; exact hwim
    have hg1 : (1 : ℝ) ≤ ((gδ δ γ : ℕ) : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left _ hδ
    have hw1 : 1 ≤ w.im := by
      rw [hwim', le_div_iff₀ hδR]
      have : (δ : ℝ) ≤ 32 := by exact_mod_cast hδ32
      nlinarith
    obtain ⟨P, h1, h2, hH⟩ := hb w hw1
    exact ⟨P, h1, h2, by rw [hw, hH, hwim']⟩
  obtain ⟨P2, l2, u2, e2⟩ := data 2 (by norm_num) (by norm_num)
  obtain ⟨P4, l4, u4, e4⟩ := data 4 (by norm_num) (by norm_num)
  obtain ⟨P16, l16, u16, e16⟩ := data 16 (by norm_num) (by norm_num)
  obtain ⟨P32, l32, u32, e32⟩ := data 32 (by norm_num) (by norm_num)
  set z : ℂ := ((γ • τ : UpperHalfPlane) : ℂ)
  set I0 := (γ • τ).im
  have hI : 0 < I0 := (γ • τ).im_pos
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) (γ • τ)
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) (γ • τ)
  have hx : X0.xC z - 2 = X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2) := by
    unfold X0.xC; ring
  rw [hx]
  have hnorm : ‖X0.etaD 2 z ^ 2 * X0.etaD 16 z / (X0.etaD 4 z * X0.etaD 32 z ^ 2)‖ ^ 4 =
      (‖X0.etaD 2 z‖ ^ 4) ^ 2 * ‖X0.etaD 16 z‖ ^ 4 /
        (‖X0.etaD 4 z‖ ^ 4 * (‖X0.etaD 32 z‖ ^ 4) ^ 2) := by
    simp only [norm_div, norm_mul, norm_pow]
    ring
  rw [hnorm]
  set A2 := ‖X0.etaD 2 z‖ ^ 4
  set A4 := ‖X0.etaD 4 z‖ ^ 4
  set A16 := ‖X0.etaD 16 z‖ ^ 4
  set A32 := ‖X0.etaD 32 z‖ ^ 4
  have p4 : 0 < A4 := by have := norm_pos_iff.2 n4; positivity
  have p32 : 0 < A32 := by have := norm_pos_iff.2 n32; positivity
  set g2 : ℝ := ((gδ 2 γ : ℕ) : ℝ)
  set g4 : ℝ := ((gδ 4 γ : ℕ) : ℝ)
  set g16 : ℝ := ((gδ 16 γ : ℕ) : ℝ)
  set g32 : ℝ := ((gδ 32 γ : ℕ) : ℝ)
  have hg4 : 1 ≤ g4 := by
    show (1 : ℝ) ≤ ((Nat.gcd 4 (γ 1 0).natAbs : ℕ) : ℝ)
    exact_mod_cast Nat.gcd_pos_of_pos_left (γ 1 0).natAbs (by norm_num : 0 < 4)
  have hg32 : 1 ≤ g32 := by
    show (1 : ℝ) ≤ ((Nat.gcd 32 (γ 1 0).natAbs : ℕ) : ℝ)
    exact_mod_cast Nat.gcd_pos_of_pos_left (γ 1 0).natAbs (by norm_num : 0 < 32)
  have hg2 : 0 ≤ g2 ∧ g2 ≤ 2 := ⟨by positivity, by
    show ((Nat.gcd 2 (γ 1 0).natAbs : ℕ) : ℝ) ≤ 2
    exact_mod_cast Nat.gcd_le_left (γ 1 0).natAbs (by norm_num : 0 < 2)⟩
  have hg16 : 0 ≤ g16 ∧ g16 ≤ 16 := ⟨by positivity, by
    show ((Nat.gcd 16 (γ 1 0).natAbs : ℕ) : ℝ) ≤ 16
    exact_mod_cast Nat.gcd_le_left (γ 1 0).natAbs (by norm_num : 0 < 16)⟩
  set E2 := Real.exp (-(Real.pi * (g2 ^ 2 * T / (2 : ℕ)) / 3))
  set E4 := Real.exp (-(Real.pi * (g4 ^ 2 * T / (4 : ℕ)) / 3))
  set E16 := Real.exp (-(Real.pi * (g16 ^ 2 * T / (16 : ℕ)) / 3))
  set E32 := Real.exp (-(Real.pi * (g32 ^ 2 * T / (32 : ℕ)) / 3))
  set Ee := Real.exp (-(Real.pi * T * expS γ / 96))
  have hE : E2 ^ 2 * E16 = Ee * E4 * E32 ^ 2 := by
    simp only [E2, E4, E16, E32, Ee, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [expS, g2, g4, g16, g32]
    push_cast
    ring
  have hE2 : 0 < E2 := Real.exp_pos _
  have hE4 : 0 < E4 := Real.exp_pos _
  have hE16 : 0 < E16 := Real.exp_pos _
  have hE32 : 0 < E32 := Real.exp_pos _
  have hEe' : Ee = E2 ^ 2 * E16 / (E4 * E32 ^ 2) := by
    rw [hE]; field_simp
  have eA2 : A2 = E2 * P2 * (g2 ^ 2 * T / (2 : ℕ)) / ((2 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e2
  have eA4 : A4 = E4 * P4 * (g4 ^ 2 * T / (4 : ℕ)) / ((4 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e4
  have eA16 : A16 = E16 * P16 * (g16 ^ 2 * T / (16 : ℕ)) / ((16 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e16
  have eA32 : A32 = E32 * P32 * (g32 ^ 2 * T / (32 : ℕ)) / ((32 : ℕ) * I0) := by
    rw [eq_div_iff (by positivity)]; exact e32
  have hP4 : 0 < P4 := lt_of_lt_of_le hm l4
  have hP32 : 0 < P32 := lt_of_lt_of_le hm l32
  have hg4' : 0 < g4 := by linarith
  have hg32' : 0 < g32 := by linarith
  have hiden : A2 ^ 2 * A16 / (A4 * A32 ^ 2) = E2 ^ 2 * E16 / (E4 * E32 ^ 2) *
      (4096 * ((P2 ^ 2 * P16) / (P4 * P32 ^ 2)) * (((g2 ^ 2) ^ 2 * g16 ^ 2) / (g4 ^ 2 * (g32 ^ 2) ^ 2))) := by
    rw [eA2, eA4, eA16, eA32]
    push_cast
    field_simp
    ring
  rw [hiden, hEe', mul_comm (64 * M ^ 3 / m ^ 3 * 64 * 4096)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hPr : (P2 ^ 2 * P16) / (P4 * P32 ^ 2) ≤ M ^ 3 / m ^ 3 := by
    have hPa : P2 ^ 2 * P16 ≤ M ^ 3 := by
      have : 0 ≤ P2 := (hm.trans_le l2).le
      have : 0 ≤ P16 := (hm.trans_le l16).le
      calc P2 ^ 2 * P16 ≤ M ^ 2 * M := by gcongr
        _ = M ^ 3 := by ring
    have hPb : m ^ 3 ≤ P4 * P32 ^ 2 := by
      calc m ^ 3 = m * m ^ 2 := by ring
        _ ≤ P4 * P32 ^ 2 := by gcongr
    exact div_le_div₀ (by positivity) hPa (by positivity) hPb
  have hgr := gratio_le hg2.1 hg2.2 hg16.1 hg16.2 hg4 hg32
  calc 4096 * ((P2 ^ 2 * P16) / (P4 * P32 ^ 2)) * (((g2 ^ 2) ^ 2 * g16 ^ 2) / (g4 ^ 2 * (g32 ^ 2) ^ 2))
      ≤ 4096 * (M ^ 3 / m ^ 3) * 4096 := by gcongr
    _ = 64 * M ^ 3 / m ^ 3 * 64 * 4096 := by ring

/-- `f =O[atImInfty] g` from `|f − c|⁴ ≤ K g⁴` for `Im τ ≥ 32` and `g ≥ 1` (Shimura's `bigO_of_pow4`,
for a general majorant). -/
theorem bigO_of_pow4' {f : UpperHalfPlane → ℂ} {g : UpperHalfPlane → ℝ} {K : ℝ} (hK : 0 ≤ K) (c : ℂ)
    (hg : ∀ τ, 1 ≤ g τ) (h : ∀ τ : UpperHalfPlane, 32 ≤ τ.im → ‖f τ - c‖ ^ 4 ≤ K * g τ ^ 4) :
    f =O[atImInfty] g := by
  refine Asymptotics.IsBigO.of_bound (K + 1 + ‖c‖) ?_
  rw [Filter.eventually_iff, atImInfty_mem]
  refine ⟨32, fun τ hτ => ?_⟩
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs]
  set E := g τ
  have hE1 : 1 ≤ E := hg τ
  rw [abs_of_pos (lt_of_lt_of_le one_pos hE1)]
  have h1 : ‖f τ - c‖ ≤ (K + 1) * E := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity) ?_
    calc ‖f τ - c‖ ^ 4 ≤ K * E ^ 4 := h τ hτ
      _ ≤ (K + 1) ^ 4 * E ^ 4 := by
          gcongr
          exact (by linarith : K ≤ K + 1).trans (le_self_pow₀ (by linarith) (by norm_num))
      _ = ((K + 1) * E) ^ 4 := by ring
  calc ‖f τ‖ = ‖(f τ - c) + c‖ := by ring_nf
    _ ≤ ‖f τ - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (K + 1) * E + ‖c‖ * E := by gcongr; nlinarith [norm_nonneg c]
    _ = (K + 1 + ‖c‖) * E := by ring

theorem gcd_mod32 (δ n : ℕ) (hδ : δ ∣ 32) : Nat.gcd δ n = Nat.gcd δ (n % 32) := by
  calc Nat.gcd δ n = Nat.gcd (n % δ) δ := Nat.gcd_rec δ n
    _ = Nat.gcd (n % 32 % δ) δ := by rw [Nat.mod_mod_of_dvd n hδ]
    _ = Nat.gcd δ (n % 32) := (Nat.gcd_rec δ (n % 32)).symm

theorem expS_table : ∀ r : ℕ, r < 32 → r ≠ 0 →
    2 * Nat.gcd 32 r ^ 2 + 8 * Nat.gcd 4 r ^ 2 ≤ 32 * Nat.gcd 2 r ^ 2 + 2 * Nat.gcd 16 r ^ 2 := by
  decide +kernel

/-- **Ligozat's order of `x` at the cusp `γ∞` is `≥ 0` when `32 ∤ c`.** -/
theorem expS_nonneg (γ : SL(2, ℤ)) (h : ¬ (32 : ℤ) ∣ γ 1 0) : 0 ≤ expS γ := by
  set n := (γ 1 0).natAbs
  have hr : n % 32 ≠ 0 := by
    intro h0
    apply h
    exact Int.natCast_dvd.2 (Nat.dvd_of_mod_eq_zero h0)
  have ht := expS_table (n % 32) (Nat.mod_lt _ (by norm_num)) hr
  have e2 := gcd_mod32 2 n (by norm_num)
  have e4 := gcd_mod32 4 n (by norm_num)
  have e16 := gcd_mod32 16 n (by norm_num)
  have e32 := gcd_mod32 32 n (by norm_num)
  rw [← e2, ← e4, ← e16, ← e32] at ht
  have ht' : (2 * (Nat.gcd 32 n : ℝ) ^ 2 + 8 * (Nat.gcd 4 n : ℝ) ^ 2) ≤
      32 * (Nat.gcd 2 n : ℝ) ^ 2 + 2 * (Nat.gcd 16 n : ℝ) ^ 2 := by exact_mod_cast ht
  simp only [expS, gδ]
  linarith

theorem expS_one : expS 1 = -1536 := by
  simp only [expS, gδ]
  norm_num

/-- **`x` has at most a double pole at `∞`**: `x(τ) = O(e^{4π Im τ})`. -/
theorem xC_bigO_atImInfty : (fun τ : UpperHalfPlane => X0.xC τ) =O[atImInfty]
    fun τ => Real.exp (4 * Real.pi * τ.im) := by
  obtain ⟨K, hK, hb⟩ := xC_sub_two_bound
  refine bigO_of_pow4' hK 2 (fun τ => Real.one_le_exp (by have := τ.im_pos; positivity))
    fun τ hτ => ?_
  have h := hb 1 τ hτ
  rw [one_smul, expS_one] at h
  refine h.trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **`x` is bounded at every cusp `γ∞` not equivalent to `∞`** (`32 ∤ c`). -/
theorem xC_bounded_cusp (γ : SL(2, ℤ)) (h : ¬ (32 : ℤ) ∣ γ 1 0) :
    IsBoundedAtImInfty (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) := by
  obtain ⟨K, hK, hb⟩ := xC_sub_two_bound
  have hS := expS_nonneg γ h
  have : (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane)) =O[atImInfty]
      fun _ => (1 : ℝ) := by
    refine bigO_of_pow4' hK 2 (fun _ => le_rfl) fun τ hτ => ?_
    refine (hb γ τ hτ).trans ?_
    rw [one_pow, mul_one]
    have : Real.exp (-(Real.pi * τ.im * expS γ / 96)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := τ.im_pos
      have := Real.pi_pos
      have : 0 ≤ Real.pi * τ.im * expS γ := by positivity
      linarith
    nlinarith
  exact this

end Cusp

/-! ## §4.2 The pole bounds as one statement -/

/-- Pole bounds of x0-32's `x`: at most a double pole at `∞`, bounded at every other cusp. -/
def EtaCuspBounds : Prop :=
  ((fun τ : UpperHalfPlane => X0.xC τ) =O[UpperHalfPlane.atImInfty]
      fun τ => Real.exp (4 * Real.pi * τ.im)) ∧
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ¬ (32 : ℤ) ∣ γ 1 0 →
      UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => X0.xC (γ • τ : UpperHalfPlane))

/-- **The eta model has the pole structure of an identification** (proved, §C0). -/
theorem etaCuspBounds : EtaCuspBounds := ⟨xC_bigO_atImInfty, xC_bounded_cusp⟩

/-- `x` is unbounded at `∞` (`|x(it)| → ∞`, x0-32's `tendsto_norm_xC_atTop`). -/
theorem not_bounded_xC : ¬ UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => X0.xC τ) := by
  intro hb
  obtain ⟨M, A, hMA⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.1 hb
  obtain ⟨t, ht⟩ := ((X0.tendsto_norm_xC_atTop.eventually_gt_atTop M).and
    (Filter.eventually_ge_atTop (max A 1))).exists
  have htpos : 0 < t := lt_of_lt_of_le one_pos ((le_max_right A 1).trans ht.2)
  have hτ : 0 < ((t : ℂ) * Complex.I).im := by simpa using htpos
  have := hMA ⟨(t : ℂ) * Complex.I, hτ⟩ (by
    show A ≤ ((t : ℂ) * Complex.I).im
    simpa using (le_max_left A 1).trans ht.2)
  exact absurd this (not_le.2 ht.1)

/-! ## §4.3 The eta model is such an identification -/

/-- **The eta-quotient model `phiC = (x, y)` of x0-32 is an identification `(X₀(32), ∞) ≅ (A, O)` in the
sense of `IsX0Identification`.** -/
theorem isX0Identification_eta (hc : EtaCuspBounds) :
    IsX0Identification (fun τ => X0.xC τ) (fun τ => X0.yC τ) := by
  refine ⟨X0ModuliUsed.isRatModFn_x, X0ModuliUsed.isRatModFn_y, fun τ => Shimura.etaModelEquation τ,
    not_bounded_xC, hc.1, hc.2⟩

/-! # §5. The contribution -/


/-- **`TYZSplit.TYZThm33` from TYZ Theorem 3.3 in its printed form** (and the printed main theorem of CM
`hCM`, already a hypothesis of `frozenTarget`). -/
theorem tyzThm33_of_printed (hCM : T5Glue.ShimuraMainCM) (h : TYZThm33Printed) : TYZThm33 := by
  have hI := cmInputs hCM
  apply tyzThm33_of_epsAfter (tyzProp324Used_of hI)
  let w : ℕ → PtA := fun n => if n % 8 = 5 then tyzHeegnerPt n else tyzZ7 n
  have hz : zOfLift w = basePt := by
    funext n
    by_cases h5 : n % 8 = 5 <;> simp [zOfLift, w, basePt, h5, tyzZn]
  rw [← hz]
  refine h _ _ (isX0Identification_eta etaCuspBounds) w ?_ ?_
  · intro n hn _
    have e : w n = heegnerPt (tyzForm n hn) := by simp [w, hn, tyzHeegnerPt]
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)
  · intro n hn _
    have h5 : n % 8 ≠ 5 := by omega
    have e : w n = heegnerPt (tyzForm7 n hn) := by simp [w, tyzZ7, hn]
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)


/-- **The leaf's hypotheses are satisfiable** (so `TYZThm33Printed` is not vacuous): the eta model is an
identification and, given `hCM`, its values at the CM points `τ_n` are algebraic. -/
theorem tyzThm33Printed_hyps_satisfiable (hCM : T5Glue.ShimuraMainCM) :
    ∃ X Y : UpperHalfPlane → ℂ, IsX0Identification X Y ∧ ∃ w : ℕ → PtA,
      (∀ n : ℕ, ∀ hn : n % 8 = 5, Squarefree n → toC (w n) = ptOf X Y (tyzForm n hn).tauH) ∧
      (∀ n : ℕ, ∀ hn : n % 8 = 7, Squarefree n → toC (w n) = ptOf X Y (tyzForm7 n hn).tauH) := by
  have hI := cmInputs hCM
  refine ⟨_, _, isX0Identification_eta etaCuspBounds,
    fun n => if n % 8 = 5 then tyzHeegnerPt n else tyzZ7 n, fun n hn _ => ?_, fun n hn _ => ?_⟩
  · have e : (if n % 8 = 5 then tyzHeegnerPt n else tyzZ7 n) = heegnerPt (tyzForm n hn) := by
      simp [hn, tyzHeegnerPt]
    beta_reduce
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)
  · have h5 : n % 8 ≠ 5 := by omega
    have e : (if n % 8 = 5 then tyzHeegnerPt n else tyzZ7 n) = heegnerPt (tyzForm7 n hn) := by
      simp [h5, tyzZ7, hn]
    beta_reduce
    rw [e]
    exact toC_heegnerPt _ (hI.alg _ _)

end ZInQ.Contrib.TYZGenus.H33Dict

namespace CloudB3SC7H33

/-- The exact `h33` target, conditionally reduced to the existing CM input and printed TYZ Theorem 3.3.
The complete reduction above is reused from project revision d489fc13; no new Gross–Zagier proof or
unconditional closure of either premise is claimed. -/
theorem h33_proof (hCM : _root_.T5Glue.ShimuraMainCM)
    (hPrinted : ZInQ.Contrib.TYZGenus.H33Dict.TYZThm33Printed) :
    ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33 :=
  ZInQ.Contrib.TYZGenus.H33Dict.tyzThm33_of_printed hCM hPrinted

end CloudB3SC7H33
