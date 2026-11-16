import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.GZStatements.Hensel
import ZInQKernel.Contrib.TYZGenus.CM
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Modular

/-!
# gz-hl3: `GZDecomp.GrossZagierHeegner` (`hL3`) from the Gross–Zagier formula, Gross's conjugation
relation and the Heegner point, over genuine definitions

Task gz-hl3 (2026-11-15). Report: `docs/research/gz-hl3.md`; scratch and log: `scratch/gz-hl3/`.

`ZInQ.GZDecomp.GrossZagierHeegner` (`hL3` of `ZInQ.OneProof.frozenTarget`) folded the Heegner point,
the modular parametrization and the Gross–Zagier formula into one statement about `E(K)`. This
file states them separately, over genuine definitions, and proves `hL3` from them:

* §1 objects: the Eichler integral `φ_f(τ) = Σ aₙ/n qⁿ` (`eichler`), `c Λ_f ⊆ L` (`PeriodsIn`), the
  period lattice of `E` (`IsPeriodLattice`: `g₂ = c₄/12`, `g₃ = c₆/216`, Mathlib's `PeriodPair`), the
  point `(℘(z) − b₂/12, (℘'(z) − a₁x − a₃)/2)` of `E(ℂ)` (`weierPt`; on the curve: `weierPt_some`),
  Heegner forms (the kernel's `TYZGenus.CM.HeegnerForm N D`, `N ∣ A`, `B² − 4AC = D`) with residue
  `B ≡ β (mod 2N)`, `Γ₀(N)`-classes, complete sets of representatives (`IsHeegnerReps`), and the
  Heegner point `Σ_{Q ∈ S} φ(τ_Q) ∈ E(ℂ)` (`heegnerC`); the canonical height is Tau Ceti's;
* §2 the leaves (`def … : Prop`): `WeierstrassUniformization`, `StrongWeilCurve`
  (Eichler–Shimura), `IsogenyLattice` (Faltings), `HeegnerPointRational` (Shimura reciprocity /
  Gross), `GrossZagierFormula` (GZ I.6.3 and Ch. V, positive constant forgotten),
  `GrossConjugation` (Gross 1984 §5);
* §3 glue, proved: Heegner representatives exist (`heegnerRepsExist`: reduction to the fundamental
  domain of `SL₂(ℤ)`, the transform of forms, `[SL₂(ℤ) : Γ₀(N)] < ∞`);
* §4 glue lemmas; §5 `grossZagierHeegner_of_leaves`.

The `C_d` form (`GZStatements.GrossZagierHeegnerCd`) is in `GrossZagierHeegner/Cd.lean`.
No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine Modular MatrixGroups

namespace ZInQ.GZHL3

/-! ## §1. Objects -/

/-- **The Eichler integral** `φ_f(τ) = 2πi ∫_{i∞}^{τ} f(z) dz = Σ_{n ≥ 1} aₙ(f)/n · e^{2πinτ}` of a
weight-2 newform. -/
def eichler {N : ℕ} [NeZero N] (f : Newform N 2) (τ : ℍ) : ℂ :=
  ∑' n : ℕ, coeff f (n + 1) / ((n : ℂ) + 1) *
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * (τ : ℂ))

/-- **`c · Λ_f ⊆ L`**, where `Λ_f = {φ_f(γτ) − φ_f(τ) : γ ∈ Γ₀(N)}` is the period lattice of
`2πi f(τ) dτ` (independent of `τ`): `z ↦ c z` induces `Γ₀(N)\ℍ → ℂ/L`, `τ ↦ c φ_f(τ)`. -/
def PeriodsIn {N : ℕ} [NeZero N] (f : Newform N 2) (c : ℂ) (L : PeriodPair) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, c * (eichler f (γ • τ) - eichler f τ) ∈ L.lattice

/-- **`L` is the period lattice of `E` over `ℂ`** (for the invariant differential
`dx/(2y + a₁x + a₃)` of the given model): `g₂(L) = c₄/12`, `g₃(L) = c₆/216`, i.e.
`(x, y) = (℘_L(z) − b₂/12, (℘'_L(z) − a₁x − a₃)/2)` maps `ℂ/L` onto `E(ℂ)`. -/
def IsPeriodLattice (E : WeierstrassCurve ℚ) (L : PeriodPair) : Prop :=
  L.g₂ = (E⁄ℂ).c₄ / 12 ∧ L.g₃ = (E⁄ℂ).c₆ / 216

open Classical in
/-- **The point of `E(ℂ)` with parameter `z ∈ ℂ/L`**: `(℘_L(z) − b₂/12, (℘'_L(z) − a₁x − a₃)/2)`,
and `O` for `z ∈ L` (for `IsPeriodLattice E L` the `else` branch is only taken at `z ∈ L`:
`weierPt_some`). -/
def weierPt (E : WeierstrassCurve ℚ) (L : PeriodPair) (z : ℂ) : (E⁄ℂ).Point :=
  if h : z ∉ L.lattice ∧ (E⁄ℂ).Nonsingular (L.weierstrassP z - (E⁄ℂ).b₂ / 12)
      ((L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - (E⁄ℂ).b₂ / 12) - (E⁄ℂ).a₃) / 2)
  then .some _ _ h.2 else 0

/-- `Q = [A, B, C]` has **residue `β`**: `B ≡ β (mod 2N)`. -/
def HasResidue {N : ℕ} {D : ℤ} (β : ℤ) (Q : HeegnerForm N D) : Prop := (2 * N : ℤ) ∣ Q.B - β

/-- `τ_Q` and `τ_{Q'}` are **`Γ₀(N)`-equivalent**. -/
def Gamma0Equiv {N : ℕ} {D : ℤ} (Q Q' : HeegnerForm N D) : Prop :=
  ∃ γ ∈ CongruenceSubgroup.Gamma0 N, γ • Q.tauH = Q'.tauH

/-- **A complete set of representatives of the Heegner points of discriminant `D` and residue
`β`**: forms `[A, B, C]`, `N ∣ A`, `B ≡ β (mod 2N)`, `B² − 4AC = D`, one in each
`Γ₀(N)`-class. -/
def IsHeegnerReps (N : ℕ) (D β : ℤ) (S : Finset (HeegnerForm N D)) : Prop :=
  (∀ Q ∈ S, HasResidue β Q) ∧
    ∀ Q : HeegnerForm N D, HasResidue β Q → ∃! Q', Q' ∈ S ∧ Gamma0Equiv Q Q'

/-- **The Heegner point `y_K = Σ_{σ ∈ Gal(H/K)} φ(x₁)^σ` in `E(ℂ)`**, for the parametrization
`φ(τ) = weierPt E L (c φ_f(τ))`: `Σ_{Q ∈ S} φ(τ_Q)`. -/
def heegnerC (E : WeierstrassCurve ℚ) (L : PeriodPair) {N : ℕ} [NeZero N] (f : Newform N 2)
    (c : ℂ) {D : ℤ} (S : Finset (HeegnerForm N D)) : (E⁄ℂ).Point :=
  ∑ Q ∈ S, weierPt E L (c * eichler f Q.tauH)

/-! ## §2. The leaves

Each Heegner-point leaf is stated for one curve `E` (`…At E`) and then for every elliptic curve
over `ℚ`; the `C_d`-restricted forms (`…Cd`) are in §6. -/

/-- **Uniformization.** For `a, b ∈ ℂ` with `a³ − 27b² ≠ 0` there is a lattice `L` with
`g₂(L) = a`, `g₃(L) = b`. J. Silverman, *The Arithmetic of Elliptic Curves* (GTM 106, 2nd ed.,
2009), Thm VI.5.1 (UNVERIFIED number); J.-P. Serre, *A Course in Arithmetic*, Ch. VII §3
(UNVERIFIED). -/
def WeierstrassUniformization : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b

/-- **Modular parametrization of `E` in analytic form**: if `E/ℚ` has the L-series of a weight-2
newform `f` of level `N` and trivial character and `L` is the period lattice of `E`, there is a
rational `c ≠ 0` with `c Λ_f ⊆ L`; then `τ ↦ weierPt E L (c φ_f(τ))` is a modular
parametrization `X₀(N) → E` defined over `ℚ`, with `φ^*ω = c · 2πi f(τ) dτ`. Proved from
`StrongWeilCurve` and `IsogenyLattice` (`eichlerShimuraParamAt_of_leaves`); for `C_d` it is
Shimura's theorem for CM curves (§6). -/
def EichlerShimuraParamAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ L : PeriodPair, IsPeriodLattice E L → ∃ c : ℚ, c ≠ 0 ∧ PeriodsIn f c L

/-- **Eichler–Shimura: the strong Weil curve of a rational newform.** For a weight-2 newform `f`
of level `N`, trivial character and rational coefficients, there is an elliptic curve `E'/ℚ` with
`aₙ(E') = aₙ(f)` for all `n ≥ 1`, and its period lattice contains `c Λ_f` for a rational `c ≠ 0`.

Content: `Λ_f` is a lattice and `ℂ/Λ_f` is the complex torus of the optimal quotient `E_f` of
`J₀(N)`, defined over `ℚ`, with `L(E_f, s) = L(f, s)` (G. Shimura, *Introduction to the arithmetic
theory of automorphic functions*, 1971, Thm 7.14 and §7.5, UNVERIFIED numbers; Diamond–Shurman,
*A first course in modular forms*, Thm 6.6.6 and §8.8, UNVERIFIED); the pullback of the
invariant differential of `E_f` under `X₀(N) → E_f` is `c_E · 2πi f(τ) dτ` with the Manin
constant `c_E ∈ ℚ^×` (rational `q`-expansion; Manin, Russian Math. Surveys 27 (1972), UNVERIFIED). -/
def StrongWeilCurve : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → ∃ q : ℚ, coeff f n = q) →
    ∃ E' : WeierstrassCurve ℚ, E'.IsElliptic ∧ (∀ n : ℕ, n ≠ 0 → coeff f n = (E'.LFunction n : ℂ)) ∧
      ∀ L' : PeriodPair, IsPeriodLattice E' L' → ∃ c : ℚ, c ≠ 0 ∧ PeriodsIn f c L'

/-- **Faltings' isogeny theorem, in analytic form.** If `E, E'/ℚ` are elliptic curves with the
same L-series, and `L, L'` are their period lattices, then `m L' ⊆ L` for a rational `m ≠ 0`.

Content: `E` and `E'` are isogenous over `ℚ` (G. Faltings, Invent. Math. 73 (1983), 349–366,
Korollar 2, UNVERIFIED number); an isogeny `α : E' → E` is `z ↦ m z` on `ℂ/L' → ℂ/L` with
`α^*ω_E = m ω_{E'}` (Silverman, AEC, Thm VI.4.1 and Cor. III.5.3, UNVERIFIED numbers), and
`m ∈ ℚ` since `α` and the invariant differentials are defined over `ℚ`. -/
def IsogenyLattice : Prop :=
  ∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic],
    (∀ n : ℕ, n ≠ 0 → E.LFunction n = E'.LFunction n) →
    ∀ L L' : PeriodPair, IsPeriodLattice E L → IsPeriodLattice E' L' →
      ∃ m : ℚ, m ≠ 0 ∧ ∀ z ∈ L'.lattice, (m : ℂ) * z ∈ L.lattice

/-- **Rationality of the Heegner point (Shimura's reciprocity law for CM points; Gross).**
Heegner setting: `E/ℚ` with the L-series of a newform `f` of level `N`, trivial character; an
odd fundamental discriminant `D < −4` with every `p ∣ N` split in `ℚ(√D)`; `β` with
`β² ≡ D (mod 4N)`; a complete set `S` of representatives of the Heegner points of discriminant
`D` and residue `β` (`IsHeegnerReps`); the modular parametrization `φ(τ) = weierPt E L (c φ_f(τ))`,
`c ∈ ℚ^×`, `c Λ_f ⊆ L`; `K = ℚ(√D)` embedded by `ι(√D) = i√|D|`. Then `Σ_{Q ∈ S} φ(τ_Q) ∈ E(ℂ)` is
the image of a point of `E(K)`: it is `y_K = Tr_{H/K} φ(x₁)` for the Heegner point
`x₁ = (𝒪_K, 𝔫, [𝒪_K])`, `𝔫 = (N, (β + √D)/2)`, because `Gal(H/K) ≅ Cl(K)` permutes the `h(D)`
Heegner points of residue `β` simply transitively and `φ` is defined over `ℚ`.

Sources: B. Gross, *Heegner points on X₀(N)*, in *Modular forms* (Durham 1983), Ellis Horwood
1984, §1–§3 (UNVERIFIED); Gross–Zagier, Invent. Math. 84 (1986), Ch. II §1 and Ch. V §1
(UNVERIFIED); Shimura 1971, Thm 5.4 and §6.8 (UNVERIFIED). -/
def HeegnerPointRationalAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℚ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
      ∃ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S

/-- `HeegnerPointRationalAt` for every elliptic curve over `ℚ`. -/
def HeegnerPointRational : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], HeegnerPointRationalAt E

/-- **The Gross–Zagier formula (Ch. V form, constant forgotten).** In the Heegner setting, let
`y ∈ E(K)` be the Heegner point (`ι(y) = Σ_{Q ∈ S} φ(τ_Q)`), and let `F`, `G` be the entire
continuations of `L(f, s) = L(E, s)` and of `L(f ⊗ χ_D, s) = Σ aₙ(f) χ_D(n) n^{−s}`, so that
`F G = L(E/K, s)`. Then `L'(E/K, 1) = κ · ĥ(y)` for some real `κ > 0`.

Source: B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
225–320: Thm I.6.3 (`L'(f, χ, 1) = 8π²(f, f) ĥ(c_{χ,f}) / (h u² √|D|)` for the `f`-isotypic
component of the Heegner divisor in `J₀(N)(H) ⊗ ℂ`) and its consequence for `E`, Ch. V Thm 2.1
(`L'(E/K, 1) = ‖ω‖² ĥ(y_K) / (c² u² √|D|)`-type formula with an explicit positive constant);
all numbers and the constant UNVERIFIED. Weaker than the print: the printed positive constant is
replaced by `∃ κ > 0` (this also absorbs the normalization of Tau Ceti's `canonicalHeight` over
`K` and the degree of `φ`); folded in: `L(E/K, s) = L(f, s) L(f ⊗ χ_D, s)` for `(D, N) = 1`
(GZ Ch. I, UNVERIFIED locator; textbook). -/
def GrossZagierFormulaAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℚ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight

/-- `GrossZagierFormulaAt` for every elliptic curve over `ℚ`. -/
def GrossZagierFormula : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], GrossZagierFormulaAt E

/-- **Gross's conjugation relation** `ȳ_K = −ε y_K` modulo torsion, `ε` the sign of the functional
equation of `L(E, s)` (`rootNumber f hχ`, the sign in `Λ_N(2 − s) = ε Λ_N(s)`). In the Heegner
setting, with `y ∈ E(K)` the Heegner point and `σ` the nontrivial automorphism of `K`
(`σ(√D) = −√D`): `σ y + y` is torsion if `ε = +1`, and `σ y − y` is torsion if `ε = −1`.

Source: B. Gross, *Heegner points on X₀(N)* (1984), §5 (UNVERIFIED): complex conjugation and
`w_N` act on Heegner points by `(𝒪, 𝔫, [𝔞]) ↦ (𝒪, 𝔫̄, [𝔞⁻¹])` and `(𝒪, 𝔫̄, [𝔞 𝔫⁻¹])`, and
`φ ∘ w_N = −ε φ + (torsion)`; restated in Gross–Zagier 1986, Ch. V §2 (UNVERIFIED). -/
def GrossConjugationAt (E : WeierstrassCurve ℚ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1),
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D β : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∀ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S →
    ∀ (L : PeriodPair) (c : ℚ), IsPeriodLattice E L → c ≠ 0 → PeriodsIn f c L →
    ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K], Module.finrank ℚ K = 2 →
    ∀ δ : K, δ ^ 2 = (D : K) →
    ∀ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) →
    ∀ y : (E⁄K).Point, Affine.Point.map ι y = heegnerC E L f c S →
    ∀ σ : K ≃ₐ[ℚ] K, σ δ = -δ →
      (rootNumber f hχ = 1 → IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y + y)) ∧
      (rootNumber f hχ = -1 → IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y))

/-- `GrossConjugationAt` for every elliptic curve over `ℚ`. -/
def GrossConjugation : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], GrossConjugationAt E

/-- **(GLUE) Heegner representatives exist**: the Heegner points of discriminant `D` and residue
`β` fall into finitely many `Γ₀(N)`-classes (`h(D)` of them). Gross 1984 §1, GZ II §1
(UNVERIFIED); provable from reduction theory (`SL₂(ℤ)`-classes of forms of discriminant `D` are
finite, `[SL₂(ℤ) : Γ₀(N)] < ∞`). -/
def HeegnerRepsExist : Prop :=
  ∀ (N : ℕ) [NeZero N] (D β : ℤ), IsOddImagFundDisc D → (4 * N : ℤ) ∣ D - β ^ 2 →
    ∃ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S

/-! ## §3. Glue: Heegner representatives exist (proved) -/

namespace Reps

open ZInQ.Contrib.TYZGenus.CM (cmPoint cmPoint_im)

/-! ### CM points -/

theorem sqrt_sq_D {D : ℤ} (hD : D < 0) :
    (Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) ^ 2 = (D : ℂ) := by
  have h0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast hD
    linarith
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h0]
  push_cast; ring

theorem sqrt_pos_D {D : ℤ} (hD : D < 0) : 0 < Real.sqrt (-(D : ℝ)) := by
  apply Real.sqrt_pos.mpr
  have : (D : ℝ) < 0 := by exact_mod_cast hD
  linarith

theorem cmPoint_re (A B D : ℤ) : (cmPoint A B D).re = -(B : ℝ) / (2 * A) := by
  have h : (2 * (A : ℂ)) = ((2 * (A : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [cmPoint, h, Complex.div_ofReal_re]
  simp

/-- `τ_Q` is a root of `Q`. -/
theorem cmPoint_root {A B C D : ℤ} (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * C = D) (hD : D < 0) :
    (A : ℂ) * cmPoint A B D ^ 2 + B * cmPoint A B D + C = 0 := by
  have hs := sqrt_sq_D hD
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hd : ((B : ℂ) ^ 2 - 4 * A * C = D) := by exact_mod_cast hdisc
  rw [cmPoint]
  field_simp
  linear_combination hs - hd

/-- The root of `Q` in the upper half plane is `τ_Q`. -/
theorem eq_cmPoint {A B C D : ℤ} (hA : 0 < A) (hdisc : B ^ 2 - 4 * A * C = D) (hD : D < 0)
    {z : ℂ} (hz : 0 < z.im) (h : (A : ℂ) * z ^ 2 + B * z + C = 0) : z = cmPoint A B D := by
  set s : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) with hsdef
  have hs := sqrt_sq_D hD
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hd : ((B : ℂ) ^ 2 - 4 * A * C = D) := by exact_mod_cast hdisc
  have hprod : (2 * A * z + B - s) * (2 * A * z + B + s) = 0 := by
    linear_combination 4 * (A : ℂ) * h + hd - hs
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rw [cmPoint]
    field_simp
    linear_combination h1
  · exfalso
    have him := congrArg Complex.im h1
    simp [hsdef] at him
    have hApos : (0 : ℝ) < A := by exact_mod_cast hA
    have := sqrt_pos_D hD
    nlinarith

/-! ### `SL₂(ℤ)` acting on forms -/

/-- Coefficients of the form whose root is `γ • τ_Q`, `γ = [[a, b], [c, d]]`. -/
def tA (A B C _a _b c d : ℤ) : ℤ := A * d ^ 2 - B * d * c + C * c ^ 2
def tB (A B C a b c d : ℤ) : ℤ := -2 * A * b * d + B * (a * d + b * c) - 2 * C * a * c
def tC (A B C a b _c _d : ℤ) : ℤ := A * b ^ 2 - B * a * b + C * a ^ 2

theorem det_SL (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rw [Matrix.det_fin_two] at this
  exact this

section Transform

variable {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (γ : SL(2, ℤ))

/-- shorthand -/
def A' : ℤ := tA Q.A Q.B Q.C (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
def B' : ℤ := tB Q.A Q.B Q.C (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
def C' : ℤ := tC Q.A Q.B Q.C (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

theorem disc' : B' Q γ ^ 2 - 4 * A' Q γ * C' Q γ = D := by
  have h := det_SL γ
  have hd := Q.disc
  simp only [A', B', C', tA, tB, tC]
  linear_combination (Q.B ^ 2 - 4 * Q.A * Q.C) *
    (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 + 1) * h + hd

theorem A'_pos : 0 < A' Q γ := by
  have h := det_SL γ
  have key : 4 * Q.A * A' Q γ = (2 * Q.A * γ 1 1 - Q.B * γ 1 0) ^ 2 - D * γ 1 0 ^ 2 := by
    have hd := Q.disc
    simp only [A', tA]; linear_combination (-(γ 1 0) ^ 2) * hd
  have hA := Q.A_pos
  have hD := Q.D_neg
  have hcd : γ 1 0 ≠ 0 ∨ γ 1 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at h
    simp at h
  have hpos : 0 < (2 * Q.A * γ 1 1 - Q.B * γ 1 0) ^ 2 - D * γ 1 0 ^ 2 := by
    rcases hcd with hc | hc
    · have : 0 < γ 1 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * Q.A * γ 1 1 - Q.B * γ 1 0)]
    · by_cases hc0 : γ 1 0 = 0
      · rw [hc0]
        have : 0 < (2 * Q.A * γ 1 1) ^ 2 := by positivity
        simpa using this
      · have : 0 < γ 1 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (2 * Q.A * γ 1 1 - Q.B * γ 1 0)]
  nlinarith

theorem primitive' : Int.gcd (Int.gcd (A' Q γ) (B' Q γ)) (C' Q γ) = 1 := by
  have h := det_SL γ
  set g := Int.gcd (Int.gcd (A' Q γ) (B' Q γ)) (C' Q γ)
  have hgA : (g : ℤ) ∣ A' Q γ := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  have hgB : (g : ℤ) ∣ B' Q γ := (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  have hgC : (g : ℤ) ∣ C' Q γ := Int.gcd_dvd_right _ _
  set a := γ 0 0; set b := γ 0 1; set c := γ 1 0; set d := γ 1 1
  have eA : Q.A = A' Q γ * a ^ 2 + B' Q γ * a * c + C' Q γ * c ^ 2 := by
    simp only [A', B', C', tA, tB, tC]
    linear_combination (-Q.A) * (a * d - b * c + 1) * h
  have eB : Q.B = 2 * A' Q γ * a * b + B' Q γ * (a * d + b * c) + 2 * C' Q γ * c * d := by
    simp only [A', B', C', tA, tB, tC]
    linear_combination (-Q.B) * (a * d - b * c + 1) * h
  have eC : Q.C = A' Q γ * b ^ 2 + B' Q γ * d * b + C' Q γ * d ^ 2 := by
    simp only [A', B', C', tA, tB, tC]
    linear_combination (-Q.C) * (a * d - b * c + 1) * h
  have hA : (g : ℤ) ∣ Q.A := by
    rw [eA]; exact dvd_add (dvd_add (dvd_mul_of_dvd_left hgA _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgB _) _)) (dvd_mul_of_dvd_left hgC _)
  have hB : (g : ℤ) ∣ Q.B := by
    rw [eB]; exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hgA _) _) _) (dvd_mul_of_dvd_left hgB _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hgC _) _) _)
  have hC : (g : ℤ) ∣ Q.C := by
    rw [eC]; exact dvd_add (dvd_add (dvd_mul_of_dvd_left hgA _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgB _) _)) (dvd_mul_of_dvd_left hgC _)
  have h1 : g ∣ Int.gcd (Int.gcd Q.A Q.B : ℤ) Q.C :=
    Int.dvd_gcd (Int.natCast_dvd_natCast.mpr (Int.dvd_gcd hA hB)) hC
  rw [Q.primitive] at h1
  exact Nat.dvd_one.mp h1

/-- **The transformed Heegner form** (level `M`, given `M ∣ A'`), with root `γ • τ_Q`. -/
def transform (M : ℕ) (hM : (M : ℤ) ∣ A' Q γ) : HeegnerForm M D where
  A := A' Q γ
  B := B' Q γ
  C := C' Q γ
  A_pos := A'_pos Q γ
  N_dvd := hM
  disc := disc' Q γ
  D_neg := Q.D_neg
  primitive := primitive' Q γ

theorem transform_tauH (M : ℕ) (hM : (M : ℤ) ∣ A' Q γ) :
    (transform Q γ M hM).tauH = γ • Q.tauH := by
  apply UpperHalfPlane.ext
  symm
  have hτ : (Q.A : ℂ) * (Q.tauH : ℂ) ^ 2 + Q.B * (Q.tauH : ℂ) + Q.C = 0 :=
    cmPoint_root Q.A_pos Q.disc Q.D_neg
  set τ : ℂ := (Q.tauH : ℂ)
  have hdet : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast det_SL γ
  set z : ℂ := ((γ • Q.tauH : ℍ) : ℂ) with hzdef
  set w : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ)
  have hw : w ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ Q.tauH
    simpa [UpperHalfPlane.denom, w, τ] using this
  have hzw : z * w = ((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ) := by
    rw [hzdef, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    exact div_mul_cancel₀ _ hw
  have hu : (((γ 1 1 : ℤ) : ℂ) * z - (γ 0 1 : ℤ)) * w = τ := by
    linear_combination ((γ 1 1 : ℤ) : ℂ) * hzw + τ * hdet
  have hv : (-((γ 1 0 : ℤ) : ℂ) * z + (γ 0 0 : ℤ)) * w = 1 := by
    linear_combination (-((γ 1 0 : ℤ) : ℂ)) * hzw + hdet
  have hroot : ((A' Q γ : ℤ) : ℂ) * z ^ 2 + (B' Q γ : ℤ) * z + (C' Q γ : ℤ) = 0 := by
    set u := ((γ 1 1 : ℤ) : ℂ) * z - (γ 0 1 : ℤ)
    set v := -((γ 1 0 : ℤ) : ℂ) * z + (γ 0 0 : ℤ)
    have e : ((A' Q γ : ℤ) : ℂ) * z ^ 2 + (B' Q γ : ℤ) * z + (C' Q γ : ℤ) =
        (Q.A : ℂ) * u ^ 2 + Q.B * u * v + Q.C * v ^ 2 := by
      simp only [A', B', C', tA, tB, tC, u, v]; push_cast; ring
    have e2 : ((A' Q γ : ℤ) : ℂ) * z ^ 2 + (B' Q γ : ℤ) * z + (C' Q γ : ℤ) = 0 ∨ w ^ 2 = 0 := by
      apply mul_eq_zero.mp
      rw [e]
      linear_combination ((Q.A : ℂ) * (u * w + τ) + Q.B * v * w) * hu +
        ((Q.B : ℂ) * τ + Q.C * (v * w + 1)) * hv + hτ
    exact e2.resolve_right (pow_ne_zero 2 hw)
  exact eq_cmPoint (A'_pos Q γ) (disc' Q γ) Q.D_neg (γ • Q.tauH).im_pos hroot

/-- For `γ ∈ Γ₀(N)` the transform keeps level `N`. -/
theorem dvd_A' (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : (N : ℤ) ∣ A' Q γ := by
  have hc : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  simp only [A', tA]
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_left Q.N_dvd _)
    (dvd_mul_of_dvd_right hc _)) (dvd_mul_of_dvd_right (dvd_pow hc two_ne_zero) _)

/-- For `γ ∈ Γ₀(N)` the residue `B mod 2N` is kept. -/
theorem residue_transform (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) {β : ℤ} (hQ : HasResidue β Q) :
    HasResidue β (transform Q γ N (dvd_A' Q γ hγ)) := by
  have hc : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have h := det_SL γ
  obtain ⟨k, hk⟩ := Q.N_dvd
  obtain ⟨m, hm⟩ := hc
  obtain ⟨r, hr⟩ := hQ
  show (2 * N : ℤ) ∣ B' Q γ - β
  refine ⟨r - k * γ 0 1 * γ 1 1 + Q.B * γ 0 1 * m - Q.C * γ 0 0 * m, ?_⟩
  simp only [B', tB]
  rw [hm] at h
  rw [hk, hm]
  linear_combination hr + Q.B * h

end Transform

/-! ### `Γ₀(N)`-equivalence is an equivalence relation -/

theorem equiv_refl {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : Gamma0Equiv Q Q :=
  ⟨1, Subgroup.one_mem _, one_smul _ _⟩

theorem equiv_symm {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D} (h : Gamma0Equiv Q Q') :
    Gamma0Equiv Q' Q := by
  obtain ⟨γ, hγ, e⟩ := h
  exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by rw [← e, inv_smul_smul]⟩

theorem equiv_trans {N : ℕ} {D : ℤ} {Q Q' Q'' : HeegnerForm N D} (h : Gamma0Equiv Q Q')
    (h' : Gamma0Equiv Q' Q'') : Gamma0Equiv Q Q'' := by
  obtain ⟨γ, hγ, e⟩ := h
  obtain ⟨γ', hγ', e'⟩ := h'
  exact ⟨γ' * γ, Subgroup.mul_mem _ hγ' hγ, by rw [mul_smul, e, e']⟩

/-! ### Finiteness -/

theorem form_ext {N : ℕ} {D : ℤ} {Q Q' : HeegnerForm N D} (hA : Q.A = Q'.A) (hB : Q.B = Q'.B) :
    Q = Q' := by
  have hC : Q.C = Q'.C := by
    have h1 := Q.disc
    have h2 := Q'.disc
    rw [hA, hB] at h1
    have hA0 := Q'.A_pos
    have : 4 * Q'.A * (Q.C - Q'.C) = 0 := by linear_combination h2 - h1
    have := (mul_eq_zero.mp this).resolve_left (by positivity)
    linarith
  cases Q; cases Q'
  simp only at hA hB hC
  subst hA hB hC
  rfl

theorem tauH_injective {N : ℕ} {D : ℤ} : Function.Injective (fun Q : HeegnerForm N D => Q.tauH) := by
  intro Q Q' h
  have h' : cmPoint Q.A Q.B D = cmPoint Q'.A Q'.B D := congrArg (fun z : ℍ => (z : ℂ)) h
  have him := congrArg Complex.im h'
  have hre := congrArg Complex.re h'
  rw [cmPoint_im, cmPoint_im] at him
  rw [cmPoint_re, cmPoint_re] at hre
  have hs := sqrt_pos_D Q.D_neg
  have hA0 : (0 : ℝ) < Q.A := by exact_mod_cast Q.A_pos
  have hA0' : (0 : ℝ) < Q'.A := by exact_mod_cast Q'.A_pos
  have hA : (Q.A : ℝ) = Q'.A := by
    field_simp at him
    nlinarith
  have hA' : Q.A = Q'.A := by exact_mod_cast hA
  have hB : (Q.B : ℝ) = Q'.B := by
    rw [hA] at hre
    field_simp at hre
    linarith
  exact form_ext hA' (by exact_mod_cast hB)

/-- A form whose root lies in the fundamental domain has bounded coefficients. -/
theorem bounded_of_mem_fd {M : ℕ} {D : ℤ} (R : HeegnerForm M D) (h : R.tauH ∈ 𝒟) :
    R.A ≤ -D ∧ |R.B| ≤ -D := by
  obtain ⟨hn, hr⟩ := h
  have hA0 : (0 : ℝ) < R.A := by exact_mod_cast R.A_pos
  have hre : R.tauH.re = -(R.B : ℝ) / (2 * R.A) := cmPoint_re _ _ _
  have him : R.tauH.im = Real.sqrt (-(D : ℝ)) / (2 * R.A) := cmPoint_im _ _ _
  have hD0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast R.D_neg
    linarith
  have hBA : |(R.B : ℝ)| ≤ R.A := by
    rw [hre, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * R.A)] at hr
    rw [div_le_iff₀ (by positivity)] at hr
    linarith
  have hns : Complex.normSq (R.tauH : ℂ) = R.tauH.re ^ 2 + R.tauH.im ^ 2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
  rw [hns, hre, him, div_pow, div_pow, Real.sq_sqrt hD0, neg_sq, ← add_div,
    le_div_iff₀ (by positivity)] at hn
  have hB2 : (R.B : ℝ) ^ 2 ≤ (R.A : ℝ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hBA 2
  have hA1 : (1 : ℝ) ≤ R.A := by exact_mod_cast R.A_pos
  have hAD : (R.A : ℝ) ≤ -D := by nlinarith
  have hAD' : R.A ≤ -D := by exact_mod_cast hAD
  refine ⟨hAD', ?_⟩
  have : |(R.B : ℝ)| ≤ -D := hBA.trans hAD
  exact_mod_cast this

theorem finite_bounded (M : ℕ) (D : ℤ) :
    {R : HeegnerForm M D | R.A ≤ -D ∧ |R.B| ≤ -D}.Finite := by
  let f : HeegnerForm M D → ℤ × ℤ := fun R => (R.A, R.B)
  have hf : Function.Injective f := fun R R' h => form_ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hfin : (f ⁻¹' ((Finset.Icc D (-D) ×ˢ Finset.Icc D (-D) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ))).Finite :=
    Set.Finite.preimage hf.injOn (Finset.finite_toSet _)
  refine hfin.subset fun R hR => ?_
  obtain ⟨h1, h2⟩ := hR
  have := R.A_pos
  simp only [Set.mem_preimage, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc, f]
  refine ⟨⟨by linarith, h1⟩, ?_, ?_⟩ <;> [linarith [neg_abs_le R.B]; linarith [le_abs_self R.B]]

/-- **Every Heegner form of residue `β` is `Γ₀(N)`-equivalent to one in a finite set.** -/
theorem exists_finite (N : ℕ) [NeZero N] (D β : ℤ) :
    ∃ T : Set (HeegnerForm N D), T.Finite ∧ (∀ Q ∈ T, HasResidue β Q) ∧
      ∀ Q : HeegnerForm N D, HasResidue β Q → ∃ Q' ∈ T, Gamma0Equiv Q Q' := by
  classical
  let Kset : Set SL(2, ℤ) :=
    Set.range (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N => q.out)
  have hK : Kset.Finite := Set.finite_range _
  let Rset := {R : HeegnerForm 1 D | R.A ≤ -D ∧ |R.B| ≤ -D}
  let W : Set ℍ := Set.image2 (fun k w => k⁻¹ • w) Kset ((fun R : HeegnerForm 1 D => R.tauH) '' Rset)
  have hW : W.Finite := hK.image2 _ ((finite_bounded 1 D).image _)
  let T : Set (HeegnerForm N D) := {Q | HasResidue β Q ∧ Q.tauH ∈ W}
  refine ⟨T, ?_, fun Q hQ => hQ.1, fun Q hQ => ?_⟩
  · exact (hW.preimage tauH_injective.injOn).subset fun Q hQ => hQ.2
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd Q.tauH
  let R := transform Q g 1 (by simp)
  have hR : R.tauH = g • Q.tauH := transform_tauH Q g 1 _
  have hRb : R ∈ Rset := bounded_of_mem_fd R (hR ▸ hg)
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) g
  set k := (QuotientGroup.mk g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out with hkdef
  set γ : SL(2, ℤ) := (h : SL(2, ℤ))⁻¹ with hγdef
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 N := Subgroup.inv_mem _ h.2
  have hgk : g = k * γ := by rw [hh, hγdef, mul_inv_cancel_right]
  let Q' := transform Q γ N (dvd_A' Q γ hγ)
  have hQ' : Q'.tauH = γ • Q.tauH := transform_tauH Q γ N _
  refine ⟨Q', ⟨residue_transform Q γ hγ hQ, ?_⟩, ⟨γ, hγ, hQ'.symm⟩⟩
  refine ⟨k, ⟨_, hkdef.symm⟩, R.tauH, ⟨R, hRb, rfl⟩, ?_⟩
  show k⁻¹ • R.tauH = Q'.tauH
  rw [hR, hQ', hgk, mul_smul, inv_smul_smul]

/-- **Heegner representatives exist** (glue `HeegnerRepsExist`, proved). -/
theorem exists_reps (N : ℕ) [NeZero N] (D β : ℤ) :
    ∃ S : Finset (HeegnerForm N D), IsHeegnerReps N D β S := by
  classical
  obtain ⟨T, hT, hTres, hTall⟩ := exists_finite N D β
  by_cases hne : Nonempty (HeegnerForm N D)
  swap
  · exact ⟨∅, fun Q hQ => absurd hQ (Finset.notMem_empty _), fun Q _ => absurd ⟨Q⟩ hne⟩
  let rep : HeegnerForm N D → HeegnerForm N D :=
    fun Q => Classical.epsilon (fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q Q'')
  have rep_spec : ∀ Q, (∃ Q'' ∈ T, Gamma0Equiv Q Q'') → rep Q ∈ T ∧ Gamma0Equiv Q (rep Q) := by
    intro Q hQ
    obtain ⟨Q'', h1, h2⟩ := hQ
    show Classical.epsilon _ ∈ T ∧ Gamma0Equiv Q (Classical.epsilon _)
    exact Classical.epsilon_spec (p := fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q Q'') ⟨Q'', h1, h2⟩
  have rep_congr : ∀ Q Q₁, Gamma0Equiv Q Q₁ → rep Q = rep Q₁ := by
    intro Q Q₁ h
    have : (fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q Q'') = (fun Q'' => Q'' ∈ T ∧ Gamma0Equiv Q₁ Q'') := by
      funext Q''
      apply propext
      exact ⟨fun ⟨a, b⟩ => ⟨a, equiv_trans (equiv_symm h) b⟩, fun ⟨a, b⟩ => ⟨a, equiv_trans h b⟩⟩
    show Classical.epsilon _ = Classical.epsilon _
    rw [this]
  refine ⟨hT.toFinset.image rep, ?_, ?_⟩
  · intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    rw [Set.Finite.mem_toFinset] at hQ
    exact hTres _ (rep_spec Q ⟨Q, hQ, equiv_refl Q⟩).1
  · intro Q hQ
    obtain ⟨Q₀, hQ₀, hQQ₀⟩ := hTall Q hQ
    have hs₀ := rep_spec Q₀ ⟨Q₀, hQ₀, equiv_refl Q₀⟩
    refine ⟨rep Q₀, ⟨Finset.mem_image.mpr ⟨Q₀, (Set.Finite.mem_toFinset _).mpr hQ₀, rfl⟩,
      equiv_trans hQQ₀ hs₀.2⟩, ?_⟩
    rintro Q' ⟨hQ'S, hQQ'⟩
    obtain ⟨Q₁, hQ₁, rfl⟩ := Finset.mem_image.mp hQ'S
    rw [Set.Finite.mem_toFinset] at hQ₁
    have hs₁ := rep_spec Q₁ ⟨Q₁, hQ₁, equiv_refl Q₁⟩
    apply rep_congr
    exact equiv_trans (equiv_trans hs₁.2 (equiv_symm hQQ')) hQQ₀

end Reps

/-- **`HeegnerRepsExist`, proved**: reduction to the fundamental domain of `SL₂(ℤ)` (Mathlib
`ModularGroup.exists_smul_mem_fd`), the transform of forms, and `[SL₂(ℤ) : Γ₀(N)] < ∞`. -/
theorem heegnerRepsExist : HeegnerRepsExist := fun N _ D β _ _ => Reps.exists_reps N D β

/-! ## §4. Glue lemmas -/

/-- The discriminant condition of `WeierstrassUniformization` for `(c₄/12, c₆/216)`. -/
theorem disc_ne_zero (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ((E⁄ℂ).c₄ / 12) ^ 3 - 27 * ((E⁄ℂ).c₆ / 216) ^ 2 ≠ 0 := by
  have h := WeierstrassCurve.c_relation (E⁄ℂ)
  have hΔ : (E⁄ℂ).Δ ≠ 0 := (E⁄ℂ).isUnit_Δ.ne_zero
  intro h0
  apply hΔ
  linear_combination (1 / 1728 : ℂ) * h + h0

/-- The period lattice exists (uniformization). -/
theorem exists_isPeriodLattice (hU : WeierstrassUniformization) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] : ∃ L : PeriodPair, IsPeriodLattice E L :=
  hU _ _ (disc_ne_zero E)

/-- `weierPt` is not junk: off the lattice it is the point `(℘ − b₂/12, (℘' − a₁x − a₃)/2)`. -/
theorem weierPt_some (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : IsPeriodLattice E L) {z : ℂ} (hz : z ∉ L.lattice) :
    (E⁄ℂ).Nonsingular (L.weierstrassP z - (E⁄ℂ).b₂ / 12)
      ((L.derivWeierstrassP z - (E⁄ℂ).a₁ * (L.weierstrassP z - (E⁄ℂ).b₂ / 12) - (E⁄ℂ).a₃) / 2) := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have h := L.derivWeierstrassP_sq z hz
  rw [hL.1, hL.2] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆] at h ⊢
  linear_combination (1 / 4 : ℂ) * h

/-- An embedding `ℚ(√D) → ℂ` with `√D ↦ i √|D|`. -/
theorem exists_embedding {K : Type} [Field K] [NumberField K] {D : ℤ} (hD : D < 0) (δ : K)
    (hδ : δ ^ 2 = (D : K)) :
    ∃ ι : K →ₐ[ℚ] ℂ, ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) := by
  set w : ℂ := Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) with hw
  have hw2 : w ^ 2 = (D : ℂ) := by
    have h0 : (0 : ℝ) ≤ -(D : ℝ) := by
      have : (D : ℝ) < 0 := by exact_mod_cast hD
      linarith
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt h0]
    push_cast; ring
  let ι₀ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hz : ι₀ δ ^ 2 = (D : ℂ) := by rw [← map_pow, hδ, map_intCast]
  have hprod : (ι₀ δ - w) * (ι₀ δ + w) = 0 := by linear_combination hz - hw2
  rcases mul_eq_zero.mp hprod with h | h
  · exact ⟨ι₀, sub_eq_zero.mp h⟩
  · refine ⟨ZInQ.Contrib.TYZGenus.CM.conjQ.comp ι₀, ?_⟩
    have : ι₀ δ = -w := eq_neg_of_add_eq_zero_left h
    simp only [AlgHom.comp_apply, this, ZInQ.Contrib.TYZGenus.CM.conjQ, hw]
    simp [Complex.conj_ofReal]

/-- In a quadratic field `ℚ(δ)`, `δ ∉ ℚ`, an automorphism fixing `δ` is the identity. -/
theorem algEquiv_eq_one_of_fix {K : Type} [Field K] [Algebra ℚ K] (hK : Module.finrank ℚ K = 2)
    {δ : K} (hδ : δ ∉ Set.range (algebraMap ℚ K)) (σ : K ≃ₐ[ℚ] K) (hσ : σ δ = δ) : σ = 1 := by
  have hli : LinearIndependent ℚ ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hδ
      refine ⟨-s / t, ?_⟩
      have : t • δ = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap ℚ K t ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr ht
      rw [map_div₀, map_neg, div_eq_iff ht', ← this]
      ring
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hlin : σ.toLinearMap = LinearMap.id := by
    refine b.ext fun i => ?_
    fin_cases i
    · simp [b, map_one]
    · simp [b, hσ]
  ext x
  have := congrArg (fun g : K →ₗ[ℚ] K => g x) hlin
  simpa using this

/-- A simple zero at `1` has nonzero derivative. -/
theorem deriv_ne_zero_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h1 : analyticOrderAt F 1 = 1) : deriv F 1 ≠ 0 := by
  have hFa : AnalyticAt ℂ F 1 := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF) 1
    (Set.mem_univ _)
  obtain ⟨g, hga, hg1, hgF⟩ := (hFa.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  have hd : deriv F 1 = deriv (fun s => (s - 1) * g s) 1 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hgF] with s hs
    simpa using hs
  rw [hd]
  have : HasDerivAt (fun s => (s - 1) * g s) (1 * g 1 + (1 - 1) * deriv g 1) 1 :=
    ((hasDerivAt_id 1).sub_const 1).mul hga.differentiableAt.hasDerivAt
  rw [this.deriv]
  simpa using hg1

theorem zero_of_order_one {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h1 : analyticOrderAt F 1 = 1) : F 1 = 0 := by
  have hFa : AnalyticAt ℂ F 1 := (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF) 1
    (Set.mem_univ _)
  obtain ⟨g, hga, hg1, hgF⟩ := (hFa.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  simpa using hgF.self_of_nhds

/-- `L'(E/K, 1) = F'(1) G(1) ≠ 0` when `F` has a simple zero at `1` and `G(1) ≠ 0`. -/
theorem deriv_mul_ne_zero {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h1 : analyticOrderAt F 1 = 1) (hG1 : G 1 ≠ 0) : deriv (fun s => F s * G s) 1 ≠ 0 := by
  have h : HasDerivAt (fun s => F s * G s) (deriv F 1 * G 1 + F 1 * deriv G 1) 1 :=
    (hF 1).hasDerivAt.mul (hG 1).hasDerivAt
  rw [h.deriv, zero_of_order_one hF h1, zero_mul, add_zero]
  exact mul_ne_zero (deriv_ne_zero_of_order_one hF h1) hG1

/-! ## §5. `GrossZagierHeegner` from the leaves -/

/-- **The modular parametrization from Eichler–Shimura and Faltings** (glue). -/
theorem eichlerShimuraParamAt_of_leaves (hU : WeierstrassUniformization) (hSW : StrongWeilCurve)
    (hI : IsogenyLattice) (E : WeierstrassCurve ℚ) [E.IsElliptic] : EichlerShimuraParamAt E := by
  intro N _ f hχ hf L hL
  obtain ⟨E', hE', hf', hL'⟩ := hSW N f hχ fun n hn => ⟨_, hf n hn⟩
  obtain ⟨L', hL'E⟩ := exists_isPeriodLattice hU E'
  obtain ⟨c, hc, hcL⟩ := hL' L' hL'E
  have hEE : ∀ n : ℕ, n ≠ 0 → E.LFunction n = E'.LFunction n := fun n hn => by
    have := (hf n hn).symm.trans (hf' n hn)
    exact_mod_cast this
  obtain ⟨m, hm, hmL⟩ := hI E E' hEE L L' hL hL'E
  refine ⟨m * c, mul_ne_zero hm hc, fun γ hγ τ => ?_⟩
  have := hmL _ (hcL γ hγ τ)
  push_cast
  rwa [mul_assoc]

/-- **`GrossZagierHeegner` for one curve `E`** from the leaves at `E` (with the proved glue:
Heegner representatives (`heegnerRepsExist`), `β` by Hensel
(`GZStatements.exists_sq_mod_four_mul_of_heegnerHyp`), the sign of a simple zero
(`GZDecomp.signOfSimpleZero`), `L'(E/K, 1) = F'(1) G(1) ≠ 0`, `ĥ = 0` on torsion). -/
theorem heegner_at (hU : WeierstrassUniformization) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hES : EichlerShimuraParamAt E) (hHP : HeegnerPointRationalAt E)
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
  obtain ⟨L, hL⟩ := exists_isPeriodLattice hU E
  obtain ⟨c, hc, hcL⟩ := hES N f hχ hf L hL
  obtain ⟨ι, hι⟩ := exists_embedding hDisc.1 δ hδ'
  obtain ⟨y, hy⟩ := hHP N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι hι
  refine ⟨y, ?_, ?_⟩
  · -- infinite order: `ĥ(y) ≠ 0` since `L'(E/K, 1) = κ ĥ(y) ≠ 0`
    obtain ⟨κ, -, hκ⟩ := hGZ N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι
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
    · -- `σ = 1`
      have hnr : δ ∉ Set.range (algebraMap ℚ K) := by
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

/-! ## §5b. Gross–Zagier's Chapter V consequences, proved from the leaves -/

/-- **GZ Ch. V (consequence of the formula): `y_K` has infinite order iff `L'(E/K, 1) ≠ 0`**
(Gross–Zagier 1986, Ch. V, corollary of Thm 2.1, UNVERIFIED locator), from `GrossZagierFormulaAt`
and Néron–Tate nondegeneracy (Tau Ceti `canonicalHeight_eq_zero_iff_isOfFinAddOrder` with
Mathlib's Northcott property of number fields). -/
theorem heegnerPoint_infinite_iff (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hGZ : GrossZagierFormulaAt E) (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ))
    (D β : ℤ) (hD : IsOddImagFundDisc D) (hD4 : D < -4) (hH : HeegnerHyp N D)
    (hβ : (4 * N : ℤ) ∣ D - β ^ 2) (S : Finset (HeegnerForm N D)) (hS : IsHeegnerReps N D β S)
    (L : PeriodPair) (c : ℚ) (hL : IsPeriodLattice E L) (hc : c ≠ 0) (hcL : PeriodsIn f c L)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = (D : K)) (ι : K →ₐ[ℚ] ℂ)
    (hι : ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ))
    (y : (E⁄K).Point) (hy : Affine.Point.map ι y = heegnerC E L f c S)
    (F G : ℂ → ℂ) (hF : IsEntireCont (coeff f) 2 F) (hG : IsEntireCont (twistCoeff f D) 2 G) :
    ¬IsOfFinAddOrder y ↔ deriv (fun s => F s * G s) 1 ≠ 0 := by
  obtain ⟨κ, hκ0, hκ⟩ := hGZ N f hχ hf D β hD hD4 hH hβ S hS L c hL hc hcL K hK δ hδ ι hι y hy
    F G hF hG
  rw [hκ, ← WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder]
  constructor
  · intro h h0
    have : (κ : ℂ) * (y.canonicalHeight : ℂ) = ((κ * y.canonicalHeight : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_eq_zero] at h0
    exact h ((mul_eq_zero.mp h0).resolve_left hκ0.ne')
  · intro h h0
    exact h (by rw [h0]; simp)

/-- **GZ Ch. V: rank at least one** (Gross–Zagier 1986, Ch. V, UNVERIFIED locator): if `L(E, s)`
has a simple zero at `s = 1` and there is an odd Heegner discriminant `D < −4` for the level with
`L(E^D, 1) ≠ 0`, then `E(ℚ)` has a point of infinite order (`y_K + ȳ_K = 2 y_K` mod torsion). From
the leaves at `E` and the kernel's descent glue `GZDecomp.exists_rat_point_of_heegner`. -/
theorem exists_rat_point_of_leaves (hU : WeierstrassUniformization) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (hES : EichlerShimuraParamAt E) (hHP : HeegnerPointRationalAt E)
    (hGZ : GrossZagierFormulaAt E) (hGC : GrossConjugationAt E)
    (N : ℕ) [NeZero N] (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ))
    (D : ℤ) (hD : IsOddImagFundDisc D) (hD4 : D < -4) (hH : HeegnerHyp N D)
    (F G : ℂ → ℂ) (hF : IsEntireCont (coeff f) 2 F) (hG : IsEntireCont (twistCoeff f D) 2 G)
    (h1 : analyticOrderAt F 1 = 1) (hG1 : G 1 ≠ 0) :
    ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P := by
  have hD0 : (D : ℚ) < 0 := by exact_mod_cast hD.1
  obtain ⟨K, hKf, hKa, hK2, δ, hδ⟩ := exists_quadratic_field hD0
  classical
  obtain ⟨y, hy, hyσ⟩ := heegner_at hU E hES hHP hGZ hGC N f hχ hf D hD hD4 hH F G hF hG h1 hG1
    K hK2 ⟨δ, by simpa using hδ⟩
  exact exists_rat_point_of_heegner hK2 y hy hyσ

/-- **`GZDecomp.GrossZagierHeegner` (`hL3`) from six leaves**: uniformization, Eichler–Shimura's
strong Weil curve, Faltings' isogeny theorem (analytic form), the rationality of the Heegner
point, the Gross–Zagier formula and Gross's conjugation relation. -/
theorem grossZagierHeegner_of_leaves (hU : WeierstrassUniformization) (hSW : StrongWeilCurve)
    (hI : IsogenyLattice) (hHP : HeegnerPointRational) (hGZ : GrossZagierFormula)
    (hGC : GrossConjugation) : GrossZagierHeegner := by
  intro E _
  exact heegner_at hU E (eichlerShimuraParamAt_of_leaves hU hSW hI E) (hHP E) (hGZ E) (hGC E)

end ZInQ.GZHL3

