import ZInQKernel.Contrib.TYZDecomp.CurveA
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# cm-points: CM (Heegner) points on `X₀(32) = A`, their fields of definition, Shimura reciprocity

Task cm-points (2026-11-13). Report: `docs/research/cm-points.md`; log: `scratch/cm-points/log.md`.
Owner of this file: cm-points. Shared with tasks x0-32 (`TYZGenus/X0.lean`) and ring-class
(`TYZGenus/RingClass.lean`); `TYZGenus/Package.lean` consumes it.

The curve is `A : y² = x³ + 4x` (`TYZDecomp.CurveA.curveA`, Cremona 32a1, which is `X₀(32)` itself,
and `ℚ`-isomorphic to TYZ's `2y² = x³ + x` by `(x, y) ↦ (2x, 4y)`). Everything below is stated over
genuine definitions:

* `§1` the Galois action `galPt σ` of `Gal(ℚ̄/ℚ)` on `A(ℚ̄)` (Mathlib's `Point.map`), and `A(K)`
  for `K ⊆ ℚ̄` as an additive subgroup `ptsOver K` of `A(ℚ̄)`;
* `§2` the complex uniformization: a fixed embedding `ιC : ℚ̄ → ℂ` with `ιC i = I`, the period
  lattice `latA` of `A` (pinned by its invariants `g₂ = −16`, `g₃ = 0`: the Weierstrass map
  `z ↦ (℘(z), ℘'(z)/2)` then lands on `y² = x³ + 4x`), and the modular parametrization
  `modParam τ = Σ_{m ≥ 1} (a_m/m) e^{2πimτ}`, with `a_m` the coefficients of Mathlib's `L(A, s)`
  (`WeierstrassCurve.LFunction`);
* `§3` Heegner forms `[A, B, C]` of level `N` and discriminant `D` (`N ∣ A`, `B² − 4AC = D < 0`), their
  CM points `τ_Q = (−B + √D)/(2A)` in the upper half plane, and the point
  `heegnerPt Q ∈ A(ℚ̄)`: the unique algebraic point whose complex image is `modParam τ_Q` modulo
  `latA` (junk `0` if there is none; there always is, by the leaf `CMAlgebraic`);
* `§4` the leaves (`def … : Prop`): algebraicity of CM values (`CMAlgebraic`), the field of
  definition of a CM point (`CMFieldOfDefinition`, over the ring class field of the order of
  discriminant `D`, a parameter until `RingClass.lean` provides it), Shimura reciprocity at split
  primes (`ShimuraReciprocity`) and complex conjugation (`CMComplexConj`);
* `§5` TYZ's points: the Heegner form `[16(n+1), −8, 1]` of discriminant `−64n` (TYZ L1203–1205 as
  quoted in `tyz-t1.md` §3.1) and the genus-point sum `Σ_{t ∈ Φ} t(z)`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.CM

open ZInQ.Contrib.TYZDecomp.CurveA Complex

/-! ## §1. Galois action and points over subfields -/

/-- `Gal(ℚ̄/ℚ)`. -/
abbrev GalQ : Type := Qbar ≃ₐ[ℚ] Qbar

/-- The action of `σ ∈ Gal(ℚ̄/ℚ)` on `A(ℚ̄)` (coordinatewise; `A` is defined over `ℚ`). -/
def galPt (σ : GalQ) : PtA →+ PtA :=
  WeierstrassCurve.Affine.Point.map (W' := curveA) (σ.toAlgHom)

/-- `A(K) ⊆ A(ℚ̄)` for an intermediate field `K` of `ℚ̄/ℚ`: the image of `A(K) → A(ℚ̄)`. -/
def ptsOver (K : IntermediateField ℚ Qbar) : AddSubgroup PtA :=
  (WeierstrassCurve.Affine.Point.map (W' := curveA) (F := K) (K := Qbar) K.val).range

/-! ## §2. The complex uniformization and the modular parametrization -/

/-- A fixed embedding `ℚ̄ → ℂ` (any `ℚ`-algebra map; `ℂ` is algebraically closed). -/
def ι₀ : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

open Classical in
/-- The embedding `ℚ̄ → ℂ` used throughout, normalized by `ιC iQ = I` (compose `ι₀` with complex
conjugation if `ι₀ iQ = −I`). -/
def ιC : Qbar →+* ℂ :=
  if ι₀ iQ = I then ι₀.toRingHom else (starRingEnd ℂ).comp ι₀.toRingHom

/-- A junk period pair (used only if no lattice has the invariants of `A`). -/
def junkPeriodPair : PeriodPair where
  ω₁ := 1
  ω₂ := I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨h1, h2⟩

open Classical in
/-- **The period lattice of `A`**, pinned by its invariants: a period pair with `g₂ = −16`,
`g₃ = 0`, so that `z ↦ (℘(z), ℘'(z)/2)` satisfies `y² = x³ + 4x` (Mathlib's
`PeriodPair.derivWeierstrassP_sq`: `℘'² = 4℘³ − g₂℘ − g₃`). The lattice with given invariants is
unique (uniformization theorem, STANDARD; not proved here), so `latA.lattice` is pinned; it is
`(Ω⁺/2)(1 + i)ℤ[i]`, `Ω⁺` the real period (rv-tyz-inputs §1.5a). Junk if no such pair exists
(one does, by the uniformization theorem). -/
def latA : PeriodPair :=
  if h : ∃ L : PeriodPair, L.g₂ = -16 ∧ L.g₃ = 0 then h.choose else junkPeriodPair

/-- **`z ∈ ℂ` and `P ∈ A(ℚ̄)` correspond under `ℂ/Λ_A ≅ A(ℂ)`, `z ↦ (℘(z), ℘'(z)/2)`**, with
`A(ℚ̄) ⊆ A(ℂ)` through `ιC`. -/
def IsUnifImage (z : ℂ) : PtA → Prop
  | .zero => z ∈ latA.lattice
  | .some x y _ => z ∉ latA.lattice ∧ ιC x = latA.weierstrassP z ∧ ιC y = latA.derivWeierstrassP z / 2

/-- The coefficient `a_m` of `L(A, s) = Σ a_m m^{−s}` (Mathlib's `WeierstrassCurve.LFunction`;
`a_m` is the `m`-th Fourier coefficient of the newform of level 32 attached to `A`, by modularity
of CM curves, Shimura 1971 / Deuring; not used in any proof here). -/
def aCoeff (m : ℕ) : ℤ := curveA.LFunction m

/-- **The modular parametrization** `X₀(32) → ℂ/Λ_A`, `τ ↦ 2πi ∫_{i∞}^τ f = Σ_{m ≥ 1} (a_m/m) q^m`,
`q = e^{2πiτ}` (absolutely convergent for `Im τ > 0`). For the optimal curve 32a1 its period
lattice is `Λ_A` (Manin constant 1), so composed with `IsUnifImage` it is the modular
parametrization `X₀(32) → A`, defined over `ℚ`, sending `∞` to `O`. -/
def modParam (τ : ℂ) : ℂ :=
  ∑' m : ℕ, ((aCoeff m : ℂ) / m) * Complex.exp (2 * Real.pi * I * m * τ)

/-! ## §3. Heegner forms and CM points -/

/-- A **Heegner form of level `N` and discriminant `D`**: a primitive positive definite binary
quadratic form `[A, B, C]` with `N ∣ A` and `B² − 4AC = D < 0`. -/
structure HeegnerForm (N : ℕ) (D : ℤ) where
  A : ℤ
  B : ℤ
  C : ℤ
  A_pos : 0 < A
  N_dvd : (N : ℤ) ∣ A
  disc : B ^ 2 - 4 * A * C = D
  D_neg : D < 0
  primitive : Int.gcd (Int.gcd A B) C = 1

/-- The CM point `τ_Q = (−B + √D)/(2A)` (`√D = i√|D|`), the root of `Aτ² + Bτ + C` in the upper
half plane. -/
def HeegnerForm.tau {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : ℂ :=
  (-(Q.B : ℂ) + I * (Real.sqrt (-(D : ℝ)) : ℂ)) / (2 * (Q.A : ℂ))

open Classical in
/-- **The image on `A` of the Heegner point attached to `Q`**: the point of `A(ℚ̄)` whose complex
image is `modParam τ_Q` (unique, since `ιC` is injective). Junk `0` if there is none. -/
def heegnerPt {D : ℤ} (Q : HeegnerForm 32 D) : PtA :=
  if h : ∃ P : PtA, IsUnifImage (modParam Q.tau) P then h.choose else 0

/-- The lattice `⟨1, τ_Q⟩ ⊂ ℂ` (a proper fractional ideal of the order of discriminant `D`). -/
def HeegnerForm.lat {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : Submodule ℤ ℂ :=
  Submodule.span ℤ {1, Q.tau}

/-- The lattice `⟨1/N, τ_Q⟩ ⊃ ⟨1, τ_Q⟩`: the Heegner point is the cyclic `N`-isogeny
`ℂ/⟨1, τ_Q⟩ → ℂ/⟨1/N, τ_Q⟩`. -/
def HeegnerForm.latN {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : Submodule ℤ ℂ :=
  Submodule.span ℤ {1 / (N : ℂ), Q.tau}

/-- The conjugate form `[A, −B, C]`; `τ_{Q̄} = −conj(τ_Q)`. -/
def HeegnerForm.conj {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : HeegnerForm N D where
  A := Q.A
  B := -Q.B
  C := Q.C
  A_pos := Q.A_pos
  N_dvd := Q.N_dvd
  disc := by have h := Q.disc; linear_combination h
  D_neg := Q.D_neg
  primitive := by
    have h := Q.primitive
    rwa [Int.gcd_neg]

/-! ## §4. The leaves -/

/-- **Leaf CM-1 (algebraicity of CM values; Shimura).** For every Heegner form `Q` of level 32,
`modParam τ_Q` is the complex image of a point of `A(ℚ̄)`. Sources: the modular parametrization
`X₀(32) → A` is defined over `ℚ` (Shimura, *Introduction to the arithmetic theory of automorphic
functions*, 1971, Thm. 7.14 and §7.5, UNVERIFIED numbers; for CM curves also Deuring), with
Manin constant 1 for 32a1 (Cremona's tables; Edixhoven, UNVERIFIED locator), and CM points of
`X₀(N)` are algebraic (Shimura 1971, Ch. 5–6, main theorem of complex multiplication; Gross,
*Heegner points on X₀(N)*, in Modular Forms (Durham 1983), 1984, §1–3, UNVERIFIED numbers).
Refereed (textbook). -/
def CMAlgebraic : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm 32 D), ∃ P : PtA, IsUnifImage (modParam Q.tau) P

/-- **Leaf CM-2 (field of definition of a CM point).** For a family `H D` of subfields of `ℚ̄`
(intended: the ring class field `K(j(𝒪_D))` of the order of discriminant `D` in
`K = ℚ(√D)`, provided by `RingClass.lean`), every Heegner point of discriminant `D` on `A` is
defined over `H D`. Source: Gross (1984) §1–3 / Shimura (1971) Thm. 5.7 and §6.8 (the point
`(ℂ/𝔞 → ℂ/𝔫⁻¹𝔞)` of `X₀(N)` is rational over the ring class field), plus the modular
parametrization over `ℚ` (UNVERIFIED numbers). Refereed (textbook). For non-maximal orders
whose conductor shares a prime with `N` (TYZ's `D = −64n`, conductor 4, `N = 32`) this is the
version of Shimura's reciprocity law for the full CM-point set of `X₀(N)`, which TYZ use at
L1203–1260 (not re-read here). -/
def CMFieldOfDefinition (H : ℤ → IntermediateField ℚ Qbar) : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm 32 D), heegnerPt Q ∈ ptsOver (H D)

/-- `√D ∈ ℚ̄` normalized by `ιC √D = i√|D|` (for `D < 0`). -/
def sqrtD (D : ℤ) : Qbar :=
  Classical.epsilon fun r : Qbar => r ^ 2 = (D : Qbar) ∧ ιC r = I * (Real.sqrt (-(D : ℝ)) : ℂ)

/-- The ring of integers of `ℚ̄` (the integral closure of `ℤ`). -/
abbrev OQbar : Subalgebra ℤ Qbar := integralClosure ℤ Qbar

/-- **`σ` is an arithmetic Frobenius at a prime of `ℚ̄` above the prime `𝔭 = (p, (−b + √D)/2)`
of `K = ℚ(√D)`**: there is a prime ideal `𝔓` of the algebraic integers containing `p` and
`(−b + √D)/2`, such that `σ x ≡ x^p (mod 𝔓)` for every algebraic integer `x`. -/
def IsFrobAbove (σ : GalQ) (p : ℕ) (b D : ℤ) : Prop :=
  ∃ 𝔓 : Ideal OQbar, 𝔓.IsPrime ∧ ((p : OQbar) ∈ 𝔓) ∧
    (∃ π : OQbar, (π : Qbar) = (-(b : Qbar) + sqrtD D) / 2 ∧ π ∈ 𝔓) ∧
    ∀ x y : OQbar, (y : Qbar) = σ (x : Qbar) → y - x ^ p ∈ 𝔓

/-- The ideal `𝔭̄ = (p, (−b − √D)/2)` of the order of discriminant `D`, as a lattice in `ℂ`
(`√D = i√|D|`). -/
def conjPrimeLat (p : ℕ) (b D : ℤ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {(p : ℂ), (-(b : ℂ) - I * (Real.sqrt (-(D : ℝ)) : ℂ)) / 2}

/-- `L' = λ·L` for some `λ ∈ ℂ^×` (homothety of lattices). -/
def IsHomothetic (L L' : Submodule ℤ ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ L' = L.map (LinearMap.mulLeft ℤ c)

/-- **Leaf CM-3 (Shimura reciprocity for Heegner points of level 32, at split primes).**
Let `Q` be a Heegner form of level 32 and discriminant `D`, `p` an odd prime with `p ∤ D` split in
`K = ℚ(√D)`, `b² ≡ D (mod 4p)`, and `𝔭 = (p, (−b + √D)/2)`. If `σ ∈ Gal(ℚ̄/ℚ)` is a Frobenius at a
prime above `𝔭` (so `σ|_{H_D} = Art(𝔭)`), then `σ` maps the Heegner point of `Q` to that of every
Heegner form `Q'` (same level, same discriminant) with `Q'.B ≡ Q.B (mod 64)` (same `𝔫`) whose
pair of lattices `(⟨1, τ'⟩, ⟨1/32, τ'⟩)` is homothetic, by one `λ`, to
`(𝔭̄⟨1, τ⟩, 𝔭̄⟨1/32, τ⟩)`, `𝔭̄ = 𝔭⁻¹·p`; i.e. `Art(𝔭)(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔭⁻¹𝔞])`.
Sources: main theorem of complex multiplication (Shimura 1971, Thm. 5.4; Silverman, *Advanced
topics*, Thm. II.8.2 and Cor. II.4.?; Gross 1984 §3, `σ_𝔟(𝒪, 𝔫, [𝔞]) = (𝒪, 𝔫, [𝔞𝔟⁻¹])`;
UNVERIFIED numbers; direction: arithmetic Frobenius, `j(𝔞)^{Art 𝔭} = j(𝔭⁻¹𝔞)`), with the modular
parametrization defined over `ℚ`. Refereed (textbook). -/
def ShimuraReciprocity : Prop :=
  ∀ (D : ℤ) (Q Q' : HeegnerForm 32 D) (p : ℕ) (b : ℤ) (σ : GalQ),
    p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ D → (4 * (p : ℤ)) ∣ b ^ 2 - D →
    IsFrobAbove σ p b D → (64 : ℤ) ∣ Q'.B - Q.B →
    (∃ c : ℂ, c ≠ 0 ∧
      Q'.lat = (conjPrimeLat p b D * Q.lat).map (LinearMap.mulLeft ℤ c) ∧
      Q'.latN = (conjPrimeLat p b D * Q.latN).map (LinearMap.mulLeft ℤ c)) →
    galPt σ (heegnerPt Q) = heegnerPt Q'

/-- **Leaf CM-4 (complex conjugation on Heegner points).** The automorphism `σ` of `ℚ̄` inducing
complex conjugation through `ιC` maps the Heegner point of `[A, B, C]` to that of `[A, −B, C]`
(`τ_{Q̄} = −conj τ_Q`; the `a_m` are real and `A`, `Λ_A`, the parametrization are defined over `ℝ`).
STANDARD (Gross 1984 §1, UNVERIFIED locator); used by TYZ in the proof of Theorem 3.6 through
the matrix `j = [[1, 0], [8, −1]]` (rv-tyz-inputs §1.5). -/
def CMComplexConj : Prop :=
  ∀ (σ : GalQ), (∀ x : Qbar, ιC (σ x) = starRingEnd ℂ (ιC x)) →
    ∀ (D : ℤ) (Q : HeegnerForm 32 D), galPt σ (heegnerPt Q) = heegnerPt Q.conj

/-! ## §5. TYZ's Heegner points and genus-point sums -/

/-- TYZ's Heegner form for `n ≡ 5 (mod 8)`: `[16(n+1), −8, 1]`, discriminant `−64n`, the fixed
point of TYZ's embedding `√−n ↦ [[−1, 1/4], [−4(n+1), 1]]` (TYZ L1203–1205, as read in
`tyz-t1.md` §3.1; source not on this host). `f₀(P_n)` is its Heegner point on `X₀(32)` (order
`ℤ[4√−n]`, conductor 4). -/
def tyzForm (n : ℕ) (hn : n % 8 = 5) : HeegnerForm 32 (-64 * n) where
  A := 16 * (n + 1)
  B := -8
  C := 1
  A_pos := by positivity
  N_dvd := by
    have : (n : ℤ) % 8 = 5 := by exact_mod_cast hn
    omega
  disc := by ring
  D_neg := by
    have : (0 : ℤ) < n := by have := hn; omega
    linarith
  primitive := by simp

/-- `f₀(P_n)` on `A`, for `n ≡ 5 (mod 8)` (junk `0` otherwise). -/
def tyzHeegnerPt (n : ℕ) : PtA :=
  if hn : n % 8 = 5 then heegnerPt (tyzForm n hn) else 0

/-- TYZ's `z_n = f_n(P_n) = (1 − [i]) f₀(P_n)` for `n ≡ 5 (mod 8)` (test vector `f_n = f₀ − f₀∘[i]`,
relative to the component of `P_n`; the sign of `[i]` is the one singled out numerically in
`tyz-t1.md` §3.1, AI-derived, VERIFIED there by computation; not a printed statement). -/
def tyzZn (n : ℕ) : PtA := tyzHeegnerPt n - iPt (tyzHeegnerPt n)

/-- The genus-point sum `Σ_{t ∈ Φ} t(z)` for a finite set `Φ` of automorphisms of `ℚ̄`
(TYZ: `Z(n) = Σ_{t ∈ Φ₀} f_n(P_n)^t`, L1318, `Φ₀ ⊂ Gal(H'_n/K_n)` represented by lifts). -/
def genusSum (Φ : Finset GalQ) (z : PtA) : PtA := ∑ t ∈ Φ, galPt t z

end ZInQ.Contrib.TYZGenus.CM
