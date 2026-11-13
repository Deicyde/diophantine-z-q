import ZInQKernel.Contrib.TYZDecomp.CurveA
import ZInQKernel.Contrib.TYZGenus.X0
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
* `§2` `A(ℚ̄) ⊆ A(ℂ)`: a fixed embedding `ιC : ℚ̄ → ℂ` with `ιC i = I`, the induced injective
  `toC : A(ℚ̄) → A(ℂ)`, and the modular parametrization `X0.phiC : ℍ → A(ℂ)` of task x0-32
  (eta quotients; `TYZGenus/X0.lean`);
* `§3` Heegner forms `[A, B, C]` of level `N` and discriminant `D` (`N ∣ A`, `B² − 4AC = D < 0`), their
  CM points `τ_Q = (−B + √D)/(2A)` in the upper half plane, and the point
  `heegnerPt Q ∈ A(ℚ̄)`: the unique algebraic point with `toC P = X0.phiC τ_Q` (junk `0` if there is
  none; there always is, by the leaf `CMAlgebraic`);
* `§4` the leaves (`def … : Prop`): algebraicity of CM values (`CMAlgebraic`), the field of
  definition of a CM point (`CMFieldOfDefinition`, over the ring class field of the order of
  discriminant `D`, a parameter until `RingClass.lean` provides it), Shimura reciprocity at split
  primes (`ShimuraReciprocity`) and complex conjugation (`CMComplexConj`, proved: `cmComplexConj`);
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

/-! ### Basic facts (proved) -/

section Basic
open WeierstrassCurve.Affine

theorem galPt_zero (σ : GalQ) : galPt σ (0 : PtA) = 0 := rfl

theorem galPt_some (σ : GalQ) {x y : Qbar} (h : curveAbar.toAffine.Nonsingular x y) :
    ∃ h', galPt σ (.some x y h) = .some (σ x) (σ y) h' :=
  ⟨_, rfl⟩

theorem mem_ptsOver_iff (K : IntermediateField ℚ Qbar) (P : PtA) :
    P ∈ ptsOver K ↔ IsDefinedOver K P := by
  constructor
  · rintro ⟨Q, rfl⟩
    rcases Q with _ | ⟨x, y, h⟩
    · trivial
    · exact ⟨x.2, y.2⟩
  · intro hP
    rcases P with _ | ⟨x, y, h⟩
    · exact ⟨0, rfl⟩
    · obtain ⟨hx, hy⟩ := hP
      have h' : (curveA.baseChange K).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA) (f := K.val) K.val.injective _ _).mp h
      exact ⟨.some _ _ h', rfl⟩

theorem iPt_mem {K : IntermediateField ℚ Qbar} (hi : iQ ∈ K) {P : PtA} (hP : P ∈ ptsOver K) :
    iPt P ∈ ptsOver K := by
  rw [mem_ptsOver_iff] at hP ⊢
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  · exact ⟨K.neg_mem hP.1, K.mul_mem hi hP.2⟩

theorem galPt_mem {K : IntermediateField ℚ Qbar} (σ : GalQ) (hσ : ∀ x ∈ K, σ x ∈ K) {P : PtA}
    (hP : P ∈ ptsOver K) : galPt σ P ∈ ptsOver K := by
  rw [mem_ptsOver_iff] at hP ⊢
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  · obtain ⟨h', e⟩ := galPt_some σ h
    rw [e]
    exact ⟨hσ x hP.1, hσ y hP.2⟩

theorem galPt_iPt (σ : GalQ) (hσ : σ iQ = iQ) (P : PtA) :
    galPt σ (iPt P) = iPt (galPt σ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := galPt_some σ h
    rw [e, iPt_some, iPt_some]
    obtain ⟨h'', e'⟩ := galPt_some σ (nonsingular_iPt h)
    rw [e', Point.some.injEq]
    exact ⟨map_neg σ x, by rw [map_mul, hσ]⟩

end Basic

/-! ## §2. `A(ℚ̄) ⊆ A(ℂ)` and the modular parametrization of `X0.lean`

The modular parametrization is task x0-32's `X0.phiC : ℍ → A(ℂ)`, `τ ↦ (x(τ), y(τ))` with the
eta quotients `x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2`, `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)`; that it is
the modular parametrization `X₀(32) ≅ A` with `dx/2y = 2πi f dτ` is the content of x0-32's leaves
`X0.X0AnalyticModel`. -/

/-- A fixed embedding `ℚ̄ → ℂ` (any `ℚ`-algebra map; `ℂ` is algebraically closed). -/
def ι₀ : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

/-- Complex conjugation as a `ℚ`-algebra map. -/
def conjQ : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.toAlgHom).restrictScalars ℚ

open Classical in
/-- The embedding `ℚ̄ → ℂ` used throughout, normalized by `ιC iQ = I` (compose `ι₀` with complex
conjugation if `ι₀ iQ = −I`). -/
def ιCA : Qbar →ₐ[ℚ] ℂ := if ι₀ iQ = I then ι₀ else conjQ.comp ι₀

/-- `ιCA` as a ring homomorphism. -/
abbrev ιC : Qbar →+* ℂ := ιCA.toRingHom

/-- `A(ℚ̄) → A(ℂ)` through `ιC` (injective, `toC_injective`). -/
def toC : PtA →+ X0.PtAC := WeierstrassCurve.Affine.Point.map (W' := curveA) ιCA

/-- The CM point `τ_Q = (−B + √D)/(2A)` (`√D = i√|D|`), the root of `Aτ² + Bτ + C` in the upper
half plane (used for `D < 0`, `A > 0`). -/
def cmPoint (A B D : ℤ) : ℂ :=
  (-(B : ℂ) + I * (Real.sqrt (-(D : ℝ)) : ℂ)) / (2 * (A : ℂ))

theorem cmPoint_im (A B D : ℤ) : (cmPoint A B D).im = Real.sqrt (-(D : ℝ)) / (2 * A) := by
  have h : (2 * (A : ℂ)) = ((2 * (A : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [cmPoint, h, Complex.div_ofReal_im]
  simp

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

/-- `τ_Q ∈ ℂ`. -/
def HeegnerForm.tau {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : ℂ := cmPoint Q.A Q.B D

/-- `τ_Q ∈ ℍ`. -/
def HeegnerForm.tauH {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) : UpperHalfPlane :=
  ⟨Q.tau, by
    rw [HeegnerForm.tau, cmPoint_im]
    have hD : (0 : ℝ) < -(D : ℝ) := by
      have := Q.D_neg; have : (D : ℝ) < 0 := by exact_mod_cast this
      linarith
    have hA : (0 : ℝ) < Q.A := by exact_mod_cast Q.A_pos
    positivity⟩

open Classical in
/-- **The image on `A` of the Heegner point attached to `Q`**: the point of `A(ℚ̄)` whose image
in `A(ℂ)` is `X0.phiC τ_Q` (unique, `toC_injective`). Junk `0` if there is none (there is one,
by the leaf `CMAlgebraic`). -/
def heegnerPt {D : ℤ} (Q : HeegnerForm 32 D) : PtA :=
  if h : ∃ P : PtA, toC P = X0.phiC Q.tauH then h.choose else 0

theorem ι₀_iQ_sq : ι₀ iQ ^ 2 = -1 := by rw [← map_pow, iQ_sq, map_neg, map_one]

/-- **`ιC i = I`.** -/
theorem ιC_iQ : ιC iQ = I := by
  show ιCA iQ = I
  unfold ιCA
  split_ifs with h
  · exact h
  · have h2 : (ι₀ iQ - I) * (ι₀ iQ + I) = 0 := by
      have := ι₀_iQ_sq
      linear_combination this - Complex.I_sq
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) h
    · have : ι₀ iQ = -I := eq_neg_of_add_eq_zero_left h3
      show conjQ (ι₀ iQ) = I
      rw [this]
      simp [conjQ]

theorem toC_injective : Function.Injective toC :=
  WeierstrassCurve.Affine.Point.map_injective (W' := curveA) ιCA

/-- Given `CMAlgebraic`, `heegnerPt Q` is the algebraic point over `X0.phiC τ_Q`. -/
theorem toC_heegnerPt {D : ℤ} (Q : HeegnerForm 32 D) (h : ∃ P : PtA, toC P = X0.phiC Q.tauH) :
    toC (heegnerPt Q) = X0.phiC Q.tauH := by
  simp only [heegnerPt, h, ↓reduceDIte]
  exact h.choose_spec

/-- `heegnerPt` is pinned: any algebraic point over `X0.phiC τ_Q` is `heegnerPt Q`. -/
theorem heegnerPt_eq {D : ℤ} (Q : HeegnerForm 32 D) {P : PtA} (hP : toC P = X0.phiC Q.tauH) :
    heegnerPt Q = P :=
  toC_injective ((toC_heegnerPt Q ⟨P, hP⟩).trans hP.symm)

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
the value `X0.phiC τ_Q ∈ A(ℂ)` of the modular parametrization is the image of a point of `A(ℚ̄)`.
Sources: the modular parametrization `X₀(32) → A` is defined over `ℚ` (Shimura, *Introduction to the arithmetic theory of automorphic
functions*, 1971, Thm. 7.14 and §7.5, UNVERIFIED numbers; for CM curves also Deuring), with
Manin constant 1 for 32a1 (Cremona's tables; Edixhoven, UNVERIFIED locator), and CM points of
`X₀(N)` are algebraic (Shimura 1971, Ch. 5–6, main theorem of complex multiplication; Gross,
*Heegner points on X₀(N)*, in Modular Forms (Durham 1983), 1984, §1–3, UNVERIFIED numbers).
Refereed (textbook). All CM leaves are stated over x0-32's `X0.phiC`; they are true because (and only if) that eta
model is the `ℚ`-rational modular parametrization, which is the content of x0-32's leaves
`X0.X0AnalyticModel`. -/
def CMAlgebraic : Prop :=
  ∀ (D : ℤ) (Q : HeegnerForm 32 D), ∃ P : PtA, toC P = X0.phiC Q.tauH

/-- **Leaf CM-2 (field of definition of a CM point).** For a family `H D` of subfields of `ℚ̄`
(intended: the ring class field `K(j(𝒪_D))` of the order of discriminant `D` in
`K = ℚ(√D)`, provided by `RingClass.lean`), every Heegner point of discriminant `D` on `A` is
defined over `H D`. Source: Gross (1984) §1–3 / Shimura (1971) Thm. 5.7 and §6.8 (the point
`(ℂ/𝔞 → ℂ/𝔫⁻¹𝔞)` of `X₀(N)` is rational over the ring class field), plus the modular
parametrization over `ℚ` (UNVERIFIED numbers). Refereed (textbook). For non-maximal orders
whose conductor shares a prime with `N` (TYZ's `D = −64n`, conductor 4, `N = 32`) this is the
version of Shimura's reciprocity law for the full CM-point set of `X₀(N)`, which TYZ use at
L1203–1260 (not re-read here). `H` is a free parameter: this is a closed leaf only for a pinned family (the ring class fields); the
closed TYZ instance is `Package.CMFieldOfDefinitionTYZ` (via `Package.cmFieldTYZ_of`). The main
theorem uses neither. -/
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

/-- **CM-4 (complex conjugation on Heegner points); proved below as `cmComplexConj`** (from
`η(−z̄) = conj η(z)`), so not a leaf. The automorphism `σ` of `ℚ̄` inducing
complex conjugation through `ιC` maps the Heegner point of `[A, B, C]` to that of `[A, −B, C]`
(`τ_{Q̄} = −conj τ_Q`; the `a_m` are real and `A`, `Λ_A`, the parametrization are defined over `ℝ`).
STANDARD (Gross 1984 §1, UNVERIFIED locator); used by TYZ in the proof of Theorem 3.6 through
the matrix `j = [[1, 0], [8, −1]]` (rv-tyz-inputs §1.5). -/
def CMComplexConj : Prop :=
  ∀ (σ : GalQ), (∀ x : Qbar, ιC (σ x) = starRingEnd ℂ (ιC x)) →
    ∀ (D : ℤ) (Q : HeegnerForm 32 D), galPt σ (heegnerPt Q) = heegnerPt Q.conj

/-! ### `CMComplexConj` is a theorem -/

section ComplexConj
open ComplexConjugate

theorem qParam_conj (h : ℝ) (z : ℂ) :
    Function.Periodic.qParam h (-conj z) = conj (Function.Periodic.qParam h z) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- **`η(−z̄) = conj η(z)`** (real `q`-coefficients). -/
theorem eta_conj (z : ℂ) : ModularForm.eta (-conj z) = conj (ModularForm.eta z) := by
  unfold ModularForm.eta
  rw [map_mul, qParam_conj]
  congr 1
  rw [Function.LeftInverse.map_tprod (g := starRingEnd ℂ) _ Complex.continuous_conj
    Complex.continuous_conj (fun w => Complex.conj_conj w)]
  congr 1
  funext n
  simp only [ModularForm.eta_q, map_sub, map_one, map_pow, qParam_conj]

theorem etaD_conj (d : ℕ) (z : ℂ) : X0.etaD d (-conj z) = conj (X0.etaD d z) := by
  unfold X0.etaD
  rw [← eta_conj]
  congr 1
  simp

theorem xC_conj (z : ℂ) : X0.xC (-conj z) = conj (X0.xC z) := by
  unfold X0.xC
  simp only [etaD_conj, map_add, map_div₀, map_mul, map_pow, map_ofNat]

theorem yC_conj (z : ℂ) : X0.yC (-conj z) = conj (X0.yC z) := by
  unfold X0.yC
  simp only [etaD_conj, map_neg, map_div₀, map_mul, map_pow]

/-- Complex conjugation on `A(ℂ)` (`A` is defined over `ℚ`). -/
def conjPt : X0.PtAC →+ X0.PtAC := WeierstrassCurve.Affine.Point.map (W' := curveA) conjQ

theorem conjQ_apply (z : ℂ) : conjQ z = conj z := rfl

theorem conjQ_injective : Function.Injective conjQ := conjQ.injective

theorem phiC_conj (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = -conj (τ : ℂ)) :
    X0.phiC τ' = conjPt (X0.phiC τ) := by
  unfold X0.phiC
  have ex : X0.xC τ' = conjQ (X0.xC τ) := by rw [h, xC_conj]; rfl
  have ey : X0.yC τ' = conjQ (X0.yC τ) := by rw [h, yC_conj]; rfl
  by_cases hn : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hn' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [ex, ey]
      exact (WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA) (f := conjQ)
        conjQ_injective _ _).mpr hn
    rw [dif_pos hn', dif_pos hn]
    simp only [conjPt, WeierstrassCurve.Affine.Point.map_some, ex, ey]
  · have hn' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [ex, ey]
      exact fun h' => hn ((WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA)
        (f := conjQ) conjQ_injective _ _).mp h')
    simp only [hn, hn', ↓reduceDIte, map_zero]

theorem toC_galPt (σ : GalQ) (hσ : ∀ x : Qbar, ιC (σ x) = conj (ιC x)) (P : PtA) :
    toC (galPt σ P) = conjPt (toC P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := galPt_some σ h
    rw [e]
    simp only [toC, conjPt, WeierstrassCurve.Affine.Point.map_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hσ x, hσ y⟩

theorem conjPt_conjPt (P : X0.PtAC) : conjPt (conjPt P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [conjPt, WeierstrassCurve.Affine.Point.map_some, conjQ_apply, Complex.conj_conj]

theorem tau_conj {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    ((Q.conj).tauH : ℂ) = -conj ((Q.tauH : UpperHalfPlane) : ℂ) := by
  show cmPoint Q.A (-Q.B) D = -conj (cmPoint Q.A Q.B D)
  simp only [cmPoint, map_div₀, map_add, map_neg, map_mul, map_intCast, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- **`CMComplexConj` holds** (proved from `η(−z̄) = conj η(z)`; no leaf needed). -/
theorem cmComplexConj : CMComplexConj := by
  intro σ hσ D Q
  have hσinv : ∀ x : Qbar, ιC (σ.symm x) = conj (ιC x) := fun x => by
    have := hσ (σ.symm x)
    rw [AlgEquiv.apply_symm_apply] at this
    rw [this, Complex.conj_conj]
  by_cases h : ∃ P : PtA, toC P = X0.phiC Q.tauH
  · obtain ⟨P, hP⟩ := h
    rw [heegnerPt_eq Q hP]
    symm
    apply heegnerPt_eq
    rw [toC_galPt σ hσ, hP, phiC_conj _ _ (tau_conj Q)]
  · have h0 : heegnerPt Q = 0 := by simp only [heegnerPt, h, ↓reduceDIte]
    have h1 : ¬ ∃ P : PtA, toC P = X0.phiC Q.conj.tauH := by
      rintro ⟨P, hP⟩
      apply h
      refine ⟨galPt σ.symm P, ?_⟩
      rw [toC_galPt σ.symm hσinv, hP, phiC_conj _ _ (tau_conj Q), conjPt_conjPt]
    have h1' : heegnerPt Q.conj = 0 := by simp only [heegnerPt, h1, ↓reduceDIte]
    rw [h0, h1', map_zero]

end ComplexConj

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

/-- A genus-point sum of a point of `A(F)` lies in `A(K)` when every `t ∈ Φ` maps `F` into `K`
(glue towards `Package.GenusPtsDefined`). -/
theorem genusSum_mem {F K : IntermediateField ℚ Qbar} {Φ : Finset GalQ} {z : PtA}
    (hΦ : ∀ t ∈ Φ, ∀ x ∈ F, t x ∈ K) (hz : z ∈ ptsOver F) : genusSum Φ z ∈ ptsOver K := by
  refine (ptsOver K).sum_mem fun t ht => ?_
  rw [mem_ptsOver_iff] at hz ⊢
  rcases z with _ | ⟨x, y, h⟩
  · trivial
  · obtain ⟨h', e⟩ := galPt_some t h
    rw [e]
    exact ⟨hΦ t ht x hz.1, hΦ t ht y hz.2⟩

end ZInQ.Contrib.TYZGenus.CM
