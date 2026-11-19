import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Glue

/-!
# The isogeny–lattice glue (G2) from an analytic and an algebraic glue

The reduction of `NewformPeriodsRational` (`RC53Assist/NewformPeriods`) uses the named GLUE
`IsogenyLatticeGlue` (G2): an isogeny `E₁ → E₂` over `ℚ` maps a period lattice of `E₁` into one of
`E₂` after multiplication by a nonzero RATIONAL number. This file proves G2 from two narrower named
glues, separating its analytic and its algebraic content:

* `IsPullbackScalar β r` (definition): the isogeny `β` pulls the invariant differential
  `ω₂ = dx₂ / (2y₂ + a₁x₂ + a₃)` back to `r · ω₁`, stated with Kähler differentials of the function
  field of the source, denominators cleared:
  `(2y₁ + a₁x₁ + a₃) · d(β^* x₂) = r · β^*(2y₂ + a₁x₂ + a₃) · dx₁` in `Ω[K(E₁)/F]`.
  In characteristic zero `Ω[K(E₁)/F]` is a line spanned by `dx₁ ≠ 0`, so the scalar, if it exists,
  is unique (Tau Ceti's `existsUnique_smul_invariantDifferential`; `IsogenyScalar.lean` proves
  `IsPullbackScalar β r ↔ β^* ω₂ = r • ω₁`). Non-vacuity: `isPullbackScalar_id` (the identity
  isogeny, `r = 1`; PROVED).
* `IsLatticeOfEmb σ E Lat` (definition): for `E` over a field `F` with an embedding `σ : F → ℂ`,
  `Lat` is the normalized period lattice of `E` over `ℂ` (`g₂ = σ(c₄)/12`, `g₃ = σ(c₆)/216`);
  for `F = ℚ` it is `IsLatticeOf` (`isLatticeOfEmb_ratCast`, PROVED).
* **`IsogenyLatticeAnalyticGlue` (G2an, GLUE)**: for an isogeny over a subfield `F ⊆ ℂ` (in
  particular over `ℂ` itself, `σ = id`) with pull-back scalar `α`, `σ(α) · Λ₁ ⊆ Λ₂` for the
  normalized period lattices. Classical proof: through the normalized uniformizations
  `x = ℘ − b₂/12`, `y = (℘′ − a₁x − a₃)/2`, which pull `ωᵢ` back to `dz`, the base change of `β`
  to `ℂ` is a holomorphic pointed map `ℂ/Λ₁ → ℂ/Λ₂`; its lift `ℂ → ℂ` has doubly periodic, hence
  constant, derivative, so it is `z ↦ c z` with `c Λ₁ ⊆ Λ₂`, and `c = σ(α)` because it pulls `dz`
  back to `c dz` (Silverman, *The Arithmetic of Elliptic Curves*, VI.4.1 and VI.5). Not proved here.
* **`IsogenyScalarRationalGlue` (G2alg, GLUE)**: an isogeny over `ℚ` has a pull-back scalar, and it
  is a nonzero rational number. Classical proof: `β^* ω₂` is a holomorphic invariant differential
  on `E₁`, so `β^* ω₂ = h ω₁` with `h ∈ ℚ(E₁)` without zeros or poles, hence a constant of
  `ℚ(E₁)`, i.e. `h ∈ ℚ`; `h ≠ 0` since `β` is nonconstant and separable in characteristic zero
  (Silverman III.5.2, II.4.2(c)). Not proved here; `IsogenyScalar.lean` reduces it to the
  constancy of the pull-back coefficient (`PullbackCoefficientConstantGlue`), proving the rest.
* **`isogenyLatticeGlue_of_glues` (PROVED)**: `IsogenyLatticeAnalyticGlue →
  IsogenyScalarRationalGlue → IsogenyLatticeGlue`.

**Why `j`-level information cannot replace G2alg.** Results relating the `j`-invariants of
isogenous curves (the vendored modular-polynomial theorems: `Φ_N(j(E₁), j(E₂)) = 0`, via Vélu
quotients) determine the lattices only up to homothety by a COMPLEX scalar, and they do not see
quadratic twists. Take `E₁` without complex multiplication and `E₂ = E₁^{(2)}` its quadratic twist
by `2`: `c₄(E₂) = c₄(E₁)/4`, `c₆(E₂) = c₆(E₁)/8` up to `ℚ`-isomorphism, so `j(E₂) = j(E₁)` and the
normalized lattices satisfy `Λ₂ = √2 · Λ₁`. If `r · Λ₁ ⊆ √2 · Λ₁` for a nonzero rational `r`, then
`r/√2` would be a multiplier of `Λ₁`, hence an integer (no complex multiplication), which is
absurd. So the `j`-relation (here `Φ₁(j₁, j₂) = j₁ − j₂ = 0`) holds while the conclusion of G2
fails; what excludes this case is the `ℚ`-rationality of the pull-back of the differential (`E₁`
and `E₁^{(2)}` are not isogenous over `ℚ`), i.e. G2alg. (Argument in prose, not formalised.)

Kinds: definitions, GLUE (the two named `Prop`s) and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.NewformPeriods

/-! ### The pull-back scalar of the invariant differential -/

section Differential

variable {F : Type} [Field F]

/-- The coordinate function `x` in the coordinate ring `F[x, y]/(W)`. -/
def coordX (W : WeierstrassCurve.Affine F) : W.CoordinateRing :=
  AdjoinRoot.of W.polynomial Polynomial.X

/-- The coordinate function `y` in the coordinate ring `F[x, y]/(W)`. -/
def coordY (W : WeierstrassCurve.Affine F) : W.CoordinateRing :=
  AdjoinRoot.root W.polynomial

/-- The denominator `2y + a₁x + a₃` of the invariant differential `ω = dx / (2y + a₁x + a₃)`. -/
def omegaDen (W : WeierstrassCurve.Affine F) : W.CoordinateRing :=
  2 * coordY W + AdjoinRoot.of W.polynomial (Polynomial.C W.a₁) * coordX W +
    AdjoinRoot.of W.polynomial (Polynomial.C W.a₃)

/-- **The pull-back scalar of an isogeny** (Silverman III.5.2): `β^* ω₂ = r · ω₁`, i.e.
`(2y₁ + a₁x₁ + a₃) · d(β^* x₂) = r · β^*(2y₂ + a₁x₂ + a₃) · dx₁` in the Kähler differentials of the
function field of the source over `F`. Kind: definition. -/
def IsPullbackScalar {W₁ W₂ : WeierstrassCurve.Affine F} (β : TauCeti.Isogeny W₁ W₂) (r : F) :
    Prop :=
  algebraMap W₁.CoordinateRing W₁.FunctionField (omegaDen W₁) •
      KaehlerDifferential.D F W₁.FunctionField (β.pullback (coordX W₂)) =
    (algebraMap F W₁.FunctionField r * β.pullback (omegaDen W₂)) •
      KaehlerDifferential.D F W₁.FunctionField
        (algebraMap W₁.CoordinateRing W₁.FunctionField (coordX W₁))

/-- **Non-vacuity of `IsPullbackScalar`**: the identity isogeny has pull-back scalar `1`.
PROVED. -/
theorem isPullbackScalar_id (W : WeierstrassCurve.Affine F) :
    IsPullbackScalar (TauCeti.Isogeny.id W) 1 := by
  unfold IsPullbackScalar
  simp only [TauCeti.Isogeny.id_pullback, TauCeti.CoordinatePullback.id_apply, map_one, one_mul]

end Differential

/-! ### Normalized period lattices over a subfield of `ℂ` -/

/-- **The normalized period lattice of a curve over a subfield of `ℂ`**: for `σ : F → ℂ`, `Lat`
has `g₂ = σ(c₄)/12` and `g₃ = σ(c₆)/216` (the lattice of the normalized uniformization of the base
change of `E` to `ℂ`). Kind: definition. -/
def IsLatticeOfEmb {F : Type} [Field F] (σ : F →+* ℂ) (E : WeierstrassCurve F)
    (Lat : PeriodPair) : Prop :=
  Lat.g₂ = σ E.c₄ / 12 ∧ Lat.g₃ = σ E.c₆ / 216

/-- For `F = ℚ`, `IsLatticeOfEmb` is `IsLatticeOf`. PROVED. -/
theorem isLatticeOfEmb_ratCast {E : WeierstrassCurve ℚ} {Lat : PeriodPair}
    (h : IsLatticeOf E Lat) : IsLatticeOfEmb (Rat.castHom ℂ) E Lat :=
  ⟨by rw [h.1]; rfl, by rw [h.2]; rfl⟩

/-! ### The two narrower glues and the reduction -/

/-- **G2an — over `ℂ`, an isogeny acts on the normalized lattices by its pull-back scalar**
(GLUE). For an isogeny `β : E₁ → E₂` over a field `F` with an embedding `σ : F → ℂ` (for `F = ℂ`,
`σ = id`: an isogeny over `ℂ`) and its pull-back scalar `α` (`β^* ω₂ = α ω₁`), the normalized
period lattices satisfy `σ(α) · Λ₁ ⊆ Λ₂`. Classical proof in the file header (Silverman VI.4.1,
VI.5). Not proved here. -/
def IsogenyLatticeAnalyticGlue : Prop :=
  ∀ (F : Type) [Field F] (σ : F →+* ℂ) (E₁ E₂ : WeierstrassCurve F), E₁.IsElliptic →
    E₂.IsElliptic → ∀ (β : TauCeti.Isogeny E₁.toAffine E₂.toAffine) (α : F),
      IsPullbackScalar β α → ∀ Lat₁ Lat₂ : PeriodPair, IsLatticeOfEmb σ E₁ Lat₁ →
        IsLatticeOfEmb σ E₂ Lat₂ → ∀ l ∈ Lat₁.lattice, σ α * l ∈ Lat₂.lattice

/-- **G2alg — the pull-back scalar of a `ℚ`-isogeny is a nonzero rational number** (GLUE). Every
isogeny `β : E₁ → E₂` over `ℚ` has a pull-back scalar `r ∈ ℚ`, `r ≠ 0`. Classical proof in the file
header (Silverman III.5.2, II.4.2(c); constants of `ℚ(E₁)`). Not proved here. -/
def IsogenyScalarRationalGlue : Prop :=
  ∀ E₁ E₂ : WeierstrassCurve ℚ, E₁.IsElliptic → E₂.IsElliptic →
    ∀ β : TauCeti.Isogeny E₁.toAffine E₂.toAffine, ∃ r : ℚ, r ≠ 0 ∧ IsPullbackScalar β r

/-- **G2 from G2an and G2alg**: the rational pull-back scalar of the `ℚ`-isogeny (G2alg) scales
`Λ₁` into `Λ₂` (G2an at `F = ℚ`, `σ = ℚ ↪ ℂ`). Classification: PROVED (from the two GLUEs). -/
theorem isogenyLatticeGlue_of_glues (han : IsogenyLatticeAnalyticGlue)
    (halg : IsogenyScalarRationalGlue) : IsogenyLatticeGlue := by
  intro E₁ E₂ h₁ h₂ hβ Lat₁ Lat₂ hL₁ hL₂
  obtain ⟨β⟩ := hβ
  obtain ⟨r, hr, hsc⟩ := halg E₁ E₂ h₁ h₂ β
  exact ⟨r, hr, fun l hl => han ℚ (Rat.castHom ℂ) E₁ E₂ h₁ h₂ β r hsc Lat₁ Lat₂
    (isLatticeOfEmb_ratCast hL₁) (isLatticeOfEmb_ratCast hL₂) l hl⟩

end ZInQ.Contrib.CloudB3RC53.ModularWeil
