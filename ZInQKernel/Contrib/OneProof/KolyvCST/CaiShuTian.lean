import ZInQKernel.Contrib.OneProof.PoleS12.Leaves
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.EichlerIntegral.Basic

/-!
# Cai–Shu–Tian, Theorem 1.1 (explicit Gross–Zagier formula): the part that can be stated

Task kolyv-cst-printed. The manuscript (`diophantine_zq.tex`) cites
`\cite[Theorem 1.1]{cst}` at L2428 (proof of Proposition `ex:sec7-genus-lower`: "applies
twice", with the conditions of L2429–2432) and at L8268–8272 (proof of Proposition
`ex:app-detector`: "the unaveraged height formula", with Rankin derivative
`L'(E^{(D_w)},1) L(E^{(h_*)},1) ≠ 0`, so `P_{D_w}` is nontorsion). Bibitem L11181–11183:
L. Cai, J. Shu and Y. Tian, "Explicit Gross–Zagier and Waldspurger formulae", Algebra & Number
Theory 8 (2014), arXiv:1408.1733. **Not read for this task** (no network): every clause below is
UNVERIFIED (pending reading); docs/research/kolyv-cst-printed.md §2 lists what a print reader must
check. No proof of the theorem and no Gross–Zagier argument is written here.

## What is stated: `CSTThm11Split`

A special case (never stronger) of Theorem 1.1, in the domain the manuscript uses:

* `E/ℚ` an elliptic curve without complex multiplication, `f` the weight-2 cusp form on `Γ₀(N)`
  with `q`-expansion coefficients the Dirichlet coefficients of Mathlib's `L`-series of `E`, at the
  least such level `N` (`newformLevel`, written fresh: the level of the newform of `E`);
* `φ` a complex-analytic modular parametrization `τ ↦ ℘_Λ(κ · ∫ f)`, with `Λ` a lattice of `E`
  (`phiAn`, written fresh; Mathlib's `℘` and Tau Ceti's Eichler integral);
* `K` imaginary quadratic of discriminant `D ∉ {−3, −4}` (no extra units: `u = 1`), **every prime
  of `N` split in `K`** (so `μ(N, D) = 0` and the condition at primes of `(N, D)` is vacuous),
  `c ≥ 1` prime to `N`, `O_c = ℤ + c𝓞_K` (`conductorOrder`), `H_c` its ring class field and
  `χ : Pic(O_c) → ℂ^×` primitive (Tau Ceti's `ringClassField`, `ringClassArtinEquiv`);
* the Heegner point: `τ` the root in `ℍ` of a primitive form `[A, B, C]` with `N ∣ A` and
  discriminant `Dc²`, and **any** `y ∈ E(H_c)` whose image under an embedding `ι : H_c → ℂ` is
  `φ(τ)`; `P_t = σ_t(y)` with `σ_t` the Artin image of `t ∈ Pic(O_c)`;
* `L(s, E, χ)` the Euler product over the primes `𝔭` of `K` of Mathlib's local factors of `E/K`
  at `T = χ(𝔭) N𝔭^{-s}`, with `χ(𝔭) = 0` for `𝔭 ∣ c` (`twistedLFunction`, written fresh);
* `ĥ_K = ĥ_{H_c}/[H_c : K]`, with `ĥ_{H_c}` Tau Ceti's Néron–Tate pairing over the number field
  `H_c` (relative to `H_c`), extended hermitian-linearly to `P_χ = Σ_t χ(t) P_t`.

Conclusion: there is `C > 0` depending only on `(E, f, Λ, κ)` such that
`L'(1, E, χ) = C / (c √|D|) · ĥ_K(P_χ)` for all such `(K, c, χ, [A,B,C], ι, y)`. The print has
`C = 8π² (f, f)_{Γ₀(N)} / deg φ` (as an earlier audit and the manuscript's L2430–2431 describe it;
UNVERIFIED): the Petersson norm and `deg φ` are fixed by `(E, f, Λ, κ)`, so the existential `C`
is a consequence of the print, and it is what both manuscript uses need (L2428: the ratio of two
instances, L2433–2436; L8269: nonvanishing ⇔ nontorsion).

## What is not stated, and why (stop rule)

* **`X₀(N)` over `ℚ`, the algebraic Heegner point `x_c ∈ X₀(N)(H_c)` and the parametrization
  `φ : X₀(N) → E` over `ℚ`** are absent from Mathlib and Tau Ceti. The statement replaces them by
  the complex-analytic model and quantifies over every algebraic `y` with `ι(y) = φ(τ)`. The
  dictionary (Shimura's theory of CM points and the Eichler–Shimura construction) is a
  translation, not a Lean theorem: provenance (c), on the spot. For non-CM `E` every analytic `φ`
  allowed here is `n β ∘ φ₀` with `φ₀` algebraic over `ℚ` and `β` a `ℚ`-isogeny (the reason for
  the non-CM hypothesis).
* **The Rankin–Selberg `L(s, f × θ_χ)`** is absent; `twistedLFunction` is the Euler product of
  `E/K` twisted by `χ`. Their equality (automorphic induction of `χ`; local factors at `𝔭 ∣ c`
  equal to `1` for primitive `χ`) is a translation, provenance (c), SPECULATIVE at `𝔭 ∣ c`.
* **The constant** `8π²(f, f)/deg φ` (Tau Ceti has Petersson products, `CuspForm.peterssonInnerCosets`,
  but `deg φ` needs `X₀(N)`): replaced by the existential `C > 0`, a consequence.
* The general hypotheses at primes `p ∣ N` that are not split are not stated (the print's
  conditions there are known only through the audit summary): special case only.
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain ArithmeticFunction Complex
open scoped UpperHalfPlane

namespace ZInQ.Manuscript.KolyvCST.CST

/-! ### The order `ℤ + c𝓞_K` (copied from `ZInQ.Contrib.TYZGenus.RingClass`, whose module imports
Route K) -/

section ConductorOrder

variable (K : Type) [Field K] [NumberField K]

/-- `ℤ + c 𝓞_K` as a `ℤ`-subalgebra of `K` (copy of `TYZGenus.RingClass.conductorOrderSubalgebra`). -/
def conductorOrderSubalgebra (f : ℕ) : Subalgebra ℤ K where
  carrier := {x | ∃ a : ℤ, ∃ y : 𝓞 K, x = a + f * (y : K)}
  mul_mem' := by
    rintro _ _ ⟨a, y, rfl⟩ ⟨b, z, rfl⟩
    refine ⟨a * b, a * z + b * y + f * y * z, ?_⟩
    simp only [map_add, map_mul, map_intCast, map_natCast, Int.cast_mul]
    ring
  add_mem' := by
    rintro _ _ ⟨a, y, rfl⟩ ⟨b, z, rfl⟩
    exact ⟨a + b, y + z, by simp only [map_add, Int.cast_add]; ring⟩
  algebraMap_mem' := fun r => ⟨r, 0, by simp⟩

theorem conductorOrderSubalgebra_le_integralClosure (f : ℕ) :
    conductorOrderSubalgebra K f ≤ integralClosure ℤ K := by
  rintro _ ⟨a, y, rfl⟩
  exact (integralClosure ℤ K).add_mem ((integralClosure ℤ K).algebraMap_mem a)
    ((integralClosure ℤ K).mul_mem ((integralClosure ℤ K).natCast_mem f) y.2)

/-- **The order `O_c = ℤ + c 𝓞_K`** (copy of `TYZGenus.RingClass.conductorOrder`); for an
imaginary quadratic `K` it is the order of conductor `c`. -/
def conductorOrder (f : ℕ) [NeZero f] : NumberFieldOrder K where
  toSubalgebra := conductorOrderSubalgebra K f
  finite := by
    have h := conductorOrderSubalgebra_le_integralClosure K f
    have : Module.Finite ℤ (integralClosure ℤ K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
    exact Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  spans := by
    apply top_unique
    rw [← (maximalNumberFieldOrder K).spans]
    apply Submodule.span_le.mpr
    intro y hy
    have hf : ((f : ℚ)) ≠ 0 := by exact_mod_cast NeZero.ne f
    have hmem : (f : K) * y ∈ conductorOrderSubalgebra K f :=
      ⟨0, ⟨y, hy⟩, by rw [Int.cast_zero, zero_add]; rfl⟩
    have : y = (f : ℚ)⁻¹ • ((f : K) * y) := by
      rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hf), one_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end ConductorOrder

/-! ### The newform of `E` and its level -/

/-- `E` has a weight-2 cusp form on `Γ₀(N)` whose `q`-expansion coefficients are the Dirichlet
coefficients of Mathlib's `L`-function of `E` (`PoleS12.IsModular` at the level `N`). -/
def HasCuspFormAtLevel (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2,
    ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)

/-- **The level of the newform of `E`** (written fresh): the least `N > 0` at which `E` has a
weight-2 cusp form on `Γ₀(N)` with the coefficients of `L(E, s)`. The `q`-expansion determines
the function, so that form is the newform `f_E` (a newform of level `N` lies in no `S₂(Γ₀(M))`
with `M < N`, since `Γ₀(M)` and `Γ₀(N)` generate `Γ₀(gcd(M, N))`); by Carayol this level is the
conductor of `E` (the `N` of the print). `0` if `E` is not modular (never, by BCDT). -/
def newformLevel (E : WeierstrassCurve ℚ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ HasCuspFormAtLevel E N}

/-! ### The complex-analytic modular parametrization (written fresh) -/

/-- The weight-2 Eichler integral `τ ↦ Σ_{m ≥ 1} (a_m/m) qᵐ = 2πi ∫_{i∞}^τ f(z) dz` (Tau Ceti's
`eichlerIntegral` at width 1, order 1). -/
def eichlerPotential (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  TauCeti.eichlerIntegral 1 1 f τ

/-- The point of `E(ℂ)` with Weierstrass coordinates `x = ℘_Λ(z) − b₂/12`,
`y = (℘'_Λ(z) − a₁x − a₃)/2` (`O` for `z ∈ Λ`). For a lattice with `g₂ = c₄/12`, `g₃ = c₆/216`
(`IsLatticeOf`) the coordinates satisfy the equation of `E` off `Λ`, so the second `if` never
takes its `else` branch there; it only avoids a proof inside the definition. -/
def weierPt (E : WeierstrassCurve ℚ) (Λ : PeriodPair) (z : ℂ) : (E.baseChange ℂ).toAffine.Point :=
  if z ∈ Λ.lattice then 0 else
    if h : (E.baseChange ℂ).toAffine.Nonsingular (Λ.weierstrassP z - (E.b₂ : ℂ) / 12)
        ((Λ.derivWeierstrassP z - (E.a₁ : ℂ) * (Λ.weierstrassP z - (E.b₂ : ℂ) / 12) -
          (E.a₃ : ℂ)) / 2) then
      .some _ _ h
    else 0

/-- `Λ` is a period lattice of `E`: `ℂ/Λ ≅ E(ℂ)` through `weierPt` (`g₂ = c₄/12`,
`g₃ = c₆/216`). -/
def IsLatticeOf (E : WeierstrassCurve ℚ) (Λ : PeriodPair) : Prop :=
  Λ.g₂ = (E.c₄ : ℂ) / 12 ∧ Λ.g₃ = (E.c₆ : ℂ) / 216

/-- `Λ` has no complex multiplication: its only multipliers are the integers (`E` has no CM). -/
def IsNonCMLattice (Λ : PeriodPair) : Prop :=
  ∀ α : ℂ, (∀ l ∈ Λ.lattice, α * l ∈ Λ.lattice) → ∃ n : ℤ, α = n

/-- `κ ≠ 0` scales the periods of `f` on `Γ₀(N)` into `Λ`, so that `phiAn` is `Γ₀(N)`-invariant:
an analytic map `X₀(N)(ℂ) → E(ℂ)` with `∞ ↦ O`. -/
def IsParamScale (N : ℕ) (f : ℍ → ℂ) (Λ : PeriodPair) (κ : ℂ) : Prop :=
  κ ≠ 0 ∧ ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ,
    κ * (eichlerPotential f (γ • τ) - eichlerPotential f τ) ∈ Λ.lattice

/-- **The analytic modular parametrization** `φ(τ) = ℘_Λ-point of κ · ∫_{i∞}^τ 2πi f`. -/
def phiAn (E : WeierstrassCurve ℚ) (f : ℍ → ℂ) (Λ : PeriodPair) (κ : ℂ) (τ : ℍ) :
    (E.baseChange ℂ).toAffine.Point :=
  weierPt E Λ (κ * eichlerPotential f τ)

/-! ### Heegner forms and CM points -/

/-- `[A, B, C]` is a Heegner form of level `N` and discriminant `Δ`: `A > 0`, `N ∣ A`,
`B² − 4AC = Δ`, primitive. When `gcd(N, Δ) = 1` its root `τ` and `Nτ` have the same
discriminant, so `τ` is a Heegner point of `X₀(N)` with CM by the order of discriminant `Δ`. -/
def IsHeegnerForm (N : ℕ) (Δ A B C : ℤ) : Prop :=
  0 < A ∧ (N : ℤ) ∣ A ∧ B ^ 2 - 4 * A * C = Δ ∧ Int.gcd (Int.gcd A B) C = 1

/-- The root `(−B + √Δ)/(2A)` in the upper half plane (`i` if it is not there, which does not
happen for `A > 0`, `Δ < 0`). -/
def cmPoint (A B Δ : ℤ) : ℍ :=
  let z : ℂ := (-(B : ℂ) + I * (Real.sqrt (-(Δ : ℝ)) : ℂ)) / (2 * (A : ℂ))
  if h : 0 < z.im then ⟨z, h⟩ else UpperHalfPlane.I

/-! ### Ring class characters and the twisted `L`-function (written fresh) -/

section RingClass

variable {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- `χ(𝔭)` for a prime `𝔭` of `K`: `χ` of the class of `𝔭 ∩ O` in `Pic O` (Tau Ceti's `picClass`)
if `𝔭` is prime to the conductor of `O`, and `0` otherwise. -/
def chiAt (χ : Pic O →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if h : 𝔭.asIdeal ∈ integralIdealsPrimeTo O.conductorModulus then
    ((χ (O.picClass ⟨𝔭.asIdeal, h⟩) : ℂˣ) : ℂ)
  else 0

/-- **`L(s, E, χ)` as a formal Dirichlet series** (written fresh): the Euler product over the
primes `𝔭` of `K` of `1/f_𝔭(χ(𝔭) N𝔭^{-s})`, where `f_𝔭` is Mathlib's local polynomial of
`E/K` at `𝔭` (minimal model over `K_𝔭`: `1 − a T + N𝔭 T²`, `1 ∓ T` or `1`). This is
`WeierstrassCurve.LFunction` of `E/K` with each local factor twisted by `χ(𝔭)`
(`localPowerSeries` rescaled by `χ(𝔭)`); for `𝔭 ∣ c` the factor is `1`. -/
def twistedLFunction (E : WeierstrassCurve ℚ) (χv : HeightOneSpectrum (𝓞 K) → ℂ) :
    ArithmeticFunction ℂ :=
  eulerProduct fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
    ofPowerSeries (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
      (PowerSeries.rescale (χv 𝔭) (PowerSeries.map (Int.castRingHom ℂ)
        (((E.baseChange K).baseChange (𝔭.adicCompletion K)).localPowerSeries
          (𝔭.adicCompletionIntegers K))))

end RingClass

/-- `χ : Pic(O_c) → ℂ^×` is **primitive** of conductor `c`: for no proper divisor `c'` of `c`
does it factor through `Gal(H_{c'}/K)`, i.e. for each such `c'` some `σ ∈ Gal(H_c/K)` fixing
`H_c ∩ H_{c'}` has `χ(σ) ≠ 1` (in `Kˢ`, `H_{c'} ⊆ H_c`). -/
def IsPrimitiveRingClassChar (K : Type) [Field K] [NumberField K] (c : ℕ) [NeZero c]
    (χ : Pic (conductorOrder K c) →* ℂˣ) : Prop :=
  ∀ c' : ℕ, ∀ _ : NeZero c', c' ∣ c → c' ≠ c →
    ∃ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
      (∀ x : ringClassField (conductorOrder K c),
        (x : SeparableClosure K) ∈ ringClassField (conductorOrder K c') → σ x = x) ∧
      χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) ≠ 1

/-- The rational prime `p` splits in `K`: `p𝓞_K = 𝔭𝔮` with `𝔭 ≠ 𝔮` maximal. -/
def SplitsIn (K : Type) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∃ 𝔭 𝔮 : Ideal (𝓞 K), 𝔭.IsMaximal ∧ 𝔮.IsMaximal ∧ 𝔭 ≠ 𝔮 ∧
    Ideal.span {(p : 𝓞 K)} = 𝔭 * 𝔮

/-! ### The height of `P_χ` -/

section Height

variable {H : Type} [Field H] [NumberField H] (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- `ĥ_{H}`-pairing of `E(H)`: Tau Ceti's Néron–Tate pairing over the number field `H`
(heights relative to `H`, `[H : ℚ]` times the absolute height). -/
def ntPairing (P Q : (E.baseChange H).toAffine.Point) : ℝ :=
  WeierstrassCurve.Affine.neronTatePairing (E.baseChange H).toAffine P Q

end Height

/-- **Cai–Shu–Tian, Theorem 1.1, split case (stated, not proved).** See the module docstring for
the objects. For every non-CM elliptic curve `E/ℚ` with newform `f` of level `N`, period lattice
`Λ` and analytic parametrization scale `κ`, there is `C > 0` such that for every imaginary quadratic
`K` with discriminant `D ∉ {−3, −4}` in which every prime of `N` splits, every `c ≥ 1` prime to
`N`, every primitive ring class character `χ` of `Pic(O_c)`, every Heegner form `[A, B, C]` of
level `N` and discriminant `Dc²`, every embedding `ι : H_c → ℂ` and every `y ∈ E(H_c)` with
`ι(y) = φ(τ_{[A,B,C]})`, and every entire continuation `F` of `L(s, E, χ)`:
`F'(1) = C / (c √|D|) · ĥ_K(Σ_t χ(t) σ_t y)`, with
`ĥ_K(Σ_t χ(t) P_t) = [H_c : K]⁻¹ Σ_{t,t'} χ(t) conj χ(t') ⟨P_t, P_{t'}⟩_{H_c}`.

Provenance (b), cited by the manuscript (bibitem `cst`, L11181–11183; cited L2428, L8269).
Rating: printed form, special case, over written-fresh definitions; UNVERIFIED (pending reading),
counts GLUE. -/
def CSTThm11Split : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2),
    (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
    ∀ (Λ : PeriodPair), IsLatticeOf E Λ → IsNonCMLattice Λ →
    ∀ κ : ℂ, IsParamScale (newformLevel E) f Λ κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
        discr K ≠ -3 → discr K ≠ -4 →
        (∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p) →
        ∀ (c : ℕ) [NeZero c], Nat.Coprime c (newformLevel E) →
        ∀ χ : Pic (conductorOrder K c) →* ℂˣ, IsPrimitiveRingClassChar K c χ →
        ∀ A B C' : ℤ, IsHeegnerForm (newformLevel E) (discr K * c ^ 2) A B C' →
        ∀ ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ,
        ∀ y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point,
          WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
            phiAn E f Λ κ (cmPoint A B (discr K * c ^ 2)) →
        ∀ F : ℂ → ℂ, Differentiable ℂ F →
          (∀ s : ℂ, 3 / 2 < s.re →
            F s = LSeries (twistedLFunction E (chiAt (conductorOrder K c) χ)) s) →
          deriv F 1 =
            ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) *
              (((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ)⁻¹ : ℝ) : ℂ) *
              ∑ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
              ∑ σ' : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
                ((χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℂˣ) : ℂ) *
                  (starRingEnd ℂ) ((χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ') :
                    ℂˣ) : ℂ) *
                  ((ntPairing E
                    (WeierstrassCurve.Affine.Point.map (W' := E.toAffine)
                      (σ.toAlgHom.restrictScalars ℚ) y)
                    (WeierstrassCurve.Affine.Point.map (W' := E.toAffine)
                      (σ'.toAlgHom.restrictScalars ℚ) y) : ℝ) : ℂ)

end ZInQ.Manuscript.KolyvCST.CST
