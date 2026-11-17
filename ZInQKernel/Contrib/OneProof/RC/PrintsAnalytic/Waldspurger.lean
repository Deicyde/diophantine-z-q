import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Lane RC8: Waldspurger's comparison of squarefree Fourier coefficients (weight 3/2)

**Uses in the manuscript (11/5 text).** tex L2553–2563 (`One common family and the final order
of choices`): "The even source is a fixed algebraic vector in the full good-Hecke eigenspace.
Waldspurger's Corollary 2, including its same-dyadic-squareclass removal of the auxiliary
condition, compares the actual squarefree Fourier functionals [waldspurger]. ... each normalized
coefficient ratio is a rational number times a two-power root of unity." App E,
`ex:app-even-phase` (L7792–8205): the nonzero reference functional "is the content of Waldspurger's
global theta theorem and its Fourier-functional calculation [waldspurgerICM, Theorem 1 and
Proposition 1] and [waldspurger, Proposition 18 and its proof, pp. 466–467]" (L7829–7833); "The
nonzero space implies hypothesis (H1) by Waldspurger's Proposition 2 [Section I.2, p. 377]"
(L7957–7958); "Corollary 2 [pp. 483–484] applies to every `f ∈ V` and any positive squarefree pair
whose ratio is a square in every `ℚ_p` at a prime dividing the level" (L7960–7962); "In
[Corollary 2, pp. 483–484] take `k = 3, χ = ψ, χ₀ = ψχ_{-1}, ρ₀ = ρ_E ⊗ η, n₁ = D₀, n₂ = D`. ... The
corollary, in its printed order, is `a_f(D₀)² 𝓛_D ψ(D/D₀) D^{1/2} = a_f(D)² 𝓛_{D₀} D₀^{1/2}`", with
`𝓛_D = L(E^{(σD)}, 1)` (L7969–7981); hence (E.10).

**The print.** J.-L. Waldspurger, *Sur les coefficients de Fourier des formes modulaires de poids
demi-entier*, J. Math. Pures Appl. 60 (1981), 375–484. **Not read: UNVERIFIED** (no public copy was
found). The statement of Corollaire 2 used here is taken from S. Purkait, *Explicit application of
Waldspurger's theorem*, LMS J. Comput. Math. 16 (2013) 216–245, arXiv:1208.4329, Corollary 5.2
("We also state the following corollary of Waldspurger [30, p. 483]"), read:
> Let `φ ∈ S^{new}_{k-1}(M_φ, χ²)` be a newform such that `φ` satisfies (H1). Suppose
> `f(z) = ∑ aₙqⁿ ∈ S_{k/2}(N, χ, φ)` for some `N ≥ 1` such that `M_φ` divides `N/2`. Suppose that
> `n₁, n₂` are positive squarefree with `n₁/n₂ ∈ (ℚ_p^×)²` for all `p ∣ N`. Then
> `a²_{n₁} L(φ ⊗ χ₀^{-1}χ_{n₂}, 1) χ(n₂/n₁) n₂^{k/2-1} = a²_{n₂} L(φ ⊗ χ₀^{-1}χ_{n₁}, 1) n₁^{k/2-1}`,
with `χ₀(n) = χ(n)(-1/n)^{(k-1)/2}`, `S_{k/2}(N, χ, φ) = {f ∈ S'_{k/2}(N, χ) : T_{p²} f = λ_p(φ) f for
all p ∤ N}` (`S'` the orthogonal complement of the unary theta series), and "(H1)" Flicker's
condition, which holds when the space is nonzero (Purkait, Theorems 5, 6; the manuscript's
"Proposition 2"). Purkait's statement has no (H2), matching the manuscript's reading of the final
paragraph of Waldspurger's proof (p. 484) for a same-`ℚ₂`-squareclass pair. Proposition 18 and the
ICM theorem (the nonvanishing input) were not read either.

**Genuine definitions.** Half-integral weight forms are not in Mathlib; they are defined here
genuinely, following Shimura (*On modular forms of half integral weight*, Ann. of Math. 97 (1973)
440–481, §1), which is the setting of Waldspurger and Purkait:
* `thetaFun z = θ(z) = ∑_{n ∈ ℤ} e^{2πin²z}` (Mathlib's `jacobiTheta (2z)`);
* `thetaMultiplier γ z = j(γ, z) = θ(γz)/θ(z)` for `γ ∈ Γ₀(4)`;
* `IsHalfIntegralWeightCuspForm k N χ g`: `g` holomorphic on `ℍ`, `g(γz) = χ(d) j(γ, z)^k g(z)` for
  `γ = (a b; c d) ∈ Γ₀(N)` (`4 ∣ N`), and vanishing at every cusp in the branch-free form
  `|cz + d|^{-k/2} |g(αz)| → 0` as `Im z → ∞`, for every `α ∈ SL₂(ℤ)`;
* `hiwCoeff g n`: the `n`-th Fourier coefficient (Mathlib's `qExpansion` at width `1`; `g(z+1) = g(z)`
  since `T ∈ Γ₀(N)` and `j(T, z) = 1`);
* `heckeT3`: Shimura's `T(p²)` on Fourier coefficients in weight `3/2` (Shimura 1973, Theorem 1.7,
  with `λ = 1`): `b(n) = a(p²n) + χ(p)(-n/p) a(n) + χ(p)² p a(n/p²)`.
What is **not** formalized (size of a full theory): the finite dimensionality and the
`q`-expansion principle for these spaces, Hecke operators as operators on them, Petersson inner
products and the unary theta subspace, the Shimura lift (Shimura 1973, Main Theorem), Waldspurger's
theorems, and Ramsey's algebraic model (used by the manuscript for algebraicity). Nothing about
these definitions is proved here.

**Use check.** The manuscript takes `k = 3` (weight `3/2`), `χ = ψ`, `φ₀ = f_E ⊗ η` with
`η = ψχ_{-σ}`, so `φ₀ ⊗ χ₀^{-1} ⊗ χ_D = f_E ⊗ χ_{σD}` and `L(φ₀ ⊗ χ₀^{-1}χ_D, 1) = L(E^{(σD)}, 1)` ✓;
`V` is the full good-Hecke eigenspace (`T(p²)` eigenvalue `η(p)a_p(E)` at `p ∤ N`), which lies in `S'`
because unary theta series have good eigenvalues of absolute value `p + 1 > 2√p ≥ |η(p)a_p(E)|`
(L8053–8059) ✓; `M_{φ₀} ∣ N/2` and (H1) hold when `V ≠ 0` (Shimura's decomposition; Proposition 2)
✓; `D, D₀` are positive squarefree in the same unit classes at every prime of the level (`S₀`) ✓, and
prime to the level, so `ψ(D/D₀) = ψ(D)ψ(D₀)^{-1}` ✓. `WaldspurgerCor2` states the corollary in exactly
this specialization. `WaldspurgerNonvanishing` states the classical form of the nonvanishing input
that App E extracts from Proposition 18 and the ICM theorem: it includes Elliot's local
construction of a scalar `K₀`-type (App E L7837–7940; ELLIOT), and its print is UNVERIFIED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 UpperHalfPlane CongruenceSubgroup Filter
open scoped MatrixGroups

/-- **Jacobi's theta function** `θ(z) = ∑_{n ∈ ℤ} e^{2πin²z}` on `ℍ` (Mathlib's `jacobiTheta τ`
is `∑ e^{πin²τ}`, so `θ(z) = jacobiTheta (2z)`). -/
def thetaFun (z : ℍ) : ℂ := jacobiTheta (2 * (z : ℂ))

/-- **Shimura's theta multiplier** `j(γ, z) = θ(γz)/θ(z)`, the automorphy factor of weight `1/2` on
`Γ₀(4)` (Shimura, Ann. of Math. 97 (1973), §1; `θ` has no zeros on `ℍ`). -/
def thetaMultiplier (γ : SL(2, ℤ)) (z : ℍ) : ℂ := thetaFun (γ • z) / thetaFun z

/-- **`g` is a cusp form of weight `k/2`, level `N`, character `χ`** (Shimura's
`S_{k/2}(N, χ)`, `k` odd, `4 ∣ N`): holomorphic on `ℍ`; `g(γz) = χ(d) j(γ, z)^k g(z)` for every
`γ = (a b; c d) ∈ Γ₀(N)`; and `g` vanishes at every cusp: `|cz + d|^{-k/2} |g(αz)| → 0` as
`Im z → ∞`, for every `α = (a b; c d) ∈ SL₂(ℤ)` (the absolute value of `(g|_{k/2}α)(z)` for any
choice of the square root, so no branch enters). -/
def IsHalfIntegralWeightCuspForm (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℍ → ℂ) : Prop :=
  DifferentiableOn ℂ (g ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} ∧
  (∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ z : ℍ,
    g (γ • z) = χ ((γ 1 1 : ℤ) : ZMod N) * thetaMultiplier γ z ^ k * g z) ∧
  (∀ α : SL(2, ℤ), Tendsto
    (fun z : ℍ => ‖g (α • z)‖ * ‖((α 1 0 : ℤ) : ℂ) * (z : ℂ) + ((α 1 1 : ℤ) : ℂ)‖ ^ (-(k : ℝ) / 2))
    atImInfty (nhds 0))

/-- The `n`-th Fourier coefficient `a(n)` of a function of period `1` on `ℍ` (Mathlib's
`q`-expansion at width `1`). -/
def hiwCoeff (g : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 g).coeff n

/-- **Shimura's Hecke operator `T(p²)` in weight `3/2`, on Fourier coefficients** (Shimura 1973,
Theorem 1.7, `k = 3`, `λ = 1`), for a prime `p ∤ N`: `b(n) = a(p²n) + χ(p)(-n/p) a(n) + χ(p)² p a(n/p²)`,
with `a(n/p²) = 0` unless `p² ∣ n`; `(-n/p)` is the Legendre symbol. -/
def heckeT3 (N : ℕ) (χ : DirichletCharacter ℂ N) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (p ^ 2 * n) + χ p * (jacobiSym (-(n : ℤ)) p : ℂ) * a n +
    χ p ^ 2 * (p : ℂ) * (if p ^ 2 ∣ n then a (n / p ^ 2) else 0)

/-- **`g` lies in the full good-Hecke eigenspace attached to `E` and `η`**: a weight-`3/2` cusp
form of level `N` and character `ψ` with `T(p²) g = η(p) a_p(E) g` for every prime `p ∤ N` (the
eigenvalues of the Shimura lift `f_E ⊗ η`; the manuscript's space `V`, App E L7942–7955). -/
def IsInWaldspurgerEigenspace (E : WeierstrassCurve ℚ) (N : ℕ) (ψ η : DirichletCharacter ℂ N)
    (g : ℍ → ℂ) : Prop :=
  IsHalfIntegralWeightCuspForm 3 N ψ g ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      heckeT3 N ψ p (hiwCoeff g) n = η p * lcoeff E p * hiwCoeff g n

/-- `D` and `D₀` (positive, prime to `N`) lie in one unit squareclass at every prime of `N`:
`DD₀ ≡ 1 (mod 8)` at `2` and `DD₀` a square modulo odd `p ∣ N`; by Hensel this is
`D/D₀ ∈ (ℚ_p^×)²` for every `p ∣ N`. -/
def SameUnitClassesAtLevel (N D D₀ : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → (p = 2 → (D * D₀) % 8 = 1) ∧ (p ≠ 2 → IsSquare ((D * D₀ : ℕ) : ZMod p))

/-- **Waldspurger, Corollaire 2 (p. 483), weight `3/2`, in the specialization of App E
L7968–8028** (PRINT; J. Math. Pures Appl. 60 (1981) 375–484; print UNVERIFIED, statement from
Purkait, arXiv:1208.4329, Corollary 5.2). Let `E/ℚ` be an elliptic curve, `4 ∣ N`, `ψ, η` Dirichlet
characters modulo `N` with `η = ψχ_{-σ}` (`σ = ±1`) on integers prime to `N`, and `g` in the full
good-Hecke eigenspace of `E` and `η` (`T(p²) g = η(p)a_p(E) g` at `p ∤ N`). For positive squarefree
`D₀, D` prime to `N`, in one unit squareclass at every prime of `N`, and entire continuations `F₀`,
`F` of `L(E^{(σD₀)}, s)` and `L(E^{(σD)}, s)`:
`a_g(D₀)² L(E^{(σD)}, 1) ψ(D) ψ(D₀)^{-1} √D = a_g(D)² L(E^{(σD₀)}, 1) √D₀`
(the corollary "in its printed order", App E L7978–7981). -/
def WaldspurgerCor2 : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ N : ℕ, 4 ∣ N →
    ∀ (ψ η : DirichletCharacter ℂ N) (σ : ℤ), (σ = 1 ∨ σ = -1) →
      (∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)) →
      ∀ g : ℍ → ℂ, IsInWaldspurgerEigenspace E N ψ η g →
        ∀ D₀ D : ℕ, 0 < D₀ → 0 < D → Squarefree D₀ → Squarefree D → D₀.Coprime N →
          D.Coprime N → SameUnitClassesAtLevel N D D₀ →
          ∀ F₀ F : ℂ → ℂ, IsLContinuation (qtwist E ((σ * D₀ : ℤ) : ℚ)) F₀ →
            IsLContinuation (qtwist E ((σ * D : ℤ) : ℚ)) F →
            hiwCoeff g D₀ ^ 2 * F 1 * ψ D * (ψ D₀)⁻¹ * (Real.sqrt D : ℂ) =
              hiwCoeff g D ^ 2 * F₀ 1 * (Real.sqrt D₀ : ℂ)

/-- **Waldspurger's nonvanishing input, in the classical form App E extracts from it** (PRINT +
ELLIOT; J. Math. Pures Appl. 60 (1981), Proposition 18 and its proof, pp. 466–467, and Waldspurger,
ICM 1983, Theorem 1 and Proposition 1, as cited at App E L7829–7833: the nonzero central value
supplies a theta lift with nonzero `D₀`-th Whittaker functional; the passage to a classical form with
scalar character and level supported on `S₀` is Elliot's local construction, App E L7837–7940;
print UNVERIFIED). Let `S₀ ∋ 2` contain every prime of the conductor of `E` (the level of a
functional equation of `L(E, s)`), `σ = ±1`, and `D₀ > 0` squarefree prime to `S₀` with
`L(E^{(σD₀)}, 1) ≠ 0`. Then for some `N` with `4 ∣ N` and prime support in `S₀`, and characters
`ψ, η = ψχ_{-σ}` modulo `N`, the eigenspace of `E` and `η` contains `g` with `a_g(D₀) ≠ 0`. -/
def WaldspurgerNonvanishing : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
    ∀ S₀ : Finset ℕ, (∀ p ∈ S₀, p.Prime) → 2 ∈ S₀ →
      (∀ (N : ℕ) (w : ℤ), RootNumberAt E N w → ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) →
      ∀ D₀ : ℕ, 0 < D₀ → Squarefree D₀ → (∀ p ∈ S₀, ¬ p ∣ D₀) →
        AnalyticRank (qtwist E ((σ * D₀ : ℤ) : ℚ)) 0 →
        ∃ N : ℕ, 4 ∣ N ∧ (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S₀) ∧
          ∃ ψ η : DirichletCharacter ℂ N,
            (∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)) ∧
            ∃ g : ℍ → ℂ, IsInWaldspurgerEigenspace E N ψ η g ∧ hiwCoeff g D₀ ≠ 0

end ZInQ.Manuscript.RC.PrintsAnalytic
