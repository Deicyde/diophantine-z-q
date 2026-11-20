import ZInQKernel.Contrib.OneProof.PoleS12.Leaves
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators

/-!
# Theorem A of Breuil–Conrad–Diamond–Taylor, as printed, with condition (2)

C. Breuil, B. Conrad, F. Diamond and R. Taylor, *On the modularity of elliptic curves over `ℚ`:
wild 3-adic exercises*, J. Amer. Math. Soc. 14 (2001), 843–939; the manuscript cites the author
manuscript (bibitem `bcdt`, `\cite[Theorem A]{bcdt}`). Page images of pp. 1–3 of the author
manuscript were read. This file states the printed Theorem A, read with the Introduction's
condition (2), over the existing objects:

* cusp forms of weight `k` and level `N` (p. 1): Mathlib's `CuspForm` on `Γ₁(N)`;
* the Fourier coefficients `c_n(f)` and the L-series `L(f, s) = ∑ c_n(f)/n^s` (p. 1): the
  coefficients of the `q`-expansion of period one and Mathlib's `LSeries` of them;
* the Hecke operators `T_p`, `p ∤ N` (p. 2): the vendored double-coset operator `heckeTCuspNat`;
  `Dictionary.lean` proves that it is given by the printed formula;
* an eigenform (p. 2): a simultaneous eigenvector of the `T_p` for the primes `p ∤ N` — neither
  normalisation, nor a nebentypus, nor an eigenvalue at the primes dividing `N` is part of the
  printed notion, and none is assumed;
* `L(E, s)` (p. 3): Mathlib's `WeierstrassCurve.LSeries`.

The level of condition (2) is the conductor `N(E)`. The library has no conductor of an elliptic
curve, so `BCDTThmAPrinted` keeps an unspecified positive level: it is implied by the printed
statement, which it weakens only by forgetting that the level is `N(E)`.
`BCDTThmAPrintedAtLevel` is the same statement at a prescribed level function, the printed one
for the conductor. `Descent.lean` proves `BCDTThmAPrinted → PoleS12.BCDTThmA`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.BCDTPrint

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2

/-- **DEFINITION**, an eigenform in the sense of Breuil–Conrad–Diamond–Taylor, Introduction,
p. 2 of the author manuscript: "The operators `T_p` for `p ∤ N` can be simultaneously
diagonalised on the space `S_k(N)` and a simultaneous eigenvector is called an *eigenform*."
Here `S_k(N)` is the space of cusp forms of weight `k` on `Γ₁(N)` (p. 1) and `T_p` is the
vendored Hecke operator `heckeTCuspNat k p` of the double coset `Γ₁(N) diag(1, p) Γ₁(N)`, given
by the printed formula (`heckeTCuspNat_apply_eq_printed`, `Dictionary.lean`); the notion is the
printed one (`isPrintedEigenform_iff`, `Literal.lean`). An eigenvector is nonzero. No
normalisation `c_1(f) = 1`, no diamond (nebentypus) eigen-relation and no eigen-relation at the
primes dividing `N` is required: the print requires none. -/
def IsBCDTEigenform {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  f ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ N →
    ∃ c : ℂ, heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f = c • f

/-- **DEFINITION**, the L-series of a cusp form, Breuil–Conrad–Diamond–Taylor, p. 1 of the
author manuscript: "If `f ∈ S_k(N)` then it has an expansion `f(z) = ∑_{n=1}^∞ c_n(f) e^{2πinz}`
and we define the L-series of `f` to be `L(f, s) = ∑_{n=1}^∞ c_n(f)/n^s`." The coefficient
`c_n(f)` is the `n`-th coefficient of the `q`-expansion of period one (the translation
`z ↦ z + 1` lies in `Γ₁(N)`), and the series is Mathlib's `LSeries`. -/
def cuspLSeries {N : ℕ} {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (qExpansion 1 f).coeff n) s

/-- **DEFINITION**, condition (2) of Breuil–Conrad–Diamond–Taylor, Introduction, p. 3 of the
author manuscript, at a given level `N`: "The L-function `L(E, s)` of `E` equals the L-function
`L(f, s)` for some eigenform `f` of weight 2 and level `N(E)`", with `N` in place of `N(E)`.
`L(E, s)` is Mathlib's `WeierstrassCurve.LSeries` (the Dirichlet series of the Euler product of
the local factors of the minimal models) and `L(f, s)` is `cuspLSeries f`. The two L-functions
are compared where they are Dirichlet series, on a right half-plane `Re s > σ`; equality there
determines the analytic continuations by the identity theorem. For an eigenform this equality is
equivalent to `c_n(f) = a_n(E)` for every `n ≥ 1` (`coeff_eq_of_eq_cuspLSeries`, `Descent.lean`;
`condition2At_iff`, `Dictionary.lean`). -/
def Condition2At (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] : Prop :=
  ∃ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2, IsBCDTEigenform f ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries f s

/-- **PRINT**, Breuil–Conrad–Diamond–Taylor, Theorem A, read with condition (2) of the
Introduction; J. Amer. Math. Soc. 14 (2001) 843–939; the author manuscript is the cited copy
(bibitem `bcdt`), pp. 1–3, page images read. This is a proposition, not an axiom.

Verbatim printed text. Theorem A (p. 1): "Theorem A. If `E/ℚ` is an elliptic curve, then `E`
is modular." Definitions (p. 1): "If `N` is a positive integer then we let `Γ₁(N)` denote the
subgroup of `SL₂(ℤ)` consisting of matrices that modulo `N` are of the form `(1 ∗; 0 1)`. [...]
Recall that a cusp form of weight `k ≥ 1` and level `N ≥ 1` is a holomorphic function `f` on the
upper half complex plane `𝔥` such that • for all matrices `(a b; c d) ∈ Γ₁(N)` and all `z ∈ 𝔥`,
we have `f((az + b)/(cz + d)) = (cz + d)^k f(z)`; • and `|f(z)|² (Im z)^k` is bounded on `𝔥`.
The space `S_k(N)` of cusp forms of weight `k` and level `N` is a finite dimensional complex
vector space. If `f ∈ S_k(N)` then it has an expansion `f(z) = ∑_{n=1}^∞ c_n(f) e^{2πinz}` and
we define the L-series of `f` to be `L(f, s) = ∑_{n=1}^∞ c_n(f)/n^s`." Hecke operators and
eigenforms (p. 2): "For each prime `p ∤ N` there is a linear operator `T_p` on `S_k(N)` defined
by `(f|T_p)(z) = p^{−1} ∑_{i=0}^{p−1} f((z + i)/p) + p^{k−1} (cpz + d)^{−k}
f((apz + b)/(cpz + d))` for any `(a b; c d) ∈ SL₂(ℤ)` with `c ≡ 0 mod N` and `d ≡ p mod N`.
The operators `T_p` for `p ∤ N` can be simultaneously diagonalised on the space `S_k(N)` and a
simultaneous eigenvector is called an eigenform. If `f` is an eigenform then the corresponding
eigenvalues, `a_p(f)`, are algebraic integers and we have `c_p(f) = a_p(f) c_1(f)`." Modularity
(pp. 2–3): "Now consider an elliptic curve `E/ℚ`. [...] Let `N(E)` denote the conductor of `E`.
It is known that the following conditions are equivalent. (1) The L-function `L(E, s)` of `E`
equals the L-function `L(f, s)` for some eigenform `f`. (2) The L-function `L(E, s)` of `E`
equals the L-function `L(f, s)` for some eigenform `f` of weight 2 and level `N(E)`. [...]
When these equivalent conditions are satisfied we call `E` modular."

Formalized: every elliptic curve `E/ℚ` satisfies condition (2) (`Condition2At`) at some positive
level. Faithfulness notes: (i) the level is not identified with the conductor `N(E)`, which the
library lacks, so the statement is implied by the print and is weaker only in that respect
(`BCDTThmAPrintedAtLevel` is the printed form at a prescribed level); (ii) `S_k(N)` is Mathlib's
`CuspForm` on `Γ₁(N)`, which `Dictionary.lean` identifies with the printed definition
(`isPrintedCuspForm_iff`); (iii) `T_p` is the vendored double-coset operator, given by the
printed formula (`heckeTCuspNat_apply_eq_printed`); (iv) an eigenform is exactly
`IsBCDTEigenform`; (v) the equality of L-functions is required on some right half-plane only,
which for an eigenform is equivalent to `c_n(f) = a_n(E)` for all `n ≥ 1` (`condition2At_iff`).
`Literal.lean` writes the same statement with the printed definitions themselves (cusp forms as
functions, the printed `T_p`, the printed expansion) and proves it equivalent
(`bcdtThmAPrintedLiteral_iff`). -/
def BCDTThmAPrinted : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ (N : ℕ) (_ : NeZero N), Condition2At E N

/-- **DEFINITION**, Theorem A with condition (2) at a prescribed level function. For
`level E = N(E)`, the conductor, this is condition (2) at level N(E) as printed; for another level
function it is merely the corresponding statement, asserted by nothing here, and it can be false
(for example for the constant level 1, since there are no weight-two cusp forms of level one).
It is not used as the printed statement. It implies `BCDTThmAPrinted`
(`bcdtThmAPrinted_of_atLevel`). -/
def BCDTThmAPrintedAtLevel (level : WeierstrassCurve ℚ → ℕ+) : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → Condition2At E (level E : ℕ)

/-- **PROVED**, by forgetting the level: Theorem A at any positive level function gives
`BCDTThmAPrinted`. -/
theorem bcdtThmAPrinted_of_atLevel {level : WeierstrassCurve ℚ → ℕ+}
    (h : BCDTThmAPrintedAtLevel level) : BCDTThmAPrinted :=
  fun E hE => ⟨level E, inferInstance, h E hE⟩

end ZInQ.Contrib.RC53Assist.BCDTPrint
