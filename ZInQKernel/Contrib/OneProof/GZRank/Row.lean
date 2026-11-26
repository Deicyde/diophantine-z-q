import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Statement
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# The single-print rows that replace `hRank`

Two rows, each one refereed printed theorem read as a direct instance:

* `GZThm73NonTorsion`: Gross–Zagier, *Heegner points and derivatives of L-series*,
  Invent. Math. 84 (1986), 225–320, Theorem (7.3)(1), p. 231, in the form proved in
  Chapter V, §2, pp. 309–312 (standing assumption of p. 310).
* `CarayolCor08`: Carayol, *Sur les représentations l-adiques associées aux formes modulaires
  de Hilbert*, Ann. Sci. École Norm. Sup. (4) 19 (1986), 409–468, §0.8, Corollaire, p. 411.

Both are propositions over the tree's existing objects: the Tau Ceti newform
`HeckeRing.GL2.Newform N 2` (Miyake's primitive form: a normalised good Hecke eigenform in the new
subspace of `S₂(Γ₁(N))`) with trivial nebentypus `f.χ = 1`, i.e. a newform on `Γ₀(N)`; its
L-series `BCDTPrint.cuspLSeries`, the Dirichlet series `∑ a_n(f) n^{-s}` of its `q`-expansion;
and Mathlib's `WeierstrassCurve.LSeries` and `WeierstrassCurve.LFunction` for `L(E, s)` and its
Dirichlet coefficients `a_n(E)`. Two L-series are compared on a right half-plane, as in
`BCDTPrint.Condition2At`: equality there determines the continuations.

The page images of both papers were read (Gross–Zagier pp. 231 and 309–312, from the GDZ scan
of Invent. Math. 84; Carayol pp. 410–411, from the numdam scan).
-/

noncomputable section

namespace ZInQ.Manuscript.PoleS12.GZRank

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.BCDTPrint (cuspLSeries)

/-- **PRINT**, Gross–Zagier, Invent. Math. 84 (1986), Theorem (7.3)(1), p. 231, as proved in
Chapter V, §2, pp. 309–312. This is a proposition; nothing here asserts it.

Verbatim printed text. Theorem (7.3), p. 231: "(7.3) **Theorem.** *Assume that `L(E, 1) = 0`.
Then there is a rational point `P` in `E(ℚ)` such that `L′(E, 1) = α·Ω·⟨P, P⟩` with
`α ∈ ℚ^×`. In particular: 1) If `L′(E, 1) ≠ 0`, then `E(ℚ)` contains elements of infinite
order. 2) If `L′(E, 1) ≠ 0` and `rank E(ℚ) = 1`, then formula (7.2) is true for some non-zero
rational number `α`.*"

Standing assumption of the proof, Chapter V, §2, pp. 309–310: "In §7 of Chap. I we described
several applications of our main theorem to the Birch–Swinnerton-Dyer conjecture for an elliptic
curve `E` over `ℚ`, under the assumption that the L-series of `E` coincides with that of a
modular form `f`. [...] For the rest of this section we suppose given a newform `f` of weight 2
and level `N` and an elliptic curve `E` over `ℚ` related in this way." The proof of (7.3) is on
p. 312: "This theorem is trivial if `L′(E, 1) = 0` (take `P = 0`), so we can assume
`ord_{s=1} L(E, s) = 1`. [...] As in §1 we choose a `K` by Waldspurger's theorem so that
`L_ε(f, 1) ≠ 0`. [...] If we take `P = P_K + P̄_K ∈ E(ℚ)`, and combine Theorem (2.1) and the last
two formulas, we obtain the desired formula `L′(E, 1) = αΩĥ(P)` with `α ∈ ℚ^×`."

Formalized: clause 1) under the standing assumption of p. 310. Dictionary: (i) "a newform of
weight 2 and level `N`" on `Γ₀(N)` is a Tau Ceti `Newform N 2` with `f.χ = 1`; (ii) "related in
this way", `L(E, s) = L(f, s)`, is equality of the Dirichlet series on a right half-plane;
(iii) `L(E, 1) = 0` and `L′(E, 1) ≠ 0` are read through the entire continuation `F` of `L(E, s)`
from `Re s > 3/2` (unique by the identity theorem), as in
`SilvermanRank.SilvermanAEC_C_16_5_5_RankOne`; (iv) "elements of infinite order" in `E(ℚ)` is a
point of Mathlib's `E.toAffine.Point` that is not of finite additive order. The level `N` is
any positive integer, as on p. 310, which asks only for a newform of some level `N` ("the
covering map `π : X₀(N) → E (N = level of f)`" comes from Faltings' isogeny theorem). -/
def GZThm73NonTorsion : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : HeckeRing.GL2.Newform N 2), f.χ = 1 →
    ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries f.toCuspForm s) →
      ∀ F : ℂ → ℂ, Differentiable ℂ F → (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
        F 1 = 0 → deriv F 1 ≠ 0 → ∃ P : E.toAffine.Point, ¬ IsOfFinAddOrder P

/-- **PRINT**, Carayol, Ann. Sci. École Norm. Sup. (4) 19 (1986), §0.8, Corollaire, p. 411.
This is a proposition; nothing here asserts it.

Verbatim printed text, p. 411: "0.8. APPLICATION. — Le théorème précédent, appliqué dans le cas
particulier où `F = ℚ` et `k = 2`, fournit facilement une réponse affirmative à une conjecture
concernant les courbes elliptiques de Weil : COROLLAIRE. — *Soit `f ∈ S₂(Γ₀(N))` une nouvelle
forme rationnelle, valeur propre normalisée des opérateurs de Hecke, et soit `E_f` la courbe
elliptique sur `ℚ` associée à `f`. Alors la fonction L de `E_f` est égale à `L(f, s)`, et le
conducteur géométrique de `E_f` est égal à `N`.* En effet, notons `π` la représentation
automorphe attachée à `f`, et soit `σ^l` la représentation l-adique que le théorème associe à
`π`. De la définition de `E_f` et du théorème de Čebotarev, il résulte que `σ^l` est isomorphe à
la représentation naturelle de Galois sur l'espace `H¹(E_f ⊗ ℚ̄, ℚ_l)`. L'égalité des séries L
découle de ce fait et du théorème."

Formalized: the equality of L-functions (the conductor clause is dropped, which only weakens the
statement). Dictionary: (i) `f ∈ S₂(Γ₀(N))` a normalised Hecke newform is a Tau Ceti
`Newform N 2` with `f.χ = 1`; (ii) `E_f`, "la courbe elliptique sur `ℚ` associée à `f`", is read
as an elliptic curve `E` over `ℚ` whose Dirichlet coefficients `a_p(E)` equal `a_p(f)` at all but
finitely many primes. `E_f` has this property (the Eichler–Shimura relation at `p ∤ N`, which is
what the proof uses of "la définition de `E_f`" together with Čebotarev); conversely every such
`E` is isogenous to `E_f` (Faltings), and `L(E, s)` is an isogeny invariant, so the reading
extends the print from `E_f` to its isogeny class; (iii) "rationnelle" is not a separate
hypothesis: for a newform with a curve `E` as in (ii), `a_p(f) ∈ ℚ` for almost all `p` and every
coefficient is rational (each Galois conjugate of `f` is a newform of level `N` with the same
eigenvalues at almost all primes, hence equal to `f` by strong multiplicity one); (iv) "la
fonction L de `E_f` est égale à `L(f, s)`" is equality of the Dirichlet series on a right
half-plane. Items (ii) and (iii) need a reading before the row counts as a direct instance. -/
def CarayolCor08 : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : HeckeRing.GL2.Newform N 2), f.χ = 1 →
    ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
      (∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
        (qExpansion 1 f.toCuspForm).coeff p = (E.LFunction p : ℂ)) →
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries f.toCuspForm s

end ZInQ.Manuscript.PoleS12.GZRank
