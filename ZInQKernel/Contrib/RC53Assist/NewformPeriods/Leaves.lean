import ZInQKernel.Contrib.RC53Assist.NewformPeriods.RationalParametrization
import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic

/-!
# The printed leaves for `NewformPeriodsRational`

Shimura 1973, Theorem 1, and Faltings 1983, Korollar 2.

Both sources are in the manuscript's bibliography (`diophantine_zq.tex`, sha256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`):

* `shimura-factors` (bibitem tex L11053–11057): G. Shimura, *On the factors of the jacobian variety
  of a modular function field*, J. Math. Soc. Japan **25** (1973), 523–544, Theorem 1; cited at
  tex L770–771 ("Shimura's quotient construction and Euler-factor identity
  \cite[Theorem 1]{shimura-factors}"). Copy read: the publisher's open-access PDF on Project
  Euclid, doi:10.2969/jmsj/02530523, 22 pages, sha256
  `0899e62a3c96b52e2d189458674b8c415c25016c14b1ac7f120088011d5a9ca2` (a scan; the page images were
  read; printed p. 523 is PDF page 1, so p. 525 is PDF page 3 and p. 526 is PDF page 4).
* `faltings1983` (bibitem tex L11084–11086): G. Faltings, *Endlichkeitssätze für abelsche
  Varietäten über Zahlkörpern*, Invent. Math. **73** (1983), 349–366; erratum **75** (1984), 381;
  cited at tex L621 and L732–733. Copy read: the GDZ Göttingen PDF of the article, 19 pages,
  sha256 `f72a869f4a050e6e4a435cc790f4ac2e47b61fcac35d564041b5f43d89c2f87a` (PDF page 1 is a cover;
  printed p. 360 is PDF page 13, p. 361 is PDF page 14). The erratum (GDZ PDF, sha256
  `c3a71300e1806f71a71b006e0b1d68d126c62af38c0fbf1e325b5aefc857d455`, printed p. 381) replaces only
  the assertion of Satz 2 by "Die Folge h(A_n) wird stationär", which it says suffices for the
  rest ("die für das Weitere ausreicht"); Korollar 2 is unaffected.

The readings below are page-image readings (not human-certified); the quotes are as read.

## `Shimura1973Thm1RationalGamma0` — Shimura 1973, Theorem 1, p. 526

A special case, in consequence form.

Setting, p. 525: "Let Γ be a group of level N, and J the jacobian variety of 𝔥*/Γ. Let
ψ: 𝔥* → J be the map obtained by composing the natural map 𝔥* → 𝔥*/Γ with a canonical map of
𝔥*/Γ into J. Then there is an isomorphism μ: S₂(Γ) → D_J defined by δψ(μ(f)) = f(z)dz for
f ∈ S₂(Γ), where δψ is the "pull back" associated with ψ, and z is a standard variable on 𝔥."
(p. 524: D_B is "the vector space over C of all holomorphic 1-forms on B".) Also p. 525: "For a
positive integer n, let q be the largest divisor of n prime to N, and put n = mq. Then we define
T_n and ξ_n by T_n = T_mT_q, ξ_n = ξ_mξ_q, T_m = [ΓαΓ]₂, ξ_m = {ΓαΓ} with α = [1 0; 0 m], and
T_q = Σ_β[ΓβΓ]₂, ξ_q = Σ_β{ΓβΓ}, where Σ_β is extended over all distinct ΓβΓ with det(β) = q,
β ≡ [1 0; 0 q] (mod N)."

Hypotheses and statement, p. 526: "As shown in [11, §7.3], there is a "standard model" of 𝔥*/Γ
defined over Q (see also §4 below), so that J can naturally be defined over Q. Let
f(z) = Σ_{n=1}^∞ a_n e^{2πinz}, with a₁ = 1, be an element of S₂(Γ), that is a common
eigenfunction of T_n for all n (i.e., f|T_n = a_n f). Fix f, and let K be the subfield of C
generated over Q by the complex numbers a_n for all n."

"THEOREM 1. There exists a triple (A, ν, θ) formed by the objects satisfying the following
conditions:
(i) (A, ν) is a quotient of J by an abelian subvariety rational over Q.
(ii) θ is an isomorphism of K into End(A)⊗Q such that ν∘ξ_n = θ(a_n)∘ν for all n. …
(iii) dim(A) = [K : Q].
Moreover, let I denote the set of all isomorphisms of K into C. Then, for every σ ∈ I, there
exists an element f_σ of S₂(Γ) such that f_σ|T_n = a_n^σ f for all n, and
f_σ(z) = Σ_{n=1}^∞ a_n^σ e^{2πinz}. With these f_σ, one has
(iv) δν(D_A) = μ(Σ_{σ∈I} Cf_σ).
Under the conditions (i, ii), the triple (A, ν, θ) is unique up to isomorphisms over Q.
Furthermore, the one-dimensional part of the zeta function of A over Q coincides, up to finitely
many Euler factors for bad primes, with Π_{σ∈I}(Σ_{n=1}^∞ a_n^σ n^{-s}), provided that
Γ = Γ₀(N), or Σ_{σ∈I} Cf_σ is stable under the map h(z) ↦ h(−1/Nz)/z²."

(In "f_σ|T_n = a_n^σ f" the last `f` is evidently `f_σ`; not used here, since `I = {id}`.)

**What the Lean leaf keeps** (special case `Γ = Γ₀(M)`, `K = ℚ`, so `I = {id}`, `f_id = f`,
`dim A = 1`): for every normalized full Hecke eigenform `g ∈ S₂(Γ₀(M))` with rational
coefficients `b`, there are an elliptic curve `A/ℚ` (a Weierstrass equation, `A.IsElliptic`) and a
point `(x, y)` of `A` over `ℚ(j, j_M) ⊆ ℚ((q))` with `x` nonconstant (the composite of the canonical
map at the cusp `∞` with `ν`), such that the pull-back of `ω_A = dx/(2y + a₁x + a₃)` is a complex
multiple of `g(q) dq/q` (clause (iv)), and `A.LFunction p = b p` for all but finitely many
primes `p` (the Euler-factor clause, `Γ = Γ₀(M)`). Clause (ii), `θ` and uniqueness are dropped.
The leaf is a consequence of the print together with the translations listed next; it adds no
clause that the print does not give.

**Translations used to read the print this way** (CONSEQUENCE GLUE, not literal PRINT; each is
classical and listed as an open formalization obligation in the README):
1. the standard model of `X₀(M)` over `ℚ`, its rational cusp `∞`, and its function field
   `ℚ(j, j(Mz))` embedded in `ℚ((q))` by the `q`-expansion at `∞` (`modularFunctionFieldQ`;
   Shimura's reference [11] is his 1971 book, which is not in the manuscript's bibliography);
2. a one-dimensional abelian variety over `ℚ` is an elliptic curve with a Weierstrass equation, and
   `D_A = C ω_A`;
3. the canonical map at `∞` and `ν` are defined over `ℚ`, so their composite is a `ℚ`-point of `A`
   over the function field, and clause (iv) with `δφ(μ(g)) = g(z)dz` and `dz = dq/(2πi q)` reads
   `θx = c · ĝ · (2y + a₁x + a₃)` for some `c ∈ ℂ` (`PullbackIsMultiple`);
4. at a prime of good reduction the one-dimensional part of the zeta function of `A` has Euler
   factor `(1 − a_p p^{-s} + p^{1−2s})^{-1}`, `a_p = p + 1 − #Ã(𝔽_p) = A.LFunction p` (Mathlib's
   coefficient), while the Euler factor of `Σ b_n n^{-s}` at `p ∤ M` is
   `(1 − b_p p^{-s} + p^{1−2s})^{-1}`; equal factors give `A.LFunction p = b p`;
5. Tau Ceti's `heckeTCompositeGamma0 M n` acting on the trivial-character space of `Γ₁(M)` is
   Shimura's `T_n` on `S₂(Γ₀(M))` (p. 525), so `IsNormalizedFullEigenformGamma0` is the print's
   hypothesis "a₁ = 1 … a common eigenfunction of T_n for all n".

## `Faltings1983Kor2EllipticQ` — Faltings 1983, §5, Korollar 2, p. 361

A special case of iii) ⇒ i).

p. 360: "Sei K Zahlkörper, A/K eine abelsche Varietät der Dimension g, l eine Primzahl,
T_l = T_l(A) der Tate-Modul, auf dem π = Gal(K̄/K) operiert." p. 361: "Die L-Reihe eines A's ist
bekanntlich definiert als L(A, s) = Π_v 1/det(1 − (N_v)^{-s}·F_v | T_l(A)) = Π_v L_v(A, s), wobei
das Produkt über fast alle Stellen von K zu erstrecken ist. Die lokalen L-Faktoren L_v(A, s) sind
unabhängig von l."

"Korollar 2. Seien A₁, A₂ wie im Korollar 1. Es sind äquivalent
i) A₁ und A₂ sind isogen.
ii) T_l(A₁) ⊗_{Z_l} Q_l ≅ T_l(A₂) ⊗_{Z_l} Q_l als π-Modul.
iii) L_v(s, A₁) = L_v(s, A₂) für fast alle Stellen v von K.
iv) L_v(s, A₁) = L_v(s, A₂) für alle v."
("Korollar 1. Seien A₁ und A₂ abelsche Varietäten über K." The proof: "Die Äquivalenz von i) und
ii) folgt aus Satz 4, die von ii) und iii) aus Satz 3 (+Čebotarev) …".)

**What the Lean leaf keeps**: `K = ℚ`, `A₁, A₂` elliptic curves given by Weierstrass equations, and
the implication iii) ⇒ i), with iii) in the form "the Dirichlet coefficients `E₁.LFunction p` and
`E₂.LFunction p` agree for all but finitely many primes `p`", and i) as an isogeny `E₁ → E₂` over
`ℚ` in Tau Ceti's sense (`TauCeti.Isogeny`: a pull-back of coordinate rings carrying the point at
infinity to the point at infinity). Translations (CONSEQUENCE GLUE): at a prime of good reduction
`L_p(s, E)^{-1} = 1 − a_p p^{-s} + p^{1−2s}` with `a_p = tr(F_p | T_l E) = p + 1 − #Ẽ(𝔽_p)`, which
is Mathlib's coefficient (so the hypothesis gives iii), the bad primes being finite in number); and
an isogeny of elliptic curves over `ℚ` gives a `TauCeti.Isogeny`.

**Existing leaves considered for reuse.** `PkgI3.FaltingsTate` (Satz 4 and Korollar 1, the
`Hom`-form, stated in `ZInQKernel.HDecomp.Objects` and `ZInQKernel.Contrib.G9.I3Layer`) is cited
here as the related existing interface; passing from it to the isogeny needed here would also need
Satz 3, Čebotarev, and a Tate-module/abelian-variety dictionary for Weierstrass curves, so
Korollar 2 (same §5, p. 361, right after Korollar 1) is stated instead. The Shimura row `R16Thm1b.ShimuraThm1Af`
(Theorem 1 at `Γ = Γ₁(N)`, with the quotient `J/I_f J`) is not part of this source edition and
does not contain clause (iv), the differential clause this reduction needs; it is not reused.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NewformPeriods

open CongruenceSubgroup UpperHalfPlane

/-- **Normalized full Hecke eigenform on `Γ₀(M)`** (the print's hypothesis, translation 5 above):
`a₁(g) = 1` and `g` is, as a function on `ℍ`, a Tau Ceti full Hecke eigenform of level `M`,
weight `2` and trivial nebentypus (an eigenvector of `T_n` for every `n ≥ 1`, the indices not
prime to `M` included). -/
def IsNormalizedFullEigenformGamma0 (M : ℕ) [NeZero M]
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) : Prop :=
  (qExpansion 1 g).coeff 1 = 1 ∧
    ∃ e : HeckeRing.GL2.Eigenform M 2, e.χ = 1 ∧ ∀ τ : ℍ, e.toCuspForm τ = g τ

/-- **Shimura 1973, Theorem 1 (p. 526), at `Γ = Γ₀(M)` with rational coefficients, consequence
form** (PRINT, special case, over the CONSEQUENCE GLUE translations 1–5 of the module docstring).
For every `M > 0` and every normalized full Hecke eigenform `g ∈ S₂(Γ₀(M))` whose coefficients
are the rationals `b n`, there are an elliptic curve `A/ℚ` (the quotient `A` of `J₀(M)` of (i),
(iii)) and a nonconstant point `(x, y)` of `A` over `ℚ(X₀(M)) = ℚ(j, j_M) ⊆ ℚ((q))` (the composite
of the canonical map with `ν`), such that the pull-back of `ω_A` is `c · g(q) dq/q` for some
`c ∈ ℂ` (clause (iv); `c ≠ 0` and `c ∈ ℚ` then follow, `ne_zero_of_pullbackIsMultiple` and
`exists_rat_eq_of_pullbackIsMultiple`), and `A.LFunction p = b p` for all primes `p` outside a
finite set (the Euler-factor clause for `Γ = Γ₀(M)`). -/
def Shimura1973Thm1RationalGamma0 : Prop :=
  ∀ (M : ℕ) [NeZero M] (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2),
    IsNormalizedFullEigenformGamma0 M g →
    ∀ b : ℕ → ℚ, (∀ n : ℕ, (qExpansion 1 g).coeff n = (b n : ℂ)) →
      ∃ A : WeierstrassCurve ℚ, A.IsElliptic ∧
        ∃ x y : LaurentSeries ℚ, IsModularPointQ M A x y ∧
          (∃ c : ℂ, PullbackIsMultiple A x y (qExpansion 1 g) c) ∧
          ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ((A.LFunction p : ℤ) : ℚ) = b p

/-- **Faltings 1983, §5, Korollar 2 (p. 361), iii) ⇒ i), for elliptic curves over `ℚ`** (PRINT,
special case, over the CONSEQUENCE GLUE translations of the module docstring). Two elliptic curves
over `ℚ` whose `L`-coefficients agree at all but finitely many primes are isogenous over `ℚ`: there
is an isogeny `E₁ → E₂` (`TauCeti.Isogeny`). -/
def Faltings1983Kor2EllipticQ : Prop :=
  ∀ E₁ E₂ : WeierstrassCurve ℚ, E₁.IsElliptic → E₂.IsElliptic →
    (∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → E₁.LFunction p = E₂.LFunction p) →
      Nonempty (TauCeti.Isogeny E₁.toAffine E₂.toAffine)

end ZInQ.Contrib.RC53Assist.NewformPeriods
