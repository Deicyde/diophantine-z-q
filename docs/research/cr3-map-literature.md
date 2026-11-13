# CR3 attack: a map of the literature that produces points on congruent number curves

Task: catalogue the mathematics that could produce rational points (or rank at least one) on the
curves `C_d : y² = x³ − d²x` of hypothesis CR3 (`ZInQ.CertifiedRank`,
`ZInQKernel/Hypotheses/CertifiedRank.lean`) and on the Route K surfaces of rs-pole §2.2, without
Heegner points or L-functions, or with inputs that could plausibly be formalized. For each tool:
statement, source, status, relevance to eliminating CR3, formalizability in Lean 4 + Mathlib.

Marks as in `docs/research/rs-pole.md`: **VERIFIED** (proved here, checked against repository
sources, or exact computation), **STANDARD** (published theorem, reference given),
**SPECULATIVE** (idea, unproved). **UNVERIFIED** marks a citation that could not be checked
inside the repository (no network access in this run); all bibliographic details marked so are
from memory and need checking before any citation.

Scratch: `scratch/cr3-map/check_reform.py` (stdlib only, 30 samples per check).

## 0. Verdict

- **Elimination.** No catalogued tool produces, for the curves CR3 covers (`d ≡ 5 (mod 8)`,
  `ω(d)` unbounded, prime set of `d` containing the arbitrary primes of `β`), a rational point
  without one of: (i) Heegner/CM points whose non-triviality is proved through Gross–Zagier and
  Waldspurger (TYZ), (ii) finiteness of `Ш(C_d)[2^∞]` (Kriz's 2-converse, or the conditional
  Swinnerton-Dyer school), or (iii) Heegner/mock-Heegner points with a purely algebraic mod-2
  non-triviality proof, which is known only when the prime factors of `d` are restricted
  (Heegner, Birch, Monsky; Tian 2014 for "all primes `≡ 1 (mod 8)` but one"). Route (iii) is the
  only L-function-free source of points in unbounded `ω`, and its prime restrictions are
  incompatible with the arbitrary primes of `β` (rs-pole §2.3, pc-audit §4.5).
- **Structural reason, sharpened here** (§1, R1–R7): CR3's conclusion is *exactly* the
  existence of a rational point on the explicit genus-one quartic `D_{d,a} : d·a·w² = a²s⁴ − 1`,
  whose Jacobian `y² = x³ + 4d²x` is 2-isogenous to `C_d`; its hypothesis says `D_{d,a}` is a Selmer element. So CR3 is a
  Hasse principle for 2-coverings; the only general obstruction is `Ш[2]`, and no finite or
  local argument can rule out `Ш[2] ≠ 0`. The descent lemma DL (proved in Lean) is precisely the
  *unconditional half* of Swinnerton-Dyer's method (choose a fibre with minimal Selmer group);
  CR3 is the *conditional half* of the same method.
- **The freedom does not help with any tool found** (R4–R7): the free witness enters only
  through `σ = s(q)`, a fixed high-degree rational function; with `σ` free the problem is trivial
  (`θ = 1`), with `σ = s(q)` every family-type argument needs a section of an elliptic surface
  over `ℙ¹_q` whose generic Mordell–Weil group is torsion for the obvious pullback.
- **Cleanest narrowing found:** CR3^rk, "for squarefree `d ≡ 5 (mod 8)` with `dim Sel₂(C_d) = 3`
  and some first coordinate `≡ 7 (mod 8)` in absolute value, `C_d(ℚ)` has a point of infinite
  order" (§4, N2). Mathematically equivalent to CR3 (RK9), but it drops all Kummer-class
  bookkeeping from the trusted statement and is literally the rank statement that Kriz, TYZ+GZ,
  and "Ш[2^∞] finite" each give. Its Lean cost is RK9: Kummer injectivity plus a descent on
  heights, both of the kind already done for `mordellWeilE`. Equivalent alternative: N1, the
  pure quartic form above.

## 1. Results log (definitions, lemmas, constructions tried)

**R1. Abscissa classes on `C_d` (VERIFIED: derivation; 30/30 exact checks, `check_reform.py`).**
For `a ≠ 0` squarefree and `d ≠ 0`: `C_d` has a rational point with `x ∈ aℚ*²` iff
`d ∈ a(a²s⁴ − 1)·ℚ*²` for some `s ∈ ℙ¹(ℚ)` (`s = ∞` read as `d ∈ aℚ*²`, the torsion point
`(±d, 0)` up to `C_d ≅ C_{−d}`). *Proof.* Rescaling `(x, y, d) ↦ (λ²x, λ³y, λ²d)` reduces to
`x = a`: `a(a² − d'²) = y²`, i.e. the conic `a² − d'² = a w²` with point `(d', w) = (a, 0)`.
Lines `w = s(a − d')` give `d' = a(as² − 1)/(as² + 1)`, class `a(a²s⁴ − 1)`. Explicit point:
`d = a(a²s⁴ − 1)`, `x = a(as² + 1)²` (checked). This is the congruent-curve analogue of
rs-pole Proposition 1 (there `g_β(t) = β(βt² − 1)(βt² + 3)` for `E_ℓ`).

**R2. CR3 as a quartic (VERIFIED from R1 and the CR3 docstring).** Under CR3's hypotheses
(`d ≡ 5`, `|a| ≡ 7 (mod 8)`, so `a ≢ ±1, ±d` and the point cannot be torsion), CR3's conclusion
is equivalent to `D_{d,a}(ℚ) ≠ ∅`, where `D_{d,a} : d a w² = a²s⁴ − 1` (`s` finite). `D_{d,a}`
is the homogeneous space of the 2-isogeny descent attached to the class `a` (with `Y = daw` it reads
`Y² = da³s⁴ − da`, whose Jacobian `y² = x³ + 4d²a⁴x ≅ y² = x³ + 4d²x` is 2-isogenous to `C_d`;
VERIFIED algebra, STANDARD theory, Silverman AEC X.3–X.4), and the Selmer hypothesis says it is everywhere locally soluble. So CR3 is
literally "this everywhere locally soluble genus-one quartic has a rational point".

**R3. The Route K surface (VERIFIED, algebra).** For Route K's `Φ_C(B)` with multiplier `m`
(points on `C_n` and `C_{nθ}` with abscissas in `βℚ*²`), R1 gives: `Φ_C(B)` for this `m` iff the
double cover `X_{β,θ} : w² = θ(β²s⁴ − 1)(β²t⁴ − 1)` of `ℙ¹ × ℙ¹` has a rational point (take
`n ≡ β(β²s⁴ − 1)`; `s = ∞` gives `n = β`, the "torsion first curve" case that solved 24/30
samples in rs-pole §4.1). `X_{β,θ}` is a twisted Kummer surface of `D × D'` with `D, D'`
geometrically isomorphic to `y² = x³ − x` (CM by `ℤ[i]`), hence a K3 surface of geometric
Picard rank 20 (STANDARD: Kummer of `E × E`, `E` CM, is singular; Shioda–Inose 1977). The
"auxiliary primes of `n`" of DL are a choice of fibre of `X_{β,θ} → ℙ¹_s`. Not checked: whether
the Lean interface `poleSoluble_of_points` accepts a non-integral `n` class (it is stated with
`n : ℤ`); any `n` here can be rescaled to a squarefree integer.

**R4. Norm structure (VERIFIED).** `β²s⁴ − 1 = −N_{ℚ(√β)}(1 + s√β) · N_{ℚ(√−β)}(1 + s√−β)`, and
admissibility gives `θ c² = 1 − βu²` with `βu² = B/m`, so `θ ∈ N_{ℚ(√β)}(ℚ(√β)*)`. Hence
`X_{β,θ}` has points at every place where the `ℚ(√−β)`-norm conditions hold. This explains
why local data are always satisfiable but says nothing global.

**R5. The congruent-number parametrization (VERIFIED, 30/30).** For coprime `u > v > 0` and
`n = uv(u² − v²)`, `P = (nu/v, n²/v²) ∈ C_n(ℚ)` has abscissa class `u² − v²`. Every congruent
`n` is of this form up to squares (STANDARD, Euclid/Fibonacci). R1 is the class-refined version.

**R6. The free witness, analysed as a fibration (VERIFIED as an argument; uses STANDARD facts).**
Write `σ = s(q)` (rs-pole §2.1: `B = R₀σ²`). Fix `m` and the one-curve case `s = ∞`. The set of
good `σ` is the image of the rational points of `S_m : w² = m(m − R₀σ²)(β²t⁴ − 1)`.
- `S_m` is a double cover of `ℙ¹_σ × ℙ¹_t` branched along a bidegree `(2, 4)` curve; `K = −F`
  with `F` the fibre over `ℙ¹_σ`, so `S_m` is a rational elliptic surface over `ℙ¹_σ` and a conic
  bundle over `ℙ¹_t`. It has rational points (`t = ∞`, `σ = 0`), and they are dense.
- With `σ` free nothing is needed: `σ = 0` makes `θ = 1` (rs-pole's trivial witness). All
  difficulty sits in the constraint `σ ∈ s(U(ℚ))`.
- The generic fibre of `S_m → ℙ¹_σ` has Jacobian the twist of `C_β` by
  `Δ(σ) = m(m − R₀σ²)`. Its `ℚ(σ)`-Mordell–Weil group is torsion: twisted points are
  morphisms from the conic `w² = Δ(σ)` (genus 0) to `C_β`, hence constant (STANDARD argument).
  So `S_m → ℙ¹_σ` has no section giving the class `β`, and there is no "free family".
- Pulling back along `s : ℙ¹_q → ℙ¹_σ` of degree `D` gives an elliptic surface `Z_m` over `ℙ¹_q`
  with `K = (D − 2)F` (Kodaira dimension 1 for `D ≥ 3`). A family-type proof needs a section
  or a low-degree multisection of `Z_m` over `ℚ(q)`, i.e. a nonzero
  `Hom(Jac(H), C_β)` for the hyperelliptic curve `H : w² = m(m − R₀s(q)²)` of genus about
  `D − 1`, with the right Kummer class. Nothing in the construction of `s` (traces of inverses of
  products, rs-pole §1.2) suggests such a factor. (Assessment SPECULATIVE.)
- Route E (rs-pole §4.3) forbids `q` polynomial in parameters only for families uniform in the
  instance; for one fixed instance a rational curve `q = q(λ)` with denominators anisotropic over
  `ℚ_p` at the finitely many contact primes is not excluded `p`-adically. The obstacle for such a
  curve is R6's geometry, not `p`-adic badness. (VERIFIED as a remark on rs-pole's lemma.)

**R7. No genus-0 shortcut on `X_{β,θ}` (STANDARD facts, applied).** K3 surfaces are not
uniruled, so `X_{β,θ}` has no rational parametrization. The obvious curves `t = ±s`,
`t = 1/(βs)` require `θ` or `−θ` to be a square (VERIFIED: `G(1/(βs)) = −G(s)/(β²s⁴)`). A
`ℚ`-rational elliptic fibration of `X_{β,θ}` with a `ℚ`-section would give points for every
`(β, θ)` with the same `m`, which is more than DL+CR3 provide (they choose `m`); none is known.

## 2. Catalogue A: elementary and explicit sources of points

**A1. Pythagorean / Euclid parametrization.** Statement: `n` congruent iff `n ≡ uv(u² − v²)`
mod squares; explicit points (R5, R1). Source: classical (Dickson, *History*, vol. II, ch. XVI).
Status STANDARD. Relevance: none on its own: it describes congruent numbers but does not decide
whether a given `n` (or `D_{d,a}`) is one. It is the exact form of the target (R1). Lean: trivial
(polynomial identities, as in `check_reform.py`).

**A2. Polynomial families of congruent numbers and high-rank families.** Statement: explicit
`d(t) ∈ ℤ[t]` with `rank C_{d(t)}(ℚ(t)) ≥ 1, 2, 3` (e.g. `d = t(t⁴ − 1)`-type families; rank ≥ 3
families of Johnstone–Spearman; rank ≥ 2 of Rubin–Silverberg). Source: Johnstone–Spearman,
*Congruent number elliptic curves with rank at least three*, Canad. Math. Bull. 53 (2010)
(UNVERIFIED); Rubin–Silverberg, *Twists of elliptic curves of rank at least four* (2004)
(UNVERIFIED). Chahal, *On an identity of Desboves*, Proc. Japan Acad. 60 (1984): every residue
class mod `m` contains congruent numbers (UNVERIFIED). Status STANDARD/UNVERIFIED. Relevance:
our first curve already has such a family (`n = β(β²s⁴ − 1)`, R1). The obstruction is the
*pairing* of two curves `C_n`, `C_{nθ}` with one `n`, i.e. `X_{β,θ}(ℚ)` (R3), and the value
`θ = θ(q)` is not polynomial in any free parameter (R6). Lean: easy per family.

**A3. Classical prime cases (Genocchi, Heegner, Birch, Stephens, Monsky).** Statement: primes
`p ≡ 5, 7 (mod 8)` are congruent; `2p` with `p ≡ 3, 7 (mod 8)` congruent; `p ≡ 3 (mod 8)` not
congruent (Genocchi, by descent). Sources: K. Heegner, Math. Z. 56 (1952); B. Birch,
*Diophantine analysis and modular functions* (Bombay 1968) and Invent. Math. 1969 (UNVERIFIED);
N. Stephens, J. reine angew. Math. 1975 (Birch–Stephens root numbers; quoted by TYZ, see
nt-tyz §1); P. Monsky, *Mock Heegner points and congruent numbers*, Math. Z. 204 (1990) 45–68
(UNVERIFIED). Status STANDARD. Method: (mock) Heegner points built from Weber modular functions;
non-triviality by an algebraic 2-adic argument, no L-functions. Relevance: none for CR3 directly
(rs-pole §2.3: `supp β ⊆ supp d`, `ω(β)` unbounded). Lean: needs Weber's class invariants and
Shimura reciprocity (main theorem of CM), absent from Mathlib; a large project even for one
prime class.

**A4. Two-prime and few-prime results.** Statement: congruent/non-congruent criteria for
`d = pq`, `2pq` by Monsky, Lagrange, Serf, Iskra (non-congruence for many primes `≡ 3 (mod 8)`),
Feng (non-congruence via graph/Rédei conditions). Sources: Iskra, Proc. Japan Acad. 72 (1996);
Feng, Acta Arith. 75 (1996) (both UNVERIFIED). Status STANDARD. Relevance: the non-congruence
results are the wrong direction; the congruence results are bounded `ω`. Lean: the
non-congruence (descent) side is what the repository's Selmer system already encodes.

**A5. Monsky's matrix and complete 2-descent.** Statement: `dim Sel₂(C_d) = 2 + corank` of an
explicit `𝔽₂` matrix (Monsky, appendix to Heath-Brown, Invent. Math. 118 (1994)). Status
STANDARD; in Lean as Proposition 0 (`RouteK/Selmer*`). Relevance: gives upper bounds on rank and
the target class; never a point. Already used.

## 3. Catalogue B: local-to-global principles

**B1. Hasse–Minkowski, Legendre, conics.** Statement: quadratic forms over `ℚ` satisfy the
Hasse principle. Source: standard (Serre, *A Course in Arithmetic*). Status STANDARD.
Relevance: produces points on the genus-0 parts only (the conic of R1 in `(d', w)`, the conic
bundle `S_m → ℙ¹_t` of R6). In both places the genus-0 problem already has an explicit point,
so HM adds nothing. Lean: Mathlib has quadratic reciprocity and Legendre symbols; a full
Hasse–Minkowski over `ℚ` is not in Mathlib to this note's knowledge (UNVERIFIED); Legendre's
three-square-type ternary theorem would be a medium project.

**B2. Châtelet surfaces and conic bundles.** Statement: Brauer–Manin is the only obstruction to
the Hasse principle and weak approximation on Châtelet surfaces `y² − az² = P(t)`, `deg P ≤ 4`.
Source: Colliot-Thélène, Sansuc, Swinnerton-Dyer, J. reine angew. Math. 373/374 (1987)
(UNVERIFIED pages). Status STANDARD. Relevance: the surfaces met here with a genus-0 fibration
(`S_m`) have explicit points already; the needed object is a genus-one fibre, not the surface.
Lean: very hard (Brauer groups); not needed.

**B3. Quadric bundles, fibration method under Schinzel (Colliot-Thélène–Swinnerton-Dyer,
Harpaz–Wittenberg).** Statement: rational points on fibrations into rationally connected
varieties, unconditionally in low-degree cases, conditionally on Schinzel's hypothesis in
general. Status STANDARD (conditional parts conditional). Relevance: the fibres here are
genus-one, not rationally connected (rs-global C2: the parity device needs genus ≥ 1). None.

**B4. Swinnerton-Dyer's method for pencils of genus-one curves and Kummer surfaces.**
Statement: for suitable pencils of 2-coverings (diagonal quartics, Kummer surfaces of products
of elliptic curves with full 2-torsion), there is a fibre whose 2-Selmer group is as small as
parity allows; *if `Ш` of that fibre is finite*, the fibre has a rational point, so the surface
satisfies the Hasse principle (or Brauer–Manin is the only obstruction). Sources:
Swinnerton-Dyer, *Arithmetic of diagonal quartic surfaces II*, Proc. LMS 80 (2000);
Skorobogatov–Swinnerton-Dyer, *2-descent on elliptic curves and rational points on certain
Kummer surfaces*, Adv. Math. 198 (2005); Harpaz–Skorobogatov, *Hasse principle for Kummer
varieties*, Algebra Number Theory 10 (2016); Harpaz, *Second descent and rational points on
Kummer varieties*, Proc. LMS 118 (2019) (all UNVERIFIED as to exact hypotheses; in particular
whether CM or isogenous factors, as for `X_{β,θ}`, are excluded). Status STANDARD, conditional
on finiteness of `Ш` (to this note's knowledge every version producing points is conditional).
Relevance: **the closest match in the literature.** `X_{β,θ}` (R3) is exactly such a Kummer
surface; DL (Lean, proved) is the unconditional Selmer-minimization half of this method; the
remaining half is the `Ш`-finiteness input that CR3 encodes. So this literature confirms that
the gap is precisely CR3 and supplies no substitute. Lean: the descent half is done in this
project; the conditional half is the hypothesis.

**B5. Hasse principle for genus-one curves.** Statement: fails in general; the failure for
2-coverings is measured by `Ш[2]` (Lind, Reichardt `2y² = 1 − 17x⁴`). Status STANDARD.
Relevance: shows that CR3 (R2) cannot be proved from local data alone: the Selmer hypothesis is
local data, and `Ш[2] ≠ 0` examples with `dim Sel₂ = 3` and rank 0 are not excluded by any
finite computation unless `Ш[2^∞]` is controlled. No higher descent can *produce* a point: a
`2^k`-descent only shrinks Selmer upper bounds. Lean: n/a.

## 4. Catalogue C: rank-one theorems and what they import

**C1. Gross–Zagier + Kolyvagin; Coates–Wiles, Rubin (CM).** Statement: analytic rank ≤ 1
implies rank = analytic rank and `Ш` finite; for CM curves Coates–Wiles/Rubin give rank 0 when
`L(1) ≠ 0`. Sources: Gross–Zagier, Invent. Math. 84 (1986); Kolyvagin, Izv. 1989; Coates–Wiles,
Invent. Math. 39 (1977); Rubin, Invent. Math. 103 (1991). Status STANDARD. Relevance: the forward
theorem used in the current trust chain (RK7). Lean: out of reach (L-functions of elliptic
curves, modular parametrization, heights of Heegner points).

**C2. Tian–Yuan–Zhang genus points.** Statement (nt-tyz Proposition N, VERIFIED there against
arXiv:1411.4728v1): `n ≡ 5 (mod 8)`, `T_5b(n)` odd ⇒ `𝓛(n) ≠ 0`. Source: Asian J. Math. 21
(2017). Status STANDARD. What it imports (VERIFIED from nt-tyz §1.1): Waldspurger,
Yuan–Zhang–Zhang's Gross–Zagier, Tian's induction. The point `P(n)` is explicit (CM points on a
modular curve), but the recursion defining it carries the coefficients `𝓛(d₁)`, which are
L-values whose parity comes from Waldspurger, and the decomposition `P_χ = ε 2^h 𝓛(d₁)𝒫(d₀)` is
Gross–Zagier (nt-tyz §1.2, Theorem 3.3). So the L-functions are not removable by reading the
proof differently (VERIFIED from the notes). Relevance: current route; covers the slot curves
(tyz-5b). Lean: out of reach.

**C3. Tian's induction for restricted primes.** Statement: for `n ≡ 5, 6, 7 (mod 8)` whose odd
prime factors are all `≡ 1 (mod 8)` except one, under a 4-rank condition on
`Cl(ℚ(√−n))`, `n` is congruent; infinitely many congruent numbers with `k` prime factors in each
class. Source: Y. Tian, *Congruent numbers and Heegner points*, Cambridge J. Math. 2 (2014)
(arXiv:1210.8231; cited in nt-tyz §1.1). Status STANDARD. Whether the non-torsion step is free of
Gross–Zagier: UNVERIFIED (this note's recollection is that the Heegner point is shown
non-torsion by an algebraic 2-divisibility induction, with GZ used only for the analytic
statement). Relevance: if L-function-free, it is the only route to points with unbounded `ω`
without L-functions; but its prime restriction conflicts with arbitrary primes of `β`, and the
slot construction's "virtual prime" gluing (slot-k) is a Selmer-level trick that does not change
actual residues of the primes of `β`. Lean: needs modular curve `X₀(32)`, CM points over ring
class fields, Shimura reciprocity: far beyond Mathlib.

**C4. Kriz's 2-converse.** Statement: for `C_d` (CM by `ℤ[i]`, `p = 2`), `corank Sel_{2^∞} ≤ 1`
⇒ rank = analytic rank = corank and `Ш` finite. Source: arXiv:2002.04767v5, Thms 9.23, 10.13,
10.17 (VERIFIED against the text in rs-pole §4.1, pc-audit RK1). Status: preprint (one repaired
error, pc-audit). Relevance: covers CR3 entirely; uses `p`-adic L-functions (Rubin, Katz) and
supersingular main conjectures. Lean: out of reach.

**C5. 2-parity (Monsky; Dokchitser–Dokchitser).** Statement: `corank Sel_{2^∞}(E/ℚ) ≡` root
number parity. Sources: Monsky, Math. Z. 221 (1996) (UNVERIFIED); Dokchitser–Dokchitser, Ann.
of Math. 172 (2010). Status STANDARD. Relevance: gives corank one, never a point (rank ≥ 1 needs
`Ш` finite). Lean: hard; and useless without `Ш`.

**C6. Distribution results (Heath-Brown, Swinnerton-Dyer, Kane, Smith).** Statement: the
distribution of `dim Sel₂(C_d)`; Smith: 100% of `d ≡ 5, 6, 7 (mod 8)` have `Sel_{2^∞}` corank one.
Sources: Heath-Brown, Invent. Math. 111 (1993), 118 (1994); Smith, arXiv:1702.02325 (UNVERIFIED
publication status). Status STANDARD/preprint. Relevance: density statements over all `d`; our
family is thin (`n ⊇ β`), and corank one still needs a converse (C4) to give points. None.

**C7. Stark–Heegner / Darmon points, Rubin's `p`-adic height formula.** Conjectural
constructions or formulas that presuppose a point. Status: conjectural/STANDARD respectively.
Relevance none.

## 5. Catalogue D: CM and K3-specific geometry

**D1. CM by `ℤ[i]`: endomorphisms and isogenies.** `[i] : (x, y) ↦ (−x, iy)` and `1 + i` (a
2-isogeny) act on `C_d` over `ℚ(i)`; `C_d ≅ C_{−d}` and `C_d` is 2-isogenous to
`y² = x³ + 4d²x`. Status STANDARD. Relevance: gives only the torsion classes and the 2-isogeny
descent already in Proposition 0. Lean: elementary (formulas over `ℚ(i)`).

**D2. Elliptic fibrations of Kummer surfaces of `E × E'` (Oguiso; Kuwata–Shioda).** Statement:
the eleven Jacobian elliptic fibrations of `Km(E × E')` and their Mordell–Weil lattices; for
CM `E = E'` (Picard rank 20) more fibrations and explicit sections. Sources: Oguiso, J. Math.
Soc. Japan 41 (1989); Kuwata–Shioda, Adv. Stud. Pure Math. 50 (2008) (UNVERIFIED). Status
STANDARD over `ℚ̄`. Relevance: on the twisted form `X_{β,θ}` over `ℚ` the sections are defined
over fields depending on `β, θ` (`ℚ(i, √β, √θ, …)`). A `ℚ`-section uniform in `θ` would give
points for every admissible `θ` with a fixed `m` (R7), stronger than what is known to be true.
SPECULATIVE whether some fibration has a section defined over `ℚ` for the *specific* twists;
the experiment E-1 below tests the precondition. Lean: explicit sections would be polynomial
identities (easy to verify once found).

**D3. Shioda–Inose structure, rational curves on singular K3s.** Statement: singular K3s
(Picard rank 20) are determined by their transcendental lattice; they contain infinitely many
rational curves over `ℚ̄` (Bogomolov–Mumford; Chen; for Kummers, images of elliptic curves
through torsion). Status STANDARD. Relevance: rational curves over `ℚ̄` do not give rational
points; those defined over `ℚ` on `X_{β,θ}` would come from `ℚ`-rational correspondences between
the twisted curves, which reduce to points on the twists themselves (graphs of isogenies have
genus one). None found (R7). Lean: n/a.

**D4. Potential density (Bogomolov–Tschinkel) for K3 with elliptic fibration.** Rational
points are dense over some finite extension. Status STANDARD. Relevance: none (over `ℚ` the
existence of one point is the issue).

## 6. Catalogue E: Lean-side inputs available (VERIFIED from the repository)

Dirichlet's theorem (Mathlib), quadratic reciprocity, Proposition 0 and the explicit Selmer
system, DL (`ZInQ.RouteK.descent_lemma`), Szemerédi in the primes (`ZInQ.greenTaoDense`), the
Selberg sieve and `ZInQ.Density.goodPrimeDensity`, Mordell–Weil for one curve
(`ZInQ.mordellWeilE`, via `AddCommGroup.fg_of_descent'` and `approx_parallelogram_law`). Of these
only the last bears on points: finite generation never gives rank ≥ 1. Sieve and prime-pattern
tools could choose `n` with prescribed factorization type, but every point-producing theorem
above needs, beyond factorization type, either restricted residues of *all* primes (A3, C3) or
a deep converse (C2, C4).

## 7. Routes tried toward elimination, and outcomes

| # | Construction | Outcome |
| --- | --- | --- |
| T1 | One-curve case `n = β`: points on `θ w² = β²t⁴ − 1` from the conic bundle `S_m` (R6) | `σ` free: trivial (`θ = 1`). `σ = s(q)`: needs a section of `Z_m → ℙ¹_q`; generic MW torsion for the pullback; no handle. Fails. |
| T2 | Pair the two curves through a `ℚ`-rational curve on `X_{β,θ}` | Obvious curves force `±θ ∈ ℚ*²` (R7); K3 not uniruled; no uniform section known (D2). Fails. |
| T3 | Choose `n` (auxiliary primes) so a restricted-prime Heegner theorem (A3, C3) applies | `supp β ⊆ supp n` with arbitrary residues; restricted theorems exclude them. Fails (as pc-audit §4.5). |
| T4 | Use the multiplier `m` to make `β` have restricted primes | `β = sqf(mR₀)` only changes by primes of 2730. Fails. |
| T5 | Read TYZ's genus-point proof as L-function-free | Recursion coefficients `𝓛(d₁)` and Theorem 3.3 are GZ/Waldspurger (C2). Fails. |
| T6 | Swinnerton-Dyer/Harpaz–Skorobogatov for `X_{β,θ}` | Conditional on `Ш` finite, i.e. on the CR3-type input. Confirms DL = unconditional half. No elimination. |
| T7 | Higher descents (4-, 8-descent) to force a point | Descents only bound rank above; cannot prove existence. Fails (B5). |
| T8 | Weak approximation in `q` to land in a thin set of good `σ` | The good set (R6) is the image of rational points of a rational elliptic surface; `s(U(ℚ))` is a thin set of a degree-`D` map; no theorem guarantees an intersection. Open; SPECULATIVE; see E-2. |

## 8. Narrowings of CR3 (the fallback)

**N1. CR3^quart (VERIFIED equivalent, R2).** For squarefree `d ≡ 5 (mod 8)` and squarefree
`a | d` with `|a| ≡ 7 (mod 8)`: if `Σ(𝒞_d)` has 8 solutions and one has first coordinate `[a]`,
then `d a w² = a²s⁴ − 1` has a rational solution. Pure Diophantine; no curve group. Lean cost:
the R1 identity (`x = a(as² + 1)²` after rescaling by `w`), a few lines. Same strength as CR3.

**N2. CR3^rk (recommended trust statement).** Same hypotheses (or only: `dim Sel₂(C_d) = 3`
and some Selmer first coordinate `≡ ±7 (mod 8)`): `C_d(ℚ)` contains a point of infinite order.
- Mathematically equivalent to CR3 via RK9 (pc-audit; tyz-5b §1.3, VERIFIED there): with
  `C_d(ℚ)[2] = (ℤ/2)²` and rank ≥ 1, `C_d(ℚ)/2C_d(ℚ)` has 8 elements, injects into
  `Sel₂ = Σ(𝒞_d)` (8 elements), so every Selmer class, in particular `[a]`, is realized, and
  `P + 2Q` (Q of infinite order) gives a non-torsion representative with `x ∈ aℚ*²`.
- Gain: the trusted sentence is exactly what Kriz (C4), TYZ+GZ (C2+C1) and
  "`Ш(C_d)[2^∞]` finite + Cassels" each conclude, with no Kummer bookkeeping inside the trust
  boundary.
- Lean cost (SPECULATIVE effort tier: medium investment): (i) Kummer map
  `C_d(ℚ) → (ℚ*/ℚ*²)²` is a homomorphism with kernel `2C_d(ℚ)` (the "x, x ± d squares ⇒ halvable"
  lemma; classical, elementary); (ii) the forward direction of Proposition 0 (point ⇒ solution of
  `Σ`), which `Covering.lean` already states in `Loc`/`Sel2` form; (iii) a point of infinite order
  outside `2C_d(ℚ) + C_d[2]`, from a height descent: generalize `approx_parallelogram_law` and
  `fg_of_descent'` from the one curve of `mordellWeilE` to `C_d` over `ℚ`.
- Not weaker as a hypothesis than CR3 (equivalent given Lean-proved Proposition 0); the gain is
  standardness and auditability, not strength.

**N3. CR3^Ш (exists as `CertifiedRankSel`).** `Ш(C_d)[2] = 0` in coordinates. Equivalent, already
in Lean (`RouteK/Selmer/Covering.lean:381`). N2 is preferable as a statement because "rank ≥ 1"
is what the cited theorems state verbatim; `Ш[2] = 0` requires the extra RK9 step on the paper
side.

**N4. Restrict the domain to the slot curves.** CR3 could quantify only over the configurations
the slot construction outputs (two-prime base configuration glued with `≡ 1 (mod 8)` primes,
slot-k §2). That set still has unbounded `ω` and arbitrary residues for the primes of `β`, so no
theorem in §§2–5 becomes applicable; the narrowing only shrinks the trusted domain. Low value.

## 9. Experiment specs (not run; devserver, PARI/GP or Sage)

**E-1. Do the surfaces `X_{β,θ}` have points for every `m`?** For 30 admissible `B` (generator of
`scratch/rv-route-k/descent_search.py`) and all 16 positive `m`, search `X_{β,θ}` for points with
`s, t` of height ≤ 10⁴ using `ellrank` on the fibres `θ G(s) W² = G(t)` for `s` of height ≤ 50.
Signal: if some `(B, m)` has no point while DL's `m` does, a uniform `ℚ`-section (D2) is
impossible and T2 is closed for good; if every `m` always works, search the Kuwata–Shioda
fibrations of `X_{β,θ}` for a section defined over `ℚ(β, θ)` generically.

**E-2. Thin-set intersection (T8).** For 3 fixed instances, sample `q ∈ U(ℚ)` of increasing
height, compute `θ(q)` (factor with `factor`, 20–40 digits), and test `θ(q) ∈ G(ℚ)ℚ*²` by
`ellrank` on `θ W² = β²t⁴ − 1` (and by the full DL search). Report the proportion of `q` for which
the one-curve case has a *found point* (not a Selmer certificate). Signal: a stable positive
proportion only says that T8 is plausible, never a proof; zero found points at heights where
`ellrank` succeeds for random twists would mean the family is atypical.

## 10. Ranking (recency check included)

| Rank | Option | Kind | Chance |
| --- | --- | --- | --- |
| 1 | N2 (rank ≥ 1 trust statement) + RK9 in Lean | narrowing | high; medium investment |
| 2 | N1 (quartic form) | narrowing | high; cheap win; same strength |
| 3 | C3 (Tian's algebraic induction) generalized to arbitrary residues without GZ | elimination via CM theory | very low, and Lean-infeasible |
| 4 | D2/E-1 (a `ℚ`-section on a fibration of `X_{β,θ}`) | elimination | very low; one cheap experiment decides the precondition |
| 5 | T8/E-2 (thin-set intersection in `q`) | elimination | very low; no theorem in sight |

All candidates surfaced in this run; the pre-existing items (TYZ, Kriz, Route E, prime-case
criteria) keep their ranks from rs-pole and pc-audit. Re-ranking them together changes nothing:
every elimination candidate recurs under several framings (Hasse principle, Kummer surfaces,
families) with the same obstruction, `Ш[2]` for a Selmer-minimal curve with unbounded `ω`.
