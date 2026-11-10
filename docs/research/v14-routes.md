# Version 14 and our four hypotheses: what changed in the arithmetic route

Status: research note, 2026-11-09 (task v14-routes). Every claim carries a mark.
VERIFIED means checked against the text (the 11/5 manuscript `diophantine_zq.tex`, the Version 13
source `~/gt-src/v14/quartic_v13.tex`, the Version 14 addition `~/gt-src/v14/addition.tex`, the Lean
sources or a note of this repository) or by an exact computation in `scratch/v14-routes/`.
STANDARD means a published theorem whose exact statement was checked. SPECULATIVE means an idea or an
assessment that is not proved. UNCHECKED means a source that could not be read here.

Line numbers: "N5 L" is a line of `diophantine_zq.tex` (11/5), "V13 L" a line of `quartic_v13.tex`
after removing carriage returns (the file mixes CRLF and LF line ends; removing the CRs does not
change the line count), "V14 L" a line of `addition.tex`. The diffs used are
`scratch/v14-routes/main.diff` (N5 lines 141-6589 against V13 lines 209-6789, the main text) and
`scratch/v14-routes/app.diff` (N5 lines 6590-11250 against V13 lines 11905-16544, the appendices
A-H). In those files a hunk at left line `l` is N5 line `l + 140` (main) or `l + 6589` (appendices).

## Summary

1. **The source of Version 14 is not available in full.** `~/gt-src/v14/quartic_v14.tex` is a
   127-byte GitHub API "Not Found" reply, not TeX (VERIFIED). The upstream repository could not be
   fetched from this machine (tried 2026-11-09). What is available is `addition.tex`, the new
   Version 14 section `sec:v14` ("A quartic presentation with 299 variables", 955 lines), and the
   full Version 13 (November 7, 22,087 lines). The comparison below is therefore 11/5 against
   Version 13, plus Version 13 against the Version 14 section. Any change that Version 14 makes
   outside `sec:v14` (to the introduction, say) has not been seen. The section's first lines say
   it does not modify Version 13 or the original polynomial (V14 L1-2, L5-7, VERIFIED).
2. **No change to the main construction's arithmetic.** Version 14 says: "We retain the arithmetic
   inputs, qualifications and source editions of Sections v12-inputs and v13. The polynomial of
   the main construction is unchanged" (V14 L5-7, VERIFIED). Between 11/5 and Version 13 the
   statements of Theorem 4.1 (six-contact estimate), Lemma 5.1, Theorem 5.2 (PC), Theorem 5.3
   (RC), Lemmas 5.4-5.5 and Proposition 6.2 are byte-identical; no diff hunk falls inside them
   (VERIFIED). The changes in the main text are attributions to OpenAI's preprints, a fuller
   valuation argument for the multiplication tests, and three repairs inside the proof of RC
   (Kato's 1999 theorem at the prime 2, the scope of a congruence off the coefficient filter, and
   a determinant specialization lemma) (VERIFIED, §2).
3. **The new material is a second construction, the "quartic route".** Versions 4-14 add
   explicit quartic polynomials (Version 14: 299 variables, 6,630 monomials) defining ℤ in ℚ by a
   different construction: four elliptic labels, a Lucas growth test and a root-height bound. It
   has no universal compiler, no multiplication template and no Proposition 6.2. Its deep inputs
   are (VERIFIED, §3):
   - a five-contact height estimate (`hyp:o8-height`, V13 L6854, exponent 24, and the sharper
     `thm:quartic-height19`, V13 L8922, exponent 19, constant below 2^2093966), proved by the same
     kind of argument as Theorem 4.1: a Shimura curve (discriminant 210), QM surfaces,
     modularity through Pan's theorem, Faltings heights and a CM estimate;
   - a seven-witness pole predicate (`hyp:o8-pole`, V13 L7720) proved from the same restricted
     converse RC, for the same curves `y² = x(x − ℓ)(x + 3ℓ)`;
   - a simultaneous prime theorem for polynomial patterns of Gaussian primes
     (`thm:v5-simultaneous-primes`, V13 L16566, after Sun, arXiv:2610.20691), proved in a
     2,600-line appendix of the manuscript with the Green–Tao nilsequence machinery over `ℚ(i)`.
4. **Nothing in Versions 13-14 weakens, removes or replaces any of our hypotheses.**
   - SixContactMin: Theorem 4.1 is unchanged. The quartic route needs a height estimate of the
     same depth, for another contact set.
   - CertifiedRankSel: Route K does not use RC or Sections 7-9 and Appendices E-G at all, so the
     repairs there do not matter to us. The quartic route's pole still rests on RC.
   - GreenTaoDense and GoodPrimeDensity: Proposition 6.2 is unchanged. The quartic route's prime
     input is strictly harder than ours.

   Adopting the quartic route in Lean would cost a new construction and new soundness and
   completeness proofs, months of work, and would buy no hypothesis (SPECULATIVE estimate, §4).
5. **Two items worth recording** (§5). Version 13 cites OpenAI's *pointwise 2-converse for
   elliptic curves with rational two-torsion* (7 October 2026) and states that RC is a special case
   of its Theorem 1.1. If that theorem covers the congruent number curves `C_d`, it would give a
   second, independent source for CR₃^Sel. It could not be read here (UNCHECKED), and it is
   unrefereed. Second, the exponent-19 height proof replaces Gaudron–Rémond 2014 by
   Gaudron–Rémond 2023 and `J₁(N)` by a quotient `X_H`, which gives a constant polynomial in the
   contact radical. This is a new height argument, but it uses the same kind of deep inputs.
6. **Recommendation** (§6). V14 does not change the priorities. GoodPrimeDensity and
   GreenTaoDense are the only hypotheses that Lean work can remove, and both are in progress;
   finish them first. The next hypothesis to attack is **CertifiedRankSel**: move the elementary
   half of its justification into Lean. Proposition 0 is now a Lean theorem, so the step from the
   Selmer condition to TYZ's criterion (tyz-5b §4: Lemma 4.1 and Theorem 4.3, plain 𝔽₂ linear
   algebra on the Lean Selmer system) is the next piece of unrefereed new mathematics that can
   become kernel-checked. *First task:* prove in Lean that a Route K Selmer system with 8 solutions,
   one of them with first coordinate `a`, `|a| ≡ 7 (mod 8)`, has `det M_5b = 1` over `𝔽₂`.
   *Success:* the theorem builds for every number of primes with the standard axioms, and a
   `decide` cross-check agrees with brute-force counts for up to 4 primes. SixContactMin has no
   comparable elementary half (nt-h, rs-height), and Version 14 offers no new route to it.

## 1. What Version 14 is

`addition.tex` begins with the comments "Isolated Version 14 author draft; assembled independent
review is required" and "This file does not modify the original polynomial or Version 13" (V14 L1-2,
VERIFIED). Its one theorem, `thm:v14-quartic` (V14 L9-29), asserts:

> There is a specified integer polynomial `P_299` of total degree four in 299 variables such that
> `X ∈ ℤ ⟺ ∃ v ∈ ℚ^298 : P_299(X, v) = 0`. It has 6,630 nonzero monomials, content one, and largest
> absolute coefficient `186624·3^(2^26)`. … There is also a specified integer quartic `P_314` with
> [the same property] … Every coefficient has absolute value strictly less than `2^6496`.

Every subsection (V14 L36-955) works inside the quartic route of Version 13 (§3 below). The notation
can mislead: "the fixed-difference chart for H" (V14 L75), "the H/V0 domain", "the H-depth bootstrap"
(V14 L526) and "squared-H" refer to the **auxiliary point** `H` of the quartic source, not to the
height hypothesis H (VERIFIED by reading: `H` is the point with `U = f(H)²`, V14 L103, and the
"H choice" is chosen in a progression, V14 L680). The changes are of three kinds (VERIFIED):

- **Private witness changes with explicit inverse maps.** These are the affine H chart and the
  squared-H replacement (V14 L75-131), the reciprocal point charts and the deletion of the alternate
  ordinates (V14 L396-525, L802-835), shorter power chains (V14 L837-853), the sparse Lucas
  recentering (V14 L855-865), and the fourteen constant coordinates of the ordinary presentation
  (V14 L900-935).
- **Changed arithmetic certificates, with separate proofs of soundness and completeness.** These
  are the shifted 3-adic parity anchor (V14 L133-247), the three common-scale test groups replacing
  separate pole blocks (V14 L249-394, L617-684), the auxiliary point domains with a depth-10
  bootstrap (V14 L526-615), and the coupling of the scale to the quaternion anchor, with an
  explicit weak-approximation argument on the quadric `u² + 6v² − 2z² = N` (V14 L686-790).
- **Retained arithmetic inputs, quoted, not reproved** (V14 L51-72): "the squareclass
  calculation, formal expansions and logarithm estimates, simultaneous contact-prime construction
  with its real-density condition, preparation-zero pole criterion, root-height implication,
  Lucas argument and scalar-depth-24 argument". In particular the root-height conclusion
  `B² − 6 < 7𝓗|N|^{19/k}` with `1 ≤ 𝓗 < 2^2093966` (V14 L60-64) is the exponent-19 height estimate
  of Version 13, and the pole completeness interface "uses the same small-prime squareclasses and
  depths, square reduced denominator, and real interval (0, 17)" (V14 L69-72), which is the
  preparation-zero lemma `v5:preparation-zero-bridge` (V13 L10563).

One step avoids the height estimate in a special case: "The independently restored scalar anchor
gives `B > (40𝓗)^10`, excluding all three radicals equal to one without using H or auxiliary
logarithms" (V14 L66-68). The case it excludes, contact radical one, is not the general case,
so the root-height implication is still needed (V14 L60-65, L378-382, L608-614; VERIFIED).

The only `\ref`s in `addition.tex` are to `sec:v13`, `subsec:v12-inputs` and its own labels
(VERIFIED). It never refers to Theorem 4.1, Theorem 5.2, Theorem 5.3 or Proposition 6.2.

## 2. The main route: 11/5 against Version 13

### 2.1 Labels and line numbers (VERIFIED)

| Item | Label | N5 line | V13 line | Changed? |
| --- | --- | --- | --- | --- |
| Generator certificate (G) | `prop:generator` | 268 | 339 | attribution sentence added before §3 |
| Theorem 4.1, six-contact estimate | `thm:height` | 404 | 480 | statement and proof unchanged; attribution paragraph at the start of §4 |
| Lemma 5.1, one-sided obstruction | `lem:pole` | 988 | 1067 | unchanged |
| Theorem 5.2, PC | `hyp:PC` | 1001 | 1080 | unchanged |
| Theorem 5.3, RC | `hyp:RC` | 1005 | 1090 | statement unchanged; preceded by an attribution paragraph |
| Lemma 5.4, corank | `lem:corank` | 1072 | 1157 | unchanged |
| Lemma 5.5, forward rank (GZK) | `lem:forward-rank` | 1086 | 1171 | unchanged, still cites Kolyvagin MPI/90-69 |
| Proposition 6.2, 22-prime pattern | `prop:fixed-prime-pattern` | 1267 | 1385 | unchanged |
| §6 test list and valuation deduction | (in §6) | 1172-1198 | 1260-1316 | rewritten (§2.2) |
| §7 restricted converse | `sec:rc` | 1760 | 1878 | attribution; Kato at 2 (§2.3) |
| §8 actual classes | (unlabelled) | 2718 | 2855 | off-filter scope (§2.3) |
| §9 two limits | `sec:limits` | 4382 | 4568 | new Lemma `lem:v10-determinant-specialization` (§2.3) |
| Appendix E, even coefficient source | `app:even-source` | 6825 | 12236 | Kato 1999 at the prime 2 (§2.3) |
| Appendix F, odd theta forms | `app:odd-source` | 8206 | 13737 | unchanged |
| Appendix G, final family | `app:endpoints` | 9981 | 15512 | layout of one display only |
| Appendix H, de Rham comparison | (unlabelled) | 10936 | 16469 | unchanged |

Version 13 keeps sections 1-13 and appendices A-H in the same order and adds main-text sections
14-18 (base residual compiler, explicit quartic, interfaces, 962-variable quartic, degree lower
bound; V13 L6790-11904) and, after the appendices, the simultaneous-prime appendix (V13 L16545) and
the Version 9, 12 and 13 quartic sections (V13 L19176, L19800, L20772). The `\appendix` command is at
V13 L11905, so those later sections are lettered as appendices.

### 2.2 Changes in sections 3-6 (VERIFIED)

- Attribution sentences (N5 after L254, L377, L973, L1004, L1123, L1760). For example, before RC:
  "The following statement is the `E = E_ℓ`, `s₂(E) = 1` case of [openaipointwise, Theorem 1.1],
  and also follows as a special case of [openaigoldfeld, Theorem 1.1]. We give the restricted
  argument here; these preprints are cited for attribution, not assumed as additional converse
  inputs" (V13 L1084-1088). Before §4: "the preprint's height assertion is not taken as an
  additional premise" (V13 L449-453).
- The multiplication test list (N5 L1172-1174, V13 L1260-1267) now states the conjugation
  explicitly: the three tests are `A_i − σ(A'_i)` with `A_i = L(z(U_i))/L(z(H))` and
  `A'_i = L(z(V_i))/L(z(V_0))`, "the primed ratio is conjugated before the difference is taken". The
  Lean template already does this: `feq (D 8) ((q 0).sub (q 3).conj)` and its two companions
  (`ZInQKernel/Syntax/Templates/Certificate.lean` lines 63-64). So the text has caught up with the
  saved template, and nothing changes for us.
- The valuation deduction at a contact prime (N5 L1194-1198) is expanded into an explicit argument
  (V13 L1287-1316) with the same conclusion, "one common group and place has its first eight tests
  of valuation at least one and its last four of valuation at least 25". Our Lean proof of
  multiplication soundness already proves that conclusion.

### 2.3 Changes inside the proof of RC (VERIFIED)

- §7 (N5 L1886, V13 L2011): the 2-part of Kato's divisibility is justified through Kato,
  *Euler systems, Iwasawa theory, and Selmer groups*, Kodai Math. J. 22 (1999), Theorem 0.8, with a
  new paragraph in Appendix E (V13 L12677-12787) checking its index set, the class of §0.7 and the
  comparison of the two cohomology conventions. The Euler-system definition (K8) is enlarged to
  every `m` prime to `cd_s` (N5 L6994-7021, V13 L12405-12443).
- §8 (N5 L2638-2644, V13 L2767-2781): the congruence `a_p(E^{(k)}) ≡ p + 1 (mod 8)` is now asserted
  at every fresh good split prime, inside or outside the coefficient filter. The reason given is
  that the selected prime is in fact outside the filter.
- §9 (N5 L3986-4006, L4364; V13 L4124-4191, L4549): a new Lemma "Determinant specialization with no
  dimension jump" (Smith normal form over a DVR) justifies specializing the generic coordinate at
  `t = 0`.

These are repairs to the manuscript's own proof of RC (Theorem 5.3). Route K proves PC from CR₃
for the curves `y² = x(x − ℓ)(x + ℓ)`, and CR₃ rests on Tian–Yuan–Zhang and Gross–Zagier–Kolyvagin
(`docs/research/tyz-5b.md`, `nt-tyz.md`), not on RC. So none of §§7-9 or Appendices E-G enters our
Lean development or the justification of CertifiedRankSel (VERIFIED against KERNEL_PLAN.md and
`ZInQ.poleCompleteness_of_certifiedRank`). Lemma 5.5 (`lem:forward-rank`), which Route K uses
through tyz-5b step 5, is unchanged, including its citation of Kolyvagin's MPIM preprint MPI/90-69
(N5 L11163, V13 L21875). The unrefereed-citation issue of nt-tyz §5.2 therefore stands.

### 2.4 Appendices B and C, and §13 (VERIFIED)

Appendix B now identifies four source files S30, S18, S29, S32 as sections of OpenAI's
pointwise-converse preprint (V13 L11965-11972). Appendix C gains a dictionary from the saved
templates to the mathematical relations (V13 L12060-12147). Its `pole` row is `Q_pole(B)²` for the
manuscript's pole polynomial with the `x + 3ℓ` curves. §13 adds Mazur's Conjecture 2 and the
remark that OpenAI already obtained Turing degree `0'`. None of this touches a hypothesis.

## 3. The quartic route (Versions 4-14)

### 3.1 Its curve is our curve (VERIFIED)

The quartic route uses `K = ℚ(√2)`, `d = 3 − √2`, `D = d²`, `E : y² = x³ − Dx`, and
`P_* = (57/8 − 7√2/2, −165/8 + 417√2/32)`, with `2E(K) = ℤP_*` "from Proposition prop:generator by
the unit change of variables recorded there" (V13 L10733-10747). The main curve has `d = 75 − 53√2`
(N5 L257). With `ε = 1 + √2`, the map `(x, y) ↦ (ε⁴x, ε⁶y)` sends the main curve to the quartic
curve and `P₀` to `P_*` exactly (`scratch/v14-routes/checks.py`, output `checks.output.txt`; the
manuscript records the same change at N5 L279-281). So our Lean Mordell–Weil theorem
(`ZInQ.mordellWeilE`) would transfer to the quartic route by an isomorphism.

### 3.2 Its height input (VERIFIED)

`hyp:o8-height` (V13 L6854): with `S_* = {p ≤ 76176}`, `𝒟 = {0, 1, 2401, −343/32}` and the
five contacts `∞, 0, 1, 2401, −343/32`, "for every `a ∈ ℚ \ 𝒟`, `h(a) ≤ H_* M_5(a)^24`", with
`log₂ H_* < 4783227`. `thm:quartic-height19` (V13 L8922): "`h(a) ≤ H_19 M_5(a)^19`,
`log₂ H_19 < 2093966`". The Version 9-14 quartics use `H_19` (V13 L19212, L19884-19892,
L20815-20822; V14 L60-64).

The proofs (V13 L6854-7708 and L8935-9077) are the same kind of argument as Theorem 4.1:
- the indefinite quaternion algebra of discriminant 210, whose genus-one Atkin–Lehner quotients are
  taken from González–Rotger, J. Math. Soc. Japan 58 (2006), Theorem 4.2 and Table 2;
- integral geometry over a degree-576 field;
- a metric comparison `h(a) ≤ 2 max(0, h_F(A)) + 128`;
- modular representations through Pan's Theorem 1.0.4 and Carayol;
- a CM estimate through Yuan 2024;
- an isogeny estimate.

The exponent-19 proof keeps the geometry. In the transfer step it changes three things: it bounds
the order of the nebentypus `t ≤ 2d'` instead of the degree of the coefficient field; it works on
`X_H = X₁(N)/ker ε` with Mascot's rational model; and it uses Gaudron–Rémond, *Nouveaux théorèmes
d'isogénie*, Mém. SMF 176 (2023), Theorem 1.9(1), with the Bost lower bound as quoted by von Känel
(Forum Math. Sigma 9 (2021), (2.2)). Theorem 4.1 instead transfers from `J₁(N)` with Gaudron–Rémond,
Duke 163 (2014), Theorem 1.4 (N5 L859-905). The result is a constant polynomial in the radical
(`A_19 R^19`, V13 L9068) rather than Theorem 4.1's `Q_R^17 = R^{17RE₀}`.

This is a genuinely new height argument relative to 11/5, but it serves a different contact set
and it rests on the same classes of input: Shimura curves, QM surfaces, modularity, Faltings heights
and isogeny estimates. It does not weaken SixContactMin. That hypothesis is about the six contacts
`𝒞 = {0, −15, −20, −24, −30, −60}`, which are built into our precision test and slope predicate.
Gaudron–Rémond 2023 is not on arXiv (arXiv API search, 2026-11-09), so swapping it for GR 2014 in
Theorem 4.1 would not make the leaf readable here (UNCHECKED either way; h-leaves already lists
GR 2014 as unread).

### 3.3 Its pole input (VERIFIED)

The seven-witness predicate `Ψ(b)`, with `B = 17b`, is `U(1 + bt²) = b(1 − bt²)`,
`p² = B(1 − e)(1 + 3e)`, `h = e(B − U²)` and `Bq² = (s² − Bh)(s² + 3Bh)` (V13 L7710-7718). The
quadratic factors `(1 − e)(1 + 3e)` and `(s² − Bh)(s² + 3Bh)` are the manuscript's `x + 3ℓ`
curves again. Lemma `hyp:o8-pole` (V13 L7720) gives soundness (no negative odd valuation outside
`{2, 3, 17}`) and completeness for `b > 0` with square denominator and square in `ℚ₂, ℚ₃, ℚ₁₇`.
Its proof "applies the existing Theorem hyp:RC and Lemma lem:corank" (V13 L7731-7733), through
`lem:original-seven-simultaneous-realization` (V13 L7787) and
`lem:original-seven-parity-completeness` (V13 L7892). Section 14 says explicitly that this lemma "is
proved from Theorem hyp:RC; it is not inferred from Theorem hyp:PC, which has different variables
and a restricted completeness domain" (V13 L6827-6829). The Version 9 table lists "Pole obstruction
and realization … These include the restricted-converse dependency proved in the earlier
arithmetic sections; it has not been discarded" (V13 L19241-19244). Version 14 keeps the
"preparation-zero pole criterion" (V14 L53, L69-72).

A Route K version (`x + ℓ` curves, CR₃ in place of RC) would need the descent lemma of slot-k redone
for the multiplier 17 and the conditions at 2, 3 and 17 (SPECULATIVE; not examined).

### 3.4 Its prime input (VERIFIED)

`thm:v5-simultaneous-primes` (V13 L16566-16592), "The simultaneous prime input". Given distinct
integers `c_1, …, c_k` (`k ≥ 2`), `q`, an odd squarefree `M` with `7 ∤ M`, and `H, Y > 0`, there
are positive integers `u, w` with `q | w`, `u/w² > H` and every `p_j = u + c_jw² > Y` prime. Each
`p_j` has a Gaussian generator `π_j ≡ 9 (mod 16)`, `≡ 1 + 3i (mod 7)`, `≡ i (mod M)`, and the
adjacent norms `d_±(π_j) = N(π_j ∓ 1)` are coprime across all pairs, with prescribed 2-adic
valuations. The appendix proving it (V13 L16545-19175) "uses the published fixed-field prime
estimate of Mitsui, the one-parameter equidistribution and factorization results of Green–Tao,
and published ordinary-prime transference results", following Sun (arXiv:2610.20691v2, Theorem
4.1) and the ideal-norm method of Frei–Tinková (arXiv:2408.17441v3), "no theorem from that work is
assumed" (V13 L16549-16558). The quartic sources take their global choices from this theorem
(V13 L19252-19255, V13 L10700-10704).

Compared with our GreenTaoDense plus GoodPrimeDensity, this is harder. The pattern `u + c_jw²` is
a polynomial progression, so Tao–Ziegler's dense polynomial theorem would give the primes and the
individual Chebotarev conditions on each `p_j`. It cannot give the coprimality of `d_ε(π_j)` and
`d_η(π_h)` for `j ≠ h`, because that condition couples different members of the pattern and is not
a density condition on one prime (SPECULATIVE assessment). The manuscript needs a 2,600-line
nilsequence argument over `ℤ[i]` for exactly this reason. Sun's abstract describes his construction
as based on OpenAI's "five-contact height estimate and a pole-parity construction" (arXiv API
record of 2610.20691v2, VERIFIED), so it brings in no new kind of input.

## 4. Effect on each hypothesis, and the cost of adopting

**SixContactMin** (`ZInQKernel/Hypotheses/HeightMin.lean`, the instance `S = S_mul`, `R = D` of
Theorem 4.1).
- Theorem 4.1 is unchanged from 11/5 to Version 13, and Version 14 does not refer to it
  (VERIFIED).
- The quartic route replaces it by `H_19` for a five-point contact set. That estimate is as deep:
  its proof is the manuscript's own, on the same geometric and modular inputs (VERIFIED, §3.2).
- The special case of V14 L66-68 (radical one excluded without the height) has no counterpart in
  our soundness proofs, where the adversarial slope may have any contact radical (nt-h §1.2).
- Nothing to adopt. If the six-contact proof were ever redone along the exponent-19 template,
  SixContactMin would still be implied, since any bound `≤ H₆(D)·M^24` suffices. That would be a
  second derivation of the same statement, not a weaker hypothesis (SPECULATIVE).

**CertifiedRankSel** (`ZInQ.RouteK.Selmer.CertifiedRankSel`).
- Unaffected. Route K uses neither RC nor its proof (VERIFIED, §2.3).
- The repairs in §§7-9 and Appendix E concern RC only.
- The quartic route keeps RC (VERIFIED, §3.3), so upstream continues to depend on the manuscript's
  own proof of RC, while our development does not. Version 14 confirms that Route K is still the
  cheaper pole input.
- The one new pointer is OpenAI's pointwise 2-converse (§5).

**GreenTaoDense** and **GoodPrimeDensity** (`ZInQKernel/Hypotheses/GreenTao.lean`).
- Proposition 6.2 is unchanged (VERIFIED). Our replacement of it by 22P_AP (nt-22p §3) is
  independent of upstream.
- The quartic route's prime theorem is harder (§3.4) and offers no substitute for either
  hypothesis.
- The two hypotheses rest on Green–Tao, Ann. of Math. 167 (2008), Theorem 1.2, and Tao–Ziegler,
  Acta Math. 201 (2008) (as recorded in `GreenTao.lean`), and on Proposition D of nt-22p and
  `docs/research/pd-paper.md` (branch `wip/pd-paper`). Lean work on both is under way (branches
  `wip/gt-dense`, `wip/gt-import`, `wip/pd-lean-1`, `wip/pd-lean-2`, `wip/pd-sieve`; VERIFIED from
  the local refs).

**Cost of switching our Lean development to the quartic route** (SPECULATIVE estimate).
- The finite part would be small (299 variables, 6,630 monomials), but the main construction's
  finite part is already done.
- Everything arithmetic would be new: the point charts, the formal-group logarithm estimates at
  unramified places of `K`, the Lucas growth lemma, the root-height transfer, the parity anchor,
  the common-scale test groups and the weak-approximation completeness argument. That is roughly
  the content of V13 L6790-10421 and L19176-22075, together with V14.
- In return we would get three hypotheses: `H_19` (as deep as H), RC or a redone Route K for `Ψ`,
  and the Gaussian prime theorem (harder than GreenTaoDense plus GoodPrimeDensity).
- The frozen target accepts any polynomial within its bounds, so a switch is legal. It buys nothing
  and costs months.

## 5. Items worth recording

**OpenAI's pointwise 2-converse.** Version 13 cites OpenAI, *A pointwise 2-converse for elliptic
curves with rational two-torsion*, preprint, 7 October 2026, Theorem 1.1, source revision
`4eaee87548250b2682affda7d05d947c05554bae` of `openai/math`, and *Goldfeld's analytic density
conjecture and the 2-converse for elliptic curves* (same revision) (V13 L21951-21960). It says that
RC is "the `E = E_ℓ`, `s₂(E) = 1` case" of the first (V13 L1084). The invariant `s₂(E)` is not
defined in the manuscript (VERIFIED: its only occurrence is V13 L1084).

If Theorem 1.1 there is a pointwise statement "`corank Sel_{2^∞}(E) = 1` implies `ord_{s=1} L = 1`"
for curves with rational 2-torsion satisfying some condition `s₂(E) = 1`, and if the curves `C_d`
of CR₃^Sel satisfy it, then CR₃^Sel would follow from it, Lemma 5.4 and Lemma 5.5. That would be a
source independent of Tian–Yuan–Zhang (SPECULATIVE). The preprint could not be read: the
`openai/math` repository could not be fetched from this machine, and the title is not on arXiv
(arXiv API searches, 2026-11-09).

It is unrefereed, so at best it would be a cross-check, as Kriz is now (nt-tyz §5.1).

**The quartic route's height constant.** `H_19 < 2^2093966` is tiny next to `H₆(D)`, whose
logarithm is about `17·D·E₀·log D` with `D > 2^(2^8008)`. The difference comes from the transfer
step (§3.2) and from the small field degree (`[L:ℚ] ≤ 576` against `≤ D`), not from a different
kind of input. Our size bounds already absorb the large constant (nt-h §1.3), so this has no Lean
consequence (VERIFIED for the comparison of the texts; the consequence is SPECULATIVE).

## 6. Recommendation

Version 14 changes nothing that our hypotheses depend on, so the priorities set by our notes
stand.

1. **Finish GoodPrimeDensity and GreenTaoDense** (in progress). They are the only two hypotheses
   that Lean work can remove outright. Version 14 confirms there is no cheaper prime input in
   upstream's lineage: the quartic route's prime theorem is strictly harder.
2. **Next new attack: CertifiedRankSel, by moving its elementary half into Lean.** Of the two deep
   hypotheses, neither can be proved in Lean. SixContactMin has no elementary component: its
   justification is Shimura curves, modularity and Faltings heights from end to end (rs-height §5,
   nt-h §5, h-leaves), and Version 14 adds only another proof of the same kind. CertifiedRankSel's
   justification is a chain:
   - (a) Proposition 0, now a Lean theorem (`ZInQ.RouteK.Selmer.prop0Statement`);
   - (b) the 𝔽₂ step from "Selmer system with 8 solutions and a class `|a| ≡ 7 (mod 8)`" to
     `det M_5b(d) = 1` (tyz-5b §4: Lemma 4.1 and Theorem 4.3, new mathematics checked only by an
     automated referee);
   - (c) `det M_5b = T_5b (mod 2)` (tyz-5b §3, Smith's row 5b reproved, also new);
   - (d) TYZ in the form of Proposition N (nt-tyz §4);
   - (e) Gross–Zagier–Kolyvagin and the dimension count.

   nt-tyz §6 (route 5) judged a Lean formalization of (b) low in value because Proposition 0
   would remain in the hypothesis. That objection is gone now that (a) is proved. After (b), and
   later (c), the trusted statement shrinks to TYZ, Rédei's formulas and GZK, all published.

   *First task.* In a new file under `ZInQKernel/RouteK/`, define the `2r × 2r` matrix `M₁` and the
   bordered `(2r + 1) × (2r + 1)` matrix `M_5b` over `ZMod 2` from the Legendre data that the Route K
   system already uses (`a_{ij}`, `y_i`, `z_i`; tyz-5b, Notation), and prove:
   - tyz-5b Lemma 4.1: for `d ≡ 5 (mod 8)`, the solutions of the Lean system `Σ(𝒞_d)` with
     `b₁ = 0` and `a₀ = λ·u` map bijectively onto `ker M₁`;
   - Lemma 4.2: a symmetric corank-one matrix bordered by `v` has determinant `vᵀk`;
   - Theorem 4.3: if the system has exactly 8 solutions and one of them has first coordinate `a`
     with `|a| ≡ 7 (mod 8)`, then `det M_5b = 1`.

   Then state the variant hypothesis `CertifiedRank5b`: for squarefree `d ≡ 5 (mod 8)`, if
   `Sel₂(C_d)` has 8 elements and `det M_5b(d) = 1`, then every Selmer class comes from a rational
   point. Derive `CertifiedRankSel` from it.

   *Success criterion.* `lake build` passes, Theorem 4.3 is proved for every number `r` of odd
   primes (not only by `decide`), `#print axioms` shows only `propext`, `Classical.choice` and
   `Quot.sound`, and a `decide +kernel` cross-check of Theorem 4.3 for `r ≤ 4` agrees with a
   brute-force count of the system. The main theorem variant under `CertifiedRank5b` compiles and
   `scripts/check_target.py` passes.

   *Chance:* high for the Lean work (finite-field linear algebra over a system already in Lean).
   *Payoff:* medium. It removes the first piece of new, unrefereed mathematics from CR₃^Sel's
   trust base. The second piece, (c), is the natural follow-up: the forest lemma, with `g(d)`
   given through Rédei matrices.
3. **On SixContactMin**, the paper-side steps of nt-h §5 (the Serre route at large `ℓ`, audited in
   ser-ell, and the NoCM lemma of h-cm) remain the right next steps. Version 14 adds no option.

## Scripts

- `scratch/v14-routes/main.diff`, `scratch/v14-routes/app.diff`: the two diffs of §2 (11/5 against
  Version 13, carriage returns removed).
- `scratch/v14-routes/checks.py` (output `checks.output.txt`): exact arithmetic in `ℚ(√2)`. It
  checks that the quartic route's curve and generator are the main ones after `(ε⁴x, ε⁶y)`, the
  identity `b_*² = c_*² − D`, the norms `N(c_* + b_*) = 16` and `N(c_* − b_*) = 49/16`, and the two
  roots of `Dv² + 2b_*v − 1` quoted at V14 L121-128.
