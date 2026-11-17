# Check of Jose Brox's 200-variable quartic, and an attempt to go lower

Claude Fable 5.2, in Elliot's Claude Code session, 14 November 2026.
Source: `github.com/JoseBrox/diophantine-z-q_improvements` at commit `e950bd2` ("corrected 200-variable release", v33).
Files read: `papers/quartic_existence/quartic200_20261115_v33.tex`, its parent `quartic204_20261114_v27.tex`, the valuation-class sections of `quartic226_20261110_v21.tex` and `local_tests/mixed_valuation_tests_20261109_v11.tex`, `square_abscissa_charts_20261108_v9.tex`, `compressed_reference_20261114_v27.tex`, and the two coefficient tables.

No code from the repository was run. All checks below use my own scripts, which only read the JSON tables.

## 1. Does the 200-variable result check out?

**The new step is correct, and the published table is exactly what the paper specifies.** The result is still conditional on everything it inherits from the 204-variable parent, which I did not audit.

### What the new step is

The 204-variable system kept one "stored root block" for a point Q_4 = [b]P because the Lucas argument needed b to be a nonzero integer. Jose replaces the Lucas labels by A = 2a + 2 and b = m + 1/2. Then (A − 2)b = a(2m + 1) is automatically a nonzero integer divisible by a, so the fourth point no longer needs a certificate of nonvanishing and can be an ordinary recovered difference of two points. That swaps 14 coordinates for 10.

### What I verified

| Check | Result |
|---|---|
| Rebuilt all 186 rows from the 204-variable parent table following Section 9 of the paper (delete coordinates 169–182 and rows 122–139, the affine substitution in rows 104–121, the nine new field equations, the aggregate row, compaction, primitive normalization) | Identical to the published table, row for row, in the same order |
| Every row has degree at most 2 and parameter degree at most 1; all 200 coordinates occur | Yes |
| Expanded the sum of squares with the parameter symbolic | 3,222 parameter-separated terms, 3,221 coordinate monomials, total degree 4 |
| Coefficient of x_191^4 | 1, so degree is exactly 4 and the content is 1 |
| The two polynomial identities in the pair lemma (both points lie on the curve; the recovered difference lies on E) | Both hold identically, with D symbolic |
| Shifted Lucas theorem, converse direction: m is an integer and the identity holds | Checked for r = 2, 3, 5 and a = 2..39 |
| Shifted Lucas theorem, forward direction: admissible indices are multiples of \|a\| and the growth bound holds | Checked exhaustively for \|a\| = 4..9 over all small indices; I also re-derived the proof by hand |
| The congruence U_j(C) ≡ j or (−1)^(j−1) j mod c used in the proof | Checked for c = 4..29, j < 60 |
| The corrected normalization: the stored slot L_2 equals R(2ℓ + 2), the Lucas product rows divide by R, and the cross-square row divides by R² | Follows from the rows as rebuilt; the label entering the Lucas residual is 2a + 2 |

### What I did not verify

- Any inherited arithmetic input: the group assertion 2E(K) = ZP, the scalar height and completeness statements, the contact-height bound, the pole obstruction and realization, the prime-pattern statements.
- The changed weighted trace-height lemma (weights 1, 1, 1, R² in place of 1, 1, R², R²). The argument reads as sound but rests on a family height theorem in another paper that I did not open.
- The completeness section beyond checking that the labels chosen there satisfy the Lucas identity.
- The balanced coefficient-height proposition.

## 2. Can it go below 200?

**I did not find a valid reduction.** I looked for one in four places. Three are provably tight within the current design, and the fourth could save at most two variables and has an unsolved problem.

### 2.1 No coordinate can be eliminated by substitution

I searched the table for any coordinate defined by a row in which it appears alone and linearly, and whose other uses would stay quadratic after substitution. There are none.

### 2.2 The five local factors per detector cannot be reduced or repacked

Each factor's nonconstant terms must have pairwise distinct, nonzero valuations at a contact prime. With the weights the rows can express (q⁵, q⁴ as a product of two stored quantities, q³, q²), the available classes are: all odd integers (a general square at q⁵), 2 mod 4, 4 mod 8, and the two odd classes ±ν mod 4 separately.

- The four order-3 tests (C_2, C_3, C_4 and the Lucas residual) must be plain squares at q⁵ to reach precision 3, and each then occupies both odd classes. So they need four separate factors, each with only two further slots.
- That leaves 12 tests for 8 slots plus one extra factor with 4 slots: 20 slots for 16 tests with four of them counted double. The current layout uses all 20.

I tried moving C_1 or I to the q⁴ slot as a product of their stored squares, which would remove a stored fourth power (two variables). It fails: a general fourth power at q⁴ can have valuation exactly zero and tie with the constant term. I also tried a different row scaling to avoid storing the squares of the order-3 tests; it costs a sixth factor.

### 2.3 The contact weight and the Lucas residual are minimal by degree count

- The contact relation has degree 10 in the contact variable. With quadratic rows, degrees at most double per stored auxiliary, so three auxiliaries are needed; three are used.
- The Lucas residual contains the monomial A²·t·b. Reaching degree 4 with a single stored product is impossible for that monomial, so two stored products are needed; two are used. I looked for a lower-degree equation with the same growth and nonvanishing properties (direct label for w, a congruence on t, the difference form δ² − (A−2)δw − (A−2)w² = 1). Each needs multiplication by A − 2 to force the index to be a multiple of a, and ends at two products.

### 2.4 The one remaining stored root block (the scalar point Q_2)

This is the only structural outlier: 14 coordinates plus 2 for the chart parameter j, where a recovered pair costs 10. Converting it is the same move Jose made for Q_4, so it is the natural next step. My estimate is a saving of **at most 2 variables (198)**, and I could not make it work:

- The scalar equations need z(Q_2) = −x/y, and the aggregate needs R²·x(Q_2). In the pair chart x and y are quadratic and cubic in the coordinates, so two extra field coordinates are needed (for example x(Q_2) and y/x + s). That gives 10 + 4 against 14 + 2.
- **Unsolved:** the pair chart allows Q_2 = (0, 0). On that branch the row defining y/x places no constraint, the scalar ratio becomes free, and the scalar argument's conclusion (that |a| is at least 149^{L_N}) no longer follows. The stored root chart excludes this automatically because x(Q_2) is a nonzero square. Every guard I tried costs the two variables back.
- The scalar proof would have to be redone for a point that is only known to be a difference of two points. I did not read the scalar papers closely enough to say whether it survives.

## 3. Summary

- 200 is correctly established at the level I could check: the new lemma, its use, and the exact table.
- Within the present architecture, the detectors, the contact weights, the Lucas block and the pair charts are each at their minimum, by explicit counting arguments.
- The only lead is converting the scalar point's block, worth at most 2, blocked by the (0, 0) branch and by the need to re-prove the scalar step.
- A reduction beyond that would need a new idea at the level of the architecture: fewer than 16 local tests, fewer than four labelled points, or a different way of forcing growth.

Scripts (my own, in the session scratch folder): `verify200.py`, `lemmas.py`, `elim.py`, `show.py`.

## 4. Addendum: Astra's 199-variable construction (checked 15 November)

Astra's team resolved the (0, 0) problem of Section 2.4 by changing the scalar function from −x/y to g = −(x − η)/y with η = 1 + 2√2. I checked `CONSTRUCTION199.md` and `candidate199-quadratic.json` (SHA-256 `b2eabca9…a6cc`) independently. **I found no error. The reduction to 199 holds relative to the same inherited premises as Jose's 200.**

### Verified

| Check | Result |
|---|---|
| Rebuilt all 189 rows from Jose's 200 table using only the prose of the construction (`verify199.py`) | Identical to Astra's table, same order; coordinate map agrees |
| Shape | 199 coordinates all used, rows quadratic, parameter degree 1; sum of squares has 3,260 monomials (3,261 parameter-separated terms), degree 4, content 1, with coefficient-one pure fourth powers |
| The slots that changed meaning (x35–x38, x107, x108, x114–x116) have no consumer other than the rows the construction rewrites | Yes |
| η identities: the points with x = η satisfy 2Q = (d, 0); y² = 38 + 6√2 has norm 4·7³, not a square, so they are not K-rational; η, η ± d and y have norms ±7, ±14, 4·7³ | By hand |
| Local lemma: positive valuation of g(Q) forces [4]Q into the formal group with the same valuation | Proof read and re-derived; correct at 149 and at primes above 76176 |
| Scalar divisibility with l = 2ν(Q_2): the relation [2k][4]Q_2 = [8l]H gives v(l) − v(k) = v(Z) | Correct; torsion components are killed |
| Physical-Z circuit: the new rows give V = R²·W with the same W as Jose's rows, at the cost of the one extra coordinate J | Correct (Jose's stored ratio was Z/R, obtained free from the rescaled root chart) |
| Torsion exclusion: Q_2 finite, and y = 0 would force (x − η)S = 0 | Correct, given S ≠ 0 from the reference step |
| Labels: A = 2l + 2, and Δ equals Jose's Lucas residual with a replaced by l; completeness labels l = 2a_old, t, m satisfy it | Correct |
| Height: constant weights 1,1,1,1 and offset 11 are a direct case of Theorem 1 of Jose's weighted-trace paper (any points of E(K) other than O, any fixed weights); T ≥ 5 | Correct, and simpler than Jose's use: the h(R) term disappears |

### Not verified

- The inherited inputs, as before.
- The completeness section's real and small-prime preparation. The argument (g/z is a unit tending to 1 near the identity) is right as far as it goes, but I did not check it against the source's pole-realization hypotheses.
- The claim that the source's pole obstruction and reference exclusion do not depend on the scalar point (the non-circularity). I read Astra's account of it, not the 1.9 MB source.
- Astra's expanded quartic file was not compared term by term; I expanded their quadratic table myself and the counts agree.


## 5. Addendum: the 198-variable quartic (Conant package `H10-quartic198.zip`, checked 14 November, Pacific)

Source: Jose's 204-variable table (the copy in the package equals the one at Jose's commit `e950bd2` as polynomials). Two changes: an odd affine fourth label (204 to 200, the same idea as Jose's own 200) and an "inverse Vieta" chart for the scalar point (200 to 198). No code from the package was run.

**I found no error. The reduction to 198 holds relative to the same inherited premises.** It supersedes the 199 of Section 4: both replace the same scalar block, and this chart does it in 14 coordinates with no extra normalization coordinate.

### Why the chart works (checked by hand)

Coordinates U, V, W, M, r, P, r_2 describe the line y = (M/R)x + r/R through U_2, −V_2, −Q_2. The four equations UV = R²P, PW = r, r(U+V+W+2M) + DR² = 0, R²P + W(U+V) = M² are exactly the three Vieta relations for the line meeting y² = x³ − Dx at abscissas VW/R², UW/R², P. I verified each relation, that the three stated points lie on the line, that the reciprocal abscissas are U/r and V/r, and that the three ratio rows give L_2 = 2z(U_2)/z(H), L_2⁰ = 2z(V_2)/z(H − P_0) and Z = 2z(Q_2)/z(H).

The point that defeated my own attempt in Section 2.4 is handled by the structure: DR² ≠ 0 forces r ≠ 0, hence U, V, W, P ≠ 0, and the ratio rows force the three ordinates nonzero. So Q_2 is finite, has x ≠ 0 and y ≠ 0, and is not torsion. No guard variable is needed. The stored scalar ratio is still Z/R, so no normalization coordinate is needed either.

### Verified

| Check | Result |
|---|---|
| Every retained row of Jose's 204 table, after x_old = R^e·z_new, equals a power of R times the delivered row (`verify198.py`, with R_2 = R² used; that defining row is present) | 139 rows carried over exactly; rows 104–144 dropped |
| The six changed Lucas rows equal rows I wrote from the stated equations: stored products (L_2 − 1)L_4 and (L_2 + 1)L_3 | Identical |
| The 39 new rows (pair 4 with affine ratio L_4 − 1 and multiplier 4; the ten chart equations; the aggregate 7 + ¼Tr Σx) equal rows I wrote from the stated equations | Identical |
| Shape | 198 coordinates all used, 184 rows, quadratic, parameter degree 1; sum of squares has 2,945 monomials, degree 4, content 1 |
| Balanced table equals the unbalanced one under the stated weights with A = 149C² | Identical, row for row |
| Balanced expansion | 2,959 parameter-separated terms, 2,945 monomials; largest constant coefficient is (5898050446009651968·31581660^28)², largest C² coefficient is 31581660^28; the 14 mixed monomials cannot vanish (even constant, odd C² coefficient, C odd) |
| Lucas residual Δ = t² − (a+1)(a−1)tb + (a−1)²b² − 1 with a = 2ν(Q_2), b = 4ν(Q_4)+1 odd | Soundness index bound and growth checked numerically for both signs of a+1; completeness labels (a in 6Z, b = U_{a−1}(a+1)/(a−1) odd, Δ = 0) checked for a = 6..198 |
| Scalar divisibility: v(Z) > 9μ/4 puts Q_2 in the formal group or reducing to (0,0); translating by (0,0) changes z only by sign; then v(a) > 9μ/4 | Re-derived; correct |
| Height: constant weights, offset 7, T ≥ 1; direct case of Jose's weighted-trace theorem | Correct |

### Not verified

- The inherited premises, as before.
- The completeness preparation against the source statements it cites (P13, P14 of the upstream uniform-existence note). The text is explicit about the points Carbon found missing in the 199 note (depth at 2, 3, 17; 64 | h_*; pole realization applied to the final inputs), but I did not open the source for these.
- The affine200 intermediate table as a separate object; I checked the final table directly against the 204.
- The claimed exact coefficient height beyond the two maxima above.

## 6. Addendum: the 196-variable quartic (Jose's repository at commit `5c35db3`, checked 15 November)

Source: `papers/quartic/laurent_elimination_20261115_v38.tex` and `computation/quartic/laurent_recovery_v38/` (`config196.json`, `family196/`). No code from the repository was run.

**I found no error. The 196 is the 198 of Section 5 with two coordinates removed by an exact change of variables, so it has the same rational input projection as the 198 for every N.** Nothing arithmetic changes: every proof about the 198 (soundness, completeness, the Busy Beaver threshold) applies to the 196 word for word.

### What the step is

The 198 stores, for each of its two detectors, the inverse weight w_j, its square, and its fourth power. The fourth powers (coordinates 80 and 95 of the 198; the second is stored as w_1^4/R) are deleted. To keep every row quadratic without them, 60-odd other coordinates are rescaled by fixed integer powers of the three nonzero quantities R, w_0, w_1, and nine scalar coordinates by nonzero constants. Because R, w_0 and w_1 are nonzero on every solution of either system, the substitution is a bijection between the two zero sets that fixes the input.

### Verified (`verify196.py`)

| Check | Result |
|---|---|
| The 198 table in Jose's repository equals the one I audited | Identical as polynomials |
| Coordinates of the 196 are those of the 198, in order, minus the two deleted | Yes |
| Each of the 182 retained rows of the 198, after x_old = c·R^a·w_0^b·w_1^c·y_new, equals a monomial in R, w_0, w_1 times the corresponding 196 row (both sides reduced using only the retained power relations) | 182 of 182; no extra rows |
| The two deleted rows become identities under w_{0,4} = w_0^4 and w_{1,4} = w_1^4/R | Yes |
| The nine rows that make R, w_0, w_1 nonzero and define the retained powers (X^2 row, two scalar product rows, forced-prime row, R_2 = R^2, q_j w_j = 1, w_{j,2} = w_j^2) are literally unchanged in the 196, so nonvanishing follows from the new system itself | Yes |
| Shape of the unbalanced 196 | 196 coordinates all used, 182 quadratic rows, 2,943 monomials, degree 4, content 1, coefficient of X^4 equal to 1 |
| Parameter dependence of the unbalanced 196 | Polynomial in A with exactly three parameter monomials: −2A·x_102, −44402A·x_102²·x_114, A²·x_102² |
| Largest constant coefficient of the unbalanced 196 | 484991541504995159662206970923766531374664106904986910720 (57 digits), between 149^26 and 149^27; so its height is max of that and A², and A² is the maximum for N ≥ 7 |
| Balanced 196 equals the unbalanced one under x = C^w·y, A = 149C² | Identical, row for row |
| Balanced 196 | 2,943 monomials (2,957 parameter-separated terms), degree 4, content 1; height K_196·C² with K_196 = 11903780636513165769654680680436132271178681610029854792; no coefficient can vanish for C ≥ 149 |

SHA-256 of `family196/quadratic.json` (unbalanced), as stored in Jose's repository: `3b6ab20da25bced159559c35e512e2bb2e56959b734b4265c8f80a7bd9cdb1c1`; of `family196/polynomial.json`: `a8ab93d66fe83f4bdfd4b176d47c250c2e124f42535d7a6a133edff6a97389ad`. (An earlier version of this note gave hashes of my Windows working copy, whose line endings differ; those were wrong as identifiers.)

### Not verified

- The inherited premises, and everything about the 198 that Section 5 lists as unverified.
- The 258-variable fully specified quartic in the same paper (N = 9682). I did not look at it.

## 7. For Version 19: the fully specified 258-variable quartic, table step only (checked 15 November)

Source: Jose's repository at commit `5c35db3`, `computation/quartic/laurent_recovery_v38/` (`config259.json`, `config258.json`, `family259/`, `family258/`) and the parent `compressed_reference_v27/family260/quadratic.json`. No repository code was run.

**The two elimination steps 260 → 259 → 258 are exact, by the same check as for the 196** (`verify_elim.py`). This says nothing yet about the 260 itself or its threshold N = 9682; Carbon is reading that paper.

| Step | Deleted coordinate | Row identities | Guard rows unchanged | Result |
|---|---|---|---|---|
| 260 → 259 | detector-0 inverse weight to the fourth power | 231 of 231; deleted row becomes an identity | q_0·w_0 = 1 and w_{0,2} = w_0² | 259 coordinates, 231 rows, 3,703 monomials |
| 259 → 258 | detector-1 inverse weight to the fourth power | 230 of 230; deleted row becomes an identity | q_1·w_1 = 1 and w_{1,2} = w_1² | 258 coordinates, 230 rows, 3,705 monomials |

Both children: all coordinates used, rows quadratic, degree 4, content 1, coefficient of X⁴ equal to 1. The table's own metadata states the parameter as A = 149^(2N+1) for every N ≥ 9682.

Not checked: the 260-variable parent and its effectivity argument; the coefficient-height statements (largest coefficient 9792²·149^19364 at N = 9682); the balanced 258 table.

## 8. For Version 19: the 195-variable quartic and the explicit 257-variable quartic (Jose's repository at commit `cd474ee`, checked 16 November)

Scripts (mine; they read only the JSON tables, and no code from the repository was run): `verify195.py`, `verify257.py` in the session scratch folder `brox\`.

### The 195 chain

1. **196 with 182 rows to 196 with 176 rows** (`quartic196_redundancy_20261115_v40.tex`). Six rows are deleted: the two rational components of the reciprocal curve equation in each of the pair blocks 1, 3, 4. Verified: the 176 retained balanced rows are unchanged; in the unbalanced table all 54 rows of the three blocks are exactly the components of the stated field equations (scales 1, 2, 4; the fourth block with label shifted by 1); and the three exact identities hold as polynomial identities over Q(sqrt 2): kappa Z_p U = h REG_p - (1 - D F) RAW_p, kappa Z_a V = k REG_a - (1 - D G) RAW_a, and U - V = -(h-k) SEC + (f-g) TAN + D g (F - f^2) - D f (G - g^2). So Z_p U = 0, Z_a V = 0 and U = V follow from retained rows, and U = 0 follows once (Z_p, Z_a) is not (0, 0).
2. **Change of row basis** (`primitive_quadratic_bases_20261115_v40.tex`). Verified: the 8 by 8 rational matrix is invertible (determinant 1/214450708242592116705963714180667354532074632082); after scaling coordinates 76 and 90 by 1/3813373161796, all 176 rows of `primitive_basis196_v40/quadratic.json` (blob SHA-256 381ea54e...) equal the transformed parent rows up to nonzero constants.
3. **Affine change and Laurent elimination to 195** (`quartic195_20261116_v45.tex`). Verified: after the triangular affine change of coordinates 50, 72, 73 and the weights x_i = w^(a_i) y_i, the row x_79 = w^2 becomes an identity, the guard q w = 1 is retained literally, and every other row equals a nonzero constant times a power of C and of w times the target row on q = 1/w. 175 rows, 195 coordinates, all quadratic, coefficients polynomial in C. The quartic has 2956 coordinate monomials, 2965 parameter-separated terms, X^4 coefficient 1, and height max(126616122944180358034867798936, 149^(2N+2)) for N = 1..9, with no monomial vanishing at N = 1 or 9.

The starting table `laurent_recovery_v38/family196/quadratic.json` is unchanged since commit 5c35db3 (blob SHA-256 3b6ab20d...), which is the 196 table of Version 18.

### The explicit 257

Source `laurent_recovery_v38/family258/balanced-quadratic.json`. Verified with the same method: the deleted square (old coordinate 157 = w_1^2) becomes an identity, the guard q_1 w_1 = 1 is retained, every other row matches; 229 rows, 257 coordinates; 3679 monomials, 3684 parameter-separated terms; height max(484991541504995159662206970923766531374664106904986910720, 149^(2N+2)) for N = 1..15 and at N = 9682, where it is 149^19366 (about 2^139806, some 42,000 decimal digits).

### Not verified

- Step 1 needs (Z_p, Z_a) not (0, 0). The paper derives this from the reference chart: the two coordinates are y/x at H and at H - P, and P is not 2-torsion. I checked the algebra only, not that identification in the 196 table.
- The uniform statements for all N (support and height) beyond the values listed; the paper proves them by sign arguments I did not reproduce.
- For the 257: the effective threshold N = 9682 and every arithmetic premise behind it (effective elliptic sums, explicit contact-height constants, the corrected reference chart). None of these proofs is in the Version 18 manuscript.
- The 258 parent: I checked its two eliminations from the 260 table earlier (Section 7), not the 260 table itself against the physical system.

## 9. Carbon's explicit 244 / 250 candidate (package relay\to-fable\20261116-0336-from-carbon-v19-244-250, checked 16 November)

Script: `verify244.py` in the session scratch folder `brox\` (mine; reads Jose's JSON at cd474ee and Carbon's JSON; runs neither party's code).

### Finite part: passes

- The 247-coordinate table is Jose's `additive212_v25/unbalanced-quadratic.json` unchanged (212 coordinates, 186 rows), plus 35 cloned coordinates and 32 rows that are exactly the detector-1 rows with the cloned coordinates substituted, plus one new row, which is 4 R^2 (t0 - 2 t1 + t2) + sum_m (C_m0 - E_m0)(C_m1 - E_m1). Jose's trace row is 8 R^2 (t0 - t1) + sum_m ((C_m0 - E_m0)^2 + 2 (C_m1 - E_m1)^2).
- 247 to 244: for each detector the source has q w = 1, w2 = w^2, w4 = w2^2; w4 is deleted; the first two are retained literally; the deleted rows become identities; every other row matches up to a nonzero constant and a monomial in the three units. 216 rows, all quadratic. The parameter A occurs in one row, linearly. The quartic has 3344 monomials.
- 250: the 244 rows with A replaced by coordinate 250, and the ladder c0 = 149^449, c1 = 149^379 c0^2, c2 = 149 c1^2, c3 = c2^2, c4 = c3^2, c5 = 149 c4^2 = 149^20441 (= 2*10220 + 1). 222 rows, 3362 monomials, X^4 coefficient 1, all coordinates occur, largest coefficient the constant term 149^898 + 1747145497790223592810060471184416344603224790540808983 < 2^6483.

### Proof document: what I checked by hand

- Lemma 3.1. The two rows give t1 - t0 = S0/2 and t2 - t1 = (S0 - S1)/2, where S0 + S1 rho is the sum of the four abscissas. The identity x(2W) - d = (x0^2 - 2 d x0 - d^2)^2 / (4 y0^2) is correct (expand (x0^2 + d^2)^2 - 4 d (x0^3 - d^2 x0)). So each abscissa of a nonzero doubled point is at least d at both real embeddings, which gives t1 - t0 >= 6 and t2 - t1 >= 8. Correct.
- Remark 2.1 arithmetic: with V18's (H4.2), S = {2,3,5,7,11,13,17,37,41,2399}, E(R) = prod (1 + 1/p), the stated bounds give exponent 237 + 2*109445 + 18 + 13 = 219158. Correct as arithmetic.
- The cited V18 passages exist and say what is quoted (index height, contact-height theorem with C_3 < 2^330770, (H4.2), P05-P07, P12, the real bound in the Busy Beaver section, Lemma q196:general).
- Carbon's earlier remark that the 212 reference rows have an "exceptional-case gap" is not right: Jose's correction note says the error was in a printed table of a paper, and that the 212 table's six reference rows are the complete original ones. The built 247 keeps them unchanged, which is correct.

### Not verified; these decide whether the result stands

1. Jose's effective sum theorem (B^2 <= 2 h(S) + 80 for four nonzero multiples of P). It replaces the ineffective constant from von Buhren. It is not in Version 18. The 263 route needs it as well.
2. The passage from the four-contact bound to the reflected ten-contact bound h(t) <= K_2 M (22 + (1/2) log M)^2 with K_2 = 2^221274 (Jose's quartic262 paper), including the role of the extra prime 2029147 and the comparison between V18's radical M_S and the radical outside primes up to 76176.
3. Completeness for every N >= 3. V18's own 214 completeness (P13) only says "choose a fixed N_C"; the explicit bound Carbon quotes (lines 3964-3980) is written for the 198 system in the Busy Beaver section. The scalar formula has the same shape, but the transfer to the 212-based system has to be written out (which quotient Z, which neighbourhoods).
4. Completeness with three detectors: prime selection and pole realization for the third detector, and that the per-detector local argument (P05-P07, P17) applies verbatim to the additive detectors of the 212 table, which Version 18 proves in the setting of the 198 system.
5. The threshold inequalities of Section 4 (I read them and saw no error, but did not recompute the integer comparisons).

## 10. Jose's effective sum theorem (read 16 November)

Paper: `papers/effective_sums/effective_elliptic_sums_20261108_v10.tex` at commit cd474ee, read in full through Corollary 4. This is the input both the explicit 263 and Carbon's 250 need in place of the ineffective constant from von Buhren, and it is not in Version 18. I read it as a proof, by hand; no code was run. I found no error.

Statement. For E_D: y^2 = x^3 - D x with D in Z[sqrt 2], P of infinite order, nonzero integers n_1..n_r, x_i = x([n_i]P) positive at both real places, Z = sum x_i, B = max |n_i|: h(Z) >= max_i h(x_i) - A_r log B - B_r with A_r = (r-1) 2^(r-1), B_r = sum_k C(r-1,k-1) log k. For r = 4: 24 log B + log 864.

What I checked.
- Local expansion: from t = -x/y one gets t^2 x^2 - x - D t^2 = 0, so x = (1 + sqrt(1 + 4 D t^4)) / (2 t^2) = t^-2 + D t^2 - D^2 t^6 + ..., with integral (Catalan) coefficients. I verified dx/(2y) = dt / sqrt(1 + 4 D t^4) by direct differentiation, hence the logarithm l(t) = sum (-1)^k C(2k,k) D^k t^(4k+1) / (4k+1).
- Valuations: above 2 the denominators 4k+1 are units; at odd p (unramified in Q(sqrt 2)) v_p(4k+1) <= 4k-2, so each term with k >= 1 has valuation at least 3a for a = ord(t) >= 1. Hence ord(l(t) - t) >= 3a, ord l(t) = a, and x(t) - l(t)^-2 is integral. Injectivity of l on the formal points follows from ord l(t) = ord t; this covers the ramified place above 2, where the general theory would only give injectivity deeper in the filtration.
- Rank one: l([n]P) = n L_v whenever [n]P is formal, so x([n]P) = 1/(n^2 L_v^2) + integral.
- Local loss for a fixed index i: with J the set of formal indices at v, Z = (n_i L_v)^-2 A + integral, A = n_i^2 T_J = C_J / prod_{j in J, j != i} n_j^2 with C_J a positive integer. The loss is at most max(0, ord A) <= ord C_J. Summing over places and over subsets J containing i gives sum_J log C_J, and C_J <= k B^(2(k-1)) for |J| = k. For r = 4 the totals are 24 log B and log 864 (= 2^3 * 3^3 * 4). Correct.
- Archimedean places: positivity gives sigma(Z) >= sigma(x_i) > 0, so there is no loss.
- Positivity for multiples of P = 2 R_0: x(2Q) is a square in K, nonzero for Q of infinite order. Correct.
- Corollary 4: with V18's eq:o8-indexheight, h(x([n]P)) >= n^2 - 6 (I checked that V18's P_* is this P: h(x(P)) = log 41), one gets h(Z) >= B^2 - 6 - 24 log B - log 864, and 24 log B - B^2/2 <= 12 log 24 - 12 < 27, so B^2 <= 2 h(Z) + 80. Correct.

Limits. I did not check the second inequality of the corollary (h(Z) <= h(S_0) + h(S_1) + (3/2) log 2) beyond its form, nor the joint-height statement (the C_r, D_r bounds), which the constructions do not use. The theorem assumes P has infinite order and that the model is the integral equation y^2 = x^3 - D x; both hold here.

Consequence. Point 1 of Section 9 is, in my reading, sound. For Version 19 this is about two pages of self-contained argument using only V18's index-height bound.

## 11. The reflected ten-contact height bound (read 16 November)

Sources: Jose's `papers/quartic/quartic262_20261110_v21.tex` lines 84-155 (cd474ee), and Version 18 lines 9830-9952. Read by hand; no error found. This is point 2 of Section 9.

- The four-contact bound. Jose uses h(u) <= C M_5(u)^2 (1 + log M_5(u))^2 with C < 2^221231, M_5 the product of primes above 76176 with positive odd valuation on v, u, u-v, u-2401v, 32u+343v. Version 18's (H4.2) has the same five forms with the set S = {2,3,5,7,11,13,17,37,41,2399}: h(a) < C_2 M_S^2 E(M_S) [1 + log M_S / log B_S], C_2 < 2^(7557/32). Since every prime counted by M_S either is at most 76176 or is counted by M_5, M_S <= B_* M_5 with B_* the product of primes up to 76176 (< 2^109445). With E(n) <= 1 + log n this gives exponent 237 + 2*109445 + 18 + 13 = 219158 < 221231. So Jose's constant follows from what Version 18 already proves, as Carbon's Remark 2.1 says.
- The reflection. u = 2 + 1/t sends the contacts infinity, 0, 1, 2401, -343/32 to t = 0, -1/2, -1, 1/2399, -32/407, which is Theta; u = 2 + 1/(2 - t) gives 2 - Theta. Inverting, t = 1/(u-2) and t = (2u-5)/(u-2), with row sums 3 and 7, so h(t) <= h(u) + log 3 and h(t) <= h(u') + log 7. Multiplying the two bounds for h(t) - log 7 > 0, with the two block radicals coprime outside Sigma and each original radical at most E_2 times its Sigma-free part (E_2 = 2029147, the one prime above 76176 dividing a contact difference), gives h(t) - log 7 <= C E_2^2 M (1 + log E_2 + log M_+)(1 + log E_2 + log M_-), and the arithmetic-geometric mean inequality bounds the product by (1 + log E_2 + (1/2) log M)^2. Numerically 1 + log E_2 < 15.6 < 22 and C E_2^2 < 2^221231 * 2^42 = 2^221273; doubling absorbs log 7. Hence K_2 = 2^221274. Correct.

Not checked: the factorizations certifying that 2029147 is the only prime above 76176 dividing a contact difference or a number 1 - theta (the paper cites an independent certificate).

## 12. Explicit completeness threshold on the 212-based system (looked at 16 November)

Point 3 of Section 9. Version 18's completeness for the 214 system (P13, line 9060) has the scalar bound in the form W_s <= K_W R_s^-4 with K_W = M_Z^4 + M_Z^2 + M_F^2, hence 0 < b_s <= 9793 K_W^2 R_s^-6, and then says "choose a fixed N_C" so that this is below 17. The Busy Beaver section (lines 3925-3980) makes the same bound explicit for the 198 system: a compact neighbourhood where both real values of z(H) exceed 1/2000 in absolute value, the scalar point with |z| <= 1, so |Z_0|, |Z_1| < 2^12, |F| <= 1/7, W_s < 2^49 R_s^-4 and b_s < 2^112 R_s^-6; R_s >= 2^20 suffices.

The formula for W_s and b_s is the same in both places, and the neighbourhood construction concerns the curve, the reference point H and the scalar point, not the 198-specific coordinates. The 198 quotient carries a factor 2 (Z = 2 z([a_0]P)/z(H)) that the 214 and 212 systems do not have, which only helps. So the explicit constant transfers, and with R_s >= 149^(2N+1)/22202 the condition R_s >= 2^20 holds from N = 3 (149^7 > 22202 * 2^20). I see no obstacle. It has to be written out for the 212-based system: the Busy Beaver passage leans on Proposition q198:scalar-preparation and Lemma q198:half-generator-progression for the order of choices, and the 212 argument must cite the corresponding steps of the 214 completeness (P13-P16) instead. About half a page. I did not re-derive the measure argument that produces the neighbourhood.

## 13. Carbon's third-detector extension for the 250 (package relay\to-fable\20261116-1305-from-carbon-v19-250-third-detector, read 16 November)

Read: `THIRD_DETECTOR_MANUSCRIPT_EXTENSION.tex` in full, against the released V18 source (SHA-256 0cb9c70b...). Carbon's script was not run.

### Holds

- V18's Theorem `thm:v5-simultaneous-primes`, Lemma `arbitrary-avoidance`, Corollary `compatible-progressions` and Lemma `real-progression` are stated for any k >= 2 distinct integers; none uses the number of detectors. Carbon's hypothesis check for k = 30 is correct: the thirty coefficients D0^2 (U_j - theta) are distinct (shift gaps exceed 6 and 8, diameter of Theta_2 is 4), one is zero, M and q are fixed first, 64 | h_*, 64 | L.
- The shifts U_1, U_2 depend only on the four root labels, which are fixed before the prime theorem, as V18 P15-P16 requires.
- Local soundness (Carbon Prop. 2.x): the five factor shapes and the P05-P07 argument are those of V18 lines 9001-9015, applied to one detector and one prime at a time. Nothing links detectors.
- Fresh-witness step (P17 analogue): v_p(t_j - theta) = 1 at its own prime, 0 at the other nine, v_p(t_j - 1) = 0, hence v_p(q_j) = -1; depth table 3, 11, 1, 2, 14, 4 as in V18.
- Other primes (P18 analogue): R_j = (product of its ten primes) / (integer)^10, so every other valuation of b_j is even, including at the other detectors' primes. Simpler than V18's multiplicative case (no a_*^10).
- Real bounds, depths 4, 2, 2 at 2, 3, 17, and the pole-row dictionary for detector 2 (five rows, substitution checked by hand, zero-witness branch kept).
- Threshold inequalities of the earlier proof document, Section 4 (item 5 of Section 9 above): now recomputed by hand. Height bound for S (constant (1/2) log 448), (4.8) with constant 9, the Delta != 0 exclusion (2^118 * 15^6 > 22^3 * 2324135^6), and the Lucas step all hold.

### Defects in the write-up (not in the mathematics)

1. The displayed condition on e_p reads `2 v_p(1-theta) - 2 v_p(D0 w) >= max(4, B_p+5)`. The sign is wrong and it cannot be met. The term (1-theta)^2/(t_j-1)^2 has valuation 2 v_p(1-theta) + 4 v_p(D0 w); the condition should be that this is >= max(4, B_p+5). The later use is of the correct form.
2. B_p is defined as a lower bound for "every comparison test expression". The estimate `2(B_p+5) - B_p >= 5` needs B_p to bound the monomials as they occur in the factors (C_1^4, B_i^4, A_2^2, ...), not the bare tests. Say so.
3. "indeed |G/G^0| divides h_*" is asserted but not arranged in the scalar proposition; it is not needed (the point h_* (P, P^sigma) lies in G^0 by choice).

### Still outside what I have checked

- That Jose's 212-coordinate table is V18's 214 with the two contact circuits and the scale row replaced (his quartic212 paper). I compared Carbon's 247 with the 212 table, not the 212 with V18's 214. A V19 on the 250 would have to import that step, as the 263 imports the 262-to-257 chain.
- V18's own inputs are taken as stated (P04, P12, the scalar bound (4.1), RC, the prime theorem).

## 14. Jose's 212 table against Version 18's 214 (checked 16 November)

Script: `cmp212_214.py` in the session scratch folder `brox\` (mine; reads JSON only). This closes the open item of Section 13.

- Jose's pinned 214 source (`balanced214_v24/source/quadratic214.json`, cd474ee) equals the 214 table in the released V18 repository (`research/quartic214/construction/artifacts/candidate214-brox/candidate214-ir.json`): all 188 rows and all coordinate names.
- The 212 table (`additive212_v25/unbalanced-quadratic.json`): 178 rows are literally the 214 rows under the coordinate map; 214 rows 64, 65 and coordinates 119, 120 are deleted; eight rows change: 22, 24, 25 (detector 0 contact), 35-38 (detector 1 contact), and the trace row (214 row 182, 212 row 180). No row is rescaled.
- Eight coordinates change meaning (4, 76-78, 90-93). They occur only in the eight changed rows and in row 23, a square definition. So the scalar, reference, Lucas, root-product, factor, trace/pole rows are the 214's, untouched.
- The new contact rows are r = (t-1)^2, s = r^2 and two rows which together say (1+q) P_5(r) = r^5 with w = 1/q, P_5 having roots (1-theta)^2 for theta in Theta. The coefficients are 3813373161796 times the elementary symmetric functions, recomputed.
- The new trace row is 8 R^2 (t0 - t1) + sum of the four norms, as in Section 9.

Consequence: Carbon's 247 = 214 with (a) these contact and trace replacements, (b) a cloned detector, (c) one shift row. Every arithmetic statement V18 proves about the 214's unchanged rows applies to the same rows here.
