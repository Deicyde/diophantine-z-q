# Version 21 draft, new Part I: local mathematical review (Fable, 19 November 2026 UTC)

Reviewed object: `manuscripts/quartic_v21.tex` in Astra's worktree `...\work\version21-explicit229-20261118\repo`, SHA-256 `f72580eaeaea95933fcd9d631d6f8577586543117ad10124abf4fe346befee07` (verified before and after). Local review, not a gate result. Nothing was posted or pushed.

## Verdict

No mathematical error found in the new Part I (TeX lines 91-1243 and 3994-4028) or in the two retained-body edits. Every numerical constant I recomputed is correct. Two credit points should be settled before release (G1, G2). The rest are notes.

## Errors

None found.

## Gaps

**G1. Credit for the three-detector method (lines 96-100; CREDITS.md addition).** Part I opens "The construction in this part is due to José Brox. It uses three reflected detectors...". Brox's own accepted package attributes the three-detector method to Carbon: `research/brox-explicit229-v68/paper.tex` line 1253-1254 ("The three-detector construction there is attributed to Gemini Carbon and builds on José Brox's quadratic constructions"), `PR_DESCRIPTION.md` line 45 and `REVIEW_NOTE.md` line 59 say the same, and the retained Version 19 text (line 5800) says "Carbon added the third additive detector". As written, Part I and the new CREDITS.md sentence credit the 229 construction to Brox alone. To close: say that the 229 construction is Brox's (the inverse-Vieta graft, the two-component aggregate, the centre 3/11, the N = 15 arithmetic and the diagonal normalization) and that it builds on the three-detector construction of Gemini 4 Carbon in Section `v19:250-construction`; confirm the wording with Elliot or Brox, as the release policy requires for credit changes.

**G2. AI usage statement (line 55485) is unchanged from Version 20.** Brox's package states that "GPT-6 performed the additional independent exact-BigInt audit, repository comparisons and package/PR preparation" (PR_DESCRIPTION.md line 45). I do not know which agents contributed to Brox's 229 construction and paper. The manuscript agent guide requires the statement to name every agent that contributed to this version. To close: ask Brox which AI systems contributed and add them, or record his confirmation that the present list covers them.

## What I checked, and how

### (1) Height bound with torsion translates (lines 324-510)

- Formal expansions: with my own power-series computation for `y^2 = x^3 - D x`, `z = -x/y`: `x(z) = z^-2 + D z^2 - D^2 z^6 + 2 D^3 z^10 - ...` and invariant differential `(1 + 4 D z^4)^(-1/2) dz`, coefficients `1, -2D, 6D^2, -20D^3, 70D^4`. Both match lines 374-381.
- Valuation steps: `v_p(4j+1) <= 2j-1` for odd `p` gives term valuation `>= 3a` (the difference is `(2j-1)(2a-1) >= 0`); at 2 the denominators are units. `l(z) = z(1+eta)`, `v(eta) >= 2a`, so `x(z) - l(z)^-2` is integral. Correct.
- Principal parts: `Z = (m_i L)^-2 C_J / prod_{j in J, j != i} m_j^2 + integral`; loss at a place is at most `v(C_J)` in both cases; summing over at most `binom(3, j-1)` subsets with `C_J <= j M^(2(j-1))` gives `24 log M + log 864`. Recomputed: coefficient of `log M` is 6+12+6 = 24; constants `3 log 2 + 3 log 3 + log 4 = log 864`.
- Archimedean: `x >= -d` at both embeddings, `Z >= 1`, loss `<= h(d) = (1/2) log 7` (norm of `3 - sqrt2` is 7). Correct.
- `h(x(P_0)) = log 41`: norm of `57 - 28 sqrt2` is `41^2`, the 2-adic denominator contributes `2^6`, archimedean product `1681/64`. Correct in the coordinates of this curve. I also checked that the same point on the unit-twisted model has a different height (log 162), so the retained statement `h(x(P_*)) = log 41` at line 29598 is indeed for this model.
- `2 hat h(P_0) >= log 41 - (1/3) log 392 = 1.723 > 1`; `(1/3) log 676 = 2.172 < 3`; `12 log 96 - 12 = 42.77 < 43`; `6 + 43 + log 864 + (1/2) log 7 = 56.73 < 57`; `(2M+1)^2 <= 5M^2 + 5`. All correct, giving `B^2 < 40 h(Z) + 2285`.
- Identity for `Z` (line 502): rederived from the two shift equations; correct. Coefficient sums at the two embeddings are 22.66 and 25.97, both `< 32`; `40 log 32 = 138.6 < 140`. So `B^2 < 40 sum h(t_j) + 2425`.
- Labels: `|m_1|/2, |m_2|, |m_3|, |2 m_4 + 1|` are `|n|, |a|, |t|, |b|` with the definitions at lines 750-753. Consistent.
- Retained inputs consumed, taken as given: `prop:generator` (line 20675: `2E(K) = Z P_0`; with `P_0 = 2 R_0` and all torsion being 2-torsion this gives `E(K) = Z R_0 + E[2]`), and the duplication estimates before `eq:o8-indexheight` (line 29592). I did not re-prove the constants 392 and 676; a naive bound gives an upper constant about 77, so 676 is on the safe side.

### (2) Cutoff-free local extraction (lines 512-772)

- `v21:five-pole-obstruction`: checked all three cases; correct for every prime outside {2, 3, 17}, including `p_0 = 0`, `q_0 = 0`. The three equations are the retained five pole rows (line 6027-6029): `(17-e)(3e+17) = 289 + 34e - 3e^2`.
- Order-four logarithmic precision: needs `p` odd, unramified, `p != 5`; `v_p(4j+1) <= 4j-4` for `j >= 2`; relative precision `4r`. Correct; 5 is in `S`.
- Scalar step: the three valuation classes `2+4Z`, `1+2Z`, `4Z` are right for odd `mu` (the norm `F` has even valuation at split and inert primes); `v(W_s) > -mu/2`; the three inequalities in (v21:scalar-depths) follow. `R_s` is the parent's `R` (line 8869-8874: the four factors are `beta - 2401, beta - 1, beta, 32 beta + 343`).
- At 149: residues 59, 97, 109, 108 recomputed and all are non-residues; `v_149(R_s)` is `2N+1` or `2N-1`; `L_15 = 66`.
- Translation by `(0,0)` negates `z`; `v_p(a/h) = v(Z) > 9 mu/4`. Correct.
- `M_S(beta)`: scalar contact differences have support exactly {2, 3, 5, 7} (recomputed), a negative valuation of `beta` is even, so each prime of `M_S(beta)` gives odd positive `v_p(R_s)`. Correct.
- Contacts: denominators, pairwise differences of `Theta_c` and the differences `c/2 - theta` have prime support exactly `Gamma` (recomputed: {2,3,5,7,11,13,17,37,41,79,89,647,2399,3593}). The ten contacts are distinct. `L e_k` values at lines 267-271 recomputed and correct, `L = 2399^2 37^2`.
- Five factors: valuation classes checked term by term, including the two odd classes in `Phi_2`; `eta_j = Tr(W_j^-1)^-1`; `v_p(b_j) <= mu + 2 l`; the exponent readings at lines 721-724 are right; 409 handled.
- Where the old cutoff was used: the retained `q198:scalar-extraction` and `v19:250-local` proofs use the cutoff only through the radical `M_5` and the constant built from `prod_{p <= 76176} p`. Part I uses the retained H4.1 directly (line 18340: `h(a) < c_0 C_N R^2 E(R) log R`, `R = B_S M_S(a)`, stated for every rational `a` outside the four values), so no cutoff enters. I found no step in lines 512-772 that needs a lower bound on the prime.
- Small primes: 2, 3, 5, 17 and all of `S` are never consumed (scalar primes are outside `S`, detector primes outside `Gamma`); 149 is treated explicitly; primes of `Gamma \ S` enter only through `J_*`.
- Not re-derived by me: the statement that the exact logarithmic ratios are `k_i u_i/h + e_i` and `k_i v_i/(h-1) + e_i`. It is the retained argument at lines 9250-9284, which I read and which uses only odd `p`.

### (3) Effective soundness at N = 15 (lines 774-962), all constants recomputed exactly or to high precision

- `J_* = 30366775457346956958330 < 2^75`: correct. `c_0 C_0 B_S^2 E(B_S) log B_S = 2^236.14 < 2^237`. `c_0 C_0 = 2^147.96 < 2^149`. `calC = 2^299.21 < 2^300`. `1 + log J_* = 52.77 < 54`.
- Product of `1 + 1/p` over primes `p <= 1000` outside `Gamma` is 2.0397 `< 21/10`. `1001 log 1001 = 6915 > 6006`.
- Fractional-linear maps: `u_+ = 2 + 1/t`, `u_- = 2 + 1/(c - t)`; the five forms correspond to `Theta` and `c - Theta` (checked with `t = m/n` in lowest terms); row sums 3 and 33.
- `tau < 2^238 M_S(beta)^3` from H4.1, `(1 + log m)^2 < 2m` and `log B_S > 1`: correct.
- Case `Delta != 0`: `121 sqrt(21/10) 14^(1/3+1/36036) = 422.6 < 500`; `log J_* + (1/6) log 14 = 52.21 < 53`; left side `220 * 6005/6006 = 219.963`; right side `6.25 + 207.9444 + 5.625 = 219.8194`; `log 149 = 5.00395`, `log 500 = 6.2146`, `log 2 = 0.6931472 < 0.693148`, `log 274 = 5.6131`, `53 + 44 * 5.01 = 273.44`. The margin is 0.14 and the monotonicity argument is right.
- Case `Delta = 0`: `256036 = 484 * 529`; first term `233.3 < 240`; `149^66 > 2^239`; the Lucas comparison holds. `|Delta| <= 14 B^4` and `J_X <= 4 B e^tau` are as in the retained lemma `q198:residual-divisibility`.
- Final step `v^2 | 102`: correct.

### (4) Completeness (lines 964-1243)

- Compared paragraph by paragraph with the reviewed Version 19 completeness (lines 6116-6291). The changes are: the doubled scalar quotient (bound 4000 `< 2^12`), the affine Lucas choice, points as multiples of `R_0`, the two new shifts, centre `c/2` in place of 1. Each is consistent.
- `149^7 > 22202 * 2^20`: correct. `v_2(r_4) in {2,3}`, `r_4 = 1 mod 3`, `r_4 = 13 mod 17`, `D_s` a unit at 2, 3, 17: recomputed, correct.
- `S_0 >= -12`, `S_0 - S_1 >= -16` (the weighted average is exactly `-12 - 4` at the extreme), diameter `25/11`: correct, so the thirty coefficients are distinct.
- Paired identity for `R_j` at prepared primes and the exact identity with the tenth-power denominator: rederived; correct. Depth count `2(B_p+5) - B_p >= 10`; valuations of `408/409` are 3, 1, 1.
- Pole witnesses: the substitution `e = 17 e_*, p_0 = p_*/b, s = s_*/b, v = h_p/s_*, q_0 = q_*/(b s_*)` satisfies all three equations (checked symbolically by hand), and the `s_* = 0` branch is right. Hypotheses of `v5:preparation-zero-bridge` (line 32114: depths 3, 1, 2) are met.
- `thm:v5-simultaneous-primes` (line 38062) is applied within its stated hypotheses: distinct integers, `q >= 1`, odd squarefree modulus prime to 7, fixed cutoffs.
- Taken as given: the half-generator lemmas, the real-progression lemma, P14 of `q214:uniform-existence`, and the compact-neighbourhood argument of `q198bb:specialization`.

### (5) Stored-to-physical scalings (lines 189-248)

- Aggregate rows 175 and 207, as printed, equal `2q(x_2 - x_86) + 26 q^2 + A_0` and `2q(x_2 - 2x_86 + x_200) - 8q^2 + A_1` with `A_0 + A_1 rho` as in (v21:aggregate-components), `D = 11 - 6 rho`, including every `C` factor. Checked term by term.
- For the block `i = 1`, rows 107-114 give `F_st = f_st^2/q`, and are exactly the two secant equations of `q198:reciprocal-pairs` under `f = f_st/q`, `g = g_st/q`, `s = s_st/q`, `eta = C eta_st/q`; the term `-x_77^2` in row 113 fixes the scale. So `x(Q_1) = s_1^2/q^2 + D(f_1+g_1)/q` as stated.
- For the scalar, rows 155-162 are the inverse-Vieta equations up to one common field scaling, and that scaling cancels: they force `x(Q_2) = p_st/q` whatever the normalization of `R_2`.
- Not checked: blocks `i = 3, 4` beyond the shape of rows 127-128 and 143-144, and the chain back through the 195 coordinate maps.

### (6) Retained-body edits

- Lines 4076-4080 (ladder deletion): correct and changes no statement.
- Lines 4157-4166 (`det M_6`): the three block determinants multiply to `1/214450708242592116705963714180667354532074632082` exactly (recomputed). I did not recheck the block entries against the printed `M_6` or the sign of the column permutation.
- Whole-file diff against `quartic_v20.tex` (line endings normalized) has only: title, date, PDF title, abstract lines 76-78, the inserted Part I, and these two insertions.

### (7) Finite statements

- Maximum `149^30` attained at `y_77^2 y_101^2`, `y_104^2 y_112^2`, `y_111^2 y_112^2`: agrees with my earlier independent expansion of the same data. The unnormalized sum of squares at `N = 15` has 3,312 monomials and height `149^32` (recomputed from the source table).
- Astra's own `research/version21/construction/check.py` passes ("all 414 displayed rows and 436 scaling entries checked"). Running it rewrote `research/version21/FINITE-CHECKS.json`; the bytes are unchanged (SHA-256 `50cbb124...`, equal to the manifest), only the modification time moved.

## Notes

- **N1 (line 933).** The retained Lemma `q198:affine-lucas` is stated for "sufficiently large" `c`; its proof needs only `c >= 8`. Part I applies it "with `c_a >= 8`". For a statement advertised as fully effective, say explicitly that the bound comes from the proof (line 9327), or restate the lemma with the threshold 8.
- **N2 (lines 206-222).** The physical formulas are stated and the secant rows are cited, but the rows that fix the scale (113-114 and their analogues) are not. One sentence giving `f = f_st/q`, `s = s_st/q`, `eta = C eta_st/q` and citing those rows would make the point-of-use derivation complete.
- **N3 (line 704).** The formula for `b_j` uses `R_j = (1+q_j)^-1`. That `1 + q_j != 0` follows from the pole row `409^2 (1+q_j) b_j = 408^2 eta_j^2` and `eta_j != 0`; saying so would also dispose of the midpoint `t_j = c/2` on the soundness side.
- **N4 (lines 4034, 4040).** The retained Version 20 part still says "The new construction" and "the new polynomial". Edition-relative wording; Version 20 reworded the analogous phrases of Version 19.
- **N5.** `README.md` in the worktree says "Version 21 candidate" and "Version 20 remains the published release until this candidate has the required review". Since merging the version pull request is the release, this wording has to be final before the head that is approved.
- **N6.** Jennifer Park: the README contributor line is unchanged from main in this worktree.

## Not read or not verified

- The 207 source rows and 207 normalized rows, except rows 22-26, 34, 101-118, 149-162, 175-177 and 207; the exponent lists; I relied on my earlier independent expansion of the same data files and on the checker.
- Brox's `paper.tex` and the supplier note were compared by constants and structure (grep), not read line by line.
- Retained suppliers: H0-H4, the generator proposition's proof, the duplication constants, the prime theorem's proof, the half-generator and real-progression lemmas, P06-P14 of `q214:uniform-existence`.
- The PDF, the build record and the binding files.
- I did not execute any program under `research/brox-explicit229-v68/`.
- The bare clone at `C:\Users\glaze\Documents\upstream-138\repo.git` now fails its automatic `git gc` (missing object c1e4ed1b); fetches still work but hang on the gc step. Unrelated to this review.

## Draft relay note to Astra (not sent)

From: Fable (Claude Code, Elliot's session)
About: Version 21 draft (TeX f72580ea...): local read of Part I and the two retained edits
Needs reply: No

Optional local review, not a gate result and not the builder record you asked for. Full report: C:/Users/glaze/Documents/fable-review-v21-text.md.

I found no mathematical error in lines 91-1243 and 3994-4028 or in the two retained edits. I recomputed every constant in the height corollary and in the N = 15 proposition (J_*, the 2^237, 2^149 and 2^300 bounds, the Euler product 2.0397, 219.963 against 219.8194, 233.3 < 240), the formal expansions, the contact support (exactly Gamma), the 149 residues, the pole-witness substitution and det M6. Rows 175 and 207 equal the two aggregate formulas term by term, and rows 107-114 fix the scalings for i = 1.

Two points to settle before release:
1. Credit. Part I and the new CREDITS.md sentence say the construction is due to José Brox. His own package attributes the three-detector method to Carbon (paper.tex 1253-1254, PR_DESCRIPTION.md 45, REVIEW_NOTE.md 59), as does retained line 5800. Please name Gemini 4 Carbon for the three-detector construction that Part I builds on, and have the wording confirmed.
2. AI usage statement. It is unchanged from Version 20, and Brox's package says GPT-6 did the independent audit and package preparation. Please confirm with Brox which agents contributed to the 229 and list them.

Notes, none changing a statement: say that the affine Lucas lemma is applied with the threshold 8 taken from its proof; cite rows 113-114 (and analogues) as fixing the stored-to-physical scale; note that 1 + q_j is nonzero by the pole row; the retained Version 20 part still says "the new construction"; README still says "candidate".

Running your check.py rewrote FINITE-CHECKS.json with identical bytes (hash equal to the manifest); only its modification time changed.
