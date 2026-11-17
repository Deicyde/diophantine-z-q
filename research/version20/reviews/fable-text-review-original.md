# Fable review of the Version 20 draft text (explicit 247, PR147-prompted edits, other changes)

Reviewed 17 November 2026. Root `C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\version20-release-20261117\repo`.
`manuscripts/quartic_v20.tex` SHA-256 `fa1e3eb43be998a157e64883a3ecf6d703cca8790ea1ee5ce8a858b1b4196f37` (confirmed); compared with `manuscripts/quartic_v19.tex` SHA-256 `1f0e4db9...` (the released source).

Read-only. Astra's `check.py`, `verify247.py`, `check_printed.py` and all of Jose's and Carbon's programs were not run. My scripts: `v20text.py` and `v20rows.py` in the session scratch folder `C:\Users\glaze\AppData\Local\Temp\claude\7fbd96b289b0830c\673e4698-d945-4239-ad78-c5f5e062f088\scratchpad\v20\` (they read the TeX and JSON only; exact rational arithmetic).

## Verdict

No error found. No gap that affects a statement. A few wording notes.

## Scope 1: the new Part "Version 20: an explicit quartic in 247 variables" (TeX lines 91-1454)

I read every line of prose, Theorem `v20:247-fixed`, its proof and the size prescription, and checked the finite content from the printed text itself.

(a) Starting system. The text defines q_1..q_216 as the 244-coordinate system of Section `v19:250-maps`, "equivalently" the first 216 rows of the retained 250 table with the last ladder coordinate replaced by A. I parsed the 222 typeset rows of the retained 250 table: rows 1-216, with y_250 replaced by A, equal `unbalanced244-quadratic.json` exactly (the file in the candidate's inputs, which equals the Version 19 package file). Those rows contain no coordinate 245-249, and A occurs in exactly one row. So the starting object is the reviewed Version 19 one, and the second description fixes it exactly, including row signs.

(b) Equivalence.
- Scaling table: 65 listed values, all nonzero; indices 1 and 47 are unlisted, so the input is unscaled. The table equals the certificate's `coord_scales`.
- Row operations: the 58 single-row multipliers and the 15 displayed combination rows, parsed from the TeX, give a matrix T equal to the certificate's `T_rows` in all 216 rows.
- Invertibility by blocks: the (121,175) block is [[2,2],[-1,3]] with determinant 8; rows 179-184 involve only Q_179..Q_184 and the 6x6 block has determinant exactly 1/214450708242592116705963714180667354532074632082, as printed. The only other off-diagonal entries are (58,112), (64,10), (65,11), (102,108), (120,126), (121,216), (138,144), (156,162); each points to a row with no off-diagonal entry, so the order is acyclic; every other diagonal entry is nonzero. I also computed det T by exact elimination on the full 216x216 matrix: nonzero, equal to the certificate's `det_T`.
- T Q(Lambda z) has integer coefficients and every row is primitive, as the text asserts.
- Only row 61 involves A, and it is 22201 z_104 z_116 + z_116 - A z_104, as displayed.

(c) Ladder. 149^5110 - z_245, z_245^2 - z_246, 149 z_246^2 - z_247 have the unique rational solution (149^5110, 149^10220, 149^20441); 149 * ((149^5110)^2)^2 = 149^20441 checked.

(d) Permutation. The two printed lists have 8 and 90 distinct entries avoiding 1, 245, 246, 247; with the remaining 148 indices in increasing order this is a permutation of 1..247 fixing 1, 245, 246, 247.

Rows. Building the rows from the printed scalings, T, ladder and permutation gives exactly the 219 `V20-ROW` records (no sign or scalar freedom), and the 219 typeset rows equal their records.

(e) Theorem. From the rows: all 247 variables occur; 3,385 monomials; degree four; coefficient 1 at x_1^4; content one. The largest absolute coefficient is the constant term only, 149^10220 + 298442980098761875927809873; the ladder row contributes 149^10220 and the other rows 298442980098761875927809873. Its bit length is 73,780, so 2^73779 <= H < 2^73780. (The second largest coefficient has 11,106 digits against 22,210.) The plain text, generated from the prescription printed in the section, is 96,712 bytes with SHA-256 455afb0b7143654119db3a68a85fec2fde566cf7fbdf3f7c84bd5d75b32719b9.

Proof. It consumes exactly: nonnegativity of squares over Q; the unique ladder solution; invertibility of T and Lambda; that both coordinate changes fix the input; and the Version 19 soundness and completeness of the 244 system at A = 149^20441 (Sections `v19:250-soundness`, `v19:250-completeness`, with the substitutions of `v19:250-maps`). That reduction is correct and complete. The 250 is described as a retained intermediate with smaller coefficients and three more variables, which is accurate (2^6483 against 2^73780). Nothing asserts optimality; the number 246 occurs only as a coordinate index.

## Scope 2: the four explanatory edits

1. Secant (Section `v19:195-reduction`). New text: multiply s(h-k) = 1 - D(F+fg+G) by f-g and use s(f-g) = h+k, giving h^2 - k^2 = f - g - D(f^3 - g^3), hence U - V = 0 with U = h^2 - f + D f^3, V = k^2 - g + D g^3. Checked: with F = f^2, G = g^2, (F+fg+G)(f-g) = f^3 - g^3 and (h-k)(h+k) = h^2 - k^2. Correct, and no division by s. The scales are now named kappa, lambda in {1,2,4}.
2. Scalar lower bound (Section `v19:250-soundness`). The display now reads c >= 149^{L_N}, B >= c and h(beta) <= 2^330770 149^{-L_N} c (1 + log c / 3). This is what retained P11 states (TeX line 13482), and it is all the later inequalities use.
3. Deleted coordinates (Section `v19:250-construction`). The text names coordinate 119 as `reciprocal.rhoFifth`, coordinate 120 as the rescaled sixth-power auxiliary of the reflected second detector, and the deleted rows as x_4 x_77 - x_119 = 0 and x_91 x_92 - x_117 x_120 = 0, and says no row outside 24, 25, 37, 38 and the two deleted rows uses them. Checked against the Version 18 214 table (`candidate214-ir.json`): names, both rows and the occurrence list are exactly as stated.
4. Formal logarithm (Lemma `v19:sum-height`). I rederived the invariant differential: with u = sqrt(1+4Dt^4), x = (1+u)/(2t^2), y = -x/t, one gets dx/dt = -(1+u)/(u t^3) and 2y = -(1+u)/t^3, so dx/(2y) = dt/u = (1+4Dt^4)^{-1/2} dt; its integral is the displayed series. Additivity as a formal identity from translation invariance is the standard argument and is valid over a field of characteristic zero; the formal group law of an integral Weierstrass equation has integral coefficients whatever the reduction type, so both series converge on parameters of positive valuation, including above 2. Correct and sufficient.

## Every other difference between the Version 19 and Version 20 sources

The diff has 19 hunks. Besides the new Part and the four edits above:

| Lines (V20) | Change | As intended? |
| --- | --- | --- |
| 42, 44, 60 | Title "Version 20", date November 17, 2026, PDF title | Yes (version bookkeeping; not in CORRECTIONS.md, and need not be) |
| 76-78 | Abstract: 247 variables, 3 385 monomials, below 2^73780, 96 712 bytes | Yes; all four numbers verified |
| 1455, 1459 | Part title "The 195-variable Busy Beaver quartic and the 250-variable intermediate"; section "The retained constructions" | Yes (195 wording; structural) |
| 1491-1493 | "The fixed polynomial has ineffective coefficients ... defining threshold of the underlying parameterized construction" in place of "The family remains ineffective" | Yes (195 wording instruction) |
| 1498-1499 | "The retained intermediate has 250 coordinates"; "Gemini 4 Carbon" | Yes |
| 1536 | "nonzero ratio scales kappa, lambda in {1,2,4}" | Yes (note n1) |
| 1841 | "Gemini 4 Carbon" | Yes |
| 4538 | Heading "... contributions of Version 18" | Yes (edition-relative phrase) |
| 11382 | "This retained section serializes ..." | Yes (edition-relative phrase) |
| 51529-51531 | AI usage statement: "OpenAI Codex agents (6 Astra and 6.1 Sol), Anthropic Claude agents (Opus 5.5) and a Google Gemini agent (Gemini 4 Carbon), with auditing from Fable 5.1 and 5.2"; "the polynomials" | Yes, exactly the approved sentence |
| 51535 | One blank line added | Harmless |

Nothing else changed. Every mathematical or wording change is listed in `research/version20/CORRECTIONS.md`; the items not listed there are the version title, date, abstract, the new Part and the retitling of the retained Part, which are the Version 20 content itself. No "Gemini Carbon", "Astra 6", "Sol 6.1" or "working draft" remains in the front matter, the new Part, the retained Version 19 Part or the AI usage statement. Remaining uses of "family" in the retained Part refer to the genuine parameterized 198/196 families.

## Gaps (exposition only; each closed by the checks above)

1. The invertibility paragraph says the other off-diagonal entries "lie between these blocks in an acyclic order". What is true, and enough, is that each of the eight remaining off-diagonal entries points to a row that has no off-diagonal entry (112, 10, 11, 108, 126, 216, 144, 162). One sentence listing them would make the block-triangular claim checkable by eye.
2. The starting system is cited through three sections. Citing Theorem `v19:250-fixed` (and Lemma `q196:general` for the passage from 247 to 244 coordinates) would name the exact consumed statement.

## Wording notes

- "replacing the ladder coordinate x_{250}": the retained 250 table writes its coordinates y_i, so this should be y_{250}.
- "the unbalanced 244-coordinate system in Section `v19:250-maps`": that section does not use the word "unbalanced" and leaves row signs free; the "equivalently" clause is the precise definition. Consider leading with it.
- "In particular, lambda_1 = lambda_47 = 1": say why index 47 is mentioned (it is the input-square coordinate), or drop it.
- In the retained overview, "The latter two constructions and their arithmetic proofs are retained below" has an unclear antecedent after the rewording (inherited sentence).

## Not checked

- The rendered PDF and the build record (separate scope).
- `research/version20/DEPENDENCIES.md` beyond the entries for the four edits, `RELEASE-NOTES.md`, the manifest, and the changed checker scripts described in CORRECTIONS.md (entries n4, n5).
- The retained Version 19 and Version 18 text outside the diff hunks, which is unchanged from the released Version 19 source.
- Version 18's own proofs of the retained inputs.
- Carbon's package beyond its normalization certificate.
