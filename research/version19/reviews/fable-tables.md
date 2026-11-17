# Fable check of the printed tables and coordinate maps in the V19 draft (250 and 195)

16 November 2026. Draft: `C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\version19-250-draft-20261116\quartic_v19.tex`, SHA-256 `388eb3e876cb3d33…` (confirmed).

Scripts (mine): `v19tables.py` and `v19maps.py` in the session scratch folder
`C:\Users\glaze\AppData\Local\Temp\claude\7fbd96b289b0830c\673e4698-d945-4239-ad78-c5f5e062f088\scratchpad\`.
They parse the typeset `align*` rows of the TeX with my own tokenizer and read JSON only. Astra's `check_printed.py` and `verify250.py`, and all of Jose's and Carbon's programs, were neither imported nor run. The `% V19-ROW` comment lines in the TeX are ignored by the parser (they are used once, as a separate comparison, in item 2).

## Result: no mismatch found

### 1. The 250 table (Section `v19:250-rows`)
- All 222 printed rows parse; none skipped, no parse failure.
- Each equals, as an exact polynomial with the same sign, the corresponding row of Carbon's `explicit250-quadratic.json` (222 of 222).
- All rows are quadratic; coordinates 1..250 all occur; no parameter appears.
- Expanding the sum of the 222 squares from the printed rows: 3362 monomials, degree 4, `y_1^4` coefficient 1, content 1, largest absolute coefficient exactly `149^898 + 1747145497790223592810060471184416344603224790540808983`, attained only at the constant term, and below `2^6483`.
- That expansion equals `coefficients/quartic250-decimal.json` term for term (3362 terms).

### 2. The 195 table (Section `v19:195-rows`)
- All 175 printed rows parse, including the powers of `C` and coefficients written as `149^{2}`.
- Each equals the corresponding row of Jose's `affine_laurent195_v45/quadratic-family.json` at cd474ee (175 of 175, same sign).
- The embedded `% V19-ROW` comments agree with the typeset rows (175 of 175).
- Expansion: 2965 parameter-separated terms on 2956 coordinate monomials, powers of `C` in {0, 1, 2}, 195 coordinates, as the text says.
- At `C = 149^N` for N = 1, 2, 3, 5, 9, 10, 11, 12, 13, 14, 20, 57, 100: 2956 monomials, content 1, `x_1^4` coefficient 1, and height equal to `max(126616122944180358034867798936, 149^(2N+2))` each time. This is a check at sample N; the proof for all N is the coefficient-profile argument in the text, which I did not redo here (my earlier `verify195.py` covered the same formula from the JSON).

### 3. Coordinate maps for the 250 (Section `v19:250-maps`)
- Clone list: 35 entries, new coordinates 213..247, sources distinct, and the sources are exactly the 35 detector-1 coordinates of Jose's 212 table (names containing `detector1` or `det1`); none missed, none extra.
- Exactly 32 rows of the 212 table touch a copied coordinate other than the trace row.
- Jose's 212 table + those 32 rows under the printed clone map + the shift equation `4R^2(t_0 - 2t_1 + t_2) + sum_i z_{i,0} z_{i,1}` (built from the coordinate names) equals Carbon's `family247-intermediate-quadratic.json` row for row (219 rows). The trace row is `8R^2(t_0 - t_1) + sum_i (z_{i,0}^2 + 2 z_{i,1}^2)`.
- Laurent step, using only what is printed (deleted indices 82, 97, 224; the exponent-triple table; `H_0 = 31581660^14`, `K_0 = 82479248 H_0`; the nine listed constants): substituting the guarded units, 9 of the 219 rows vanish identically: the three guards, the three square definitions and the three fourth-power definitions. The six guards and squares are printed literally (rows found in place). Each of the other 210 rows is a nonzero rational constant times a unit monomial times its printed row, in order, and each printed row is primitive. Total 216 printed rows. Unit monomials cancelled: none for 171 rows; `w_j^{-4}` for 10 rows, `w_j^{2}` for 1 row and `w_j^{-2}` for 2 rows, for each of j = 0, 1, 2.
- The parameter `A` occurs in exactly one 247 row (`scalar.forced_prime.definition`, row 63), linearly; the printed row has `y_250` in its place.
- Ladder rows 217..222: `c_0 = 149^449`, then `c_{k+1} = 149^e c_k^2` with cumulative exponents 449, 1277, 2555, 5110, 10220, 20441 = 2·10220 + 1.

### 4. Stated numbers
- Abstract: 250 variables, 3 362 monomials, coefficients below `2^6483`, table of 437 921 bytes; 195 variables, 2 956 monomials. All match the files: `coefficients/quartic250-decimal.json` is 437,921 bytes (SHA-256 `d5373b24…f718c`).
- Theorem `v19:250-fixed` (lines 903-916): 222 rows, 3362 monomials, the height: match.
- Section headers: "222 rows", "175 rows": match.

## Remarks (not errors)
1. The 437,921-byte figure is the size of one JSON file including metadata, coordinate names and formatting. The README says so, but the abstract calls it "its complete decimal coefficient table". A reader may take it as a canonical size. A plain written-out form is about 86 kB. Consider "a complete decimal coefficient table of 437,921 bytes is supplied", or drop the figure.
2. In the maps section the symbol `c_i` is the constant and `c_i'` the third exponent; the text explains it, but a different letter for the exponent would be safer.
3. Two of my own assertions in `v19maps.py` print FAIL: they tested that copied coordinate names contain the literal string `detector1`, which three names (`amplified.det1…`) do not. The corrected comparison (names containing `detector1` or `det1`) gives 35 = 35 with no difference. This is a defect of my test, not of the manuscript.

## Not checked
- The 195 transformation data section (`v19:195-maps`: the matrix `M`, the weight lists `a_i`, `k_j`) against Jose's transformation JSON. My earlier `verify195.py` checked that chain from the JSON, not from this printed section.
- The contact-factor section (`v19:contact-factors`).
- The 250's row names (the `\texttt` labels) against the JSON names.
- The rendered PDF; only the TeX source was parsed.
- Any arithmetic argument (Sections V19.3-V19.8).
