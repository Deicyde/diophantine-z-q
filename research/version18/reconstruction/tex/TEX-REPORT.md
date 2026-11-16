# Exact 198-variable TeX component

Status: PASS. `q198-rows.tex` is ready for inclusion beneath the editor's heading carrying `\label{q198:rows}`. It has no document class, preamble, package declarations, or duplicate heading label. It requires `amsmath` and `longtable`. The separate `preview.tex` is only a compilation wrapper.

The component contains the complete 198-coordinate dictionary, 77 explicitly defined positive integer coefficient aliases, and all 184 integral quadratic residuals from Conant's frozen unbalanced 198 table. The aliases are literal decimal integers, occasionally expressed as sums of decimal blocks times explicit powers of ten. They do not depend on a coordinate or on A. The mathematical body contains attribution and the source table hash, with no local filesystem paths.

## Convention and labels

- The coordinates are `Y_0,...,Y_197`; `Y_0=x` is the distinguished input. Source JSON coordinate i becomes `Y_(i-1)`.
- There are 197 auxiliary rational coordinates. A is a fixed coefficient, with the designated specialization `A=149^(2N+1)`; it is not a coordinate.
- Source `x104` is `Y103`, and the forced positive parameter `R=x116` is `Y115`, matching `MANUSCRIPT-STATISTICS.md`.
- The dictionary retains all source names, formal identifiers j, and rescaling exponents e. Its convention `xi_j=R^e Y_i` agrees with the frozen compiler and `circuits/inverse198/README.md`.
- The component defines `q198:coordinates` and `q198:row:001` through `q198:row:184` (185 labels total). The editor supplies `q198:rows` outside this component.

## Exact round-trip evidence

`generate_q198_tex.py` reads the frozen quadratic JSON directly. `verify_q198_tex.py` does not import the generator: it parses the visible TeX integer definitions, dictionary lines, and equation right-hand sides. Source comments and printed hashes are excluded from its polynomial parser. Every reconstructed row coefficient equals the frozen JSON coefficient, including its parameter power and coordinate monomial. The checker then expands the parsed 184 squares independently and compares the entire result with the frozen quartic JSON. All 2945 terms agree; the coefficient of `Y_0^4` is 1.

The resulting receipt is `ROUNDTRIP.json`. This checks transcription and finite polynomial equality. It adds no arithmetic, rational-point, or Busy Beaver claim.

## Hashes

| Artifact | SHA-256 |
|---|---|
| TeX component `q198-rows.tex` | `a592e13b8d92fbd1602796a81b93cb035728dbde8d96c1de72dbf8c4e97e7cfc` |
| Frozen unbalanced quadratic JSON | `c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad` |
| Frozen unbalanced quartic JSON | `652b5141aaa0d9f54ef89196ae9e442787335b2fd498e250c2772dc3af98a36c` |

The frozen source directory is `work/v18-198-dependency-inventory-20261114/package/H10-quartic198/circuits/inverse198/`, relative to the repository. The source package remains unchanged.

## Reproduction and preview

From this directory, run the two Python scripts in order using Python 3.14.7 (standard library only), then compile `preview.tex` twice. The completed preview used pdfTeX 3.141592653-2.6-1.40.27, MiKTeX 25.3, with package installation and shell escapes disabled:

```powershell
python generate_q198_tex.py
python verify_q198_tex.py
pdflatex --disable-installer -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape preview.tex
pdflatex --disable-installer -interaction=nonstopmode -halt-on-error -file-line-error -no-shell-escape preview.tex
pdftoppm -r 90 -png preview.pdf page
```

The stable preview has 14 pages. Its final compilation log has no errors, warnings, overfull boxes, or underfull boxes. All 14 rendered pages were visually inspected: the four-page dictionary, all explicit integer aliases, and every equation are readable, with no clipping or overlapping text. The surrounding manuscript may use different margins or equation numbering; the editor should rerun the final manuscript build after inclusion.

No manuscript files were edited and no optimization was performed.
