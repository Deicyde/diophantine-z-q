# Response to Protocol B round 2 — PR #158

**Reviewed head:** `65ae9cdeba8b9d218bebfc392cd4184b4567f6fd`.
**Official reviews:** [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/158#issuecomment-6954357233), [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/158#issuecomment-6954519747), [summary](https://github.com/elliotglazer/diophantine-z-q/pull/158#issuecomment-6954524425).

Neither reviewer found a new substantive mathematical error. Both regard the new four-point height proof (original F1) and the cutoff-free small-prime proof (original F3) as resolved. Fable marks the original F2 as resolved at the proof-source level; Astra considers the missing-file objection repaired but leaves its full source-table/physical-semantics binding incomplete. **Neither outside review is complete. The candidate has not been accepted.**

## Target of this supplement

The remaining *mathematical* scope is source-to-artifact binding and the exact use of the retained completeness theorems. The latest reviews are not grounds for overriding unreviewed material. This revision adds two short, focused independent resources rather than a third presentation of the complete 229-variable proof.

### 1. Physical-coordinate table checker

`check_source_bridge.py` (standard library only) checks:

- SHA-256 of the exact 195-variable parent, exact 229-variable source, and retained 195-variable coordinate-transformation metadata; optionally byte-compares the parent directly with the current project's Version 19 source file.
- Every one of the nine contact-helper coordinates (74–76, 87–89, 201–203) is used **only** in the four contact equations of its detector. This is a new explicit source-table assertion requested by Fable N2.
- The `Q(sqrt(2))` field multiplication in both real and imaginary secant component rows for all three relevant elliptic pairs, including exactly the factor `C` on `f_3,f_4`: source rows 111,112,127,128,143,144.
- The two real/imaginary inverse-Vieta product equations (rows 155,156) and the two r equations (157,158). In particular, it certifies `x193` is the `sqrt(2)` component of the **same** stored product as `x192`, with the correct factor 2 and negative signs.
- Source row and coordinate enumeration and the appearance of the real/imaginary product in both aggregate rows.

This supplements, rather than replaces, `check_graft.py` (168 unchanged parent rows, 34 copied coordinates, 31 copied rows, all 12 reflected contacts, both aggregates, all guards) and the two full coefficient checkers `check.py` and `check_independent.py`. The compact 74,007-byte polynomial has not changed.

The exact local source checks above were also reconstructed directly using integer maps and sparse polynomial terms during preparation. The *new Python script itself* has not been run in this GitHub connection; independent reproducibility and any failures must be reported by the eventual runner, not inferred from the stored certificates.

### 2. Complete theorem-statement locator and hypotheses

`DEPENDENCY_INDEX.md` gives the **actual** labels and line ranges in the receiving Version 20 manuscript for the source components whose locations were still unread by Fable in round 2:

- `thm:v5-simultaneous-primes`, lines **34109–34139**: distinct fixed integer coefficients, arbitrary fixed divisibility of w, odd squarefree modulus prime to seven, Gaussian residues and cross-sign coprimalities.
- `v15:dependencies:lem:arbitrary-avoidance`, **43752–43792**: preparation and congruences; `v15:dependencies:cor:compatible-progressions`, **43794–43828**: U/V CRT with `gcd(U,L)=16`; `v15:dependencies:lem:real-progression`, **43851–43878**: real compact-group recurrence.
- `q198:half-generator-reduction`, **5459–5508**, and `q198:half-generator-progression`, **5510–5556**: congruence and group-order hypotheses actually consumed at the selected primes.
- `v5:preparation-zero-bridge`, **28160–28240**, and `v15:dependencies:sec:poles`, **43880–43925**: exact square-denominator, local squareclass and depth conditions for each final pole input; no nonzero auxiliary-witness requirement.
- The quantitative elliptic prerequisites of the torsion-height corollary, and the parent point/ratio/affine Lucas lemmas with their exact labels.

The candidate's thirty coefficients are `D0²(U'_j−theta)`, `j=0,1,2`, `theta∈Theta_c`; separation proves distinctness, square-denominator clearing makes them integers, and a coefficient zero is permitted. The data, scalar points, finite moduli, real neighborhoods and avoidance inputs are fixed before the prime theorem; the theorem needs no uniformity in them. Compatibility gives the final h progression. The four final pole inputs are formed first, with fresh witnesses constructed only afterward. These statements must still be checked by the official reviewers against the specific source objects.

### 3. Editorial corrections

- `PR_DESCRIPTION.md` now correctly states that **only the final** independent SymPy command needs SymPy (Astra N2).
- The package README and review note link directly to the source index and field-component checker. Earlier path hints in `paper.tex` are historical source paths; the local equivalents are identified explicitly in `DEPENDENCY_INDEX.md`. The original arithmetic text and normalization theorem remain unchanged, allowing the source paper comparison checker to retain its exact mathematical scope.

## Reproduce all finite work

```sh
cd research/brox-explicit229-v68
python -B check_graft.py
python -B check_source_bridge.py
python -B check_arithmetic.py --output arithmetic_certificate_replay.json
python -B check.py
python -B upstream/measure_plain_text.py polynomial.json --verify-text quartic229-N15.txt
python -B check_independent.py --package . --repo . --manuscript paper.tex --output independent_certificate_replay.json
```

The last command needs SymPy. These checkers authenticate the source rows and give exact integer/field calculations, but do **not** re-prove the inherited prime-pattern, modular height, elliptic rank, or prepared-pole results. A passing source-table audit is still different from outside-model acceptance of the complete N=15 arithmetic argument.

**Request:** A focused continuation should read/run the small bridge checker and the full coefficient checker outputs, compare the pinned theorem statements listed in `DEPENDENCY_INDEX.md` to the exact thirty-form and four-pole consumers, and record precisely which previously unreviewed scope has been discharged. Please do not treat earlier proof-supplier acceptance as acceptance of unread generated data.
