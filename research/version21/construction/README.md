# Version 21 finite reproduction

Run `python -B research/version21/construction/check.py` from the repository
root. Every new checker uses the Python standard library. No program from
Brox's package is executed.

- `INPUTS.json` pins nine unchanged data files selected from accepted PR158.
- `inputs/brox229/source/quadratic229-v62.json` is the 207-row parameterized
  source. `inputs/brox229/quadratic.json` is the normalized integer table at
  `C = 149^15`. These are different files with different roles.
- `verify229.py` authenticates every input, verifies the 195 parent, all
  copies, contact changes, both field components, helper isolation,
  scalings and inverse, every quartic coefficient and the literal text.
- `check_printed.py` parses all 207 source rows and 207 normalized rows
  from the actual manuscript, the 229 coordinate and 207 row exponents,
  and the complete coordinate/row copy tables. It rejects unknown syntax
  and missing or reordered entries. Ten corrupted-print controls must fail. It also checks the ten stored field expressions against both aggregate and secant components, all five contact coefficients and all fifteen stored contact substitutions.
- `verify_arithmetic.py` checks the finite factorizations, nonsquares,
  radical constants and rational bounds on all decisive logarithms.
- `verify247_retained.py` strengthens the earlier row comparison to exact
  equality, with ratio one, without editing the released Version 20 checker.
- `check.py` runs all of these and the retained Version 20 entry point.

The plain notation is the single-line ASCII expression specified in
`docs/explicit-record/README.md`, with the input called `x1`, decimal
integer coefficients, literal multiplication and powers, and no final newline.
The exact measurement and SHA-256 are in `../RELEASE-MANIFEST.json`.

The source helper coordinates are checked for all their consumers. The
arithmetic proof, including zero branches and the order of choices, is
in the manuscript and requires mathematical review. A finite PASS does
not supply that review. The first CI registration is pending separately.
