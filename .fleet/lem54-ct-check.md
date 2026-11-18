# Lemma 5.4 pairing landing check

**Verified:** The dry run replaces only `h54 : PoleS12.Lemma54` with
`hCT : PoleS12.CasselsTatePairingCurves`. `FrozenCT.lean` and `NonVacuity.lean` compile;
the axiom checks use only `propext`, `Classical.choice` and `Quot.sound`. The stock
`#discharges` run finds the all-curves bridge to the old `h54` with a Mordell–Weil
premise; the dry run uses the curve-family consumer with Mordell–Weil already proved.

The recorded Poonen–Stoll Introduction quote gives the full elliptic-curve pairing
with precisely the required radical and alternation. Milne I.6.13(a) corroborates the
primary kernels. The manuscript cites Poonen–Stoll at L1081 for this pairing. The
printed statement specializes to every admissible `E_ℓ`; Lean checks this implication,
an admissible example `ℓ = 11`, and compatibility with the retained assumptions relative
to the print.

The manuscript leaves the last corank inference implicit. Lean supplies it by
finite-level Kummer counts; no false inference was found in the reviewed lines.
Milne's recorded correction to blanket alternation for general abelian varieties
does not affect elliptic curves. An existing square-property docstring names L1077
for the citation; the correct line is L1081.

[Report](../docs/research/lem54-ct-check.md) ·
[Dry-run output](../scratch/lem54-ct-check/FrozenCT-output.txt). The report proposes
the exact docstring locators and a `published, LEAF/LEAF` row, provenance (b), for
the reviewer's decision. The lead retains the fold after #90. No production file
or registry was changed.
