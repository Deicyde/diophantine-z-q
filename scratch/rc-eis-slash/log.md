# rc-eis-slash results

- Base: `a014128059970016c543b1641d6b6584bdef164a`
- Mathlib: principal-level Eisenstein modular forms at weight at least three; weight-two Lipschitz identity and level-one `E2` with a slash correction.
- Lattice regularization: difference of translates of the weight-two kernel is absolutely summable by a cubic majorant; integral slash acts on both offsets.
- Cusp estimate: Lipschitz Fourier expansion of a nonzero row, bounded by a summable geometric majorant; the zero row is constant.
- Cusp transport: finite weighted sums of lattice differences slash by permuting residue classes and remain bounded at infinity.
- `Lattice.lean`: PASS, 11 theorem audits, only allowed axioms.
- `Bounds.lean`: PASS, 13 theorem audits, only allowed axioms.
- `Residues.lean`: PASS, 8 theorem audits, only allowed axioms.
- Inherited issue (EisForm report, tex 9660–9668): coefficientwise integrality of good Hecke images does not imply preservation of the diamond-only span.
- `Characters.lean`: PASS, 6 theorem audits, only allowed axioms. Pullback at the lower-right unit gives the existing product nebentypus in both orders.
- `Mean.lean`: PASS, 4 theorem audits, only allowed axioms. A nontrivial factor makes the sum of the residue weights zero.
- `Reduction.lean`: PASS, 5 theorem audits, only allowed axioms. One Fourier identification supplies both checks and the exact `BaseForm`.
- Mathlib documentation issues: sign of the solved `G2_S_transform` display; extra separate constant in the display for `G2_eq_tsum_G2Term`. Neither display is used.
- `Regroup.lean`: PASS, 6 theorem audits, only allowed axioms. The original order of the two integer sums is preserved during finite residue regrouping.
- `Fourier.lean`: PASS, 12 theorem audits, only allowed axioms. The common constant is the zero row divided by the nonzero Gauss normalization. Primitivity and even product parity yield `MissingModularity` and `Nonempty (BaseForm E c)`.
- Final verification: all eight files compiled individually with `lake env lean -j1`; 65/65 audits list only permitted axioms. No warnings or errors on the final checks.
