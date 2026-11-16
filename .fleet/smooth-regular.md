# smooth-regular (fleet note)

**Main result.** The open field `regularSmoothPerfect` (`CurveSplit.RegularSmoothPerfect`, Stacks 00TV ⇐) is **proved
outright, with no new leaf**: `ZInQ.Contrib.SmoothRegular.regularSmoothPerfect` in
`ZInQKernel/Contrib/OneProof/RegularSmoothPerfect.lean`. The proof uses the vendored Jacobian criterion
`Algebra.FormallySmooth.localization_of_isRegularLocalRing`, Mathlib's perfect-field residue step and the open smooth
locus. `#discharges`: "still assumes: []"; axioms standard.

**Scheme forms** (`ZInQKernel/Contrib/OneProof/SmoothRegular/Basic.lean`), for `X` locally of finite type over `K`:
- over a perfect `K`: smooth ⇔ regular ⇔ nonsingular (regular at closed points) ⇔ geometrically regular;
- over any `K`: smooth ⇔ geometrically regular ⇔ `X_{K̄}` regular ⇔ `X_{K̄}` nonsingular (fpqc descent from `K̄`);
- algebraic 00TV ⇒ (`isRegularLocalRing_of_smooth`, any field);
- an AbVar dictionary: `abVarOfNonsingular(After)` and `exists_abVar_iff_nonsingular(After)`.

**AbVar leaves, nonsingular variants** (each proved equivalent to the original):
- `PicZeroAbVarNonsingular` (`ZInQKernel/Contrib/OneProof/PicZeroAbVarNonsingular.lean`): discharges `picZeroAbVar`.
  It is still a composite leaf (Mumford §13 with §4 over K̄, Kleiman descent, SGA 3); now its nonsingularity hypothesis
  is in printed form.
- `WeierstrassAbVarNonsingular` (rated printed; Silverman III.1.4, VI.3.6) and `CMAbVarExistsNonsingular` (rated
  printed up to Riemann's theorem): these two are in `scratch/smooth-regular/T4.lean` against verbatim copies, because
  their originals are only on origin/wip/hcm-g1 and origin/wip/cm-primitive.

**Checks (all compiled).**
- `scratch/smooth-regular/discharges-output.txt` holds the `#discharges` output.
- `scratch/smooth-regular/autofold.json` is the fold spec. Its dry run gives strict 40/8 on 48 → 39/8 on 47 and
  strictest 39/9 → 38/9; the generated module compiles (FoldCheck.lean, standard axioms).
- Report: `docs/research/smooth-regular.md`.

**Remains.**
- Move the Weierstrass/CM variant proofs (one line each) into a Contrib file once their branches are on main.
- Add the locator rows proposed in report §6. All locators are UNVERIFIED (no network).
- A "geometrically reduced" reading of Mumford's group varieties would need reduced ⇒ smooth for group schemes over
  k̄. That is not available in Mathlib 4.35 or the vendored libraries.
