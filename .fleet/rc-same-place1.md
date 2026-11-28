# rc-same-place1 (hand-off)

**None yet.** This run completes no `SamePlaceData` field and discharges no hypothesis of
`oddStagedOfSamePlace`.

No error verdict.

Main result: items 1–7 are built under ZInQKernel/Contrib/OneProof/RC/SamePlace/. Every module builds with no
`sorry`. The axioms are only propext, Classical.choice and Quot.sound. The INTERFACE block is unchanged and
composes with this run's pieces.

Pieces supplied, by field:

* **X.Point**: `ssPoint K ell N`, the pair classes with `E[ell](K) = 0` and `X.ss = univ`. The reason:
  frobenius_sq fails on ordinary points, and J reaches only the supersingular locus.
* **point**: `pointForm.symm ∘ Y0LevelPoints.symm`. It is injective.
* **point_W**: supplied here are `pointForm`, the φ lemma `pointForm_comp_map`, `point` and `sigmaQ`/`sigmaQSS`.
  Still open: generic7's `atkinLevelAlg`, `Wint` lemma and `PointW`; generic8's `atkinLevel_moduli_special`; and
  SP2's X.W comparison for every separable seam. The point_W assembly proves `PointW` and builds the final sp.
* **point_frob**: supplied here is the pointForm half, `pointForm_residueFrob` and `frobeniusAlgHom_eq_frobenius`.
  The Y0LevelPoints half is SP2's.
* **X.frobenius**: `frobTwistSS`, the moduli Frobenius twist. It preserves supersingularity.
* **X.W**: `sigmaQSS`, the moduli σ_Q through a chosen separable seam. It preserves supersingularity.
* **frobenius_sq**: `frobenius_involutive`, derived from O.frobenius and `uniformizer_involutive` (`Π² = −ell`).
  It is ELLIOT through O, and a future discharge of O must not assume it.

X is not constructed. SP2 assembles it, and that needs X.T.

Compiles:

| Module | Items |
| --- | --- |
| Supersingular | 2 |
| PointForm | 3, 4 |
| FrobeniusTwist | 5 |
| AtkinLehner | 6 |
| FrobeniusSquare | 7 |

Item 1 is the doc fixes (commit 20ec445fc).

Remains:

* SP2:
  * X assembly (needs X.T);
  * X.T and HeckePacket;
  * the hCM-class -> ssPoint bridge;
  * the X.W comparison for every separable seam;
  * point_frob;
  * the SamePlaceData assembly, and the CMDiagram and HeckePacket agreements with PointW as a hypothesis.
* The point_W assembly: PointW and the final sp.
* Unassigned: a direct moduli proof of frobenius_sq (tex 8469–8473; UNVERIFIED).

Known issues for the integrator: the stale owner wording in files this run may not edit, and the accepted
duplicates with generic7. Both are listed in docs/research/rc-same-place1.md.

No leaf is proposed. No INTERFACE change is proposed.

Report: docs/research/rc-same-place1.md. Log: scratch/rc-same-place1/log.md.

Final SHA before this file: 8f2a435ae. This file is the last commit on wip/rc-same-place1.
