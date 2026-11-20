import ZInQKernel.Contrib.OneProof.H.TailQ
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Main

/-!
# Milne isogeny quasi-inverse — exact contribution entry point

The theorem exported by the imported source is
`ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof :
_root_.AvSplit.MilneIsogenyQuasiInverse`.

It uses the original all-fields `PkgI3.AbVar`/`Hom` objects and both scheme-morphism
multiplication equations. No new premise or copy of the target is introduced here.
Helpers and attributed source ports are in the adjacent `MilneQuasiInverse/` directory.
See its NOTICE.md for immutable sources, adaptations and the compile record.

Compiled by milne-compile (2026-11-16, Lean 4.35.0 / Mathlib v4.35.0): `#discharges` reports
`DISCHARGES [OpenAddedLeaves17.milneIsogenyQuasiInverse]`, still assumes `[]`, axioms
`[propext, Classical.choice, Quot.sound]` (scratch/milne-compile/discharges-output.txt).
This does not complete Z-in-Q.
-/
