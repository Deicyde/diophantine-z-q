# cm-serre-tate fold (fork PR #132): `cmPotentialGood` from `neronSchemeExtensionDedekind`

Fold note, 2026-11-19. This is model work and no person has reviewed it.

- **What landed.** Fork PR #132 (branch contrib/cm-serre-tate-20261118, owner's re-fold head b03f8781) merged with
  fork main 3078ae6a as c4e2a8c5.
- **What it does.** The research field `cmPotentialGood` (the CM branch's potential good reduction, manuscript
  L596-597) is proved from the existing leaf `neronSchemeExtensionDedekind` by the Serre–Tate route
  (`HDec.CMSerreTate.cmPotentialGood_of_neronSchemeExtensionDedekind`). No new leaf; the kinds row is removed.
- **Fold.** Autofold `TailZ96`: `OpenResearchLeaves70` is `OpenResearchLeaves69` without `cmPotentialGood`, and
  `HDec.HSyn.sixContactMin_of_open89` is the new top. The lakefile gains the library `CMSerreTateSupport`.
- **Count.** 32 open = 28 H (strict 6/22) + 4 before; 31 open = 27 H (strict 6/21, strictest 6/21) + hRC, hCT, hB, hK after.
- **Checks.** Built on the landing chain; `ZInQ.OneProof.frozenTarget` and `sixContactMin_of_open89` depend only on
  propext, Classical.choice and Quot.sound; the discharges reporter shows bundle 70 without `cmPotentialGood`.
