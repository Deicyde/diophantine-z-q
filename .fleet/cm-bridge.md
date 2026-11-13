# cm-bridge (2026-11-13)

**Result.** cm-numeric's class-7 file rewired to ring class field theory and extended; two final
theorems compile (`scratch/cm-bridge/Bridge.lean`, standard axioms only, 0 errors):

* `tyzThm35ReadingA_of_ringClassD_sigmaShiftsF0_lemma318_thm35First_lemma321Five_thm36Seven`
* `tyzThm35ReadingA_of_ringClassD_sigmaFixesZn_lemma318_thm35First_lemma321Five_shimura`

Out of cm-numeric's 13 hypotheses, these are gone: `IInH4`, `HprimeNormal`, `IInHprime` (ring-class);
`CMFieldOfDefinitionTYZ`, `CMFieldOfDefinition7` (both now come from `CM.CMFieldOfDefinition ringClassFieldD`);
`TYZSigmaFixesZn` (from `TYZSigmaShiftsF0`); **`GenusFieldLeLni` proved** (Bauer + genus characters);
**`Lemma321Seven` (TYZ Lemma 3.21(4)) derived from TYZ Thm 3.6(3)**, with all glue proved (genus field =
K(√p*), Artin symbols act on √p* by genus characters, N𝔭₂ = 2); and **TYZ Thm 3.6(3) derived from textbook CM**:
`tyzThm36Seven_of : ShimuraReciprocityPic (tyz-cm, verbatim copy) → EtaModelFricke (x0-32) → CMAlgebraic → TYZThm36Seven`.

**Remaining CM-side leaves:** `CM.CMFieldOfDefinition ringClassFieldD`, `TYZSigmaShiftsF0` or `TYZSigmaFixesZn`
(tyz-cm derives both of these from ShimuraReciprocityPic (+ Fricke) on its branch), `Lemma318Literal` (TYZ
torsion lemma), `Thm35First`, `Lemma321Five` (TYZ 3.21(1)), plus `ShimuraReciprocityPic`, `EtaModelFricke`,
`CMAlgebraic` in the second theorem; and the three 𝓛-leaves.

**Review finding (fixed).** An independent statement review found that the first `TYZThm36Seven` used an
unoriented 𝔭₂ (the abstract √−n), so it depended on the arbitrary `embed n` and was false for one orientation.
Now `p2Ideal` is oriented through ιC (`PosOrient`). Numerics: `thm36_7.out` (12/12; wrong sign fails 7/12),
`plan36.out` (8/8).

**Not done:** Lemma321Five (needs a β₁-lift existence glue, genus theory for H'_n, and a pinned TYZ 3.6(1)),
Lemma318Literal (needs reduction-mod-p / division-field ramification). Report: `docs/research/cm-bridge.md`.
