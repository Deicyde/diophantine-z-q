# neron-lg (fleet report)

**Verdict.** tau-n1n2's two Néron glue Props, `NeronLocalToGlobal` and `SemistableLocalToGlobal`,
are true and not vacuous. A model review found no problem. Neither can be proved outright in
Lean today: that needs spreading out, gluing of group schemes and identity components, none of
which Mathlib v4.35 has.

**Main result (Lean, proved, compiled).** Both are reduced to:
- one new **leaf**, NL `NeronLocalOnBase` (BLR §1.2 Prop. 4: the Néron property is local on a
  Dedekind base; locator UNVERIFIED);
- five smaller **glue** statements:
  - N1-g1 `AbVarSpreadsOut` (spreading out);
  - N1-g2 `NeronNearBadPoint` (a local Néron model spreads out at a bad prime);
  - N1-g3 `NeronGlueAway` (Zariski gluing);
  - N2-g2 `LocalSemistableMono`;
  - N2-g3 `SemistableGlobalOfLocal`.

A sixth glue piece, N2-g1' `GoodPlaceAnyField`, is **proved** from N1-ab by a full diagram chase
(`goodPlaceAnyField`).

`h5neron_n1_n2_of_leaves_and_glue` gives the build's N1 ∧ N2 (`ZInQ.H5Neron`) from the leaves
N1-loc, N1-ab, N2-loc and NL plus these five glue statements. Alternatively, with the leaf stated
as N2-loc⁺ (persistence under extensions, same SGA 7 IX sources), N2-g2 disappears and four glue
statements remain (`…_mono`).

**What compiles.** `scratch/neron-lg/NeronLG.lean` (about 1450 lines) imports only
`ZInQKernel.HDecomp.Faltings.H5BaseChange`. It has no sorry and no axiom, and its 22
`#print axioms` are all standard. It contains:
- every DVR of a number field is `𝓞_{K,v}` (`dvrAt_center`), and only finitely many miss `1/f`;
- composita of finitely many fields;
- localization of Néron models from NL;
- N1-loc follows from N1-self and NL;
- reusable `Over.pullback` pasting lemmas (`pbCompInv_fst`, `genSq`, `bcA_proj`);
- verbatim copies of tau-n1n2's statements (script-checked).

**What remains:**
- **Glue proofs.** N1-g1, N1-g2, N1-g3, N2-g2 and N2-g3 are not proved. N2-g2 is the next
  candidate: intersections of open subgroups plus a §4-style chase. The others need Mathlib
  descent, gluing and identity components.
- **Locators.** Check NL's locator and the EGA/SGA locators.
- **Integration.** Add NL to `TextbookLeaves` and the glue Props to `GluePieces`.

Report: `docs/research/neron-lg.md`. Log: `scratch/neron-lg/log.md`.
