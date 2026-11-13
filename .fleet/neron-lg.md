# neron-lg (fleet report)

**Verdict.** The two Néron glue Props of tau-n1n2, `NeronLocalToGlobal` and
`SemistableLocalToGlobal`, are true and not vacuous. A read-only model review found no problem.
Neither can be proved outright in Lean v4.35: that needs spreading out, gluing of group schemes and
identity components, none of which Mathlib has.

Both are now **reduced in Lean** (proved, compiled, standard axioms only) to:
- one new **leaf**, NL `NeronLocalOnBase` (BLR §1.2 Prop. 4: the Néron property is local on a
  Dedekind base);
- six smaller **glue** statements, each one geometric step:
  - N1-g1 `AbVarSpreadsOut`;
  - N1-g2 `NeronNearPoint`;
  - N1-g3 `NeronGlueAway`;
  - N2-g1' `GoodPlaceAnyField`;
  - N2-g2 `LocalSemistableMono`;
  - N2-g3 `SemistableGlobalOfLocal`.

`n1_n2_of_leaves_and_glue` gives N1 ∧ N2 (the build's `H5Neron` Props) from the leaves N1-loc,
N1-ab, N2-loc, NL and these six glue statements.

**What compiles** (`scratch/neron-lg/NeronLG.lean`, which imports only
`ZInQKernel.HDecomp.Faltings.H5BaseChange`; no sorry, no axiom; 13 `#print axioms`, all
`propext`, `Classical.choice`, `Quot.sound`):
- the assemblies `neronLocalToGlobal_of`, `semistableLocalToGlobal_of`, `goodPlacesAnyField_of`,
  `semistableCommonField`;
- the classification of the DVRs of a number field (`dvrAt_center`: every DVR `O ⊂ K` is `𝓞_{K,v}`);
- `badPlaces_finite`;
- `compositumFinset`;
- `neronModelOver_localize`: Néron models localize, from NL;
- `localNeronModelExists_of_self`: the leaf N1-loc follows from N1-self and NL;
- `neronOverAway_of_abelian`.

§1 and §5 copy tau-n1n2's statements verbatim (script-checked).

**What remains:**
- **Proofs of the six glue statements** (algebraic geometry missing from Mathlib). The closest is
  N2-g1': base change plus uniqueness, then a diagram chase through `Over.pullbackComp`.
- **Locators.** Check NL's locator (UNVERIFIED) and the EGA/SGA locators.
- **Integration.** Add NL to `TextbookLeaves` and the six glue Props to `GluePieces`.

Report: `docs/research/neron-lg.md`. Log: `scratch/neron-lg/log.md`.
