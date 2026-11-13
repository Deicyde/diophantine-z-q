# tau-n1n2 (fleet note)

**Verdict.** The Néron leaves N1 `NeronModelExists` (BLR 1.4/3) and N2
`SemistableNeronIdentityComponent` (SGA 7 IX 3.6 + 3.3) are true and not vacuous. In particular,
N2 cannot be satisfied trivially: a `GrpObj` over `Spec 𝓞` has a unit section, so N2 forces the
identity components of the special fibres to match. Neither can be proved in Lean today, in any
case, even for elliptic curves. Mathlib v4.35 has no Néron models, no abelian schemes and no
nonzero `AbVar`. The FLT project's Néron files are not on this host; by their names they cover
uniqueness and endomorphism extension, which the project already proves. Instead, both leaves are
**reduced in Lean** to three leaves closer to the literal published statements, plus two glue
statements:

- N1-loc `LocalNeronModelExists` (BLR 1.4/3 over a DVR `O ⊂ L`);
- N1-ab `AbelianSchemeIsNeron` (BLR 1.2/8);
- N2-loc `LocalSemistableIdentityComponent` (SGA 7 IX 3.6 + 3.3, local and canonical);
- glue `NeronLocalToGlobal` and `SemistableLocalToGlobal` (spreading out, gluing, compositum).

The reduction is `n1_n2_of_leaves`.

**Compiles** (`scratch/tau-n1n2/N1N2.lean`, imports `ZInQKernel.HDecomp.Faltings.H5BaseChange`;
0 errors; all 17 `#print axioms` list only propext, Classical.choice, Quot.sound):
- verbatim copies of N1 and N2, with `Iff.rfl` to the build;
- `NeronModelOver` (a Néron model over any base);
- `neronModelExistsSelf_iff`: N1 is equivalent to BLR 1.4/3 literally;
- `neronModelExists_of_local`, `semistableNeronIdentityComponent_of_local`, `n1_n2_of_leaves`;
- `isMonHom_of_reflect` / `isMonHom_of_neron`, and `semistableNeronIdentityComponent_of_some`
  (one Néron model per `L'` suffices);
- `NeronModelOver.uniqueIso`;
- sanity checks for the zero AV: `localNeronModelExists_zero`, `localSemistableAt_zero`,
  `bothSides_over`.

A read-only model review of all new definitions found no problem; its three minor docstring
fixes are applied.

**Remains.**
- The two glue Props are stated and argued, not proved: they need EGA IV §8 spreading out, gluing,
  identity components and locality of the Néron property, none of which is in Mathlib.
- The three leaves stay literature hypotheses.
- Integration suggestion: replace `TextbookLeaves.t41` by N1-loc and N1-ab, and add the glue Props
  to `GluePieces`; `neronModelExists_of_local` then supplies `t41`.
- N2 is not consumed by `sixContactMin_of_leaves` today.
- Report: `docs/research/tau-n1n2.md`; log: `scratch/tau-n1n2/log.md`.
