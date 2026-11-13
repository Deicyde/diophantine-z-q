# hdec-adopt5a (fleet note)

**Result.** All five developments are adopted into the built project, and nothing was dropped:
c9-rhof, e1-sub, x1-belyi (`ZInQKernel/HDecomp/ModCurves/{C9,E1Sub,X1Belyi}.lean`), hodge-lattice
and h5-neron (`Faltings/{HodgeLattice,H5Neron}.lean`). In addition, **h5-neron's glue H4b
`GroupModelBaseChangeExists` is now proved** (`Faltings/H5BaseChange.lean`,
`ZInQ.H5Neron.groupModelBaseChangeExists`). The draft's kernel timeout came from the iso's
declared types (`genericFibre`, `AbVar.baseChange`), not from instances. It is fixed by building
the iso at the composite's type and computing its `hom` by an explicit `Iso.trans_hom` chain.

**Compiles (VERIFIED, 02:01 PST).** `lake build ZInQKernel` exits 0 (9997 jobs).
`lake env lean scripts/print_axioms.lean` exits 0: 471 entries, 72 of them new, each exactly
`[propext, Classical.choice, Quot.sound]`. The five adopted modules are whitespace-identical to
their drafts (`same.py`: ALL SAME) and keep the drafts' imports. Leaves stay `def … : Prop`.
There is no `sorry` or `axiom`, and no line is over 100 characters. No draft held a verbatim copy
of kernel code. The only copies were part F's two definitions, now imported from `H5Neron`.

**Docstring fixes.** `VSurjOfSurjective` is now described as proved without Poincaré reducibility.
`Ej` now gives Mathlib's current model. `R03_LinYang` cites Lemma P instead of "SPECULATIVE".

**Notes for integration.**
- h5-neron is not in this base. Its files were read from `origin/wip/h5-neron` (b7c1dc21) and
  copied into `scratch/hdec-adopt5a/src/`; the branch was not merged.
- `HDecomp.lean`: the six imports are appended after the last import line, because imports cannot
  follow the docstring.
- C9 keeps its own copies of `PkgI4.EigenformRepExists`, `EigenformTwist`, `NewformOfEigenform`
  and `GaloisRep.AttachedUpToTwist`. These names will clash if `h-decomposition/Leaves.lean` or
  pkg-I4 is ever adopted.

**Remains.** The new leaves and glue Props stay hypotheses: x1-belyi's T1, T2, M1-M3;
hodge-lattice's `TangentDimAtOrigin` and `DimBaseChange`; h5-neron's N1 and N2, with the glue
`ModelHeightBaseChange`, `OpenSubgroupHeight` and `ProductModelHeight`; C9's T18, T19, R14, T24
and T25. `h-decomposition.md` and `Leaves.lean` still list the newly proved glue as open.
Report: `docs/research/hdec-adopt5a.md`.
