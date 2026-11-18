# Carayol's leaf from Darmon–Diamond–Taylor Theorem 3.1 with DDT's definition of newform

The open hypothesis `OpenResearchLeaves65.carayolThmAFrob` (`CarayolRefold.CarayolThmAFrob`) is already proved from
the earlier leaf `CarayolDDT.CarayolDDT31` (Darmon–Diamond–Taylor, *Fermat's Last Theorem* (1997), Theorem 3.1
(a)–(d), weight 2) by `CarayolRefold.frob_of_DDT31`. `CarayolDDT31` quantifies over Tau Ceti's `Newform N 2`, a
normalized cusp form in the new subspace that is an eigenvector of the Hecke operators of index prime to the level.
DDT state Theorem 3.1 for newforms in their sense (Definition 1.21: normalized eigenforms for all Hecke operators in
the new subspace), so matching the two needed DDT's Theorem 1.22. An independent reading (AI-READ, 2026-11-18) rated
`CarayolDDT31` a consequence of the print for that reason only.

The promotion is proved in the vendored Tau Ceti library (`HeckeRing.GL2.Newform.toEigenform`: a newform is an
eigenvector of every `T_n`). `ZInQKernel/Contrib/OneProof/CarayolDDT31Full.lean` adds

* `CarayolDDT.IsDDTNewform F ψ`: `F` underlies a full Tau Ceti `Eigenform` with nebentypus `ψ`, lies in the new
  subspace and has `a₁ = 1` (DDT Definition 1.21);
* `CarayolDDT.CarayolDDT31Full`: the statement of `CarayolDDT31` with `f : Newform N 2` replaced by a form `F` with
  character `ψ` satisfying `IsDDTNewform F ψ` (every other clause unchanged);

and proves

* `carayolDDT31_of_full : CarayolDDT31Full → CarayolDDT31` (through `Newform.toEigenform`),
* `carayolThmAFrob_of_DDT31Full : CarayolDDT31Full → CarayolRefold.CarayolThmAFrob`,
* `carayolDDT31Full_iff : CarayolDDT31Full ↔ CarayolDDT31` (the two leaves are equivalent), and
  `isDDTNewform_iff_DS` (comparison with the project's `IsNormalizedEigenformDS`).

`CarayolDDT31Full` is stronger than the current open row `carayolThmAFrob` (which follows from it), so replacing the
row by it trades a weaker packaged consequence for the printed theorem. That is a choice for the lead.

## Checks

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.CarayolDDT31Full`: built (16545 jobs).
* `#print axioms CarayolDDT.carayolThmAFrob_of_DDT31Full`: `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (35 open hypotheses, 15017 theorems checked):

```
DISCHARGES [OpenResearchLeaves65.carayolThmAFrob] by CarayolDDT.carayolThmAFrob_of_DDT31Full
  still assumes: [CarayolDDT.CarayolDDT31Full]
  axioms: [propext, Classical.choice, Quot.sound]
```
