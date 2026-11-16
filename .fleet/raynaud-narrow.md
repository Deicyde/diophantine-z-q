# raynaud-narrow (2026-11-16)

**Verdict.** The Raynaud leaf is not removed, but it is replaced by a narrower LEAF in printed form; the count stays
at 16/21. The live chain reads `raynaudSemistableSHOr` only through `raynaudSemistable_of14`, at number fields, i.e.
in characteristic 0 with algebraically closed residue field. This is confirmed by a closure probe on TailZ45 (268,667
constants). The cp form cannot be proved from the bundles: no field supplies quasi-unipotence or the converse of
SGA 7 IX 3.5.

**New leaf.** `RaynaudNarrow.RaynaudSemistableSHcpOr` is dict-models' `RaynaudSemistableSHOr` restricted to
`[CharZero K]` and `[PerfectField κ(O)]`, keeping the k(s)/geometric disjunction. Rated **printed form**
(a specialization of SGA 7 IX 4.7). Proved around it:

* `cpOr_of_or`: the current leaf implies it, so it is not stronger.
* `raynaudSemistableSHcp_of_cpOr'`: it gives `ReductB.RaynaudSemistableSHcp`, using the proved 04KV ascent.

The reading risk "the print may assume an algebraically closed residue field" is gone. The `m = 3` boundary (R6)
remains.

**What compiles** (lake build, standard axioms):

* `ZInQKernel/Contrib/OneProof/RaynaudSemistableSHcpOr.lean`.
* `ZInQKernel/Contrib/OneProof/RaynaudNarrowChain.lean`: generated, namespace `HDec.HSyn.RNarrow`. It re-versions
  `sixContactMin_of_open17..38` and the bundles 14..28 so that they carry `raynaudSemistableSHcp`. The closure of its
  top contains neither `RaynaudSemistableSH` nor `SHOr`.
* The proposed hand-step module `scratch/raynaud-narrow/TailZ46.lean`, together with the dry run of
  `scratch/raynaud-narrow/autofold.json` (16/21 -> 16/21), compiles.
* Main's `frozenTarget` restated over the fold's top compiles (`EndToEnd.lean`).

`#discharges` output is recorded. Its 231 extra hits are projections of the copied bundles, not discharges.

**What remains for the integrator.** The fold has two steps (report section 5):

1. Run `gen_fold.py --tree .`: it writes TailZ46, switches Main and renames the kinds row. Remove the claims row
   `raynaudSemistableSHOr` by hand.
2. Run `autofold.py scratch/raynaud-narrow/autofold.json`.

Then run the standard full-build, hash and `render_open` checks; I did not run them. The locators row proposal is in
`scratch/raynaud-narrow/locators-row-proposed.md`. Report: `docs/research/raynaud-narrow.md`.
