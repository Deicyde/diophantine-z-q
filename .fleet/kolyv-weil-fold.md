# kolyv-weil-fold handoff

**VERIFIED.** The swap builds on fork main `dcc3d7723`. The new pole supplier
takes `hRC hCT hB6 hKPrint`, keeps the Cassels–Tate proof of Lemma 5.4, and
changes only the rank supplier. In the real, temporarily spliced `Main.lean`,
`lake build +ZInQKernel.OneProof.Main` completed (16,551 jobs).
`#print axioms ZInQ.OneProof.frozenTarget` reports `propext`, `Classical.choice`
and `Quot.sound`. Real `#discharges` on the baseline confirms `[hK]` from
exactly the two new Props; it is the sole match removed after the swap
(391 → 390, 35 open hypotheses in both builds).

`Main.lean` was restored. Apply the [checked splice](../scratch/kolyv-weil-fold/main-splice.patch)
on `dcc3d7723`, or port its rank changes to the newer headline while
keeping its H chain. The [report](../docs/research/kolyv-weil-fold.md) links
both checker outputs and the manual autofold spec. Compiled import closure:
eight added modules, five of them already vendored Tau Ceti at `5a01f5fe`;
no vendoring changes. Board files are left for the lead's fold.

**Open ratings.** `hB6` is GLUE in both columns: BCDT condition (6), p. 3,
uses `X₁(N_E)`, and the manuscript's Milne realization at tex L1779–1784 is
needed for `X₀(N_E)`. `hKPrint` is the printed MPI/90-69 Thm. 1 (p. 4 with
the p. 3 hypothesis), GLUE pending the owner's ruling on unrefereed
preprints. On the requested base, H strict stays 5 LEAF / 26 GLUE on 31;
the full strict count stays 6 / 29 on 35, or becomes 7 / 28 if the
preprint is admitted as LEAF.
