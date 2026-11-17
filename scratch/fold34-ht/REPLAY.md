# Replaying the fold34-ht fold on a later head

The Contrib proof is separate from the fold:

* commit `301197af6` merges origin/wip/hodgetate-from-dr (Contrib `HodgeTatePairing{,Core,Decomp,Weil}.lean`, its
  report and scratch);
* commit `9a7266d8a` adds this task's Contrib modules `HodgeTatePairingWeil0.lean`, `HodgeTatePairingCore0.lean`,
  `HodgeTatePairingCharZero.lean` (they import only Contrib modules, `TailK` and `TailZ24`, never the top of the chain);
* commit `d3f989e44` is the generated fold (TailZ56, Main.lean, kinds.tsv, regenerated docs) plus the checks.

On a head that has further autofolds: bring in the first two commits (merge or cherry-pick), then from the repository
root

    python3 scripts/one_proof/autofold.py scratch/fold34-ht/autofold.json --dry-run   # expect GLUE -1 in both columns
    python3 scripts/one_proof/autofold.py scratch/fold34-ht/autofold.json

and run the checks (`scratch/fold34-ht/checks.sh TAG` does the dump, closure, OpenStatements and DischargesTest;
then `render_open.py`, `--check`, `frontier_crosswalk.py`, `--check`, autoform).

The spec's proof is `hodgeTateDecompAbVar_of_open {n}.hodgeTateDecompExists {t}.mumfordTorsionAlgClosed
{l}.picRepresentableAbVar {l}.kleimanPicZeroProper`. It needs the field `hodgeTateDecompAbVar` in the top research
bundle and those three fields in the top textbook/added bundles. If a later fold has proved one of them, replace
`{t}.mumfordTorsionAlgClosed` / `{l}.picRepresentableAbVar` / `{l}.kleimanPicZeroProper` in the spec by the
contribution's proof term (fully qualified, `_root_.`) and add its module to "imports".
