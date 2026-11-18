# Verification log

1. **VERIFIED:** The five new pairing modules, `ZInQKernel.OneProof.Main`, and
   `ZInQKernel.OneProof.Discharges` compiled serially using the copied artifacts from the parent
   of the pairing modules. The retained Lean sources and dependency lock match that parent.
   Only the inherited linter warnings in `SelmerCorankFam` and `Lemma54FromCasselsTate` appeared
   on the pairing route.
2. **VERIFIED:** `lake env lean scratch/lem54-ct-check/FrozenCT.lean` exited 0. Both printed signatures
   have the same target, bundles and retained hypotheses. Only `h54 : PoleS12.Lemma54` is replaced
   by `hCT : PoleS12.CasselsTatePairingCurves`. The dry run's axioms are `propext`,
   `Classical.choice`, and `Quot.sound`.
3. **VERIFIED:** `#discharges` reported 33 open hypotheses, 12,093 theorems checked and 20 matches.
   Its baseline is the original headline. Its `h54` pairing match is the all-curves bridge with
   Mordell–Weil as a premise. The dry run instead checks the consumer on the specific family,
   which has no open Mordell–Weil premise. Full output: `FrozenCT-output.txt` in this directory.
