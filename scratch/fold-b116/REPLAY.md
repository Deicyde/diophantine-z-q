# fold-b116: replaying the five items on a later head

Each item is its own commit; merges are separate commits (d2a6b 44fd0ac0, r16-shimura73 42e13ffc + 0478c133); the
logp-transc files are a plain `git checkout 707e4799 -- <files>`. From the repository root of a head that has
ss-faltings folded. After each step build `ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` plus the touched
modules, then `bash scratch/fold-b116/run_checks.sh K PREV` (dumps in /tmp/fb116; edit the `checked` list and the two
bundle names of the field check in `scratch/fold-b116/FoldCheck.lean` if the bundle numbers moved), then commit.

1. inbox 83 (ss-faltings amendment; text only):

       python3 scratch/fold-b116/item1_ssf_amend.py [TailZ files carrying the faltingsSemistableHeightBC field doc]

   Default TailZ84. On a head with later bundles pass every TailZ that the fold rebuilds anyway (the newest one);
   the script stops if a text it edits is missing.
2. d2a6b (bypass; regenerated on the post-ss-faltings chain):

       lake build ZInQKernel.Contrib.OneProof.D2A6Wrap ZInQKernel.Contrib.OneProof.A6Z30
       lake env lean scratch/fold-b116/gen-d2a6b/TaintD.lean  > scratch/fold-b116/gen-d2a6b/taintD-out.txt
       lake env lean scratch/fold-b116/gen-d2a6b/TaintD2.lean > scratch/fold-b116/gen-d2a6b/taintD2-out.txt
       python3 scratch/fold-b116/fold_d2a6b.py

   The chain is rooted at ss-faltings' `sixContactMin_of_open73_sf` (SSFChain), so it does not depend on the TailZ
   bundles above TailZ80; `fold_d2a6b.py` reads the current Main top (any `OpenResearchLeaves<n>` /
   `sixContactMin_of_open<n>`), writes the next free TailZ and `OneProof/H/D2A6Chain.lean`, and replaces the kinds
   row. gen_bypass.py stops if a field of the current top bundle is not read by the conversion to
   `OpenResearchLeaves54SFU` (a later autofold that added a field: add its conversion line, as for
   `carayolThmAIrr`), or if the textbook/added bundles are not `OpenTextbookLeaves18` / `OpenAddedLeaves27`. If
   SSFChain itself was regenerated, rerun the taints first.
3. r16-thm1b (autofold):

       lake build ZInQKernel.Contrib.OneProof.R16Thm1b
       python3 scripts/one_proof/autofold.py scratch/fold-b116/autofold-r16thm1b.json

   (the spec is r16-thm1b's, unchanged). Keep item 2 before item 3: gen_bypass.py maps the top bundle field by
   field onto `OpenResearchLeaves54SFU`, which has heckeJ1DS and afShimura; after r16-thm1b's autofold it would stop
   ("fields not read by the conversion": bShStandardModel, shimuraThm1Af) unless given conversion lines
   `heckeJ1DS := R16Thm1.heckeJ1DS_of_bSh n.bShStandardModel`, `afShimura := R16Thm1b.afShimura_of_thm1Af
   n.shimuraThm1Af`. Autofold itself does not care about the order.
4. logp-transc: `git checkout 707e4799 -- ZInQKernel/Contrib/OneProof/LogPTranscendence.lean
   ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean docs/research/logp-transc.md scratch/logp-transc
   .fleet/logp-transc.md`; `python3 scratch/fold-b116/rows_items45.py logp` (flag narrowing). Append the two imports
   to AllContrib only on a head with wip/contrib-clashes.
5. docs: `python3 scratch/fold-b116/rows_items45.py docs` (inbox 78 items 1-2, inbox 80); the dsThm966Printed field
   docstring locator (pp. 513-514) is edited in the newest TailZ only (TailZ86 here).

Then `python3 scripts/one_proof/render_open.py` and `--check`.
