# frontier (2026-11-13) — DRAFT, final version follows

**Main result.** `docs/research/frontier.md` lists every open Prop on the path to `ZInQ.FrozenTarget`:
79 = 19 LEAF + 60 GLUE (GZ 2, TYZ 10, H 67), assuming today's compiled branch results are folded in.
GZ and TYZ are compiled end to end: `ZInQ.Frontier.frozenTarget_of_open` (scratch/frontier/TYZChain.lean)
derives `ZInQ.FrozenTarget` from `ZInQ.SixContactMin` and exactly the 12 GZ/TYZ Props, standard axioms.
H: the newest compiled assembly (cpts-transport `HSyn.sixContactMin_of_leaves5`, 103 bundle fields) plus 55
per-branch edges, each checked textually by scratch/frontier/chain.py (signatures, def texts, report = open set).
