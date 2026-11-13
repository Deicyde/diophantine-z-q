# frontier (2026-11-13) — DRAFT, final version follows

**Main result.** `docs/research/frontier.md` lists every open Prop on the path to `ZInQ.FrozenTarget`:
72 = 22 LEAF + 50 GLUE (GZ 2, TYZ 7, H 63), with today's compiled branch results folded in (scenario F).
GZ and TYZ are compiled end to end: `ZInQ.Frontier.frozenTarget_of_open` (scratch/frontier/TYZChain.lean)
derives `ZInQ.FrozenTarget` from `ZInQ.SixContactMin` and exactly the 9 GZ/TYZ Props, standard axioms.
H: assemble-port's compiled `HDec.HSyn.sixContactMin_of_leaves5` (75 bundle fields) plus 18 per-branch edges,
each checked textually by scratch/frontier/chain.py (signatures, def texts, report = open set).
