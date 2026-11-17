# grx6ab-print results log

## Setup (2026-11-16 15:50 PST)
- Base 5e235a40 (integrate-w82); merged origin/main c1e4ed1b (leaf-fold32 + blueprint chapter; w82 is on main).
- Merged origin/wip/gr-dict 48db1227 (brings gr56-prove's GR56Lattice.lean and gr-dict's GRDict.lean; not on main).

## Consumers of gonzalezRotgerX6Ab (VERIFIED, grep of ZInQKernel at c1e4ed1b)
- Field of OpenResearchLeaves28 (TailZ45 L40), forwarded down to OpenResearchLeaves14.
- TailZ23 L715 `x6Rows_of_open14`: `gonzalezRotger := (gonzalezRotgerX6_iff_ab_gl hR).mpr r.gonzalezRotgerX6Ab`, read by
  TailZ21 `r1r2fpRep_of_printedW`: uses the witness (geomConnX6W_of_gr) AND R5ptProps (`ShimuraSplit.r5fp_of_point`).
- TailZ27 L105: `gonzalezRotgerCountX6Ab_of_printed n.gonzalezRotgerProp56X6 n.gonzalezRotgerX6Ab` (witness only).
- So the consumers need both the witness and R5ptProps: the field cannot be weakened to the witness alone.

## Rating reason (kinds.tsv row 12, VERIFIED read)
- "asserts the witness R1fpPropsAb plus X6Props, which no print states (the H-168 composite shape)".
- elkiesX6StarFunctionField re-rated GLUE for the same witness; shimuraMainThmIDeligneY3AbU composite GLUE.
- autofold.py: only kind=published without a "pending reading" flag counts LEAF (VERIFIED, autofold.py L190-197).

## Locator of Thm 5.12 (VERIFIED in docs/research/locators.md row "R5: fields of definition")
- JMSJ 58 (2006) Thm 5.12, p. 946; arXiv math/0612732 v1/v2 Thm 5.12, pp. 18-19. Prop 5.6 p. 943.

## Coordination
- elkies-print (same round) agreed: their fold consumes a witness Prop with the same body as GRDict.X6ModuliWitness;
  source swap to GRX6AbPrint.x6ModuliWitness_of_coarse is a one-token change.

## Lean (VERIFIED, 2026-11-16 16:00-16:25 PST, load < 25)
- `lake build +ZInQKernel.Contrib.OneProof.GRX6AbPrint`: first run 1 error (h1 consumed by obtain; fixed with `id h1`);
  second run OK (build2.txt). GR56Lattice, GRDict (gr-dict) compile on c1e4ed1b unchanged.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: OK, 0 errors (build3.txt).
- discharges.txt: `DISCHARGES [OpenResearchLeaves28.gonzalezRotgerX6Ab] by GRX6AbPrint.gonzalezRotgerX6Ab_of_print
  still assumes: [GRDict.GonzalezRotgerThm512X6, RayClassCFT.ShimuraMainThmIDeligneY3AbU, GRX6AbPrint.X6CoarseModuli,
  ZInQ.HomLattice.GAGAMorphism, AvSplit.MumfordTorsionAlgClosed]; axioms: [propext, Classical.choice, Quot.sound]`.
  All four GRX6AbPrint theorems: standard axioms.
- autofold --dry-run (autofold.json): strict 16/21 on 37 -> 18/20 on 38; strictest 16/21 -> 18/20 (-1 GLUE).
  FoldCheck.lean (dry-run minus line 1) compiles; sixContactMin_of_open39 standard axioms.
- Merged origin/wip/elkies-print 168bbb39 (ElkiesX6StarEvery.lean). Combined spec autofold-combined.json (both fields;
  Elkies' witness from x6ModuliWitness_of_coarse): strict 16/21 on 37 -> 19/19 on 38 (-2 GLUE);
  FoldCheckCombined.lean compiles, sixContactMin_of_open39 standard axioms. X6WitnessAb and GRDict.X6ModuliWitness
  unify (same body) — VERIFIED by this compile.
