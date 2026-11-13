# igusa-special — report

**Main result: textbook leaf T28 is proved.** `T28.igusaClebschSeparation_proved :
PkgI1.IgusaClebschSeparation` (ZInQKernel/Contrib/T28/Assemble.lean, written by this task as the
second finisher), from igusa-generic's `T28.separationGeneric` and this task's
`T28Special.separationBothSpecial : T28.SeparationBothSpecial` (ZInQKernel/Contrib/T28/Special.lean).
`#print axioms`: `[propext, Classical.choice, Quot.sound]` for every theorem below. Proposal:
remove T28 from the leaf list (no statement change).

**What compiles** (`lake build ZInQKernel.Contrib.T28.Assemble`: success, after merging origin/main
6c225515 and wip/igusa-generic 73bbe461): new files `ZInQKernel/Contrib/T28/Special/{Family,Bolza,
NormalForm}.lean`, `ZInQKernel/Contrib/T28/Special.lean`, `ZInQKernel/Contrib/T28/Assemble.lean`
(Bolza.lean is the slowest, ~3 min). No existing file edited; diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0.

**Exact declarations proved** (namespace `T28Special` unless noted):
- `T28.igusaClebschSeparation_proved : PkgI1.IgusaClebschSeparation`;
  `T28.igusaSeparationEq_proved : PkgI1.IgusaSeparationEq`;
  `T28.separationSpecial_proved : PkgI1.SeparationSpecial`.
- `separationBothSpecial : T28.SeparationBothSpecial`;
  `special_to_E : J10 f ≠ 0 → det yv f = 0 → ∃ a b, Eqv f (E a b)` (Bolza's criterion).
- `det_yv_Nr`: `det yv (x(x-1)(x-l)(x-m)(x-n)) = (1/384433593750)·∏` over the 15 synthemes of
  the syntheme determinants; `special_Nr`, `cls1_E … cls4_E`, `even_to_E`, `J10_Nr = 256·disc`.
- `exists_Nr : J10 f ≠ 0 → ∃ l m n, Eqv f (Nr l m n)` (root normal form).
- `E_sep`: two members of `x⁶+ax⁴+bx²+1` with weighted-equal invariants are equivalent
  (`fam_alg` elimination; `E_orbit`; `E_D4`: the D₄ stratum's second involution class,
  `t ↦ t'`, `t = 4/ρ-1`, `t' = 4ρ-1`).

**What remains:** nothing for T28. (The special locus needed `T28.det_yv_actC` from igusa-generic's
Covariance.lean, which is proved.) Host note: `~/pyenv/bin/python` does not exist (no sympy/PARI);
all computer algebra was done with a pure-python polynomial library (scratch/igusa-special/poly.py).

Details: docs/research/igusa-special.md; log: scratch/igusa-special/log.md.
