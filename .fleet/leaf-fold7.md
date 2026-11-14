# leaf-fold7 (fleet summary)

**Result.** The single proof `ZInQ.OneProof.frozenTarget` now rests on
`HDec.HSyn.sixContactMin_of_open7 (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7)
(g : OpenGlue7)`, with 69 fields (29 + 23 + 16 + 1) in place of leaf-fold6's 68 (26 + 21 + 20 + 1).

Seven split tasks were folded in:
- av-glue (T8);
- av-split (T4, T5, T35, `homLatticeCorr`, `isogenyQuasiInverse`);
- curve-split (`curveBijIso` proved; H-81, H-82, H-41, and H-83 without its guard clause);
- qm-split (`qmClassNumberOne` proved; T27, the three QM computations, STQM, R4, `r1b`);
- hodge-split (R10, R14, T23, SenTwist, FiniteImageHT, and R13 reduced to its newform case);
- mcr-glue (`ModelCoordinateResidue` reduced to `QuotientP1Coordinate`).

With frontier r3's forms applied to both bundles:
- **Published form:** 15 → 38 fields.
- **Strict count (LEAF = published form):** LEAF / GLUE 15 / 53 → 38 / 31.
- **Lenient count (consequences count as LEAF):** 44 / 24 → 56 / 13.
- **Project-glue rows:** 2 → 1.
- **Glue bundle:** still one field, now the smaller `QuotientP1Coordinate`.

**What compiles (VERIFIED).**
- The new modules `ZInQKernel/OneProof/H/TailP` … `TailX` each compile, and each is under 150 KB.
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- `DumpCompact` with `cmp_hashes`: 8594 → 9953 constants. None was removed; only `frozenTarget`'s hash changed
  (the statement change); all new constants are in TailP–TailX.
- `Check7`: the closure of 186 483 constants contains no `sorryAx`.
- The verbatim check against the split tasks' files finds only the documented edits.

**Transports.** One proof needed real work: hodge-split's R10 over the kernel's G9 layer. Plain unfolding times out
on the two copies of the Tate module, so `TailV` proves the de Rham and Hodge–Tate predicates invariant under an
isomorphism of representations and moves the statement along the identity of `V_p(A)`. Every other transport goes
through by unfolding.

**Not folded** (report §5):
- height-split: SS1 and SS2 are only consequence-level forms, and the reduction adds four glue Props; the strict
  GLUE count does not drop.
- mcr-glue's full split: the glue would go from 1 field to 4.
- qm-split H-44, H-87, H-88, H-1, H-43, H-59: each needs new glue.
- curve-split H-79: the bound `dim J₁(N) ≤ N²` would need the existing chain above step E2 restated.
- av-split H-53, H-78 and hodge-split H-9: not splittable over Mathlib today.

**What remains.** 31 fields are not in published form: 18 consequences of one theorem, 12 composites, and the glue
`QuotientP1Coordinate`. Most of them come from the moduli of the Shimura curve (group A in report §3). Flagged for
a human check: the Igusa theta expressions, `ShimuraFamily`'s "every π" step, the `ℚ̄`-model form of
Shimura–Taniyama, the coordinate forms of Mumford §1 and GAGA, and `H¹_ét` as `Hom(V_p A, ℚ_p)`.

The full report is docs/research/leaf-fold7.md; tools and log are in scratch/leaf-fold7/.
