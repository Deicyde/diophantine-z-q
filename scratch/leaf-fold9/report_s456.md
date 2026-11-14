
## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base.** `lake build +ZInQKernel.OneProof.Main` exits 0 on the base. The kernel and the chain were rebuilt in this
  worktree.
- **Hashes before.** `DumpCompact` gives 10831 constants (`hashes_before.txt`), identical to leaf-fold8's
  `hashes_after.txt`.
- **Lemmas.** `lake env lean scratch/leaf-fold9/test/R1recT.lean` compiles with no errors (about 5 s after imports).
  It took three rounds of fixes: a coercion to `Set`, `zpow` under a β-redex, and a `let` that `simp` does not
  unfold.
- **CloudW07.** `lake build ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists …NormalModel` exits 0, taking
  about 18 min.
- **modular-split.** Merged with `git merge origin/wip/modular-split` (clean, after its `.fleet` report). `TailZ6`
  (with `R15.lean`) and the new `Main` built at the first try.
- **TailZ5.** `lake build ZInQKernel.OneProof.H.TailZ5` succeeds, about 80 s, after one fix in `r5fp_of_rep`.
  - Rewriting `residueImage x = fieldOfModuliPair P` inside `R5ptProps`' conclusion gives a "motive is not type
    correct" error (an auxiliary proof term of `R5ptProps` depends on the field).
  - The fix transports the degree and the embedding along `IntermediateField.equivOfEq`.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** 10917 constants. `cmp_hashes.py` reports 0 removed and 1 changed (`frozenTarget`). The 86 new
  constants are all in `TailZ5` and `TailZ6`.
- **Check9.lean.** Conclusion; closure (212 153 constants, no `sorryAx`); head constant and module of all 61 fields;
  axioms of the CloudW07 proofs and the bridge theorems; the full types of `r1rec_of_rep` and `r5fp_of_rep`.
- **Module size.** TailZ5 is 14 KB and TailZ6 is 15 KB.

**No statement of a leaf, row or glue Prop was changed.**
- Every kept field keeps its type.
- Every removed field is filled by a compiled theorem whose type is exactly the old field's constant.
- No HDec copy was deleted, so no FaithCheck was needed.

## 5. Not folded, and why

Decision rule (leaf-fold7 §5, as the task states it). A fold is taken only if it does one of the following:
- lowers the strict GLUE count;
- replaces a composite or consequence by published-form leaves.

In either case, neither count may rise.

- **(1) mcr-quot (`modelCoordinateResidue_final9`, `heckeVertWitness_of_mcrQuot`). Not taken.**
  - Replacing the project glue `QuotientP1Coordinate` (1 strict GLUE) by mcr-quot's inputs would add:
    - L1 `ProperCurveAF` (composite), L3 `TameQuotientSmooth` (composite) and L6 `TameInertiaCyclic` (composite);
    - L5 `TameFixedPointsDisjoint` (consequence);
    - L2 `FiniteQuotientExists` (special case) and L4 `SmoothModelOfP1` (STANDARD);
    - the two new glue Props `P1SchemeQ` and `CMStabObj`;
    - and `CoverModelOfHeckeN`.

    T5 and `CurveBijIso` are theorems in the chain.
  - That is at least −1 + 6 on the strict count, and −1 + 5 on the lenient count.
  - Note for later (SPECULATIVE): the vendored CloudW07 library has the projective line `AlgebraicGeometry.projectiveLine`
    over a field, which is proper and integral with charts. It may close `P1SchemeQ`. Even then the six L-leaves
    keep the fold from paying.
- **(2) coarse-factor (`r1r2fpRep_of_canonical''`, `x6ConicModel_of_canonical''`). Not taken.**
  - H-43: qm-glue's `ConicCanonical` has the same statement as the field `x6ConicModel` (`X6Kummer.X6ConicModel`:
    `∃ Y Φ X Ψ fY π₆, R1R2fpFullProps … ∧ ConicModel X π₆`), and `x6ConicModel_of_canonical''` also takes `r1r2`.
    The replacement would be a renaming.
  - H-1: `r1r2` (comp) would become:
    - `CanonicalCoarseX6`, which is SGA 1's quotient together with Shimura–Deligne and Deligne's `π₀`, and carries
      the audit's "qualified consequence" caveat, so strict GLUE;
    - `BabaGranathX6` and `GonzalezRotgerX6`;
    - the glue `ReciprocityOfFine`.

    (`CanonicalModelY3` is implied by any of the three existential forms, since each contains `R1fpProps Y Φ`.)
    That is strict −1 + 2. It would be −1 + 1 if `ReciprocityOfFine` were proved from the field `r1rec`, which the
    bridge of §1.1 makes possible.
  - But the same bridge proves `r1rec` and `r5` from `r1r2` (−2 strict), and the two uses exclude each other.
  - So the fold that pays is the one taken: keep `r1r2`, drop `r1rec` and `r5`. `CoarseFactor` is proved
    (coarse-factor) but enters no field.
- **(4) modular-split, the parts not folded.**
  - `dimJacobianEqGenus` (comp) would become the project glue `H0DifferentialsEqHolo`. That is a real gain, since no
    literature is left, but neither count drops.
  - `r17` (c) would become `CarayolRealization` (c): neutral.
  - `eigenformHTNew` (c) would become `KatoRealizationCoh` (c) and the glue `HTDual`: strict +1.
- **(4) reduct-split, shimura-split:** see §7.
- **H-3 `r5count`, H-44 `thetaRatiosAlgebraic`, TYZ T-5 `hS`.** Unchanged from leaf-fold8 §5.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves8`, `t : OpenTextbookLeaves8`.
- Added: `r : OpenResearchLeaves9`, `t : OpenTextbookLeaves9`.
- `l : OpenAddedLeaves8` and `g : OpenGlue7` are unchanged.

**TYZ / GZ.** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` are unchanged.

**Fields removed (5), all proved, none replaced:**
- research `r1rec` (`LeafQM.AV.R1rec`) and `r5` (`LeafQM.AV.R5fp`): proved from the research field `r1r2`
  (`r1rec_of_rep`, `r5fp_of_rep`);
- textbook `t33` (`LeafModCurves.JacobianExists ℚ`) and `normalModelOfFunctionFieldQ`: proved by cloud worker W07
  (PR #11);
- research `r15` (`DeligneSerreConseq`): proved from the research field `dsThm966` (modular-split,
  `ModularSplit.deligneSerreConseq_of_ds`).

**Fields added:** none.
