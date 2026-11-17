# semiab-descend (fleet note)

**Result.** I proved height-fix's last glue Prop, `ZInQ.HeightFix.SemiAbelianDescendsPerfect`, in Lean. The
statement is unchanged and the proof covers every perfect field, so every use is covered (the only consumer,
`isSemistableRes_of_geom`, applies it to finite residue fields). The proof rests on one new published leaf,
`ZInQ.SemiAbDescend.ChevalleyPerfect`: Chevalley's structure theorem over a perfect field, existence and uniqueness
(Conrad 2002 Thm 1.1 / Milne AG Thm 8.27, numbers UNVERIFIED). `G/H` is read as a faithfully flat homomorphism
onto an abelian variety whose scheme-theoretic kernel is smooth, connected and affine. I rate the leaf printed
form, flagged "locator UNVERIFIED".

**Compiles (VERIFIED), standard axioms.** The file is `ZInQKernel/Contrib/OneProof/SemiAbelianDescendsPerfect.lean`.
It proves:
- Yoneda on affine points ⇒ isomorphism;
- a functor-of-points split-torus kernel is `Spec K[x^±1]`;
- a faithfully flat homomorphism with smooth kernel has smooth source (shear square and Mathlib's flat descent);
- open subgroups over k̄ are closed (Jacobson);
- `G⁰` over a field is an open subgroup;
- the kernel commutes with base change;
- the assembly `semiAbelianDescendsPerfect_of_chevalley`, and `bostLowerBound`/`gaudronRemondThm14` (plus the
  optional javanpeykar/pazuki rows) `_of_printed_chevalley`.

**Checks.**
- `#discharges` (`scratch/semiab-descend/discharges.txt`): the two fields are discharged; the only new leaf is
  `ChevalleyPerfect`.
- `Statements.lean`: the verbatim copies equal the originals by `rfl`.

**Fold.** `scratch/semiab-descend/autofold.json` is height-fix's fold with the glue replaced by `chevalleyPerfect`.
On this base `uniformizationLeafAll` is already proved, so the spec uses `_root_.uniformizationLeafAll_proof`.
The dry run gives 16/21 → 19/19, i.e. **−2 GLUE**, with no `--allow-rise`. The generated module compiles and
`sixContactMin_of_open39` has the standard axioms. `autofold-after-height-fix.json` is the variant to use if
height-fix is folded first.

**Remains.**
- A statement check of `ChevalleyPerfect` against the print; if the quotient dictionary is counted, it is rated a
  consequence.
- unipotent-b's `SemiAbelianDescendsSepClosed` (imperfect, separably closed fields) is not covered.
- The fold itself was not run.

Report: `docs/research/semiab-descend.md`.
