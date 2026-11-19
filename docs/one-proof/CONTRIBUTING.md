# Contributing to the single proof

`ZInQ.OneProof.frozenTarget` (`ZInQKernel/OneProof/Main.lean`) is one Lean theorem: it proves the frozen target
`ZInQ.FrozenTarget` of "Z is Diophantine in Q" from a list of open hypotheses, with no `sorry` and only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. **[OPEN.md](OPEN.md) lists every open
hypothesis** with its exact Lean statement, its kind, its source and who is working on it. Each one you prove
in Lean, or reduce to theorems in their printed form, leaves the list.

## What to contribute

Pick a hypothesis in [OPEN.md](OPEN.md) whose status is open, and claim it before you start: comment
`Claiming <field> at <commit>` on [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14), with the
field name exactly as OPEN.md shows it and the commit you start from, or open a draft pull request that links
#14 with that line in its body. Hold one claim at a time to begin with; if you stop, comment
`Releasing <field>: <what blocked you>`. The full claim rule, including lapses, is in the root
[CONTRIBUTING.md](../../CONTRIBUTING.md#choose-and-claim-one-statement). Then either:

1. **Prove it.** Write a theorem whose type is exactly the hypothesis's statement:

   ```lean
   theorem igusaCMValue24_proof : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24 := by
     ...
   ```

2. **Reduce it to published theorems.** State each theorem you use as a `def … : Prop` in its printed form,
   over genuine definitions (Mathlib's, or the repository's), with a docstring giving the edition, page and
   display you read (or UNVERIFIED if nobody has read it), and prove the hypothesis from them:

   ```lean
   /-- Bosch–Lütkebohmert–Raynaud, *Néron models* (Springer, 1990), p. <page>, §1.2 Prop. 4
   (printed form). -/
   def BLR_1_2_4 : Prop := ...

   theorem neronLocalizesDVR_of_printed (h : BLR_1_2_4) : ReductGlue.NeronLocalizesDVR := ...
   ```

   This helps when the hypothesis is GLUE (a consequence, a composite, or project glue) and the new statements
   are published leaves. Each new printed leaf enters OPEN.md flagged unread: it counts as published, and a
   statement check ([STATEMENT-CHECKS.md](STATEMENT-CHECKS.md)) compares it with the print. A leaf whose print may
   say something weaker is flagged pending reading and counts as glue until a check clears it. A new statement must be
   the published theorem or a consequence of it, never stronger, and never over a structure invented for the
   purpose.

Never change a hypothesis's statement. If you find one false, vacuous, or stronger than its source, report it
(with a corrected statement) on the issue: that is a valid and useful result.

## Where it goes

A new file `ZInQKernel/Contrib/OneProof/<StatementName>.lean`, importing the module that declares the statement
you prove and whatever else you need. OPEN.md gives the statement's Lean constant, for example
`CToPrinted.SGA7_IX_3_3`; searching the tree for its declaration (`git grep -n "def SGA7_IX_3_3"`) finds the file,
here `ZInQKernel/OneProof/H/TailZ19.lean`, so the import is `ZInQKernel.OneProof.H.TailZ19`.
Do not import `ZInQKernel.OneProof.Main`: once your file is folded, `Main` imports it, and the import would be
a cycle. Proofs only in new files: do not edit existing
modules. Keep a file under about 150 KB. Open a pull request against this fork's `main`.

## How to check it

Build, then run `#discharges` from a scratch file:

```lean
import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.<StatementName>

#discharges
```

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.<StatementName>
lake env lean <scratch file>
```

For every theorem in your file it prints which open hypotheses it proves, the hypotheses it still assumes
(your new leaves), and its axioms. A statement change does not match. A proof using `sorry` is flagged.

You may not have to run it yourself. For a pull request into `main` that only adds files under
`ZInQKernel/Contrib/OneProof/`, the same check runs on the files it adds, built on top of the current `main` (not
on the rest of your branch), as the GitHub Actions check "discharge check" on a fresh hosted runner with no
secrets and no access to project machines (`scripts/one_proof/sandbox/README.md`). The verdict is in the check's
job summary, and the run may wait for a maintainer to approve it before it starts. A pull request that changes
anything else is out of scope for the automatic check. The automatic check is being set up: until it has run on
a first contribution, include your own `#discharges` output in the pull request. The repository's default `lake build` does not compile `ZInQKernel/Contrib/OneProof`, so a green
CI check alone says nothing about a contribution.

The automatic result is advisory. The project's agents check every pull request before it is merged (the build,
`#discharges`, the axioms, and the scan for code that runs at build time); no person reads every file. A file with
code that runs at build time (`#eval`, `run_cmd`, `initialize`, new `syntax`, `notation`, macros or elaborators)
is not merged, since such code could print a forged result; if you need it, ask on the issue first.

The bar for merging:

* the Lean compiles with only the standard axioms, and the discharge check shows the hypothesis proved (until
  the automatic check has run on a first contribution: your own `#discharges` output, checked by the project's agents);
* the file has no code that runs at build time;
* each new printed leaf has a row in [`docs/research/locators.md`](../research/locators.md) and enters
  kinds.tsv flagged unread (or pending reading, if its print may say something weaker);
* the project's integrator merges it into the next fold (agent review: the checks above, run by the project's agents).

Merges into this fork carry no Protocol B review (the original repository's review protocol); a result is
reviewed again when it moves to the original repository. The integrator then folds it into the single proof: a
new bundle generation without that hypothesis (and with your leaves, if any), `frozenTarget` switched to it, the
build re-checked, and OPEN.md regenerated.

## What it costs to build

You do not need to build anything to contribute. If you want to, these are the measured figures so far.
`lake exe cache get` fetches only Mathlib's compiled files, so on your own machine this project's files build from
source. The automatic check on a pull request starts from a cached build of `main` instead.

| what was built | cold or partial | commit | measured |
| --- | --- | --- | --- |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines | not recorded | `1e30d4b2` | 11,655 Lake jobs in 20 minutes |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines | not recorded | `4c1cc906` | 11,813 Lake jobs |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines | not recorded | `053cbad0` | 12.5 minutes |
| `lake build +ZInQKernel.OneProof.Main` on the project's build machines, for leaf-fold4 ([`docs/research/leaf-fold4.md`](../research/leaf-fold4.md)) | not recorded | not recorded | 26 minutes |
| `lake build +ZInQKernel.OneProof.Main` at w66, the x6 fold ([`docs/research/x6-fold.md`](../research/x6-fold.md)) | partial rebuild | `ecdb5d846` | 12,916 Lake jobs in 8.5 minutes |
| the contributions and OneProof at w63 | not recorded | `b5ff0474` | 12,913 Lake jobs |
| the Tau Ceti dependency tree | cold | not recorded | 6,846 Lake jobs in 8 minutes 4 seconds; 3.4 GB |
| one large file compiled against an already built `ZInQKernel.OneProof.Main` | partial (that file only) | not recorded | about 8 to 9 GB of memory |
| upstream's kernel job on a GitHub-hosted runner | not recorded | not recorded | needed a 180-minute timeout and 8 GiB of extra swap |
| `lake build +ZInQKernel.OneProof.Main` on a 12-core, 18 GB machine, `LEAN_NUM_THREADS=8` (AI audit, [#62](https://github.com/Deicyde/diophantine-z-q/issues/62)) | cold, stopped for disk | `e1b31749` | 694 of the 5,225 project modules in 41 minutes, no errors; 0.44 GB of `.olean` and 3.4 GB of per-module `.setup.json` files (median 3.4 MB; they embed absolute paths, so a short checkout path matters) |
| the discharge check's build step on GitHub-hosted runners, before the build cache | cold | several pull requests | five runs stopped at the 270-minute limit (43981996517, 43968843468, 43920004200, 43839513202, 43751567891) |
| `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` in the main build cache workflow on GitHub-hosted runners (`ubuntu-latest`: 15 GiB of memory, 47 GiB of swap added) | cold, over two runs | `f3402e89`, then `be73b91c` | 16,331 Lake jobs in 451 minutes of build time. Run [44170383906](https://github.com/Deicyde/diophantine-z-q/actions/runs/44170383906) found no cache, stopped at the workflow's 310-minute limit and saved its progress; run [44219370755](https://github.com/Deicyde/diophantine-z-q/actions/runs/44219370755) restored it, finished in 141 minutes and passed the axiom check. By `du -sh`, the finished build is 37 GiB for this repository and 6.7 GiB for Mathlib; its cache archive is 3.0 GiB |
| the same workflow's next nine finished runs on pushes to `main`, each starting from the previous build | partial rebuild | `1121bf19` to `8ecaadef`, 2026-11-18 | eight jobs took 10 to 14 minutes, with 31 seconds to 5 minutes in the build step; the one at `41892618` (run [44243377928](https://github.com/Deicyde/diophantine-z-q/actions/runs/44243377928)) took 93 minutes, with 84 in the build step |

A cold build does not fit in one job on a GitHub-hosted runner. The main build cache workflow stops its build at
310 minutes, saves the progress and continues in the next run, and the first cold build finished that way on
2026-11-18. On a laptop a full build is a bigger investment: allow several hours and about 50 GB of disk. A
measured row from your machine (commit, cold or partial, cores, memory cap, peak memory, disk, Lake jobs,
wall-clock) is welcome and credited.

## For the integrator: folding a contribution

`scripts/one_proof/autofold.py SPEC.json` writes the fold of a checked contribution: a new module
`ZInQKernel/OneProof/H/TailZ<k+1>.lean` with the next generation of each affected bundle (the discharged fields
removed, the new leaves added), a theorem filling each discharged field with its proof, and the next top theorem;
it switches `Main.lean` to it and updates `kinds.tsv` and `claims.tsv`. It refuses a fold that raises either GLUE
count (the strict or the strictest column) unless given `--allow-rise`. The spec format is in the script's docstring; `scratch/contrib-kit/autofold-test.json` exercises the
mechanics (with `sorry`, so it is a test, not a fold). Then build, check the axioms, compare hashes with
`scratch/one-proof/DumpCompact.lean` and `cmp_hashes.py` (no existing constant may change except `frozenTarget`),
and regenerate OPEN.md (`scripts/one_proof/OpenStatements.lean`, then `render_open.py`, then `render_open.py --check`).

## A worked example

`scratch/contrib-kit/DischargesTest.lean` runs `#discharges` on three theorems, against the current open
hypotheses. Its output (generated from `scratch/contrib-kit/DischargesTest-output.txt`):

<!-- worked-example:begin -->
```
scratch/contrib-kit/DischargesTest.lean:13:8: warning: declaration uses `sorry`
DISCHARGES [OpenResearchLeaves71.carayolThmAFrob] by CarayolRefold.frob_of_DDT31
  still assumes: [CarayolDDT.CarayolDDT31]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by DSCoeffExt.dsThm965Printed_of_charpoly
  still assumes: [∀ (N : ℕ) [inst : NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ZInQ.Contrib.G9.PkgI4.CF N k),
   2 ≤ k →
     DSCoeffExt.IsNormalizedEigenformDS f χ →
       ∀ [inst : NumberField ↥(DSCoeffExt.coeffField f)] (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
         (lam : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(DSCoeffExt.coeffField f))),
         ↑ℓ ∈ lam.asIdeal →
           ∃ ρ,
             Continuous ⇑ρ ∧
               ∀ (p : ℕ),
                 Nat.Prime p →
                   ¬p ∣ N * ℓ →
                     (∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar),
                         ZInQ.Contrib.G9.PkgI4.LiesOver v p → ∀ σ ∈ ValuationSubring.inertiaSubgroup ℚ v, ρ ↑σ = 1) ∧
                       ∀ (b : ↥(DSCoeffExt.coeffField f)),
                         ↑b = χ ↑p * ↑p ^ (k - 1) →
                           ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ),
                             ZInQ.Contrib.G9.PkgI4.LiesOver v p →
                               ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
                                 (↑(ρ σ)).charpoly =
                                   Polynomial.X ^ 2 -
                                       Polynomial.C
                                           ((algebraMap (↥(DSCoeffExt.coeffField f))
                                               (IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                                 (↥(DSCoeffExt.coeffField f)) lam))
                                             ⟨ZInQ.Contrib.G9.PkgI4.coeff f p, ⋯⟩) *
                                         Polynomial.X +
                                     Polynomial.C
                                       ((algebraMap (↥(DSCoeffExt.coeffField f))
                                           (IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                             (↥(DSCoeffExt.coeffField f)) lam))
                                         b)]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves30.scholzeH1AbVar] by DeRhamScholze.HTMerge.scholzeH1AbVar_of_old
  still assumes: [DeRhamScholze.ScholzeDeRhamAlg, DeRhamScholze.HTAbVar.HodgeNumberH1AbVar]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmHeight62] by HDec.CMBranch.CMInputs2.cmHeight62
  still assumes: [HDec.CMBranch.CMInputs2]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmjDegree] by HDec.CMBranch.CMInputs2.cmjDegree
  still assumes: [HDec.CMBranch.CMInputs2]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmHeight62] by HDec.CMBranch.CMInputs3.cmHeight62
  still assumes: [HDec.CMBranch.CMInputs3]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmjDegree] by HDec.CMBranch.CMInputs3.cmjDegree
  still assumes: [HDec.CMBranch.CMInputs3]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves14GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves15GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves16GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves17GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves18GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves19GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves20GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves21GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves22GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves23GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves24GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves25GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves26GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves27GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves28GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves29GMEBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves31EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves32EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves33EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS.y3row
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves34EBCFSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS.y3ToP1j
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.dsThm965Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.dsThm966Printed
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS.y3ToP1j
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves36EBCFSFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves8EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS.r9a
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS.r9b
  still assumes: [HDec.HSyn.GR9.OpenResearchLeaves9EBSFU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves14GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves14GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves14GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves14GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves14GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves14GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves15GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves15GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves15GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves15GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves15GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves15GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves16GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves16GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves16GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves16GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves16GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves16GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves17GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves17GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves17GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves17GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves17GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves17GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves18GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves18GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves18GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves18GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves18GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves18GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves19GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves19GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves19GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves19GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves19GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves19GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves20GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves20GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves20GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves20GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves20GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves20GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves21GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves21GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves21GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves21GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves21GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves21GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves22GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves22GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves22GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves22GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves22GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves22GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves23GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves23GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves23GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves23GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves23GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves23GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves24GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves24GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves24GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves24GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves24GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves24GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves25GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves25GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves25GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves25GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves25GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves25GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves26GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves26GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves26GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves26GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves26GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves26GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves27GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves27GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves27GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves27GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves27GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves27GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves28GMEB_r5.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves28GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves28GMEB_r5.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves28GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves28GMEB_r5.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves28GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves28GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves28GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves28GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves28GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves28GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves28GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves29GMEB_r5.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves29GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves29GMEB_r5.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves29GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves29GMEB_r5.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves29GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves29GMEB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves29GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves29GMEB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves29GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves29GMEB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves29GMEB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves2EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves2EB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves2EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves2EB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves2EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves31EB_r5.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves31EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves31EB_r5.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves31EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves31EB_r5.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves31EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves31EB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves31EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves31EB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves31EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves31EB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves31EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves32EBCF_r5.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves32EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves32EBCF_r5.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves32EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves32EBCF_r5.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves32EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves32EBCF_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves32EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves32EBCF_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves32EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves32EBCF_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves32EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves33EBCF_r5.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves33EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves33EBCF_r5.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves33EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves33EBCF_r5.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves33EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves33EBCF_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves33EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves33EBCF_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves33EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves33EBCF_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves33EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves34EBCF_r5.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves34EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves34EBCF_r5.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves34EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves34EBCF_r5.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves34EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves34EBCF_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves34EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves34EBCF_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves34EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves34EBCF_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves34EBCF_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.afCharpolyDS965] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.afCharpolyDS965
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.bergerSurveyF] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.bergerSurveyF
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.deligneCanonicalModelY3EveryPrint] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.deligneCanonicalModelY3EveryPrint
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondSec9LowerAnSS] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.gaudronRemondSec9LowerAnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondThm14AnSS] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.gaudronRemondThm14AnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.javanpeykarThm111An] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.javanpeykarThm111An
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.modularHTCoeff] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.modularHTCoeff
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.panPrintedF] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.panPrintedF
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS.y3ToP1j
  still assumes: [HDec.HSyn.OpenResearchLeaves54SFU_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.afCharpolyDS965] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.afCharpolyDS965
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.bergerSurveyF] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.bergerSurveyF
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.carayolThmAFrob] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.carayolThmAFrob
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.deligneCanonicalModelY3EveryPrint] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.deligneCanonicalModelY3EveryPrint
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondSec9LowerAnSS] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.gaudronRemondSec9LowerAnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondThm14AnSS] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.gaudronRemondThm14AnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.javanpeykarThm111An] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.javanpeykarThm111An
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.modularHTCoeff] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.modularHTCoeff
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.panPrintedF] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.panPrintedF
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.silverbergZarhinThm35] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.silverbergZarhinThm35
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3FullThreeRepZ30] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.y3FullThreeRepZ30
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.OpenResearchLeaves59_y3x6NOS.y3ToP1j
  still assumes: [HDec.HSyn.OpenResearchLeaves59_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves5EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves5EB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves5EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves5EB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves5EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.afCharpolyDS965] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.afCharpolyDS965
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.bergerSurveyF] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.bergerSurveyF
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.carayolThmAFrob] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.carayolThmAFrob
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.deligneCanonicalModelY3EveryPrint] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.deligneCanonicalModelY3EveryPrint
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondSec9LowerAnSS] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.gaudronRemondSec9LowerAnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondThm14AnSS] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.gaudronRemondThm14AnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.javanpeykarThm111An] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.javanpeykarThm111An
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.modularHTCoeff] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.modularHTCoeff
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.panPrintedF] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.panPrintedF
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.shimuraThm1Af] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.shimuraThm1Af
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.silverbergZarhinThm35] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.silverbergZarhinThm35
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3FullThreeRepZ30] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.y3FullThreeRepZ30
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.OpenResearchLeaves60_y3x6NOS.y3ToP1j
  still assumes: [HDec.HSyn.OpenResearchLeaves60_y3x6NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.afCharpolyDS965] by HDec.HSyn.OpenResearchLeaves63NOS.afCharpolyDS965
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.bergerSurveyF] by HDec.HSyn.OpenResearchLeaves63NOS.bergerSurveyF
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.carayolThmAFrob] by HDec.HSyn.OpenResearchLeaves63NOS.carayolThmAFrob
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmHeight62] by HDec.HSyn.OpenResearchLeaves63NOS.cmHeight62
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmjDegree] by HDec.HSyn.OpenResearchLeaves63NOS.cmjDegree
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.deligneCanonicalModelY3EveryPrint] by HDec.HSyn.OpenResearchLeaves63NOS.deligneCanonicalModelY3EveryPrint
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves63NOS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves63NOS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondSec9LowerAnSS] by HDec.HSyn.OpenResearchLeaves63NOS.gaudronRemondSec9LowerAnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondThm14AnSS] by HDec.HSyn.OpenResearchLeaves63NOS.gaudronRemondThm14AnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.javanpeykarThm111An] by HDec.HSyn.OpenResearchLeaves63NOS.javanpeykarThm111An
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.modularHTCoeff] by HDec.HSyn.OpenResearchLeaves63NOS.modularHTCoeff
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves63NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.panPrintedF] by HDec.HSyn.OpenResearchLeaves63NOS.panPrintedF
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves63NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves63NOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves63NOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.shimuraThm1Af] by HDec.HSyn.OpenResearchLeaves63NOS.shimuraThm1Af
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.silverbergZarhinThm35] by HDec.HSyn.OpenResearchLeaves63NOS.silverbergZarhinThm35
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3FullThreeRepZ30] by HDec.HSyn.OpenResearchLeaves63NOS.y3FullThreeRepZ30
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.OpenResearchLeaves63NOS.y3ToP1j
  still assumes: [HDec.HSyn.OpenResearchLeaves63NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.afCharpolyDS965] by HDec.HSyn.OpenResearchLeaves64NOS.afCharpolyDS965
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.bergerSurveyF] by HDec.HSyn.OpenResearchLeaves64NOS.bergerSurveyF
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.carayolThmAFrob] by HDec.HSyn.OpenResearchLeaves64NOS.carayolThmAFrob
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmHeight62] by HDec.HSyn.OpenResearchLeaves64NOS.cmHeight62
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.cmjDegree] by HDec.HSyn.OpenResearchLeaves64NOS.cmjDegree
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.deligneCanonicalModelY3EveryPrint] by HDec.HSyn.OpenResearchLeaves64NOS.deligneCanonicalModelY3EveryPrint
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm965Printed] by HDec.HSyn.OpenResearchLeaves64NOS.dsThm965Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.dsThm966Printed] by HDec.HSyn.OpenResearchLeaves64NOS.dsThm966Printed
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondSec9LowerAnSS] by HDec.HSyn.OpenResearchLeaves64NOS.gaudronRemondSec9LowerAnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondThm14AnSS] by HDec.HSyn.OpenResearchLeaves64NOS.gaudronRemondThm14AnSS
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.javanpeykarThm111An] by HDec.HSyn.OpenResearchLeaves64NOS.javanpeykarThm111An
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.modularHTCoeff] by HDec.HSyn.OpenResearchLeaves64NOS.modularHTCoeff
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.neronSchemeExtensionDedekind] by HDec.HSyn.OpenResearchLeaves64NOS.neronSchemeExtensionDedekind
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.panPrintedF] by HDec.HSyn.OpenResearchLeaves64NOS.panPrintedF
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves64NOS.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves64NOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves64NOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.shimuraThm1Af] by HDec.HSyn.OpenResearchLeaves64NOS.shimuraThm1Af
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.silverbergZarhinThm35] by HDec.HSyn.OpenResearchLeaves64NOS.silverbergZarhinThm35
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3FullThreeRepZ30] by HDec.HSyn.OpenResearchLeaves64NOS.y3FullThreeRepZ30
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.y3ToP1j] by HDec.HSyn.OpenResearchLeaves64NOS.y3ToP1j
  still assumes: [HDec.HSyn.OpenResearchLeaves64NOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves7EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves7EB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves7EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves7EB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves7EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves8EB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves8EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves8EB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves8EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves8EB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves8EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by HDec.HSyn.OpenResearchLeaves9EB_r5.pazukiCor13Upper
  still assumes: [HDec.HSyn.OpenResearchLeaves9EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.OpenResearchLeaves9EB_r5.r9a
  still assumes: [HDec.HSyn.OpenResearchLeaves9EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.OpenResearchLeaves9EB_r5.r9b
  still assumes: [HDec.HSyn.OpenResearchLeaves9EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.ResearchLeaves3EBU_y3cNOS.r9a
  still assumes: [HDec.HSyn.ResearchLeaves3EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.ResearchLeaves3EBU_y3cNOS.r9b
  still assumes: [HDec.HSyn.ResearchLeaves3EBU_y3cNOS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9a] by HDec.HSyn.ResearchLeaves3EB_r5.r9a
  still assumes: [HDec.HSyn.ResearchLeaves3EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.r9b] by HDec.HSyn.ResearchLeaves3EB_r5.r9b
  still assumes: [HDec.HSyn.ResearchLeaves3EB_r5]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.bergerSurveyF] by HDec.PkgI4.PanDict.bergerSurveyF_of_basis
  still assumes: [HDec.PkgI4.PanDict.BergerSurveyFBasis]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.javanpeykarThm111An] by JavanpeykarAnRetype.javanpeykarThm111An_of_thm111
  still assumes: [JavanpeykarDirect.JavanpeykarThm111, ZInQ.LeafPush2.UniformizationExists]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.deligneCanonicalModelY3EveryPrint] by Y3Hodge.print_of_deligneH
  still assumes: [Y3Fix.DeligneCanonicalModelY3EveryH]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.gaudronRemondSec9LowerAnSS] by ZInQ.BostGR9.gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS
  still assumes: [ZInQ.SemistabAssembly.BostLowerBoundAnSS]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by ZInQ.ChevFree.pazukiCor13Upper_of_printed_free
  still assumes: [ZInQ.HeightFix.PazukiCor13UpperPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by ZInQ.HeightDict.pazukiCor13Upper_of_printed
  still assumes: [ZInQ.HeightDict.PazukiCor13UpperPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by ZInQ.HeightFix.pazukiCor13Upper_of_printed
  still assumes: [ZInQ.HeightFix.PazukiCor13UpperPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed,
 ZInQ.HeightFix.SemiAbelianDescendsPerfect]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves71.pazukiCor13Upper] by ZInQ.SemiAbDescend.pazukiCor13Upper_of_printed_chevalley
  still assumes: [ZInQ.HeightFix.PazukiCor13UpperPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 AvSplit.MumfordTorsionAlgClosed,
 ZInQ.SemiAbDescend.ChevalleyPerfect]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 31 open hypotheses, 15988 theorems checked, 327 discharge one
```
<!-- worked-example:end -->

`t1` assumes the hypothesis it proves (`quotientP1Coordinate`), so it reduces nothing; `t2 : True` matches
nothing; `t3` matches an open hypothesis but uses `sorry`, so it is flagged. The count of theorems checked also
includes the theorems of the contributions already folded in (`#discharges` checks the current file and every
imported module under `ZInQKernel.Contrib.OneProof`); they discharge nothing, since their hypotheses are no
longer open.

A real contribution in this shape: cm24-value (`docs/research/cm24-value.md`) proved
`IgusaCMValue24`, Lin–Yang's Igusa vector at the CM point of discriminant −24, from Mathlib's Jacobi theta
functional equation and explicit algebra, as the single theorem `CM24.igusaCMValue24_field :
HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24`. The fold (`ZInQKernel/OneProof/H/TailZ18.lean`) added the
next bundle generation without that field, filled it with the theorem, and switched `frozenTarget`; the
hypothesis left the list.

## Where things are

* [OPEN.md](OPEN.md): the open hypotheses (generated; do not edit).
* [open-statements.json](open-statements.json): the same, as data, read off the Lean build by
  `scripts/one_proof/OpenStatements.lean`.
* [kinds.tsv](kinds.tsv): the classification of each hypothesis (LEAF or GLUE, kind, flag, source, review). The
  counts in OPEN.md and in the fold reports come from it.
* [claims.tsv](claims.tsv): who holds what. To claim a hypothesis, comment `Claiming <field> at <commit>` on
  [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14) or open a draft pull request that links #14;
  claims.tsv is regenerated from the claim lines (`scripts/claims/`).
* [reviews.tsv](reviews.tsv): statement checks against the printed sources, with verdicts and rulings.
* [credits.tsv](credits.tsv): who contributed what (proofs, reductions, statement checks and fixes, reviews,
  setup), and in which fold.
* [fold-queue.tsv](fold-queue.tsv): merged contributions waiting for the next fold.
* [frontier-crosswalk.tsv](frontier-crosswalk.tsv): frontier IDs (H-101, T-3, Z-1) mapped to field names.
* [pages-wanted.md](pages-wanted.md): printed pages that someone needs to read (generated from the flags).
* [STATEMENT-CHECKS.md](STATEMENT-CHECKS.md): checking a statement against its printed source, no Lean needed.
* `scripts/one_proof/render_open.py`: regenerates OPEN.md (`--check` fails if a fold changed the hypotheses
  without updating kinds.tsv).
* `scripts/one_proof/sandbox/`: the isolated discharge check the project runs on pull requests, through
  `.github/workflows/contrib-discharges.yml`.
* `scripts/claims/`: reads the claim lines and regenerates claims.tsv.
* `docs/research/leaf-fold*.md`: the fold reports, with what each fold removed and added.

## After a fold (for the integrator)

1. Regenerate `open-statements.json` (`scripts/one_proof/OpenStatements.lean`).
2. Run `scratch/contrib-kit/DischargesTest.lean` and save its output to `scratch/contrib-kit/DischargesTest-output.txt`.
3. Check the new kinds.tsv rows: autofold.py gives each new leaf a flag_class and the area_issue of the field it
   replaces, and flags a published leaf with no flag as unread; add packet, label and tier where they apply.
4. Update the ledgers: the folded rows' status in fold-queue.tsv, a credits.tsv row (with fold and commit) for
   each folded contribution, and any recorded readings in reviews.tsv.
5. Run `scripts/one_proof/render_open.py`, then `scripts/one_proof/render_open.py --check` with
   `ONE_PROOF_HYGIENE_FILE` naming the file of site-specific patterns (see the comment above `HYGIENE` in the
   script).

## Who answers

Replies, reviews and posted checks from the project may be written by AI agents that the project runs; each one
carries a note saying so. Jack McCarthy is accountable for them.
