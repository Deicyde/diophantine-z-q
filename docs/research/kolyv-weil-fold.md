# kolyv-weil-fold: headline swap on the Cassels–Tate route

The fold replaces the two rank-route inputs of `ZInQ.OneProof.frozenTarget`
with the conductor-level weak Weil parametrization and Kolyvagin's Theorem 1
in printed form. The spliced `Main.lean` built on `dcc3d7723` with only the
three standard axioms. It retains the Cassels–Tate route to Lemma 5.4 and the
existing H proof. Both replacement inputs count as GLUE under the current rule.

**VERIFIED (Git and source).** The seven kolyv-weil commits were cherry-picked
onto fork main `dcc3d7723`; the base's `Main.lean` and board files are left to
the integrator. The proposed change to `frozenTarget` is in
[main-splice.patch](../../scratch/kolyv-weil-fold/main-splice.patch).
It keeps `r t l hRC hCT`, calls `sixContactMin_of_open84 r t l` as before,
and concludes `ZInQ.FrozenTarget`. It removes `hB` and `hK` from the
headline and adds `hB6` and `hKPrint`. The other changed consumer is
`KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print`, which now
takes `CasselsTatePairingCurves` in place of `Lemma54` to match main.
The pairing still supplies the square property and hence Lemma 5.4.
Only the rank supplier in the unfolded main pole proof changes, to
`kolyvaginRankOne_of_prints`.

**On-the-spot (proved Lean GLUE).** Specialize Kolyvagin at analytic rank
one, and pass the weak Weil map from `hB6`. The analytic continuation
assumption is the same one in the old `AnalyticRankOne`. This gives rank one
and finite Sha, so `kolyvaginThm1_of_prints` has exactly the old `hK` as
its conclusion, even though it does not need the old `IsModular` premise.
The pole proof needs only the rank projection. The old `hB` only supplied
that premise, so it leaves by bypass, without a separate proof of
`PoleS12.BCDTThmA`. The on-the-spot explanations of the function field and
conductor encodings are in [the original report](kolyv-weil.md#the-objects-in-lean).

**VERIFIED (manuscript).** No manuscript step beyond kolyv-weil's
`lem:forward-rank`, tex L1086–1113, is changed or used as a new premise.

## Known issues

| Headline binder | Print status and rating |
| --- | --- |
| `hB6 : KolyvWeil.BCDTThmA6` | **Consequence, GLUE/GLUE.** BCDT's cited author manuscript, Theorem A p. 1 and Introduction condition (6) p. 3, gives a ℚ-morphism from `X₁(N_E)`. The Lean Prop asks for a nonconstant ℚ-morphism from `X₀(N_E)`. |
| `hKPrint : KolyvWeil.KolyvaginThm1Print` | **Printed form, GLUE/GLUE pending the owner's ruling.** Kolyvagin, MPIM preprint MPI/90-69 (1990), Theorem 1 p. 4 with the weak Weil hypothesis on p. 3. The Lean statement retains both analytic ranks 0 and 1 and finiteness of the full Sha. The cited print is unrefereed. |

**VERIFIED (earlier page readings).** The BCDT mismatch is recorded in the
[issue #83 reading](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6962416523),
the [A066 audit](../theorem-application-audit/evidence/parallel-forward-modularity-report.md#L50)
and the [A070 second review](../theorem-application-audit/evidence/parallel-theta-local-a070-second-review.md#L14).
The Kolyvagin locator and weak Weil premise come from the issue #83 reading.
No source was fetched.

**STANDARD (the cited realization).** Going to `X₀(N_E)` uses trivial
nebentypus, Shimura's quotient of `J₀(N_E)`, and Faltings' isogeny theorem.
The manuscript takes this step in `sec:rc`, tex L1779–1784, via Milne,
*Modular functions and modular forms* v1.31, Theorem 11.19 and Remark 11.18
(p. 117 in the A070 review); L1785–1786 gives the composition with the
based map to the Jacobian. Thus L1092 supplies Kolyvagin's input **with an
implicit standard step**. This fold leaves the whole `X₀(N_E)` consequence
as a GLUE input. The literal printed BCDT condition (6) uses `X₁` and
cannot be passed directly to Kolyvagin.

## Counts

**VERIFIED (computed from main's `docs/one-proof/kinds.tsv` and the two
replacement ratings).** H strict **5 LEAF / 26 GLUE on 31** before and after
under either ruling. Each cell shows LEAF / GLUE.

| Scenario | H (31) | Other headline binders (4) | All headline hypotheses (35) |
| --- | ---: | ---: | ---: |
| Main, before (either ruling) | 5 / 26 | 1 / 3 | 6 / 29 |
| After, current rule (strict and strictest) | 5 / 26 | 1 / 3 | 6 / 29 |
| After, if the owner accepts the preprint as LEAF (strict) | 5 / 26 | 2 / 2 | 7 / 28 |

In the acceptance scenario the strictest counts stay at 5 / 26, 1 / 3 and
6 / 29 if that column continues to require refereeing. If the ruling also
admits the preprint in strictest, that column takes the same counts as
strict. The manual fold spec is [autofold.json](../../scratch/kolyv-weil-fold/autofold.json);
stock autofold only handles H bundle fields. Neither the kinds table nor
the generated board has been edited.

## Imports added by the splice

**VERIFIED (compiled import comparison).** The
[Lean checker](../../scratch/kolyv-weil-fold/CheckImports.lean) imports
only `Main` and reads all modules loaded into its environment. The closure
increased from 18,907 to 18,915, with no removals. The recursive source
comparison gave the same [eight additions](../../scratch/kolyv-weil-fold/imports-added.txt).
The Tau Ceti names below use the prefix `ZInQKernel.Contrib.TauCeti.`.

- `ZInQKernel.Contrib.OneProof.KolyvWeil.Leaves`
- `ZInQKernel.Contrib.OneProof.KolyvWeil.Parametrization`
- `ZInQKernel.Contrib.OneProof.KolyvWeil.PoleCompleteness`
- `Algebra.Module.Torsion.TateModule`
- `Algebra.Ring.GeomSum`
- `AlgebraicGeometry.EllipticCurve.TateModule.Basic`
- `AlgebraicGeometry.EllipticCurve.TateModule.Galois`
- `RingTheory.RootsOfUnity.Congruence`

All five Tau Ceti files are in `scratch/selmer-2infty/vendor-new.txt`;
the notice assigns that batch to Tau Ceti
`5a01f5fe3621126cccf9ba22e700493cbc7b7156`. The
[pin table](../../scratch/kolyv-weil-fold/tauceti-pin.tsv) records each
`dcc3d7723` blob, checked byte for byte against its existing vendoring
commit `4a063a7f2`. No new files were vendored. In particular,
`Def_ModularCurve_X0`, `LadicCond` and `CasselsTatePairing` are
already in the base closure.

## Build and checks

**VERIFIED (Lean 4.35.0).** With one Lean compiler process at a time and
`LEAN_NUM_THREADS=8`, the unmodified headline, `Discharges`, and the new
pole module built in [16,552 Lake jobs](../../scratch/kolyv-weil-fold/baseline-build.txt).
`lake env lean scratch/kolyv-weil-fold/Original.lean` checked the verbatim
`IsModular`, `BCDTThmA` and `KolyvaginThm1` copies against main by `rfl`.
With the splice applied to the actual `ZInQKernel/OneProof/Main.lean`,
`lake build +ZInQKernel.OneProof.Main` ran offline and succeeded in
[16,551 Lake jobs](../../scratch/kolyv-weil-fold/spliced-build.txt).
The build's `#print axioms ZInQ.OneProof.frozenTarget` reports
`[propext, Classical.choice, Quot.sound]`. The adapter and pole supplier
have the same axiom set.

[CheckHeadline.lean](../../scratch/kolyv-weil-fold/CheckHeadline.lean)
imports the real built `Main` and runs the stock `#discharges` command.
On the [baseline](../../scratch/kolyv-weil-fold/baseline-discharges.txt),
it reports 35 open hypotheses, 15,028 candidates and 391 matches. The
rank adapter discharges `[hK]` with exactly `BCDTThmA6` and
`KolyvaginThm1Print` still assumed. On the
[spliced headline](../../scratch/kolyv-weil-fold/spliced-discharges.txt),
it reports 35 open hypotheses, 15,028 candidates and 390 matches. The
`[hK]` match is the only one removed; neither replacement input is
discharged. The printed theorem type confirms both new hypotheses and the
unchanged result.

The patch is the diff of the compiled splice. `Main.lean` was restored
after the checks. A later `origin/main` already has `TailZ92` and
`sixContactMin_of_open85`; when folding there, retain that H call and its
bundle, and port only the rank binders, pole call, import and documentation.
The build and counts above are for the requested `dcc3d7723` base.
