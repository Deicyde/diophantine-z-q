# sgr-split

**Result.** The added field `shimuraGoodReductionNoGuard` (`HDec.CurveSplitGR.ShimuraGoodReductionNoGuard`, rated
composite/GLUE) is proved in Lean from **one printed leaf**:
`SGRSplit.shimuraGoodReductionNoGuard_of_printed : ShimuraIntegralModelRep → ShimuraGoodReductionNoGuard`, in the
new file `ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean` (standard axioms). The leaf
`ShimuraIntegralModelRep` is the representability of the integral moduli problem: for `p > 324`, abelian surfaces
with QM by the discriminant-6 maximal order and full level 3 (the kernel's `QMAbScheme`, r1univ-rigid) on
locally noetherian `ℤ_(p)`-schemes are classified by a proper smooth curve over `ℤ_(p)` (Kottwitz 1992 §5,
Buzzard 1997, Morita 1981; locators UNVERIFIED). So curve-split §3.6's "not statable today" no longer holds.
The NOS/Néron/BLR route cannot give the field (those leaves are about models of abelian varieties, not of the curve).

**Proved here (no new hypotheses):** the clause-by-clause glue (Yoneda for the Hecke clauses, uniqueness and
existence for the `ℚ̄`-bijection), fibres unique up to isomorphism (via `rigidityHom`), objects over a field as
`QMAbScheme`s over `Spec K`, fibres of a `QMAbScheme` at field points as objects, and three general facts:
abelian surfaces are smooth of relative dimension 2, smooth geometrically connected schemes over a field are
geometrically integral, `End` of an abelian variety is torsion-free in characteristic 0.

**Checks.** `#discharges`: the field discharged, still assumes `[SGRSplit.ShimuraIntegralModelRep]`
(`scratch/sgr-split/discharges.txt`). Autofold spec `scratch/sgr-split/autofold.json`: dry run strict
46/13 on 59 → 46/13 on 59 (no rise; the leaf is flagged pending reading so it counts GLUE), generated
`sixContactMin_of_open26` compiles with standard axioms.

**Remains.** A human reading of the leaf: whether Buzzard's/Morita's printed level structures cover level 3 at
`3 ∣ D` (Kottwitz's do), and the PEL-to-polarization-free comparison (relative Lemma P). If cleared, strict GLUE
drops to 12. The leaf also needs a row in `docs/research/locators.md` (not edited here). Report:
`docs/research/sgr-split.md`.
