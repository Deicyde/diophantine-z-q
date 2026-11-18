# kolyv-weil: the two cited inputs to Lemma 5.5

**Verdict.** BCDT Theorem A in form (6) supplies the conductor-level weak Weil
parametrization required in Kolyvagin's Theorem 1. The revised leaves use that
same predicate. Their rank-one consequence is exactly the input used by the
pole-completeness proof. This is a replacement of the two inputs to one call
in the headline; no existing declaration is edited.

Starting point (**VERIFIED**, Git): `a04588b4f`, the head of fork PR #90.
The refreshed `origin/main` lacked the PR's pole-completeness modules when
work began. Previous source reading: [fork issue #83, AI reading](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6962416523),
as recorded in `PoleS12/Leaves.lean` L40–62. No print was fetched or reread.

## Manuscript and leaf ratings

**VERIFIED (manuscript and prior page audit).** In `lem:forward-rank`
(`diophantine_zq.tex` L1086–1109), the step at L1092 invokes **BCDT Theorem A**.
Its Introduction's condition (6) gives the nonconstant ℚ-morphism
$X_0(N_E) \to E$ that Kolyvagin assumes on p. 3 of MPI/90-69. Thus L1092
supplies the parametrization for L1093 as written. The separate modular
realization at `sec:rc` L1779–1787 is consistent with this reading. Lemma 5.5
covers both analytic ranks 0 and 1; the pole application uses only 1.

| New Prop | Rating | Reference and reason |
| --- | --- | --- |
| `KolyvWeil.BCDTThmA6` | **Printed form; CITED, published LEAF.** | BCDT author manuscript as cited at L1092 (bibliography L11150–54), Theorem A p. 1, specialized to the equivalent condition (6) p. 3; JAMS 14 (2001), 843–939. The level is the conductor and the nonconstant map is over ℚ. |
| `KolyvWeil.KolyvaginThm1Print` | **Printed form; CITED preprint leaf by the task ruling.** | MPI/90-69 (1990) as cited at L1093 (bibliography L11163–67), weak Weil hypothesis p. 3 and Theorem 1 p. 4. Uses both printed rank cases and retains finiteness of the full Sha. The cited version is a preprint, so it does not meet a strictly refereed-only LEAF count. |

## The objects in Lean

- **VERIFIED (source).** Mathlib's `CongruenceSubgroup.Gamma0` and
  modular forms describe the analytic level, not the algebraic curve over
  ℚ. `TYZGenus/X0.lean` works at level 32; `X0RatStructure` and
  `X0ModuliGalois` in `RingClassLattice.lean` L640–682 describe values and
  Galois action at algebraic points. None is used. The vendored Anthropic
  FLT `Definitions/Def_ModularCurve_X0.lean` L259–260 defines the general
  rational function field `ModularCurve.modularFunctionField`, via
  `ModularCurve.jq` and the substitution `ModularCurve.qExpand`. That is
  reused at every positive level.
- **STANDARD (on-the-spot function field presentation).** The two $j$-maps on
  $X_0(N)$ send a cyclic isogeny to the $j$-invariants of its source and
  target. They are defined over ℚ and expand as $j(q),j(q^N)$. At the
  geometric generic point the elliptic curve has no CM; two homomorphisms
  to the same target of the same degree differ at most by sign, since
  the homomorphism group for isogenous non-CM elliptic curves has rank one.
  Thus the pair of $j$-maps generically separates cyclic subgroups and
  generates the function field in characteristic zero. An embedding of
  function fields in the opposite direction defines a dominant rational
  map of curves, which extends across every point of the smooth source by
  the valuative criterion of properness. This justifies using
  `E.toAffine.FunctionField →ₐ[ℚ] X0FunctionField N` as the type of
  nonconstant ℚ-morphisms. Mathlib's `WeierstrassCurve.Affine.FunctionField`
  takes the fraction field of the affine chart, which is also the function
  field of the smooth projective Weierstrass curve. The identification
  with a separate scheme model and the extension theorem are explained
  here, rather than separately formalized.
- **STANDARD (on-the-spot conductor definition).** Take the local base change at
  each prime $p$, use Tau Ceti's `WeierstrassCurve.tateModuleGaloisRepresentation`
  and `WeierstrassCurve.nonempty_linearEquiv_tateModule`, and extend the
  matrices in a Tate basis from ℤₗ to ℚₗ. Use `PkgI4.GQp` for the local
  Galois group and `LadicCond.condExp` for the Artin conductor (codimension
  of inertia invariants plus Swan; Serre–Tate 1968 §2, as documented in
  `HDecomp/Conductor/LadicCond.lean`). These codimensions are invariant
  under basis change (compare the existing
  `CarayolLevel.condExp_eq_of_intertwine`). The auxiliary prime is 3 at $p=2$, and 2 otherwise,
  always distinct from $p$. Set the exponent of $p$ in $N$ equal to
  this rational value for every prime. This is the usual conductor
  characterization: the local exponents are nonnegative integers and
  vanish at good primes. `IsConductor.unique` proves uniqueness in Lean;
  existence independent of BCDT is not proved here. This definition
  uses the full wild term, including at 2 and 3, and does not take a
  map at an arbitrary level.
- **VERIFIED (source):** the remaining reused mathematical definitions
  are `SelmerTwoPower.sha` (local triviality at all places,
  `SelmerTwoPower.lean` L116–120), Mathlib's `WeierstrassCurve.LSeries`
  and `analyticOrderAt` as in `Manuscript.AnalyticRankOne`, and
  `Module.rank ℤ E.toAffine.Point`. The existing continuation condition
  is used also at rank zero, so Mathlib's zero default for a nonanalytic
  germ cannot witness rank zero. Standard Lean construction tools include
  `Module.Basis.ofEquivFun`, `LinearMap.toMatrixAlgEquiv`,
  `MonoidHom.toHomUnits`, `Matrix.GeneralLinearGroup.map`,
  `WeierstrassCurve.baseChange`, and `Nat.factorization`.
  No TYZ or Gross–Zagier calculation is used.

## Headline change and checks

**VERIFIED (source).** `Main.lean` L159–167 sends `hB` and `hK` to
`PoleS12.poleCompleteness_of_restrictedConverseGenuine_final`, then
`_mw` uses them only via `PoleS12.kolyvaginRankOne_of_printed`. The result
is `PoleRC.KolyvaginRankOne`, the exact rank implication in
`PoleRC.crm_of_restrictedConverse_proved`.

**On-the-spot (consumer GLUE).** Give Kolyvagin the map returned by BCDT
(6) and specialize to $r=1$; the old `AnalyticRankOne` supplies exactly
the same continuation. This even proves the old `hK` Prop from the pair
of new leaves: on input `IsModular E`, use the independently supplied
conductor-level map. The old `hB` coefficient statement is not proved
by this adapter; it was only used as that unused argument. Project to
the rank conclusion, then call the existing `crm_of_restrictedConverse_proved`
and `poleCompleteness_of_crm` with the same Selmer, Kummer, and
simultaneous-construction proofs. This is the old `_mw` body with
only the rank supplier changed.

The integration would replace the `hB : PoleS12.BCDTThmA` and
`hK : PoleS12.KolyvaginThm1` binders of `ZInQ.OneProof.frozenTarget`
with `hB6 : KolyvWeil.BCDTThmA6` and
`hKPrint : KolyvWeil.KolyvaginThm1Print`, and change its sole pole call
to `KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print`.
The H bundles, `hRC`, `h54`, and the result `ZInQ.FrozenTarget`
stay as written. The companion alternative
`PoleS12.poleCompleteness_of_restrictedConverseGenuine_leaves` is
outside this replacement; it has other Lemma 5.4 inputs.

**VERIFIED (tool).** The recipe is `scratch/kolyv-weil/autofold.json`.
Stock `autofold.py --dry-run` rejects `hK` as a non-bundle field.
It cannot replace a pair of top-level binders. The spec records the exact
`hK` proof and manual call and binder replacement separately. Run
`python3 scratch/kolyv-weil/preview_fold.py` to see the proposed
import, binders and pole call as a diff without touching `Main.lean`.

## Known issues

- The old `KolyvaginThm1` had a weaker premise (a matching cusp form at
  some level) than the one on p. 3 of the preprint. That statement should
  not be assigned directly to the print. The new adapter proves it using
  **both** sources, without a cusp form to parametrization conversion.
- The task's quoted “CST Thm 1.1” is not the citation in `lem:forward-rank`.
  CST is cited separately at L2428 and L8269. This task uses BCDT as
  specified in the detailed assignment and in the manuscript at L1092.
  No replacement source is used.
- The jump to Sha[2] = 0 at tex L1111–1113 uses the earlier Kummer count
  $r+\dim\Sha[2]=1$ (L1077), which together with rank one suffices.
  Finiteness alone does not give this jump. The existing Lean consumer
  uses the parallel cardinality argument through `descentGlueM`, so
  projecting to rank leaves that proof as it stands.
