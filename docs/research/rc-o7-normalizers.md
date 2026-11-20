# (O.7): the two orientation moves

The two one-place normalizers act on the supported orbits before any
parametrization by a quadratic class group. The local split normalizer
flips its level bit, acts on the ideal class by Atkin–Lehner, and multiplies
the orbit weight by the Atkin–Lehner sign. The division uniformizer flips
the last bit, acts on the class by the division uniformizer of the PM
geometry, and preserves the orbit weight. The fiber permutation is the
actual orbit move conjugated by the source and target fiber equivalences.
The assembly stage takes its weights from the aligned
`ThetaClose.actualPmLocal` and its class operations from `PMAdelic.geometry`.

## Statements and consumers

The namespace throughout is `ZInQ.Manuscript.RC.O7Normalizers`.
Write (Q=(z,y)) for an adelic representative and its affine generator,
(x=2y-1) for the trace-zero root, (K_q) for a one-place normalizer,
and (W) for the product of the norm character and Schwartz weight.

| Declaration | Statement and consumer |
| --- | --- |
| `AdelicPoint.eq_of_fields` | Two adelic pairs with equal representatives and generators are equal. |
| `root_injective`, `root_conj` | The map $y \mapsto 2y-1$ is injective and commutes with rational conjugation. |
| `rationalConj_apply`, `rationalConj_comp`, `atRep_root` | Rational conjugation is $y \mapsto uyu^{-1}$; its compositions multiply the conjugators in order. Passing to local coordinates commutes with (2y-1). |
| `pointRel_atRep` | Related pairs have local affine generators conjugate by a completed order unit. |
| `preservesOrder_single`, `inverse_conj_mem`, `PreservesOrder.inv`, `PreservesOrder.normalizes` | Normalizing the order at one place and taking identity elsewhere gives an adelic order normalizer. Its inverse is also one. Such adelic elements normalize the integral unit group. |
| `stepPoint_rel`, `stepPoint_class` | Right multiplication on the first coordinate respects the relation on pairs, and projects to `rightClassPerm` on ideal classes. |
| `pointOfSupport_root`, `pointOfSupport_generator`, `supportOfPoint_inverse` | At a chosen class representative the two conversions preserve the supported root and the actual affine generator, and the round trip recovers the pair. |
| `chosen_pointRel_iff`, `pointRel_class`, `pointOfSupport_class` | At the chosen representative the pair relation is exactly the class unit orbit relation. It preserves the ideal class, and the conversion of a supported root has its original class. |
| `adelicOrbitsEquiv`, `orbitMove_rel`, `orbitMove_class` | The supported orbit set is the quotient of the adelic pairs. The resulting move is a permutation; a chosen output pair is related to the right translate of the input; its class is `rightClassPerm`. Supplies the class part of both moves. |
| `splitUnit_chart`, `divisionUnit_chart`, `map_rightConj` | The two transported units map to the prescribed local matrix and division uniformizer. Chart maps commute with right conjugation. |
| `splitUnit_mem`, `divisionUnit_mem`, `split_class`, `division_class` | These elements normalize the completed orders; their one-place right permutations give the existing `Adelic.atkin` and `Adelic.uniformizer`. |
| `swap_matrix`, `splitSwap_cast`, `splitSwap_trace`, `splitSwap_det`, `splitSwap_level` | Matrix conjugation exchanges the two diagonal entries. Its integral version casts to that conjugation and preserves trace and determinant. On trace-one generators it sends the level quotient root (r) to (1-r). |
| `splitSwap_weight`, `division_red_neg` | Reflection of the split root (a) gives (2(1-a)-1=-(2a-1)), so the weight gains `χ (-1)`. On trace-zero division roots the residue Frobenius negates the root. |
| `generator_rel`, `label_rel`, `pointOrientation_rel`, `pointOrientation_actual` | Changing the representative conjugates each integral generator by a unit, hence preserves commutative residue labels. On the chosen pairs the resulting orientation is exactly `O7Orbits.orientation`. |
| `levelPrime_injective`, `splitAdele_order`, `divisionAdele_order`, `generator_away` | The level indexing has no repeats. The two one-place adeles normalize the order and fix the local generator at every other prime. |
| `splitAdele_chart`, `orderChart_cast`, `divisionOrderChart_compatible`, `divisionAdele_chart` | The actual integral charts give the integral split swap and the division order's uniformizer automorphism. |
| `splitLabel_distinct`, `divisionRoot_trace`, `divisionLabel_distinct`, `residueBit_flip` | The split discriminant test gives distinct complementary residues, the division generator has trace zero, and nonzero discriminant residue gives distinct opposite roots. Swapping distinct roots negates the Boolean label. |
| `affine_map` | Ring homomorphisms preserve the affine trace-zero expression $2y-1$. |
| `split_orientation`, `division_orientation` | The actual orbit permutations flip just the appropriate level coordinate or the last coordinate. Supplies the orientation property used to define `perm`. |
| `splitUnit_valuation`, `divisionUnit_valuation`, `discriminant_product`, `norm_single` | The reduced norm valuations are (v_p(N)) and one, respectively. The discriminant character is the product over the primes of (m), also at two by the supplementary law. At a prime unramified for the character a one-place reduced norm of valuation (e) has value (χ_{h_*}(p)^e). |
| `pointWeight_rel`, `stepPoint_schwartz`, `stepPoint_weight` | For related pairs the combined weight agrees, by `ThetaJoin.weightedAt_change`). A one-place change with Schwartz factor (s) multiplies the global Schwartz factor by (s) and the combined weight by $\chi(\mathrm{Nrd}(K_q))s$. |
| `splitFactor_on_point`, `split_schwartz` | In the actual affine chart the split factor is `levelWeight`; the right normalizer multiplies it by (α_p(-1)), including at two. |
| `division_schwartz`, `division_local_schwartz` | The transported division Schwartz function on trace-zero vectors acquires (-1) by `LocalDivision.divisionSchwartz_uniformizer`, the existing $(-1/\ell_0)=-1$ rule. |
| `geometrySigns_spec`, `cusp_of_multiple` | The integer units chosen from `PMAdelic.SpecialFibre.atkinSign_eq` recover the integer signs at each level prime. A multiple of a fixed annihilator of the cusp translations kills the same translations. Supplies `cusp`. |
| `actualBridge`, `actual_disc_neg`, `actual_disc_split`, `actual_disc_detecting` | The aligned weights on the full filtered sphere have support exactly on the half-integral generators; (Dh_*) is negative, satisfies the level split tests, and is nonzero modulo the division prime. |
| `supportOrbitWeight_mk`, `orbitWeight_eq_supportOrbitWeight`, `actual_weight_mk` | The orbit weight can be read on any supported root in the orbit. The fiber version is the host's `orbitWeight`; on the actual stage it is the adelic product evaluated at the chosen representative. |
| `atkinMove_class`, `uniformizerMove_class` | The class of each actual moved orbit is exactly `PM.Geometry.atkin` or `PM.Geometry.uniformizer` from the PMAdelic construction. Supplies `atkin_class`, `uniformizer_class`. |
| `level_symbol`, `actual_atkin_weight`, `actual_uniformizer_weight` | The fixed discriminant is split at the level. At $p^e\Vert N$ the product of the parity multiplier and the norm multiplier is the aligned geometry sign. At (ℓ_0) the norm multiplier is (-1) by `DiscriminantData.inert`, canceling the Schwartz sign. Supplies `atkin_weight`, `uniformizer_weight`. |
| `flip_involutive`, `fiberPerm_apply`, `normalizers`, `ofPicardFibers` | Restrict the orbit permutation to the source and target fibers. Applying the target fiber map to `fiberPerm` gives the moved orbit. The constructors fill `DatumAt.moves`, with `p, prime, exponent` from the indexed prime divisors of (N). |

The pair model, descent, integral matrix calculation, supplementary
norm calculation, and fiber bookkeeping are on-the-spot (provenance
(c)). The norm character here is the one in the actual theta input:
remove the positive rational part of the reduced norm idèle, then use
the product of the quadratic characters of the remaining units at
the primes of $m$. For the one-place idèle of valuation $e$ at $p$,
the removed part is $p^e$. At each prime of $m$ the resulting unit is
$p^{-e}$; the quadratic character of its inverse is the same. The
product is $\chi_{h_*}(p)^e$. This calculation excludes the unit
part at $p$ because $p$ is prime to $m$.

At a level prime, `ThetaClose.levelRoots_parity` is
`LevelRoots.ParityAt` over the actual coefficient ring. It supplies
$\alpha_p(-1)=w_{p^e}\chi_{h_*}(p)^e$. Multiplying by the norm factor
leaves $w_{p^e}$ (the formal proof uses the fixed discriminant's level
split conditions). `PMAdelic.SpecialFibre.atkinSign_eq` identifies the
geometry sign as $1$ or $-1$. At the division prime, the Schwartz sign
comes from `LocalDivision.divisionSchwartz_uniformizer`, since
$\ell_0\equiv3\pmod4$; the norm factor is $-1$ by
`DiscriminantData.inert`. The detector supplies its own plus sign
through `PM.lam_frob`, used in `PM.P_uniformizer` and
`PM.lift_uniformizer_dvd`. The cuspidal term and
`PM.lift_atkin_dvd` are likewise inherited. No new printed leaves.

## Remaining hypotheses and owners

| Owner | Exact input and why it is weaker than (O.7) |
| --- | --- |
| Fixed discriminant, detector, and level data | (N>0), (\ell_0) prime and 3 modulo 4 with (\gcd(N,\ell_0)=1), `DiscriminantData m N ell`, precision (M), and the two existing filter predicates `RequestedIndices` and `LevelFilter`. Here the two filter predicates assert $D>0$, squarefree and prime to $m$, with $(D/\ell_0)=1$, $-mD\equiv1\bmod 8$, $D$ prime to $N$, and the split test at every odd prime of $N$. These are arithmetic restrictions on the parameters; they contain no orbit sum or point evaluation. |
| PM geometry and detector handoff | The existing `PMAdelic.JetchevKane`, `PMAdelic.SpecialFibre`, and `PM.Evaluation`, with their field and elliptic curve instances, and an integer lift `PM.IsLift` (the canonical `PM.valLift` is available). These compare class operators and define an actual detector; they say nothing about the weights at a discriminant or their global contribution. |
| Fixed level character choice | The integer sign used in the theta characters equals the geometry sign at each indexed level prime. This can be wired by `geometrySigns_spec`. This identifies two inputs to the calculation before choosing any orbit or (D). |
| Multiplier and modular parametrization handoff | `∀ i, L • G.cusp (p i) = 0`. It follows from the inherited annihilator of the actual cusp translations and its divisibility into (L), by `cusp_of_multiple`. This is an equality on finitely many fixed reduced cusp points and involves no CM point or weight. |
| Picard fibers | `∀ t, Cl ≃ {P : OrbitSet s.visibility (index s D) // orientation s B P = t}` for the quadratic class group. For the general constructor, `A.orientation = orientation s B` identifies the orientation function; with `ofPicardFibers` this is definitional. This asserts a parametrization of sets, without any weighting or point values. |

The other fields of `DatumAt` are outside this change. The quadratic
basis and optimal embedding data supply the stabilizer input. The
torus weight task supplies its two pointwise transports and their
power-of-two orders, before any point is evaluated. The reference
reduction and point-value tasks supply the selector and the two
pointwise CM inputs at tex 9265–9279 and 8476–8479; they compare
individual points and do not assert the weighted coefficient
comparison. The integral representative and contraction of divisibility
belong to the downstream coefficient assembly. In particular
`Normalizers.orientation` can be applied once the independent torus
weights are supplied; it compares the tuple sums at the original
precision, before the reference reduction and (O.7).

## Validation

Each new Lean file passed `lake env lean` separately. `scratch/rc-o7-normalizers/Axioms.lean` checks all 81 new theorems (including private helpers) and 41 other declarations.

| File | Theorems audited | Other declarations audited |
| --- | ---: | ---: |
| `Local.lean` | 14 | 5 |
| `Transport.lean` | 21 | 14 |
| `Norm.lean` | 4 | 0 |
| `Orientation.lean` | 19 | 6 |
| `Weights.lean` | 7 | 1 |
| `Assembly.lean` | 16 | 15 |

The only dependencies are `propext`, `Classical.choice`, and
`Quot.sound`. These are the complete results by axiom set:

- No axioms: `rightConj`.
- `propext`: `detectingPrime`, `map_rightConj`, `inverse_conj_mem`.
- `propext`, `Quot.sound`: `flip_involutive`, `fiberPerm`, `fiberPerm_apply`.
- `propext`, `Classical.choice`, `Quot.sound`: all 115 other audited declarations.

## Known issues

- Inherited citation scope issue, tex 8468–8474: the source audit in
  `docs/research/pm-adelic-join.md` records Jetchev–Kane's level hypothesis
  as `N > 1`. The comparison already present in Lean is a named input;
  its use does not assert a citation at level one.
- The inherited `ThetaJoin.FilteredSupport` and `RequestedSupport` are
  misparenthesized; the intended unfiltered support statement also has
  the counterexample recorded in `docs/research/rc-theta-close.md`.
  The support bridge here uses `ThetaClose.actualFilteredSupport`.

## Manuscript check

- 8278–8296 — gap filled: pass from the annihilator of the actual reduced cusps to its multiple (L).
- 8465–8468 — OK: use the existing adelic ideal class equivalence and the chosen adelic representative of the chosen ideal.
- 8468–8474 — error: the cited scope omits level one; see Known issues.
- 8487–8492 — OK: use the PMAdelic class actions, affine Atkin–Lehner relation, and Frobenius comparison supplied by that construction.
- 8499–8534 — OK: the trace-one split coordinate and the character of (2a-1) work for the dyadic factor as well.
- 8552–8576 — OK: the division sign and the order-unit covariance are those of the existing local factors.
- 9105–9108, 9119–9135 — OK: apply the aligned support bridge under the original filter.
- 9136–9148 — OK: read the existing split and division labels at the chosen representatives.
- 9329–9335 — gap filled: prove the normalizer descends to the actual orbit, retaining its one-place action through the change of representative.
- 9335–9340 — OK: apply the prescribed parity and multiply the reduced norm character and actual geometry sign at the same exponent.
- 9342–9346 — OK: residue Frobenius negates the trace-zero division root; the two negative weight factors cancel.
- 9347–9358 — OK: the same right division uniformizer is the class operation used by the fixed Frobenius-invariant detector.
- 9359–9364 — gap filled: compute the norm character via its actual ramified unit product after removing the rational part. This also checks the dyadic supplementary factor.
