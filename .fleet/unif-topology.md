# unif-topology (final)

**Proved (VERIFIED, compiled; axioms propext, Classical.choice, Quot.sound).** In
`ZInQKernel/Contrib/OneProof/UniformizationTopology.lean`, which imports unif-printed's module (merged cleanly
from wip/unif-printed 9c2e1809):

- `UnifTopology.exists_homeomorph_zeroLocus` (with `induced_classicalTopology_eq`, `isEmbedding_coord`,
  `range_coord`): for `U` affine and `f : Fin k → Γ(X,U)` generating `Γ(X,U)` as a ℂ-algebra, `P ↦ (fᵢ(P))` is a
  homeomorphism from `U(ℂ)` (unif-printed's `classicalTopology`) onto `V(I) ⊂ ℂ^k` with the subspace topology.
- `classicalTopology_eq_gluedTopology`: every family of affine charts covering `X(ℂ)` gives the classical topology.
- `classicalTopology_eq_analyticTopology [LocallyOfFiniteType X.hom] : classicalTopology X = analyticTopology X`.
  `analyticTopology` is the textbook definition (affine charts with the subspace topology of ℂ^k, glued).
- The three dictionary leaves are restated over `analyticTopology` (`SmoothComplexManifoldAn`, `ProperCompactAn`,
  `ConnectedConnectedAn`), each proved `↔` unif-printed's leaf. The main theorem is
  `uniformizationLeafAll_of_analytic (hM : MumfordComplexTorus) (hMan : SmoothComplexManifoldAn)
  (hPC : ProperCompactAn) (hCC : ConnectedConnectedAn) : UniformizationLeafAll`.

**#discharges:** `DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by
UnifTopology.uniformizationLeafAll_of_analytic`. It still assumes the four leaves above, axioms standard
("63 open hypotheses, 1884 theorems checked, 10 discharge one"; scratch/unif-topology/discharges.txt).

**Fold:** `scratch/unif-topology/autofold.json` (four published leaves into the textbook bundle). The dry run exits
0 and prints "46/10 on 56 -> 49/10 on 59". Against the re-rated count (field GLUE) it is 46/11 -> 49/10, i.e. -1
GLUE. The dry-run module compiles. Rating: all four leaves are printed form, and the topology reading risk is
closed. Alternative: keep unif-printed's spec and rate its leaves printed via `classicalTopology_eq_analyticTopology`.

**Remains:** nothing for the topology. These pre-existing weakenings in `SmoothComplexManifold` are weaker than the
print and are not part of this task: `∃ n` chart dimension, "some regular functions" as coordinates. Report:
docs/research/unif-topology.md.
