# sga1-etale (fleet note)

**Result: `UnifTopology.SmoothComplexManifoldAn` is proved** from one new leaf, the étale clause of SGA 1 XII 3.1 over
`analyticTopology` (`SGA1Etale.SGA1_XII_3_1_Etale`). The leaf assumes `U` is affine and `ℂ[x₁..xₙ] → Γ(U)` is étale.
It concludes (1) that `Q ↦ (fᵢ(Q))` is a local homeomorphism `U(ℂ) → ℂⁿ` near each point and (2) that every
regular function on `U` is locally analytic in the `fᵢ`. The hypothesis stays Mathlib's `Smooth`, with no bridge
to nonsingularity. `ConnectedConnectedAn` is replaced by `ConnectedPreconnectedAn` (`PreconnectedSpace`, Bourbaki's
*connexe*), and `Nonempty X(ℂ)` is proved by the Nullstellensatz for every proper irreducible `X`.

What compiles (VERIFIED, standard axioms only):
- `ZInQKernel/Contrib/OneProof/SmoothComplexManifoldEtale.lean` (26 KB; imports `UniformizationTopology`):
  - `smoothComplexManifoldAn_of_etale`
  - `uniformizationLeafAll_of_etale (hM) (hL : SGA1_XII_3_1_Etale) (hPC : ProperCompactAn) (hCC : ConnectedPreconnectedAn)`
- The glue is all proved:
  - smooth ⇒ étale charts, from Mathlib's `IsStandardSmooth.exists_etale_mvPolynomial`, which is already in the pin;
  - étale charts restrict to basic opens;
  - ℂ-points exist in nonempty opens;
  - dimension invariance via inverse derivatives, so irreducible ⇒ one `n`;
  - the ChartedSpace, IsManifold ω, holomorphy of regular functions, and local diffeomorphisms.
- `#discharges` gives `uniformizationLeafAll` by `SGA1Etale.uniformizationLeafAll_of_etale`, which still assumes
  `MumfordComplexTorus`, `SGA1_XII_3_1_Etale`, `ProperCompactAn` and `ConnectedPreconnectedAn`
  (`scratch/sga1-etale/discharges.txt`).
- The autofold spec is `scratch/sga1-etale/autofold.json`. Its dry run exits 0 with 46/10 → 49/10 (the field is
  still LEAF in `kinds.tsv`). That is -1 GLUE compared with unif-topology's fold if `SmoothComplexManifoldAn` is
  rated GLUE. The dry-run module compiles and `sixContactMin_of_open30` has standard axioms.

What remains:
- Both new leaves are rated printed form (special cases) with locators UNVERIFIED. Half (2) of the étale leaf
  also uses XII 1.1's morphism `X^an → X` (regular functions become holomorphic, with the same values).
- Someone should read SGA 1 XII to confirm that 3.1 lists *étale* and that étale analytic means local isomorphism.
- The rows for `locators.md` are proposed in the report, not added.
- Fold this spec instead of unif-topology's (it needs unif-printed's and unif-topology's files in the tree).

Report: `docs/research/sga1-etale.md`.
