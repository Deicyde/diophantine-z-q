# Contributed Lean modules (`ZInQKernel/Contrib/`)

One row per group under `ZInQKernel/Contrib/`. `ZInQKernel/Contrib/AllContrib.lean` imports 9214 of the 13046 modules,
directly or through other modules, and no module of the eight groups `CloudB3E1Dihedral`, `CloudB3E1Moving`,
`CloudB3E1NoCM`, `CloudB3E1RingClass`, `CloudB3E1TameKummer`, `CloudB3E1Torsion`, `CloudB3E2Norm` and `CloudR2Raynaud`;
no CI job builds it. The description is the first heading of the group's main module (named in the table); for the
twelve main modules that have no heading, marked †, it is written from the module's main theorem. For what each
result does for the proof, see `docs/research/frontier.md` (open Props) and `docs/research/README.md` (one line per
research note). Generated from the modules at d415070d4.

| group | modules | main module | description |
|---|---|---|---|
| `AbsFrob` | 3 | `AbsFrob/Basic.lean` | afr-absfrob: the absolute Frobenius of a scheme of characteristic `p` |
| `AbVarBC` | 12 | `AbVarBC/Main.lean` | Base change of abelian varieties: main results |
| `AVB1` | 3 | `AVB1/AlgClosed.lean` | av-b1, II: T6 and T7 over any field from Mumford's statements over an algebraically closed field |
| `AVB2` | 1 | `AVB2/SerreLemma.lean` | Serre's lemma at level 3, ring and lattice forms (task av-b2) |
| `BrauerT14T15` | 8 | `BrauerT14T15/Main.lean` | Leaves T14 and T15 (cochain forms) from Tau Ceti: summary |
| `Chebotarev` | 3 | `Chebotarev/Exists.lean` | Leaf I6.4 / T18 (Chebotarev, existence form), proved |
| `CloudB2X0Transitive` | 667 | `CloudB2X0Transitive/ModularEquation.lean` | `X₀(N)`-transitivity from the modular equation for the generic curve (flt-cqj) |
| `CloudB3E1Dihedral` | 4 | `CloudB3E1Dihedral/XiConjNoPrint.lean` | `xiConj` without the print, end to end |
| `CloudB3E1Moving` | 1 | `CloudB3E1Moving/MovingRealization.lean` | The moving character is trivial at `2N`: from the interface to the genuine decomposition groups |
| `CloudB3E1NoCM` | 3 | `CloudB3E1NoCM/Curve1.lean` | `E_ℓ` has no CM, from the single curve `y² = x(x − 1)(x + 3)` |
| `CloudB3E1RingClass` | 42 | `CloudB3E1RingClass/CurveData.lean` | The curve-specific moving data for the final companion and an admissible family |
| `CloudB3E1TameKummer` | 1 | `CloudB3E1TameKummer/TameKummerPlace.lean` | The tame comparison at a place of a number field, from the literature alone |
| `CloudB3E1Torsion` | 14 | `CloudB3E1Torsion/KmLamUnit.lean` | The Knudsen–Mumford coordinate changes by a unit along a homotopy equivalence |
| `CloudB3E2Norm` | 70 | `CloudB3E2Norm/H20PresClass.lean` | The Kummer classes of the actual points as presentation classes, and their norm identity |
| `CloudB3RC53` | 420 | `CloudB3RC53/Assembly.lean` | RC53 blueprint: the assembly of Theorem 5.3 from the printed leaves and the nodes |
| `CloudB3W11AxCompletion` | 6 | `CloudB3W11AxCompletion/AxClosure.lean` | Unconditional Ax–Sen–Tate closure for arbitrary intermediate fields |
| `CloudB3W11AxEstimate` | 1 | `CloudB3W11AxEstimate/AxApprox.lean` | Ax's uniform algebraic approximation estimate |
| `CloudB3W11Cyclotomic` | 3 | `CloudB3W11Cyclotomic/InfiniteImage.lean` | The cyclotomic character has infinite image on `Gal(ℚ̄_p/K)`, and algebraic twisted invariants vanish |
| `CloudB3W11TateTrace` | 12 | `CloudB3W11TateTrace/TwistWholeGroup.lean` | Whole-group nonzero-twist vanishing in the genuine `C_p` |
| `CloudB3W11TwistDescent` | 2 | `CloudB3W11TwistDescent/TateAdapter.lean` | Exact finite-field Tate twist adapter |
| `CloudB3W16Cartier` | 63 | `CloudB3W16Cartier/SmoothCriterion.lean` | Stacks 04QN: locally of finite type over a characteristic-zero field with locally free differentials implies smooth † |
| `CloudB3W16Connected` | 10 | `CloudB3W16Connected/StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedPoint.lean` | Connected schemes over a field with a distinguished point |
| `CloudB3W16Dimension` | 86 | `CloudB3W16Dimension/StacksFrontier/AlgebraicGeometry/Groupoids/GroupSchemeProperties/Dimension.lean` | Dimension of a group scheme over a field |
| `CloudB3W16FiniteGroup` | 2 | `CloudB3W16FiniteGroup/TorsionByCard.lean` | Torsion subgroups with the cardinalities of a free `ℤ/n`-module |
| `CloudB3W16Torsion` | 1348 | `CloudB3W16Torsion/RelativeBridges.lean` | Bridge: an abelian variety's group object gives a commutative `RelativeGroupLaw`, with matching `n`-torsion points † |
| `CloudB3W17bAnalyticIdeal` | 6 | `CloudB3W17bAnalyticIdeal/PulledIdeal.lean` | The identity ideal pulled back through an analytic morphism: coherence and vanishing locus |
| `CloudB3W17bCanonicalImage` | 9 | `CloudB3W17bCanonicalImage/IsoSupport.lean` | `vanishingLocus` of a map into the unit sheaf of modules is invariant under source isomorphisms † |
| `CloudB3W17bGAGA` | 1 | `CloudB3W17bGAGA/CanonicalAnalyticGraph.lean` | From a strong uniformization, a lattice-killing analytic map descends to a homomorphism with closed compact graph † |
| `CloudB3W17bGraphScout` | 6 | `CloudB3W17bGraphScout/AlgebraicGraphTail.lean` | Point homomorphisms of complex abelian varieties with closed group-subscheme graph come from scheme morphisms † |
| `CloudB3W17bGraphScoutReverseIdeal` | 9 | `CloudB3W17bGraphScoutReverseIdeal/OriginalKernelGraph.lean` | Over ℂ: a point homomorphism of abelian varieties with Zariski-closed graph comes from a scheme morphism † |
| `CloudB3W17bIdentity` | 4 | `CloudB3W17bIdentity/PulledIdentity.lean` | The pulled identity ideal of the original abelian variety |
| `CloudB3W17bKernel` | 1 | `CloudB3W17bKernel/KernelMap.lean` | From uniformization data, an analytic homomorphism on `A × B` points whose kernel is the graph of `pointDescentHom` † |
| `CloudB3W17bNativeGlue` | 3 | `CloudB3W17bNativeGlue/OriginalPointRealization.lean` | Original point realisation of the actual local maps, and their global gluing |
| `CloudB3W17bOka` | 294 | `CloudB3W17bOka/Oka/Analytification/GAGA/ProjectiveGAGA3.lean` | GAGA-3 for projective schemes, and Serre's GAGA theorem |
| `CloudB3W17bOkaComparison` | 47 | `CloudB3W17bOkaComparison/AbVarNativeAnalytification.lean` | Actual Oka analytic morphisms of the ORIGINAL abelian-variety complex points |
| `CloudB3W17bProjectiveBridge` | 5 | `CloudB3W17bProjectiveBridge/OkaAdapter.lean` | Actual native abelian varieties are projective in Oka's scheme category |
| `CloudB3W17bReduced` | 26 | `CloudB3W17bReduced/ComplexProduct.lean` | The product of two reduced schemes over `Spec ℂ` is reduced, via ported Stacks perfect-field results † |
| `CloudB3W17GAGA` | 6 | `CloudB3W17GAGA/CanonicalOriginalPoints.lean` | Original complex points in the actual canonical models |
| `CloudB3W17Hodge` | 48 | `CloudB3W17Hodge/CptManifold.lean` | The complex points of a smooth complex scheme are an analytic manifold, on the kernel's carrier |
| `CloudB3W17Lattice` | 2 | `CloudB3W17Lattice/CompactQuotient.lean` | A discrete subgroup with compact quotient is a full lattice |
| `CloudB3W17LocalExp` | 4 | `CloudB3W17LocalExp/UnconditionalTorus.lean` | A compact connected commutative complex Lie group is a complex torus |
| `CloudB3W17ProperCompact` | 7 | `CloudB3W17ProperCompact/AbVarCompact.lean` | Analytic complex points of an abelian variety over ℂ are compact, via the integral proper case † |
| `CloudB3W17Realify` | 6 | `CloudB3W17Realify/ComplexExp.lean` | Global analytic exponential in a finite-dimensional commutative complex Lie group |
| `CloudB3W17Uniformization` | 11 | `CloudB3W17Uniformization/Uniformization.lean` | Unconditional exact H103 uniformization |
| `CloudR2CM` | 33 | `CloudR2CM/SerreTate/CMPotentialGoodFinal.lean` | `CMPotentialGood` from the existence of Néron models over Dedekind schemes |
| `CloudR2Hom` | 2 | `CloudR2Hom/C4SourcePort/ProjectiveEmbedding.lean` | A closed projective embedding of the actual PkgI3 abelian variety |
| `CloudR2NeronExistence` | 428 | `CloudR2NeronExistence/Henselian/Main.lean` | Re-export: abelian varieties over a henselian DVR's fraction field have commutative Néron models † |
| `CloudR2NOS` | 2326 | `CloudR2NOS/NOSSepGlue/Glue.lean` | Glue: Néron–Ogg–Shafarevich converse; inertia trivial on `A[m]` for infinitely many unit `m` gives good reduction † |
| `CloudR2Poincare` | 294 | `CloudR2Poincare/FinalUnconditional.lean` | H-72: unconditional `PoincareComplement` |
| `CloudR2Raynaud` | 11 | `CloudR2Raynaud/NativeLocalNeronModel.lean` | Native same-object local model, independent of pending C5 transport |
| `CloudW01Spread` | 102 | `CloudW01Spread/FinitePresentation.lean` | Finite presentation descends to a finite stage |
| `CloudW02Connectedness` | 137 | `CloudW02Connectedness/Basic.lean` | Zariski's connectedness theorem: proper `f` to a locally noetherian base with `𝒪_Y ≅ f_*𝒪_X` is geometrically connected † |
| `CloudW03NeronSurj` | 85 | `CloudW03NeronSurj/Main.lean` | H-76: the surjective Néron mapping property for abelian schemes over a DVR |
| `CloudW06PoincareRigidity` | 5 | `CloudW06PoincareRigidity/T11bExists.lean` | H-75: T11(b), rigidity, existence half (`T11bExists`), proved |
| `CloudW07JacobiansCurves` | 714 | `CloudW07JacobiansCurves/JacobianExists.lean` | cloud-w07: frontier row H-36, `LeafModCurves.JacobianExists ℚ`, proved |
| `CloudW08EigenformTwists` | 2 | `CloudW08EigenformTwists/EigenformTwist.lean` | H-33 proved: `PkgI4.EigenformTwist` |
| `CurvesG` | 3 | `CurvesG/CurveSplit.lean` | curves-g: `CurveOfFunctionFieldQNoPoint` (T38 without its point clause) from three textbook facts |
| `Different` | 4 | `Different/Bridge.lean` | Bridge from Tau Ceti's global different theory to the leaves of `Breaks.lean`; T20 proved |
| `Dim` | 11 | `Dim/Basic.lean` | Krull dimension of spaces and schemes: covers, isomorphisms, specializing maps |
| `FrobChain` | 10 | `FrobChain/Main.lean` | Frob chain, 10: the closed reductions |
| `FrobPieces` | 1 | `FrobPieces/SmoothGeomConnIntegral.lean` | frob-pieces: `SmoothGeomConnIntegral` (alg-frob-red's leaf candidate), proved |
| `G15` | 6 | `G15/Combined.lean` | G15: the three readings of the lower filtration agree |
| `G1Adelic` | 2 | `G1Adelic/Complements.lean` | G1-adelic over Mathlib's `𝔸ᶠ[ℤ, ℚ]`: complements |
| `G9` | 20 | `G9/G9.lean` | G9: N5's appendix lemma; `r` is de Rham with Hodge–Tate weights `0, −1` |
| `GaussFE` | 2 | `GaussFE/FunctionalEquation5.lean` | `ZInQ.Literature.FunctionalEquation5`, proved |
| `HeckeAll` | 4 | `HeckeAll/Continuation.lean` | `HeckeContinuation` for every `d ≠ 0`, from Gauss's point count |
| `HeckeFE` | 1 | `HeckeFE/Basic.lean` | Hecke's theory for `C_d : y² = x³ − d²x` over `ℤ[i]` |
| `HeightBC` | 16 | `HeightBC/Main.lean` | Height base change, XVI: the closed theorems |
| `HodgeBC2` | 1 | `HodgeBC2/ExtFrac.lean` | Exterior powers commute with passage to the fraction field (Mathlib-only) |
| `HomUnify` | 1 | `HomUnify/Corr.lean` | hom-unify: the two `Hom` forms of T11(a), and the single leaf `HomLatticeCorr` |
| `KroneckerWeber` | 2 | `KroneckerWeber/Basic.lean` | The Kronecker–Weber theorem in Mathlib terms, from Tau Ceti's `kroneckerWeber` |
| `LocalKW` | 4 | `LocalKW/Basic.lean` | Local Kronecker–Weber for `ℚ_p`, from Tau Ceti's local class field theory |
| `Mobius` | 5 | `Mobius/Main.lean` | mobius-contrib: the kernel's `MobiusGlue` from the textbook leaf T5 |
| `MulEtale` | 42 | `MulEtale/Direct/AllBase.lean` | Multiplication étaleness on the given abelian scheme over any commutative ring |
| `NeronC` | 3 | `NeronC/NMPInjective.lean` | neron-c: the injective half of the Néron mapping property for abelian schemes |
| `OneProof` | 2946 | none | contributions to the proof chain of `ZInQKernel/OneProof/`: 71 subdirectories and 454 modules at the top level |
| `PoleRC` | 24 | `PoleRC/Reduction.lean` | Theorem 5.2 from `CR_M` and the simultaneous construction |
| `PSide` | 1 | `PSide/TYZInputsIff.lean` | P5: `TYZInputs` is equivalent to reading A of TYZ Theorem 3.5(2) |
| `R10` | 3 | `R10/Amend.lean` | R10 amended: the de Rham comparison for abelian varieties with the full Hodge–Tate weights |
| `RC53Assist` | 328 | `RC53Assist/BCDTPrint/Descent.lean` | From the printed Theorem A to modularity over `Γ₀(N)` |
| `RLeaf` | 13 | `RLeaf/BelyiX1.lean` | rleaf-elliptic: the glue target `BelyiX1` proved outright |
| `SmoothFibre` | 2 | `SmoothFibre/Basic.lean` | smooth-fibre: `SmoothFibreReduced`, proved from Mathlib |
| `SpreadOut` | 5 | `SpreadOut/GrpDescent.lean` | Spreading out, I: reflecting group-object structures along monoidal functors |
| `T14` | 2 | `T14/Main.lean` | Leaf T14 (T14a′ and T14b′, cochain forms) proved outright |
| `T25` | 2 | `T25/Bridge.lean` | T25 (`PkgI4.NewformOfEigenform`): the bridge to Tau Ceti's newform theory |
| `T28` | 8 | `T28/Assemble.lean` | T28 proved: Igusa invariants separate binary sextics (tasks igusa-generic + igusa-special) |
| `T31` | 5 | `T31/Main.lean` | T31: `GlueDescent.B2Q.LeafUnramified` |
| `TauCeti` | 2125 | `TauCeti/Notice.lean` | Notice: vendored Tau Ceti code |
| `TwistDescent` | 1 | `TwistDescent/GaloisDescent.lean` | twist-descent: Galois descent of morphisms of schemes |
| `TYZDecomp` | 2 | `TYZDecomp/CurveA.lean` | tyz-decomp: TYZ's curve `A` and Lemma 3.16 over genuine definitions |
| `TYZGenus` | 15 | `TYZGenus/CM.lean` | cm-points: CM (Heegner) points on `X₀(32) = A`, their fields of definition, Shimura reciprocity |
| `UnramRoots` | 6 | `UnramRoots/Metric.lean` | unram-roots, metric part: inertia and roots of unity in `ℚ̄_p` (proved) |
| `ZariskiConn` | 1 | `ZariskiConn/Basic.lean` | zariski-conn: `ProperSmoothGenConnected` from Zariski's connectedness theorem |
