# Contributed Lean modules (`ZInQKernel/Contrib/`)

One row per group under `ZInQKernel/Contrib/`. Every module is imported by `ZInQKernel/Contrib/AllContrib.lean`.
The description is the first heading of the group's main module (named in the table). For what each result does
for the proof, see `docs/research/frontier.md` (open Props) and `docs/research/README.md` (one line per research
note). Generated from the modules at f70ec251.

| group | modules | main module | description |
|---|---|---|---|
| `AbsFrob` | 3 | `AbsFrob/Basic.lean` | afr-absfrob: the absolute Frobenius of a scheme of characteristic `p` |
| `AbVarBC` | 12 | `AbVarBC/Main.lean` | Base change of abelian varieties: main results |
| `AVB1` | 3 | `AVB1/AlgClosed.lean` | av-b1, II: T6 and T7 over any field from Mumford's statements over an algebraically closed field |
| `AVB2` | 1 | `AVB2/SerreLemma.lean` | Serre's lemma at level 3, ring and lattice forms (task av-b2) |
| `BrauerT14T15` | 8 | `BrauerT14T15/Main.lean` | Leaves T14 and T15 (cochain forms) from Tau Ceti: summary |
| `Chebotarev` | 3 | `Chebotarev/Exists.lean` | Leaf I6.4 / T18 (Chebotarev, existence form), proved |
| `CurvesG` | 3 | `CurvesG/CurveSplit.lean` | curves-g: `CurveOfFunctionFieldQNoPoint` (T38 without its point clause) from three textbook facts |
| `Different` | 4 | `Different/Bridge.lean` | Bridge from Tau Ceti's global different theory to the leaves of `Breaks.lean`; T20 proved |
| `Dim` | 11 | `Dim/Basic.lean` | Krull dimension of spaces and schemes: covers, isomorphisms, specializing maps |
| `FrobChain` | 10 | `FrobChain/Main.lean` | Frob chain, 10: the closed reductions |
| `FrobPieces` | 1 | `FrobPieces/SmoothGeomConnIntegral.lean` | frob-pieces: `SmoothGeomConnIntegral` (alg-frob-red's leaf candidate), proved |
| `G15` | 6 | `G15/Combined.lean` | G15: the three readings of the lower filtration agree |
| `G1Adelic` | 2 | `G1Adelic/Complements.lean` | G1-adelic over Mathlib's `𝔸ᶠ[ℤ, ℚ]`: complements |
| `G9` | 20 | `G9/G9.lean` | G9: N5's appendix lemma; `r` is de Rham with Hodge–Tate weights `0, −1` |
| `GaussFE` | 3 | `GaussFE/Headline.lean` | The headline with `HeckeContinuation` and `FunctionalEquation5` discharged |
| `GZDecomp` | 2 | `GZDecomp/Decomp.lean` | gz-decomp, steps (2)-(3): `GrossZagierCd` from three leaves and glue |
| `GZStatements` | 4 | `GZStatements/Compat.lean` | gz-statements: the Heegner hypothesis gives the root-number compatibility of Friedberg–Hoffstein |
| `GZTheta` | 23 | `GZTheta/Main.lean` | gz-theta: main reductions of the leaf `HeckeThetaNewform` |
| `HeckeAll` | 4 | `HeckeAll/Continuation.lean` | `HeckeContinuation` for every `d ≠ 0`, from Gauss's point count |
| `HeckeFE` | 1 | `HeckeFE/Basic.lean` | Hecke's theory for `C_d : y² = x³ − d²x` over `ℤ[i]` |
| `HeightBC` | 16 | `HeightBC/Main.lean` | Height base change, XVI: the closed theorems |
| `HodgeBC2` | 1 | `HodgeBC2/ExtFrac.lean` | Exterior powers commute with passage to the fraction field (Mathlib-only) |
| `HomUnify` | 1 | `HomUnify/Corr.lean` | hom-unify: the two `Hom` forms of T11(a), and the single leaf `HomLatticeCorr` |
| `KroneckerWeber` | 2 | `KroneckerWeber/Basic.lean` | The Kronecker–Weber theorem in Mathlib terms, from Tau Ceti's `kroneckerWeber` |
| `LocalKW` | 4 | `LocalKW/Basic.lean` | Local Kronecker–Weber for `ℚ_p`, from Tau Ceti's local class field theory |
| `Mobius` | 5 | `Mobius/Main.lean` | mobius-contrib: the kernel's `MobiusGlue` from the textbook leaf T5 |
| `NeronC` | 3 | `NeronC/NMPInjective.lean` | neron-c: the injective half of the Néron mapping property for abelian schemes |
| `PSide` | 7 | `PSide/APZero.lean` | P1: `a_p(C_d) = 0` for `p ≡ 3 (mod 4)` |
| `R10` | 3 | `R10/Amend.lean` | R10 amended: the de Rham comparison for abelian varieties with the full Hodge–Tate weights |
| `RLeaf` | 13 | `RLeaf/BelyiX1.lean` | rleaf-elliptic: the glue target `BelyiX1` proved outright |
| `SmoothFibre` | 2 | `SmoothFibre/Basic.lean` | smooth-fibre: `SmoothFibreReduced`, proved from Mathlib |
| `SpreadOut` | 5 | `SpreadOut/GrpDescent.lean` | Spreading out, I: reflecting group-object structures along monoidal functors |
| `T14` | 2 | `T14/Main.lean` | Leaf T14 (T14a′ and T14b′, cochain forms) proved outright |
| `T25` | 2 | `T25/Bridge.lean` | T25 (`PkgI4.NewformOfEigenform`): the bridge to Tau Ceti's newform theory |
| `T28` | 8 | `T28/Assemble.lean` | T28 proved: Igusa invariants separate binary sextics (tasks igusa-generic + igusa-special) |
| `T31` | 5 | `T31/Main.lean` | T31: `GlueDescent.B2Q.LeafUnramified` |
| `TauCeti` | 1833 | `TauCeti/Notice.lean` | Notice: vendored Tau Ceti code |
| `TwistDescent` | 1 | `TwistDescent/GaloisDescent.lean` | twist-descent: Galois descent of morphisms of schemes |
| `TYZChain` | 10 | `TYZChain/Main.lean` | TYZ chain: reading A of TYZ Theorem 3.5 from the remaining TYZ-side leaves (no glue left) |
| `TYZDecomp` | 2 | `TYZDecomp/CurveA.lean` | tyz-decomp: TYZ's curve `A` and Lemma 3.16 over genuine definitions |
| `TYZGenus` | 20 | `TYZGenus/CM.lean` | cm-points: CM (Heegner) points on `X₀(32) = A`, their fields of definition, Shimura reciprocity |
| `UnramRoots` | 6 | `UnramRoots/Metric.lean` | unram-roots, metric part: inertia and roots of unity in `ℚ̄_p` (proved) |
| `ZariskiConn` | 1 | `ZariskiConn/Basic.lean` | zariski-conn: `ProperSmoothGenConnected` from Zariski's connectedness theorem |
