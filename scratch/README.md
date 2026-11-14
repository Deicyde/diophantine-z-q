# scratch/

Working directories of the tasks: single-file Lean assemblies, part files, check scripts and logs. Nothing here is
imported by the kernel; results that the project keeps are ported to `ZInQKernel/` (see `docs/contrib.md`) or folded
into the H assemblies (`leaf-fold6` is the newest). Each directory's task wrote a research note of the same name
in `docs/research/` when there is one; `docs/research/README.md` indexes those notes and `docs/research/frontier.md`
says what is still open.

Generated at f70ec251: the purpose and role come from an AI read of each directory at
integration w47 where that read exists, otherwise from the note's title or the directory's own README or log.
Model work, no human review.

| directory | files | purpose | role | note |
|---|---|---|---|---|
| `afr-absfrob` | 6 | afr-absfrob: `AbsFrob` and `FExtendGen` (from alg-frob-red) |  | [afr-absfrob](../docs/research/afr-absfrob.md) |
| `ag-inputs` | 5 | ag-inputs: review of pi0-x6's `π₀(X₆) = 1` argument, and `AGInputs` from standard leaves |  | [ag-inputs](../docs/research/ag-inputs.md) |
| `alg-frob-red` | 8 | alg-frob-red: reducing `FrobTrace.AlgFrobRed` |  | [alg-frob-red](../docs/research/alg-frob-red.md) |
| `ap-finish` | 1 | ap-finish log (log.md) |  |  |
| `ap-lean` | 1 | ap-lean log (log.md) |  |  |
| `atkin-li` | 7 | atkin-li: the leaf `HeckeThetaNewform` is proved |  | [atkin-li](../docs/research/atkin-li.md) |
| `aud-ap` | 4 | Audit of the progression variant of the main theorem: the statements |  | [aud-ap](../docs/research/aud-ap.md) |
| `aut-o-finite` | 4 | aut-o-finite: `AutOInnerFinite` is proved, and `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes |  | [aut-o-finite](../docs/research/aut-o-finite.md) |
| `av-b1` | 7 | av-b1: leaf-fold3's group B fields t6, t7, t8 (textbook abelian varieties) |  | [av-b1](../docs/research/av-b1.md) |
| `av-b2` | 22 | av-b2: group B of leaf-fold3; T9 and Serre's lemma become glue, `DivisiblePoints` reduced to char p |  | [av-b2](../docs/research/av-b2.md) |
| `av-glue` | 6 | av-glue: the two glue Props under `SimpleImageIsogeny` (ImageFactorization, SimpleSurjIsogeny) |  | [av-glue](../docs/research/av-glue.md) |
| `av-split` | 11 | av-split: the abelian-variety GLUE rows of frontier r3 split into published forms |  | [av-split](../docs/research/av-split.md) |
| `bdr-kertheta` | 2 | bdr-kertheta: `ker θ` is principal for `𝓞_ℂ_p`, and Mathlib's `BDeRham` is the classical `B_dR` (Lean proofs) |  | [bdr-kertheta](../docs/research/bdr-kertheta.md) |
| `bp-analytic` | 2 | bp-analytic: formalization blueprint for the analytic uniformization of abelian varieties |  | [bp-analytic](../docs/research/bp-analytic.md) |
| `bp-faltings` | 3 | bp-faltings: formalization blueprint for the stable Faltings height |  | [bp-faltings](../docs/research/bp-faltings.md) |
| `bp-hecke-fe` | 10 | bp-hecke-fe: blueprint for `HeckeContinuation` and `FunctionalEquation5` |  | [bp-hecke-fe](../docs/research/bp-hecke-fe.md) |
| `bp-modcurves` | 9 | bp-modcurves: formalization blueprint for `X₁(N)`, `J₁(N)`, the Hecke algebra, `A_f` and the Belyi degree |  | [bp-modcurves](../docs/research/bp-modcurves.md) |
| `bp-qmmoduli` | 6 | bp-qmmoduli: formalization blueprint for the Shimura-curve objects of H (leaves R1-R3, R5) |  | [bp-qmmoduli](../docs/research/bp-qmmoduli.md) |
| `bp-wave4` | 1 | bp-wave4 log (log.md) |  |  |
| `c9-rhof` | 2 | c9-rhof: glue C9 for R16's representation `ρ_{f,ι}` |  | [c9-rhof](../docs/research/c9-rhof.md) |
| `cheb-bridge` | 4 | cheb-bridge: leaf I6.4 / T18 (Chebotarev) proved from Tau Ceti |  | [cheb-bridge](../docs/research/cheb-bridge.md) |
| `cm-bridge` | 6 | cm-bridge: TYZ reading A from the 𝓛-leaves, one textbook CM leaf (`ShimuraReciprocityModFn`) and three TYZ results; `GenusFieldLeLni` and TYZ Lemma 3.21(4) derived |  | [cm-bridge](../docs/research/cm-bridge.md) |
| `cm-numeric` | 11 | cm-numeric: TYZ's class-7 CM point pinned, Shimura reciprocity checked numerically, `GenusPointLeafCM` split |  | [cm-numeric](../docs/research/cm-numeric.md) |
| `cm-points` | 12 | cm-points: CM points on X₀(32) = A, Shimura reciprocity, and TYZ's genus-point package split into genuine leaves |  | [cm-points](../docs/research/cm-points.md) |
| `conj-pieces` | 6 | conj-pieces: `ArtinTorsionSurj`, `HomLinearLift`, `ConjUniformization` (G10, under `ConjTwistNontrivial`) |  | [conj-pieces](../docs/research/conj-pieces.md) |
| `conj-twist` | 2 | conj-twist: `ConjTwistNontrivial` and `ConjTwistFromLeaves` (G10 core) |  | [conj-twist](../docs/research/conj-twist.md) |
| `contrib-check` | 1 |  |  |  |
| `contrib-tidy` | 20 | contrib-tidy: the Contrib folders made ready for two proof-only upstream PRs |  | [contrib-tidy](../docs/research/contrib-tidy.md) |
| `cpts-transport` | 14 | cpts-transport: `CPtsTransport` proved, and `BaseChangeClassUnique` proved by the same argument |  | [cpts-transport](../docs/research/cpts-transport.md) |
| `cr3-adopt` | 7 | cr3-adopt log (log.md) |  |  |
| `cr3-check` | 55 |  |  |  |
| `cr3-dl` | 1 | cr3-dl log (log.md) |  |  |
| `cr3-inf` | 1 | cr3-inf log (log.md) |  |  |
| `cr3-kummer` | 1 | cr3-kummer log (log.md) |  |  |
| `cr3-map` | 2 |  |  |  |
| `cr3-mw` | 1 | cr3-mw log (log.md) |  |  |
| `cr3-trust` | 6 | cr3-trust: a trust statement for CR₃ |  | [cr3-trust](../docs/research/cr3-trust.md) |
| `cr5b-lean` | 1 | cr5b-lean log (log.md) |  |  |
| `cr5b-sec3` | 2 | cr5b-sec3 log (log.md) |  |  |
| `curve-facts` | 5 | curve-facts: `CurveRatFactor` and `CurveSurj` reduced to three per-component curve facts |  | [curve-facts](../docs/research/curve-facts.md) |
| `curve-glue` | 21 | curve-glue: C2K and C3K reduced, and the CM-point gap in `MobiusGlue` closed |  | [curve-glue](../docs/research/curve-glue.md) |
| `curve-infra` | 10 | curve-infra: dimension equals transcendence degree, proved in general |  | [curve-infra](../docs/research/curve-infra.md) |
| `curves-g` | 10 | curves-g: group G of leaf-fold3 (Jacobians, `X₁(N)`, function fields): t33, t34, t38 |  | [curves-g](../docs/research/curves-g.md) |
| `d2-check` | 13 | d2-check: numerical guard on CR₃^DL,Rk on the curves the descent lemma produces |  | [d2-check](../docs/research/d2-check.md) |
| `def-faltings` | 2 | def-faltings: the stable Faltings height, first layer, in Lean |  | [def-faltings](../docs/research/def-faltings.md) |
| `def-ladic-cond` | 2 | def-ladic-cond: the conductor exponent of an ℓ-adic representation of `G_{ℚ_p}`, `ℓ ≠ p` |  | [def-ladic-cond](../docs/research/def-ladic-cond.md) |
| `descent-alt` | 22 | The descent lemma of Route K: what the free multiplier and the free witness can do |  | [descent-alt](../docs/research/descent-alt.md) |
| `diff-bridge` | 5 | diff-bridge: the global different leaves T20 and T21, proved |  | [diff-bridge](../docs/research/diff-bridge.md) |
| `dim-contrib` | 10 | dim-contrib: dimension theory adopted as `ZInQKernel/Contrib/Dim/` |  | [dim-contrib](../docs/research/dim-contrib.md) |
| `e1-sub` | 2 | e1-sub: E1 for R16, `ρ_{f,ι}` as a subrepresentation of `V_ℓ(J₁(N)_{L'}) ⊗ ℚ̄_ℓ` |  | [e1-sub](../docs/research/e1-sub.md) |
| `el-cert` | 5 | el-cert: redesigning the slope certificate and the test shift to avoid CR₃ |  | [el-cert](../docs/research/el-cert.md) |
| `el-e4` | 17 | el-e4: testing the frozen-Θ redesign (el-gadget E4 = el-cert M1) |  | [el-e4](../docs/research/el-e4.md) |
| `el-gadget` | 5 | el-gadget: replacing the pole gadget by one with elementary completeness |  | [el-gadget](../docs/research/el-gadget.md) |
| `el-global` | 4 | el-global: global soundness through a label on `E(K₀)` |  | [el-global](../docs/research/el-global.md) |
| `el-k3` | 10 | el-k3: points on the Kummer surfaces X_{β,θ} from their geometry |  | [el-k3](../docs/research/el-k3.md) |
| `el-qfree` | 8 | el-qfree: using the freedom in the witness `q` and in the multipliers to remove CR₃ |  | [el-qfree](../docs/research/el-qfree.md) |
| `el-special` | 7 | el-special: existential freedom, prime configurations and explicit points |  | [el-special](../docs/research/el-special.md) |
| `fibre-cover` | 3 | fibre-cover: the glue Prop `FibreCoverExists` (G2: Proposition TS and Lemma NV) |  | [fibre-cover](../docs/research/fibre-cover.md) |
| `fibre-qm-period` | 34 | fibre-qm-period: `FibreQMPeriod` reduced to the leaf's own triple and then to named Props |  | [fibre-qm-period](../docs/research/fibre-qm-period.md) |
| `frob-contrib` | 8 | frob-contrib: the absolute Frobenius and `UnramRoots` adopted under `ZInQKernel/Contrib/` |  | [frob-contrib](../docs/research/frob-contrib.md) |
| `frob-pieces` | 15 | frob-pieces: the open inputs of `FrobTrace.AlgFrobRed` |  | [frob-pieces](../docs/research/frob-pieces.md) |
| `frob-trace` | 13 | frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace) |  | [frob-trace](../docs/research/frob-trace.md) |
| `frobchain-contrib` | 9 | frobchain-contrib: the frob chain in the kernel's Contrib build (2026-11-13) |  | [frobchain-contrib](../docs/research/frobchain-contrib.md) |
| `frontier` | 14 | frontier: every open Prop on the path to `ZInQ.FrozenTarget` |  | [frontier](../docs/research/frontier.md) |
| `fs1-descend` | 4 | fs1-descend: FS1b′ `FiniteDescends` is proved (Mathlib only, no new leaf) |  | [fs1-descend](../docs/research/fs1-descend.md) |
| `fs5-nocm` | 14 | fs5-nocm: FS5 `FibreComTrivial` (NoCM on the fibre) proved, with the repaired QM clauses, from leaves, one new leaf and one named glue Prop |  | [fs5-nocm](../docs/research/fs5-nocm.md) |
| `g0-assemble` | 31 | g0-assemble: wave 26 assembled into one Lean file; `GluePieces` from `GluePieces2` |  | [g0-assemble](../docs/research/g0-assemble.md) |
| `g0-assemble2` | 57 | g0-assemble2: waves 26-27 assembled; `GluePieces3`, `ResearchLeaves3`, `sixContactMin_of_leaves3` |  | [g0-assemble2](../docs/research/g0-assemble2.md) |
| `g0-assemble3` | 86 | g0-assemble3: the results since g0-assemble2 assembled; `ResearchLeaves4`, `GluePieces4`, `sixContactMin_of_leaves4` |  | [g0-assemble3](../docs/research/g0-assemble3.md) |
| `g0-dim` | 5 | g0-dim: the glue pieces `DimFinite` and `DimBaseChange`, proved |  | [g0-dim](../docs/research/g0-dim.md) |
| `g0-fibresimple` | 8 | g0-fibresimple: `FibreSimple` reduced to four leaves and two glue Props; its quantifier makes it stronger than NoCM |  | [g0-fibresimple](../docs/research/g0-fibresimple.md) |
| `g0-heightadd` | 9 | g0-heightadd: the glue piece `HeightAdditivity` (E4) |  | [g0-heightadd](../docs/research/g0-heightadd.md) |
| `g0-mod-field` | 2 | g0-mod-field: glue steps G2, G4, G7 (the field half of `ModularConstituent`) |  | [g0-mod-field](../docs/research/g0-mod-field.md) |
| `g0-mod-galois` | 7 | g0-mod-galois: glue steps G8-G12 (the Galois side of `ModularConstituent`) |  | [g0-mod-galois](../docs/research/g0-mod-galois.md) |
| `g0-mod-newform` | 6 | g0-mod-newform: glue steps G13-G16 of `ModularConstituent` |  | [g0-mod-newform](../docs/research/g0-mod-newform.md) |
| `g0-product` | 3 | g0-product: the glue piece `ProductExists` (G17), proved |  | [g0-product](../docs/research/g0-product.md) |
| `g0-reverseisog` | 3 | g0-reverseisog: the glue piece `ReverseIsogeny` (G17 after Poincaré) |  | [g0-reverseisog](../docs/research/g0-reverseisog.md) |
| `g0-split` | 4 | g0-split: the one `sorry` of the H decomposition, split into named pieces |  | [g0-split](../docs/research/g0-split.md) |
| `g0-stablebc` | 6 | g0-stablebc: the glue piece `StableHeightBaseChange` |  | [g0-stablebc](../docs/research/g0-stablebc.md) |
| `g0-thetapoint` | 8 | g0-thetapoint: `ThetaPointOfFibre` (g0-split missing piece 9) from smaller named Props |  | [g0-thetapoint](../docs/research/g0-thetapoint.md) |
| `g0-x1belyi` | 9 | g0-x1belyi: `X1BelyiOnModel` is proved |  | [g0-x1belyi](../docs/research/g0-x1belyi.md) |
| `g1-adelic2` | 4 | g1-adelic2: G1-adelic over Mathlib's finite adeles `𝔸ᶠ[ℤ, ℚ]` |  | [g1-adelic2](../docs/research/g1-adelic2.md) |
| `g10-odd` | 2 | g10-odd: the glue Prop `G10Glue` (oddness of `r_ℓ`) |  | [g10-odd](../docs/research/g10-odd.md) |
| `g12-det` | 20 | g12-det: `G12Weight`, `DetTate`, `ResQFiniteIndex` (glue of g0-mod-galois) |  | [g12-det](../docs/research/g12-det.md) |
| `g14-trace` | 11 | g14-trace: `G14TraceCompat` (r₃ and r₅ in one compatible system) |  | [g14-trace](../docs/research/g14-trace.md) |
| `g15-decomp` | 3 | g15-decomp: the decomposition-group transport for G15 |  | [g15-decomp](../docs/research/g15-decomp.md) |
| `g15-ram` | 5 | g15-ram: G15's open Prop `G15RamG`, conductor exponents (clauses (i) and (ii)) |  | [g15-ram](../docs/research/g15-ram.md) |
| `g4-weilres` | 2 | g4-weilres: glue step G4 (Weil restriction and the Hom field) |  | [g4-weilres](../docs/research/g4-weilres.md) |
| `g8-object` | 10 | g8-object: G8's `r_ℓ` as a Lean object, and the G8-G16 interface restated over it |  | [g8-object](../docs/research/g8-object.md) |
| `g8-tate` | 13 | g8-tate: the glue left under G8 is closed, modulo two existing named glue Props |  | [g8-tate](../docs/research/g8-tate.md) |
| `g9-abvarbc` | 4 | g9-abvarbc: `G9Bridge.AbVarBaseChange` proved; `KerUnitOpen` and `MulIsogeny` proved |  | [g9-abvarbc](../docs/research/g9-abvarbc.md) |
| `g9-derham` | 3 | g9-derham: glue step G9 (N5's de Rham descent lemma), the target `G9Glue` |  | [g9-derham](../docs/research/g9-derham.md) |
| `gauss-proof` | 6 | gauss-proof: Gauss's point count, and `ZInQ.Contrib.functionalEquation5` |  | [gauss-proof](../docs/research/gauss-proof.md) |
| `glue-a6-alg` | 4 | glue-a6-alg: the A6 glue is finished in Lean |  | [glue-a6-alg](../docs/research/glue-a6-alg.md) |
| `glue-assembly` | 13 | glue-assembly: the assembly glue of H (steps C8, C10, E1, E3, E4, F2) |  | [glue-assembly](../docs/research/glue-assembly.md) |
| `glue-b3-unram` | 2 | glue-b3-unram: the kernel field `L'` of B3 is unramified outside `T` |  | [glue-b3-unram](../docs/research/glue-b3-unram.md) |
| `glue-b3b` | 2 | glue-b3b: L-B3b and T32(b) are glue; B3 (v) now rests on the bundle leaf T32(a) alone |  | [glue-b3b](../docs/research/glue-b3b.md) |
| `glue-c10` | 4 | glue-c10: the glue of step C10 (one compatible system at 3 and 5) |  | [glue-c10](../docs/research/glue-c10.md) |
| `glue-c10-link` | 2 | glue-c10-link: the trace link of C10, `c_p = ½·β(σ)⁻¹a_σ·tr α_σ` |  | [glue-c10-link](../docs/research/glue-c10-link.md) |
| `glue-conductor` | 4 | glue-conductor: Glazer's uniform conductor bound as leaves and glue (h-trust D1-D5) |  | [glue-conductor](../docs/research/glue-conductor.md) |
| `glue-conj` | 6 | glue-conj: `LeafConj` is glue (proved in Lean) |  | [glue-conj](../docs/research/glue-conj.md) |
| `glue-d1-local` | 2 | glue-d1-local: the local form of D1's degree bound `e ≤ a!` |  | [glue-d1-local](../docs/research/glue-d1-local.md) |
| `glue-descent` | 10 | glue-descent: Glazer's scalar descent (h-trust B1-B3, C1) as lemmas, leaves and Lean |  | [glue-descent](../docs/research/glue-descent.md) |
| `glue-I3-linalg` | 5 | glue-I3-linalg: the linear-algebra glue of package I3 (steps C2, E1) |  | [glue-I3-linalg](../docs/research/glue-I3-linalg.md) |
| `glue-I6-rest` | 5 | glue-I6-rest: the remaining glue of package I6 and of the conductor cluster |  | [glue-I6-rest](../docs/research/glue-I6-rest.md) |
| `glue-repo` | 8 | glue-repo: the repository's replacement arguments and bookkeeping in Part A of H |  | [glue-repo](../docs/research/glue-repo.md) |
| `glue-rho-cont` | 2 | glue-rho-cont: continuity of pkg-I3's ρ_ℓ |  | [glue-rho-cont](../docs/research/glue-rho-cont.md) |
| `glue-sqrt-disj` | 6 | glue-sqrt-disj: disjointness and the level change for B2's local square-root criterion |  | [glue-sqrt-disj](../docs/research/glue-sqrt-disj.md) |
| `glue-sqrt-local` | 7 | glue-sqrt-local: the local part of B2's square-root criterion |  | [glue-sqrt-local](../docs/research/glue-sqrt-local.md) |
| `glue-ssbc` | 3 | glue-ssbc: `SemisimpleBaseChange` proved |  | [glue-ssbc](../docs/research/glue-ssbc.md) |
| `glue-t32a` | 2 | glue-t32a: T32(a) is glue, and B3 (v) now rests on no leaf |  | [glue-t32a](../docs/research/glue-t32a.md) |
| `glue-vigneras` | 6 | glue-vigneras: Vignéras' normalizer facts for A3, proved in Lean |  | [glue-vigneras](../docs/research/glue-vigneras.md) |
| `glue-wp3` | 9 | glue-wp3: glue-descent's `LeafHasse`, `LeafLocalTwo` from the announced leaves T14-T15 |  | [glue-wp3](../docs/research/glue-wp3.md) |
| `gt-dense` | 1 | Green–Tao, dense form, from the Ilin Lean proof: plan |  | [gt-dense](../docs/research/gt-dense.md) |
| `gt-dense-plan` | 1 | gt-dense-plan log (log.md) |  |  |
| `gt-dense2` | 1 | gt-dense2 log (log.md) |  |  |
| `gt-import` | 2 | gt-import log (log.md) |  |  |
| `gt-search` | 2 | Lean formalizations of the Green–Tao theorem, and what replacing 22P_AP would take |  | [gt-search](../docs/research/gt-search.md) |
| `gz-decomp` | 6 | gz-decomp: the Gross–Zagier premise as three literature leaves plus proved glue |  | [gz-decomp](../docs/research/gz-decomp.md) |
| `gz-license` | 7 | gz-license (research note) |  | [gz-license](../docs/research/gz-license.md) |
| `gz-statements` | 5 | gz-statements: statement review of `FHNonvanishing` and `GrossZagierHeegner` |  | [gz-statements](../docs/research/gz-statements.md) |
| `gz-theta` | 12 | gz-theta: the leaf `HeckeThetaNewform` (L1 of gz-decomp) |  | [gz-theta](../docs/research/gz-theta.md) |
| `h-a011` | 4 | A011-V14: Pan's Theorem 1.0.4 applied directly to `r₅` in Version 14 |  | [h-a011](../docs/research/h-a011.md) |
| `h-a9c9-fix` | 1 | h-a9c9-fix log (log.md) |  |  |
| `h-adopt` | 2 | h-adopt work log (log.md) |  |  |
| `h-b1` | 3 | Route B1: the integral model of the Shimura curve replaced by tame specialization (audit record) |  | [h-b1](../docs/research/h-b1.md) |
| `h-b1-fix` | 3 | h-b1-fix work log (log.md) |  |  |
| `h-c38` | 1 | h-c38 log (log.md) |  |  |
| `h-cm` | 5 | The CM branch of the six-contact estimate is empty for rational u |  | [h-cm](../docs/research/h-cm.md) |
| `h-decomposition` | 1 | h-decomposition: hypothesis H as literature leaves plus glue (synthesis) |  | [h-decomposition](../docs/research/h-decomposition.md) |
| `h-map` | 5 | A map of the height hypothesis H (SixContactMin): what is used, what it rests on, and routes |  | [h-map](../docs/research/h-map.md) |
| `h-trust` | 3 | h-trust: a trust statement for H that uses no unpublished supplement |  | [h-trust](../docs/research/h-trust.md) |
| `h-v14` | 7 | The trust leaves of the six-contact estimate H, re-based on Version 14 |  | [h-v14](../docs/research/h-v14.md) |
| `h-v16-adopt` | 5 | h-v16-adopt log (log.md) |  |  |
| `h5-glue` | 13 | h5-glue: the glue of H5 (Néron models and the stable Faltings height) |  | [h5-glue](../docs/research/h5-glue.md) |
| `h5-neron` | 8 | h5-neron: Néron models and the stable Faltings height (node H5, leaves R19-R21) |  | [h5-neron](../docs/research/h5-neron.md) |
| `hdec-adopt` | 6 | hdec-adopt: the H-decomposition glue in the built project |  | [hdec-adopt](../docs/research/hdec-adopt.md) |
| `hdec-adopt2` | 6 | hdec-adopt2: the second round of H-decomposition glue in the built project |  | [hdec-adopt2](../docs/research/hdec-adopt2.md) |
| `hdec-adopt3` | 6 | hdec-adopt3: the third round of H-decomposition glue in the built project |  | [hdec-adopt3](../docs/research/hdec-adopt3.md) |
| `hdec-adopt4` | 10 | hdec-adopt4: leaf-push2, bp-analytic and rv-qm-polar in the built project |  | [hdec-adopt4](../docs/research/hdec-adopt4.md) |
| `hdec-adopt5a` | 14 | hdec-adopt5a: c9-rhof, e1-sub, x1-belyi, hodge-lattice and h5-neron in the built project |  | [hdec-adopt5a](../docs/research/hdec-adopt5a.md) |
| `hdec-adopt5b` | 7 | hdec-adopt5b: t-different, t-skolem-kw, t30-adelic, t10-etale and t28-igusa in the built project |  | [hdec-adopt5b](../docs/research/hdec-adopt5b.md) |
| `hdec-alt` | 2 | hdec-alt: published replacements for Glazer's argument, and a leaf/glue decomposition of H |  | [hdec-alt](../docs/research/hdec-alt.md) |
| `hdec-elementary` | 4 | hdec-elementary: Theorem 4.1 (H) decomposed into elementary leaves and Lean glue |  | [hdec-elementary](../docs/research/hdec-elementary.md) |
| `hdec-faithful` | 2 | hdec-faithful: Theorem 4.1 (instance `SixContactMin`) decomposed along Glazer's proof |  | [hdec-faithful](../docs/research/hdec-faithful.md) |
| `hecke-all` | 5 | hecke-all: `HeckeContinuation` for every `d ≠ 0`, from Gauss's point count |  | [hecke-all](../docs/research/hecke-all.md) |
| `hecke-rest` | 19 | hecke-rest: the four glue Props left by ts-hecke under `CoverModelOfHecke` |  | [hecke-rest](../docs/research/hecke-rest.md) |
| `height-bc` | 10 | height-bc: the Hodge line and the model height under base change (H4a, `HodgeLineBaseChange`) |  | [height-bc](../docs/research/height-bc.md) |
| `height-split` | 4 | height-split: the height and Faltings rows of the frontier, split into published forms |  | [height-split](../docs/research/height-split.md) |
| `heightbc-contrib` | 6 | heightbc-contrib: the height base-change chain in the kernel's Contrib build (2026-11-13) |  | [heightbc-contrib](../docs/research/heightbc-contrib.md) |
| `hodge-bc2` | 17 | hodge-bc2: `HodgeBCInjective` and `OmegaBaseChange` proved (2026-11-13) |  | [hodge-bc2](../docs/research/hodge-bc2.md) |
| `hodge-lattice` | 2 | hodge-lattice: the algebraic third of AN3 (`HodgeLatticeTheorem`) |  | [hodge-lattice](../docs/research/hodge-lattice.md) |
| `hom-unify` | 14 | hom-unify: the two `Hom` forms of T11(a), and G10 from `HomLinearLift` in the assembly |  | [hom-unify](../docs/research/hom-unify.md) |
| `homlattice` | 4 | homlattice: `HomLatticeCorr` reduced to AN3 at every embedding and GAGA |  | [homlattice](../docs/research/homlattice.md) |
| `hsyn` | 4 | hsyn results log (log.md) |  |  |
| `hsyn-fix` | 2 | hsyn-fix results log (log.md) |  |  |
| `hsyn-fold` | 9 | hsyn-fold results log (log.md) |  |  |
| `igusa-generic` | 12 | igusa-generic: textbook leaf T28 on the generic locus (Mestre's separation), proved |  | [igusa-generic](../docs/research/igusa-generic.md) |
| `igusa-special` | 30 | igusa-special: the special locus of T28, and T28 assembled |  | [igusa-special](../docs/research/igusa-special.md) |
| `image-plane` | 19 | image-plane: (G1') `ImagePlaneCurveClosed` is a theorem, and `MobiusGlue` follows from T5 alone |  | [image-plane](../docs/research/image-plane.md) |
| `inertia-homs` | 2 | inertia-homs: the inertia input of G4, corrected and proved from two leaves |  | [inertia-homs](../docs/research/inertia-homs.md) |
| `infra-hodge` | 23 | infra-hodge: the two product Props left by infra-stalks are proved |  | [infra-hodge](../docs/research/infra-hodge.md) |
| `infra-smooth-dim` | 14 | infra-smooth-dim: dimension theory of smooth schemes over a field |  | [infra-smooth-dim](../docs/research/infra-smooth-dim.md) |
| `infra-stalks` | 31 | infra-stalks: stalks and cotangent spaces of fibre products; five glue Props proved |  | [infra-stalks](../docs/research/infra-stalks.md) |
| `inner-twist` | 7 | inner-twist: `InnerTwistCount` and `UnramifiedConjugates` are proved |  | [inner-twist](../docs/research/inner-twist.md) |
| `kernel-field` | 6 | kernel-field: `KernelFieldExists` (G4 + B1) from six leaves and two named glue Props |  | [kernel-field](../docs/research/kernel-field.md) |
| `kerwild-fix` | 8 | kerwild-fix: `LocalGlue` at every `ℓ` with all of `G7Clauses` discharged |  | [kerwild-fix](../docs/research/kerwild-fix.md) |
| `kf-glue` | 12 | kf-glue: `EndTransport` proved; `ConjIsogMaps` reduced to Galois descent (`TwistDescent`) and `MulIsogeny` |  | [kf-glue](../docs/research/kf-glue.md) |
| `kummer-comp` | 7 | kummer-comp: `KummerCompositum` proved, so `KummerMeetGlue` is a theorem |  | [kummer-comp](../docs/research/kummer-comp.md) |
| `kummer-index` | 4 | kummer-index: leaf T14 (T14a′, T14b′) proved outright |  | [kummer-index](../docs/research/kummer-index.md) |
| `kw-basic` | 5 | kw-basic: a Kronecker–Weber module upstream can take now |  | [kw-basic](../docs/research/kw-basic.md) |
| `kw-new` | 19 | kw-new: the Kronecker–Weber theorem in the fork, and the Kronecker–Weber leaves |  | [kw-new](../docs/research/kw-new.md) |
| `leaf-adopt` | 2 | leaf-adopt: the latest leaf reports folded into the H decomposition |  | [leaf-adopt](../docs/research/leaf-adopt.md) |
| `leaf-adopt2` | 6 | leaf-adopt2: leaf-push2 and rv-qm-polar folded into the H decomposition |  | [leaf-adopt2](../docs/research/leaf-adopt2.md) |
| `leaf-adopt3` | 54 | leaf-adopt3: g0-split and wave 25 folded into the H decomposition; no `sorry` left |  | [leaf-adopt3](../docs/research/leaf-adopt3.md) |
| `leaf-fold` | 21 | leaf-fold: the closed leaves folded into the H decomposition; what remains open |  | [leaf-fold](../docs/research/leaf-fold.md) |
| `leaf-fold2` | 77 | leaf-fold2: the results since leaf-fold, folded into one statement of what is still open |  | [leaf-fold2](../docs/research/leaf-fold2.md) |
| `leaf-fold3` | 110 | leaf-fold3: the results since leaf-fold2, folded into one statement of what is still open |  | [leaf-fold3](../docs/research/leaf-fold3.md) |
| `leaf-fold4` | 119 | leaf-fold4: the results since leaf-fold3, folded into one statement of what is still open |  | [leaf-fold4](../docs/research/leaf-fold4.md) |
| `leaf-fold5` | 29 | leaf-fold5: the last glue Prop of leaf-fold4 folded in, group-B/C/G leaves weakened, 33 fields on kernel Props |  | [leaf-fold5](../docs/research/leaf-fold5.md) |
| `leaf-fold6` | 16 | leaf-fold6: leafq-check's four reductions applied to leaf-fold5's bundles, T8 kept as a leaf, 68 fields, glue 1 |  | [leaf-fold6](../docs/research/leaf-fold6.md) |
| `leaf-modcurves` | 2 | leaf-modcurves: `X₁(N)`, `J₁(N)` over `ℚ` and a concrete R16 |  | [leaf-modcurves](../docs/research/leaf-modcurves.md) |
| `leaf-push` | 3 | leaf-push: more of H's leaves stated concretely |  | [leaf-push](../docs/research/leaf-push.md) |
| `leaf-push2` | 2 | States the H leaves R18 (Javanpeykar), R22 and R3 concretely and replaces T11, T12 by textbook leaves over a uniformization predicate; now the kernel modules under HDecomp/LeafPush2. | ported → `ZInQKernel/HDecomp/LeafPush2` | [leaf-push2](../docs/research/leaf-push2.md) |
| `leaf-qm-fp` | 2 | States the Shimura-curve leaves R1, R2, R5 in field-point form (QML3, QMPair, base change, fields of moduli); now HDecomp/QM (Structures, Pairs, Leaves). | ported → `ZInQKernel/HDecomp/QM` | [leaf-qm-fp](../docs/research/leaf-qm-fp.md) |
| `leaf-review-a` | 8 | leaf-review-a: statement review of leaf-fold3's groups A, A′ and F (21 fields) |  | [leaf-review-a](../docs/research/leaf-review-a.md) |
| `leaf-review-b` | 3 | leaf-review-b: statement review of leaf-fold3's groups B, C, D, E and G (41 fields) |  | [leaf-review-b](../docs/research/leaf-review-b.md) |
| `leafq-check` | 23 | leafq-check: the seven LEAF? candidates of leaf-fold4, checked |  | [leafq-check](../docs/research/leafq-check.md) |
| `lfun-cd` | 1 | Proves that the L-series of the curves C_d is the Mathlib L-series of explicit coefficients (minimal models over the completions, Euler product); the draft became a kernel module and the dir keeps only the log. | ported → `ZInQKernel/RouteK/Rank/LFunctionCd.lean` |  |
| `lg-kerwild` | 10 | Discharges local-glue's KerWild and DescentPts on G7's data; KerWild.lean (local-glue + frob-trace + g0-dim slice + new parts) is copied verbatim as lt-local's base. | superseded; superseded by scratch/lt-local | [lg-kerwild](../docs/research/lg-kerwild.md) |
| `linked-frob` | 11 | Reduces linked-tate's glue LinkedFrob to N1-g1 AbVarSpreadsOut, ProperSmoothGenConnected and textbook leaves (flat LinkedFrob.lean, a GluePieces4 variant); frontier.md (sections 4.1, 8) marks field 44 replaced by route T (lt-local). | superseded; superseded by scratch/lt-local | [linked-frob](../docs/research/linked-frob.md) |
| `linked-ram` | 10 | Reduces g0-assemble3's LinkedRam fields kernelFieldBreaks and tateRamAtThree to UpperBreakBound and BetaSignAtTwo with lt-goodred folded (GluePieces5), and finds tateRamAtThree likely false as stated; frontier.md marks fields 45-46 replaced by route T (lt-local). | superseded; superseded by scratch/lt-local | [linked-ram](../docs/research/linked-ram.md) |
| `linked-tate` | 39 | Reduces ModelG3G6 and LinkedTateData and builds the linked Tate data over a byte-identical copy of the pin-applied h-decomposition Leaves.lean (assemble.sh, parts/, olean prefix); copied by linked-frob, lt-goodred, lt-local, g8-tate and hom-unify, and its reductions are folded into g0-assemble3. | canonical | [linked-tate](../docs/research/linked-tate.md) |
| `lit-adopt` | 1 | Moves wk-cr3's Literature.lean into the kernel as Hypotheses/CR3Literature.lean (FunctionalEquation5 restricted to 0 < Re s < 2, GrossZagierKolyvagin renamed GrossZagier), wk-h's BackToU.lean as Hypotheses/JHeight.lean, and the headline variants into MainLiterature.lean; log only. | ported → `ZInQKernel/Hypotheses/CR3Literature.lean` |  |
| `lit-readingA` | 3 | Adds to MainLiterature.lean the headline that derives FrozenTarget from SixContactMin, TYZThm35ReadingA, HeckeContinuation, FunctionalEquation5 and GrossZagier, plus the matching README and KERNEL_PLAN text (readme.diff). | ported → `ZInQKernel/MainLiterature.lean` | [lit-readingA](../docs/research/lit-readingA.md) |
| `lkw` | 3 | Proves local Kronecker-Weber for Q_p (leaf T16, I6.3) and T30's LeafSqrtCrit from vendored Tau Ceti local class field theory; the Lean is in Contrib/LocalKW and the dir keeps axiom checks. | ported → `ZInQKernel/Contrib/LocalKW` | [lkw](../docs/research/lkw.md) |
| `loc-adopt` | 6 | Applies the locator audit (locators.md) to the research notes and the TYZ docstrings (theorem numbering of Period7.tex), with scripts that check the Lean code is unchanged. | task | [loc-adopt](../docs/research/loc-adopt.md) |
| `loc-fix` | 4 | Applies the repairs of rv-loc-leaves and rv-nocm: patches scratch/h-decomposition/Leaves.lean and puts the T27 fix (QuatIndefinite, QMDichotomyYu) into the kernel's HDecomp/Objects.lean. | task → `ZInQKernel/HDecomp/Objects.lean` | [loc-fix](../docs/research/loc-fix.md) |
| `local-data` | 7 | Shows g15-ram's LocalData p r is false for a bare Galois representation and proves the large-prime criterion and the tail on G8's representation; LocalData.lean is contained verbatim in local-glue's LocalGlue.lean. | superseded; superseded by scratch/local-glue | [local-data](../docs/research/local-data.md) |
| `local-glue` | 24 | Shows LocalGlue is not a closed statement and proves it on g0-mod-field's G7 data from two leaves and one textbook Prop; LocalGlue.lean up to Step 18 is contained verbatim in lg-kerwild's KerWild.lean, and Step 19 (`localGlue_of_baseChange'`, G7LocalPackBC without the dimension clause) exists only here. | superseded; superseded by scratch/lg-kerwild | [local-glue](../docs/research/local-glue.md) |
| `lt-goodred` | 18 | Proves linked-tate's glue Props GoodRedTorsion and QMEndRank (bundle fields 42, 43; frontier.md cites these proofs as current, not ported), with a flat integration composite in integ/. | task | [lt-goodred](../docs/research/lt-goodred.md) |
| `lt-local` | 22 | Proves g0-assemble2's glue field LinkedTateLocal from TateBridge35's data (route T; LtLocal4.lean over g0-assemble3's corrected G7Data), which replaces fields 44-46; newest member of the local-data, local-glue, lg-kerwild lineage. Continued on the unmerged wip/assemble-port. | canonical | [lt-local](../docs/research/lt-local.md) |
| `mcr-glue` | 17 | mcr-glue: the glue Prop `ModelCoordinateResidue` |  | [mcr-glue](../docs/research/mcr-glue.md) |
| `metrization` | 22 | Works on g0-heightadd's three metrization glue Props: MetrizationDimUnique proved outright, MetrizationExists and ProductMetrizationGeo reduced; all its files are copied verbatim into metrization2/base. | superseded; superseded by scratch/metrization2 | [metrization](../docs/research/metrization.md) |
| `metrization2` | 31 | Continues metrization: proves JacDetNondegenerate and ProductLocalStructure and derives AnalyticUniformizationOfDim from T35; its kernel-world Kernel.lean is copied verbatim into unif-dims (base/Kernel_metrization2.lean). Its Leaves-world composites in part_final2.lean (`heightAdditivity_of_metrization_v4`/`v5`, `metrizationExists_of_uniformizationExists`) are not carried forward. | superseded; superseded by scratch/unif-dims | [metrization2](../docs/research/metrization2.md) |
| `mobius-contrib` | 5 | Moves image-plane's proof of the kernel's MobiusGlue from leaf T5 into the Contrib build as five modules, trimming unreachable declarations (Dead.lean, trim.py). | ported → `ZInQKernel/Contrib/Mobius` | [mobius-contrib](../docs/research/mobius-contrib.md) |
| `mobius-glue` | 9 | Proves qm-pin's MobiusGlue from two named curve facts and the textbook leaf T5; continued by curve-facts, curve-glue and image-plane, and now Contrib/Mobius/Glue.lean. | ported → `ZInQKernel/Contrib/Mobius/Glue.lean` | [mobius-glue](../docs/research/mobius-glue.md) |
| `model-glue` | 22 | model-glue: the glue Props `ModelCoordinate` and `ModelComparison` |  | [model-glue](../docs/research/model-glue.md) |
| `morph-descend` | 3 | Proves G4's input MorphismsDescend (EGA IV3 8.8.2) from Mathlib with no hypotheses; Descend.lean is copied verbatim into kernel-field, which g0-assemble2 folds. | task | [morph-descend](../docs/research/morph-descend.md) |
| `mul-rigidity` | 6 | Proves RigidityHom from Mathlib and reduces MulIsogeny to two cotangent glue statements; Mul.lean was copied by g9-abvarbc into Contrib/AbVarBC/Mul.lean. The RigidityHom proof (Rigidity.lean) is not in the kernel: alg-frob-red (src_Rigidity.lean) and the frob composites carry it. | ported → `ZInQKernel/Contrib/AbVarBC/Mul.lean` | [mul-rigidity](../docs/research/mul-rigidity.md) |
| `neron-c` | 6 | neron-c: leaf-fold3 fields `t3` and `t41` (Néron models) |  | [neron-c](../docs/research/neron-c.md) |
| `neron-lg` | 2 | Reduces tau-n1n2's Neron glue NeronLocalToGlobal and SemistableLocalToGlobal to the leaf NeronLocalOnBase and five glue Props; local-glue and frob-pieces copy slices of NeronLG.lean, and spread-out reduces its N1-g1. | task | [neron-lg](../docs/research/neron-lg.md) |
| `notes-fix` | 3 | Applies the fact-check factcheck-w34b: strengthens fibre_conjugates_isomorphic in the kernel's HDecomp/QM/Leaves.lean and fixes docstrings and notes. | task → `ZInQKernel/HDecomp/QM/Leaves.lean` | [notes-fix](../docs/research/notes-fix.md) |
| `notes-fix2` | 2 | Fixes items 1, 3, 4, 6, 7 of the fork's issue #2 in scratch copies (leaf-qm-fp QMLeaves.lean, rv-qm-polar QMPolar.lean, rv-blueprints R16Transfer.lean) and in hdec-adopt2's log. | task | [notes-fix2](../docs/research/notes-fix2.md) |
| `nt-22p` | 5 | Research task on the prime-pattern hypothesis 22P: positive density of good primes, the Green-Tao 2008 step and the shape of the pattern, with density scripts. | task | [nt-22p](../docs/research/nt-22p.md) |
| `nt-h` | 7 | Research task on the height hypothesis H: what the consumers use, the slack, what a change of construction can buy, and older modularity routes, with scripts. | task | [nt-h](../docs/research/nt-h.md) |
| `nt-prop0` | 9 | Designs Proposition 0 (the 2-Selmer group of C_d through 2-coverings) for Lean with probes, test scripts and a Mathlib inventory; implemented by the p0-* tasks in RouteK/Selmer. | task | [nt-prop0](../docs/research/nt-prop0.md) |
| `nt-tyz` | 11 | Research task on the Tian-Yuan-Zhang citation behind CR3 (versions, numbering, the literal Theorem 1.2 being false, reading A), with check scripts that Contrib/TYZDecomp/Leaves.lean cites. | task | [nt-tyz](../docs/research/nt-tyz.md) |
| `obj-bridge` | 2 | Builds one object layer for the I2 and I3 leaves (pkg-I3 and pkg-I2 verbatim plus ObjBridge and restated leaves); now the kernel's HDecomp/Objects.lean. | ported → `ZInQKernel/HDecomp/Objects.lean` | [obj-bridge](../docs/research/obj-bridge.md) |
| `p-side` | 4 | Proves the positive-rank targets P1-P5 (coefficients and convergence of L(C_d, s), tyzInputs_iff) as seven new Contrib modules; the dir keeps axiom checks and a PARI script. | ported → `ZInQKernel/Contrib/PSide` | [p-side](../docs/research/p-side.md) |
| `p0-assembly` | 1 | Assembles Proposition 0 (prop0, certifiedRank_of_certifiedRankSel) and adds the certifiedRankSel headline to Main.lean; log only. | ported → `ZInQKernel/RouteK/Selmer/Prop0.lean` |  |
| `p0-bits` | 1 | Proves the Proposition 0 leaves 1-4 (local Selmer conditions as row conditions, the 2-adic class condition) in the kernel; log only. | ported → `ZInQKernel/RouteK/Selmer/Bits.lean` |  |
| `p0-charsum` | 1 | Proves the character-sum inputs of Proposition 0 (Lemma Q, Lemma J, fibre counts, exists_xi) in the kernel; log only. | ported → `ZInQKernel/RouteK/Selmer/CharSum.lean` |  |
| `p0-good` | 1 | Proves the good-prime local conditions G1, G2 of Proposition 0 in the kernel; log only. | ported → `ZInQKernel/RouteK/Selmer/Good.lean` |  |
| `p0-local` | 1 | Defines 2-coverings, Sel2 and CertifiedRankSel and proves the local square criteria and Lemma B (Covering, PadicSquare, Real, BadOdd) in the kernel; log only. | ported → `ZInQKernel/RouteK/Selmer/Covering.lean` |  |
| `p0-two` | 1 | Proves the 2-adic local condition of Proposition 0 (Lemma T, loc_two_adic_iff for odd d) in the kernel; log only. | ported → `ZInQKernel/RouteK/Selmer/Two.lean` |  |
| `pc-audit` | 26 | Scripts and outputs for the audit of the deep inputs of pole completeness by Route K (bordered lemma, kernel identities, Kriz examples, TYZ beta searches); no log. | data | [pc-audit](../docs/research/pc-audit.md) |
| `pd-lean-1` | 1 | Proves files 1-2 of Proposition D (Jacobsthal sums, point counts, goodSlopePrime criteria) as Density/CharSum.lean and Density/Description.lean; log only. | ported → `ZInQKernel/Density/Description.lean` |  |
| `pd-lean-2` | 1 | Proves the rest of Proposition D (Abel summation, prime tail, lattice and residue counts, PropD, PropDFinal with the Green-Tao corollary) in the kernel's Density modules; log only. | ported → `ZInQKernel/Density/PropD.lean` |  |
| `pd-paper` | 5 | Paper proof that the good slope primes have positive density (Proposition D), with check scripts; formalized by pd-lean-1, pd-lean-2 and pd-sieve. | task | [pd-paper](../docs/research/pd-paper.md) |
| `pd-sieve` | 1 | Vendors the Selberg sieve from PNT and proves the uniform bad-prime bound (GaussSieve) used by Proposition D; log only. | ported → `ZInQKernel/Density/GaussSieve.lean` |  |
| `period-glue` | 43 | period-glue: period-map's six glue Props; three proved, three reduced to leaves, no glue left |  | [period-glue](../docs/research/period-glue.md) |
| `period-map` | 66 | Reduces fibre-qm-period's PeriodMapGlue, HauptmodulUnique and QMDenZeroCM3 to smaller named Props; folded into g0-assemble3 and continued by period-glue. | task | [period-map](../docs/research/period-map.md) |
| `pi0-x6` | 3 | Shows rv-blueprints' sketch for pi0(X6) = 1 is incomplete and proves R1pi0Props from bundle clauses; adopted by leaf-adopt3 as section Pi0X6Sec of h-decomposition's Leaves.lean. | task | [pi0-x6](../docs/research/pi0-x6.md) |
| `pin-apply` | 14 | Integrates qm-pin's repair: patches the kernel's HDecomp/QM/Leaves.lean, adds the module QM/Pin.lean, updates h-decomposition's Leaves.lean and report, and checks that the old attack fails (AttackCheck.lean). | ported → `ZInQKernel/HDecomp/QM/Pin.lean` | [pin-apply](../docs/research/pin-apply.md) |
| `pkg-I1` | 7 | States package I1 (the discriminant-6 Shimura curve: period matrix, theta constants, Igusa invariants) as literature leaves, with numerics; now under HDecomp/Analytic (QMLattice, Torus). | ported → `ZInQKernel/HDecomp/Analytic` | [pkg-I1](../docs/research/pkg-I1.md) |
| `pkg-I2` | 2 | States package I2 (reduction theory: abelian varieties as group objects, torsion, inertia) as Lean leaves; now section B of HDecomp/Objects.lean and HDecomp/A6. | ported → `ZInQKernel/HDecomp/Objects.lean` | [pkg-I2](../docs/research/pkg-I2.md) |
| `pkg-I3` | 2 | States Faltings 1983 and Mumford (Tate modules, Hom, End; steps A9, C2, C10, E1) as Lean leaves; now section A of HDecomp/Objects.lean and HDecomp/I3Linalg. | ported → `ZInQKernel/HDecomp/Objects.lean` | [pkg-I3](../docs/research/pkg-I3.md) |
| `pkg-I4` | 2 | States the modularity package (h-trust C3-C5, C7-C9, D5) as Lean leaves; now HDecomp/Conductor/LadicCond.lean and Contrib/G9 (I4Layer, KerTheta). | ported → `ZInQKernel/HDecomp/Conductor/LadicCond.lean` | [pkg-I4](../docs/research/pkg-I4.md) |
| `pkg-I5` | 8 | States the Arakelov package (steps E2-E4, F3; the Faltings height) as literature leaves, with numeric checks; now HDecomp/Faltings (Height, HodgeData). | ported → `ZInQKernel/HDecomp/Faltings` | [pkg-I5](../docs/research/pkg-I5.md) |
| `pkg-I6` | 3 | States arithmetic of Q and of local fields (h-trust B1, B2, C10, D1, D3, D4) as leaves I6.1-I6.10; now HDecomp/Conductor/I6Base.lean and HDecomp/C10. | ported → `ZInQKernel/HDecomp/Conductor/I6Base.lean` | [pkg-I6](../docs/research/pkg-I6.md) |
| `pn-adopt` | 1 | Moves pn-design's PropN.lean into the kernel (RouteK/PropN.lean and Hypotheses/TYZInputs.lean) and adds the TYZInputs headline variant to MainLiterature.lean; log only. | ported → `ZInQKernel/RouteK/PropN.lean` |  |
| `pn-design` | 4 | Lean formalization of Proposition N (TYZ inputs I1-I7, lemmas N1, N2, finalStep, matching) in PropN.lean, whose sorries pn-n2, pn-part and pn-final filled; moved into the kernel by pn-adopt. | ported → `ZInQKernel/RouteK/PropN.lean` | [pn-design](../docs/research/pn-design.md) |
| `pn-final` | 2 | Proves finalStep of pn-design's PropN.lean (scratch copy Final.lean); the proof is in the kernel's PropN.lean. | ported → `ZInQKernel/RouteK/PropN.lean` |  |
| `pn-fix` | 3 | Applies rv-pn-encoding and tyz-t1 to the kernel's TYZInputs.lean and PropN.lean: docstrings and a sorry-free witness section for L n = 0 (draft Witness0.lean). | task → `ZInQKernel/RouteK/PropN.lean` |  |
| `pn-n2` | 5 | Proves lemmaN2 of pn-design's PropN.lean (scratch N2.lean = head + body + main); the proof is in the kernel's PropN.lean. | ported → `ZInQKernel/RouteK/PropN.lean` |  |
| `pn-part` | 2 | Proves matching and lemmaN1_core of pn-design's PropN.lean, with partition infrastructure in Infra.lean; the proofs are in the kernel's PropN.lean. | ported → `ZInQKernel/RouteK/PropN.lean` |  |
| `pole-descent-k` | 5 | Python checks of explicit 2-descent for the congruent-number curves C_n (Monsky matrices, 2-adic images, Hilbert symbols), importing rs-pole's selmer_descent; no log and no report. | data |  |
| `product-height` | 4 | Proves P2 ProductModelHeight from two glue Props and refutes h5-glue's claim that AN3 is needed; ProductHeight.lean is copied verbatim into product-unif's WithProductHeight.lean. | superseded; superseded by scratch/product-unif | [product-height](../docs/research/product-height.md) |
| `product-unif` | 10 | Proves ProductUnifSplits (S-an) and reduces ProductMetrizationOfProductUnif (S-alg); its WithProductHeight.lean is the start of unif-dims' Combined.lean. | superseded; superseded by scratch/unif-dims | [product-unif](../docs/research/product-unif.md) |
| `prop-ts` | 7 | Reduces Proposition TS (PropTSAll, Beckmann's specialization inertia theorem) for the fibre cover to two bundle leaves plus named glue; PropTS.lean is the first 906 lines of prop-ts-glue's PropTSGlue.lean. | superseded; superseded by scratch/prop-ts-glue | [prop-ts](../docs/research/prop-ts.md) |
| `prop-ts-glue` | 11 | Proves SpecNonMeeting and reduces KummerMeetGlue and CoverModelOfHecke under Proposition TS; PropTSGlue.lean is the base copied by ts-hecke, ts-kummer, ts-sn and hecke-rest. The 14 glue Props folded into g0-assemble3 are an earlier state: Steps 13-16 (VerticalResidueDegree, SNSpecializeUnram, specNonMeeting; 12 open glue Props) exist only here, with ts-sn as a parallel SN proof. | canonical | [prop-ts-glue](../docs/research/prop-ts-glue.md) |
| `qm-pin` | 29 | Repairs rv-g0pieces section 4 by pinning the QM moduli map Phi through the universal family (clauses R1famProps, R1univProps); applied by pin-apply as the kernel module QM/Pin.lean. | ported → `ZInQKernel/HDecomp/QM/Pin.lean` | [qm-pin](../docs/research/qm-pin.md) |
| `r10-amend` | 1 | States the amended leaf R10 (de Rham comparison with the Hodge-Tate weight clause) and derives glue step G9 from it, in Contrib/R10; log only. | ported → `ZInQKernel/Contrib/R10` | [r10-amend](../docs/research/r10-amend.md) |
| `r1b-state` | 17 | States R1(b), the analytic uniformization clause of R1, concretely (R1bProps) and derives g0-thetapoint's FibreQMPeriod; not folded into g0-assemble3, and its T11aHom is copied into Contrib/HomUnify/Corr.lean. | task → `ZInQKernel/Contrib/HomUnify/Corr.lean` | [r1b-state](../docs/research/r1b-state.md) |
| `redei-amb` | 1 | Proves the ambiguous-class step of Redei's formula (Hilbert 90, psi, kernel bounds) in the kernel; log only. | ported → `ZInQKernel/RouteK/Redei/Ambiguous.lean` |  |
| `redei-bridge` | 1 | Bridges the odd-class-group statement to RedeiFormula and CertifiedRankTYZRk in the kernel; log only. | ported → `ZInQKernel/RouteK/Redei/Bridge.lean` |  |
| `redei-four` | 1 | Proves the 4-rank count and redeiFormula in the kernel and drops hR from the TYZCl main-theorem variants; log only. | ported → `ZInQKernel/RouteK/Redei/FourRank.lean` |  |
| `redei-fp` | 1 | Builds the quadratic-field layer for Redei's formula (Field.lean, Primes.lean) in the kernel; log only. | ported → `ZInQKernel/RouteK/Redei/Field.lean` |  |
| `redei-genus` | 1 | Proves the genus characters (Genus.lean) and the Dirichlet step (Dirichlet.lean) of Redei's formula in the kernel; log only. | ported → `ZInQKernel/RouteK/Redei/Genus.lean` |  |
| `redei-kernel` | 1 | Proves the Redei-matrix kernel criterion kernel_trivial_iff_redeiG in the kernel (root RouteK/RedeiKernel.lean); log only. | ported → `ZInQKernel/RouteK/Redei/Kernel.lean` |  |
| `redei-plan` | 2 | Plan for proving Redei's formula on Mathlib v4.35 (genus theory plus Dirichlet, no Hasse-Minkowski) with a statement probe; carried out by the redei-* tasks in RouteK/Redei. | task | [redei-plan](../docs/research/redei-plan.md) |
| `redei-stmt` | 1 | States RedeiFormula for odd squarefree d (blocks of the 5b partitions) and adds a root variant; log only, kernel file inferred from the log. | ported → `ZInQKernel/RouteK/Rank5b/Sec3/RedeiStatement.lean` |  |
| `ring-class` | 21 | Vendors Tau Ceti's ring class fields and proves cm-points' leaves HprimeNormal and IInH4 and pins the family ringClassFieldD, in Contrib/TYZGenus/RingClass*.lean. | ported → `ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean` | [ring-class](../docs/research/ring-class.md) |
| `rleaf-elliptic` | 12 | Proves the elliptic-curve textbook leaves T36 (torsion) and T37 (good reduction) from vendored Tau Ceti, so BelyiX1 holds; Contrib/RLeaf. | ported → `ZInQKernel/Contrib/RLeaf` | [rleaf-elliptic](../docs/research/rleaf-elliptic.md) |
| `rs-global` | 7 | Scripts for the architecture note rs-global (witness budget, audit roles, parity device, five-contact maps); no log. | data | [rs-global](../docs/research/rs-global.md) |
| `rs-height` | 4 | Scripts for the note on H's uses, slack and cheaper routes (CM factors, curves, dihedral covers, small M); no log. | data | [rs-height](../docs/research/rs-height.md) |
| `rs-pattern` | 11 | Scripts and outputs for the note on the fixed prime pattern 22P (good primes, slope and pattern searches in Python and C); no log. | data | [rs-pattern](../docs/research/rs-pattern.md) |
| `rs-pole` | 9 | Scripts for the pole-completeness note (2-descent library selmer_descent.py, point checks, patch and phi searches); no log. | data | [rs-pole](../docs/research/rs-pole.md) |
| `rv-a6-route` | 4 | Adversarial review of pkg-I2's Raynaud route for step A6 (Lemma PR(ii)) with quaternion valuation proofs; A6.lean was copied by glue-a6-alg into HDecomp/A6/A6.lean. | ported → `ZInQKernel/HDecomp/A6/A6.lean` | [rv-a6-route](../docs/research/rv-a6-route.md) |
| `rv-barrier` | 5 | Adversarial review of Theorem G (el-gadget) and Lemma G (el-special) with rerun scripts; its report is docs/research/rv-cr3-barrier.md. | task | [rv-cr3-barrier](../docs/research/rv-cr3-barrier.md) |
| `rv-blueprints` | 31 | Adversarial review of the three formalization blueprints, with compile audits of each blueprint file (Audit_*.lean) and repairs Q1-Q5. | task | [rv-blueprints](../docs/research/rv-blueprints.md) |
| `rv-cr3-dl` | 4 | Review of cr3-dl (RouteK/RankDL.lean) and of the rv-cr3-rank follow-up; no Lean blocker. | task | [rv-cr3-dl](../docs/research/rv-cr3-dl.md) |
| `rv-cr3-rank` | 4 | Review of CR3 in positive-rank form (RK9 and Mordell-Weil for C_d); no blocker. | task | [rv-cr3-rank](../docs/research/rv-cr3-rank.md) |
| `rv-cr3-trust` | 6 | Adversarial review of the CR3 trust statement cr3-trust.md, with Lean composition checks (Check.lean). | task | [rv-cr3-trust](../docs/research/rv-cr3-trust.md) |
| `rv-cr5b-sec3` | 4 | Referee review of cr5b-sec3 (the hypothesis CertifiedRankTYZ) with a 30-value red-team script. | task | [rv-cr5b-sec3](../docs/research/rv-cr5b-sec3.md) |
| `rv-elim3` | 32 | Adversarial review of el-cert, el-k3 and el-qfree with computations; its report is docs/research/rv-cr3-elim3.md. | task | [rv-cr3-elim3](../docs/research/rv-cr3-elim3.md) |
| `rv-fast` | 8 | Adversarial review of curve-infra, lg-kerwild, unram-roots, afr-absfrob and ring-class (reassembly checks and *Check.lean files). | task | [rv-fast](../docs/research/rv-fast.md) |
| `rv-g0pieces` | 6 | Truth review of g0-split's ten glue pieces (none refuted), with Exotic.lean probes and numeric checks; its section 4 led to qm-pin. | task | [rv-g0pieces](../docs/research/rv-g0pieces.md) |
| `rv-gluepieces2` | 47 | Truth review of the 27 fields of g0-assemble's GluePieces2, building GluePieces3 and sixContactMin_of_leaves3 in an olean-prefix assembly. | task | [rv-gluepieces2](../docs/research/rv-gluepieces2.md) |
| `rv-h-a011` | 3 | Review of the audit record A011-V14 (h-a011.md) against Pan and the V14 source. | task | [rv-h-a011](../docs/research/rv-h-a011.md) |
| `rv-h-a9c9` | 5 | Second review of A9's Milne paragraph and C9's Li-Shimura sentence, with scripts. | task | [rv-h-a9c9](../docs/research/rv-h-a9c9.md) |
| `rv-h-b1` | 5 | Review of route B1 (h-b1.md): tame specialization in place of the integral model, with rerun checks. | task | [rv-h-b1](../docs/research/rv-h-b1.md) |
| `rv-h-c3` | 2 | Second review of the de Rham descent lemma (step C3 of H). | task | [rv-h-c3](../docs/research/rv-h-c3.md) |
| `rv-h-c8` | 5 | Review of the twist-and-weight step C8 of h-trust, with normalization checks. | task | [rv-h-c8](../docs/research/rv-h-c8.md) |
| `rv-h-cm` | 2 | Check script and output for the review of h-cm.md (the CM branch of the six-contact estimate); no log. | data | [rv-h-cm](../docs/research/rv-h-cm.md) |
| `rv-h-novel` | 4 | Review of the novel steps in the proof of Theorem 4.1 (scalar descent, the system at 3 and 5, transfer), with scripts. | task | [rv-h-novel](../docs/research/rv-h-novel.md) |
| `rv-h-trust` | 4 | Review of h-trust.md, the trust statement for H, with a branch check script. | task | [rv-h-trust](../docs/research/rv-h-trust.md) |
| `rv-hsyn` | 2 | Fact-check of h-decomposition.md with a compile of its Leaves.lean (LeavesCheck.lean). | task | [rv-hsyn](../docs/research/rv-hsyn.md) |
| `rv-jac-ext` | 8 | Checks whether the degree-one-divisor extension for Axiom's Jacobians fits Theorem 4.1's bounds, with scripts. | task | [rv-jac-ext](../docs/research/rv-jac-ext.md) |
| `rv-leaves-a` | 8 | Review of the I1, I5 and assembly leaves, with hardened Lean variants. | task | [rv-leaves-a](../docs/research/rv-leaves-a.md) |
| `rv-leaves-b` | 2 | Review of the object layer and the leaves of I2, I3, I6 and the conductor cluster (Repairs.lean). | task | [rv-leaves-b](../docs/research/rv-leaves-b.md) |
| `rv-leaves48` | 7 | Review of the 48 concrete leaves of the H decomposition (agent notes, probes, repair list). | task | [rv-leaves48](../docs/research/rv-leaves48.md) |
| `rv-lit` | 6 | Review of the two literature reductions (wk-cr3, lit-adopt) against Mathlib's L-function definitions, with probes. | task | [rv-lit](../docs/research/rv-lit.md) |
| `rv-loc-leaves` | 8 | Checks the Lean leaves against the locator audit and writes the Leaves.lean patch that loc-fix applied; its Pazuki R22 definitions are copied into HDecomp/LeafPush2/R22.lean. | task → `ZInQKernel/HDecomp/LeafPush2/R22.lean` | [rv-loc-leaves](../docs/research/rv-loc-leaves.md) |
| `rv-nocm` | 5 | Review of NoCM (step A10) and the branch indices of step A5 after the locator audit (Neat.lean, OrbifoldIndex.lean); repairs applied by loc-fix. | task | [rv-nocm](../docs/research/rv-nocm.md) |
| `rv-nt-tyz` | 20 | Referee report on nt-tyz with coefficient and counterexample computations. | task | [rv-nt-tyz](../docs/research/rv-nt-tyz.md) |
| `rv-nt22p-ap` | 3 | Referee report on nt-22p: Proposition AP, Proposition D and the Green-Tao step. | task | [rv-nt22p-ap](../docs/research/rv-nt22p-ap.md) |
| `rv-nt22p-proof` | 2 | Referee report on Lemma P and the modified completeness argument of nt-22p. | task | [rv-nt22p-proof](../docs/research/rv-nt22p-proof.md) |
| `rv-nt22p-red` | 28 | Referee report on nt-22p sections 3.2-3.3 (Lemma P, the modified choice of q, Proposition AP) with searches. | task | [rv-nt22p-red](../docs/research/rv-nt22p-red.md) |
| `rv-pd-paper` | 3 | Referee report on pd-paper (positive density of the good slope primes). | task | [rv-pd-paper](../docs/research/rv-pd-paper.md) |
| `rv-prop-n` | 14 | Second review of Proposition N (nt-tyz section 4) and of F1, F2, with numerics. | task | [rv-prop-n](../docs/research/rv-prop-n.md) |
| `rv-qm-polar` | 3 | Proves the polarization premise of the QM leaves (Lemma P on QM tori); QMPolar.lean is now HDecomp/QM/Polar.lean. | ported → `ZInQKernel/HDecomp/QM/Polar.lean` | [rv-qm-polar](../docs/research/rv-qm-polar.md) |
| `rv-redei` | 4 | Review of the Lean proof of Redei's formula (no blocker, docstring nits). | task | [rv-redei](../docs/research/rv-redei.md) |
| `rv-route-k` | 45 | Search scripts and outputs for the adversarial check of Route K for pole completeness; no log. | data | [rv-route-k](../docs/research/rv-route-k.md) |
| `rv-routek` | 5 | Adversarial review of Route K (modularity through GL2-type varieties over Q), with checks. | task | [rv-routek](../docs/research/rv-routek.md) |
| `rv-slot-k-descent` | 11 | Referee report on the 2-descent behind Route K's slot construction, with Selmer computations. | task | [rv-slot-k-descent](../docs/research/rv-slot-k-descent.md) |
| `rv-slot-k-proof` | 10 | Referee report on the proof of the descent lemma in slot-k.md section 2, with validation scripts. | task | [rv-slot-k-proof](../docs/research/rv-slot-k-proof.md) |
| `rv-slot-k-red` | 30 | Referee report on the slot construction: counterexample and edge-case searches. | task | [rv-slot-k-red](../docs/research/rv-slot-k-red.md) |
| `rv-tyz-inputs` | 14 | Review of the Tian-Yuan-Zhang inputs of Proposition N with numerics (tyzcalc.py is cited by Contrib/TYZDecomp/Leaves.lean). | task | [rv-tyz-inputs](../docs/research/rv-tyz-inputs.md) |
| `rv-up` | 13 | Verification of the upstream surveys up-map, up-h, up-cr3 and up-rest. | task | [rv-up](../docs/research/rv-up.md) |
| `rv-wave17` | 15 | Review of the wave-17 Lean statements with compile checks. | task | [rv-wave17](../docs/research/rv-wave17.md) |
| `ser-ell` | 3 | Audit of nt-h section 4.2, route 1 (Serre's argument at large l), against the sources. | task | [ser-ell](../docs/research/ser-ell.md) |
| `shimura-modfn` | 6 | shimura-modfn: `Shimura.ShimuraReciprocityModFn` and the main theorem of CM for `j` |  | [shimura-modfn](../docs/research/shimura-modfn.md) |
| `slot-k` | 22 | Running notes, scripts and outputs for the descent lemma of Route K (slot construction); its Python modules are reused by cr3-check and the rv-slot-k reviews. | task | [slot-k](../docs/research/slot-k.md) |
| `smooth-fibre` | 2 | smooth-fibre: `SmoothFibreReduced` proved from Mathlib |  | [smooth-fibre](../docs/research/smooth-fibre.md) |
| `spread-out` | 13 | Reduces neron-lg's glue N1-g1 AbVarSpreadsOut to three EGA IV leaves; the modules are Contrib/SpreadOut, and SpreadOutFull.lean is a composite over frob-pieces. | ported → `ZInQKernel/Contrib/SpreadOut` | [spread-out](../docs/research/spread-out.md) |
| `sqrt2-glue` | 3 | sqrt2-glue: `SqrtTwoNotInHHprime` (√2 ∉ ℍ'_n) is proved in Lean, so TYZ Lemma 3.18 (`Lemma318Literal HHprime`) holds with no hypotheses |  | [sqrt2-glue](../docs/research/sqrt2-glue.md) |
| `ss-exponent` | 2 | ss-exponent: `SupersingularExponentA` is a theorem (Mathlib only) |  | [ss-exponent](../docs/research/ss-exponent.md) |
| `stab-clash` | 9 | stab-clash: every Contrib module importable at once |  | [stab-clash](../docs/research/stab-clash.md) |
| `swan` | 7 | Proves the glue Props SwanIndependent, SwanIntegral and AdaptedExists of the kernel's LadicCond unconditionally; folded into g0-assemble2. | task | [swan](../docs/research/swan.md) |
| `t-brauer-purity` | 8 | Proves leaf T2 (Abhyankar, T2Kernel.lean; frontier.md cites it as the proof) and the real place of T15, which is now Contrib/BrauerT14T15/Real.lean. | task → `ZInQKernel/Contrib/BrauerT14T15/Real.lean` | [t-brauer-purity](../docs/research/t-brauer-purity.md) |
| `t-different` | 6 | Proves the ramification leaves T20-T22 (Hilbert's different formula, Serre's bound, Herbrand); now HDecomp/Textbook/Different.lean and Contrib/Different/Local.lean. | ported → `ZInQKernel/HDecomp/Textbook/Different.lean` | [t-different](../docs/research/t-different.md) |
| `t-purity2` | 11 | Continues t-brauer-purity on T1, T14, T15 (narrowed and profinite-cochain forms). T15 and the T14 reduction were later done through Tau Ceti by t1415-tc, and T14 closed by kummer-index (Contrib); the T1 leaf is unused, and its dimension-2 case, built by t-purity3 from this directory's T1Local.lean, is proved inside prop-ts-glue. | superseded; superseded by scratch/t1415-tc and scratch/prop-ts-glue | [t-purity2](../docs/research/t-purity2.md) |
| `t-skolem-kw` | 10 | Proves textbook leaves T13, T17, T18, T19 (Skolem-Noether, Kronecker-Weber use, Chebotarev forms, Brauer-Nesbitt); now under HDecomp/Textbook. | ported → `ZInQKernel/HDecomp/Textbook` | [t-skolem-kw](../docs/research/t-skolem-kw.md) |
| `t10-etale` | 2 | States T10 Galois-equivariantly over Mathlib's l-adic cohomology; now HDecomp/Textbook/T10Etale.lean. | ported → `ZInQKernel/HDecomp/Textbook/T10Etale.lean` | [t10-etale](../docs/research/t10-etale.md) |
| `t1415-tc` | 6 | Proves T15 and reduces T14 to KummerIndexBound from vendored Tau Ceti's Brauer theory, as new Contrib modules; the dir keeps axiom checks. | ported → `ZInQKernel/Contrib/BrauerT14T15` | [t1415-tc](../docs/research/t1415-tc.md) |
| `t25-newform` | 5 | Proves leaf T25 NewformOfEigenform from Tau Ceti's newform theory, in Contrib/T25; the dir keeps axiom checks. | ported → `ZInQKernel/Contrib/T25` | [t25-newform](../docs/research/t25-newform.md) |
| `t28-igusa` | 28 | Proves the forward half of T28 (Igusa invariants separate binary sextics) and reduces the converse to M3 and the special locus; now HDecomp/Textbook/Igusa. | ported → `ZInQKernel/HDecomp/Textbook/Igusa` | [t28-igusa](../docs/research/t28-igusa.md) |
| `t30-adelic` | 4 | Derives T30 (LeafSqrtCrit) from local Kronecker-Weber and does the adelic bookkeeping of A3; now HDecomp/Textbook (T30SqrtCrit, G1Adelic, G1Count). | ported → `ZInQKernel/HDecomp/Textbook/T30SqrtCrit.lean` | [t30-adelic](../docs/research/t30-adelic.md) |
| `t31-unram` | 3 | Proves leaf T31 GlueDescent.B2Q.LeafUnramified in Contrib/T31; the dir keeps axiom checks. | ported → `ZInQKernel/Contrib/T31` | [t31-unram](../docs/research/t31-unram.md) |
| `t40-clash` | 9 | t40-clash: T40 can now be imported next to the other Contrib Tau Ceti modules |  | [t40-clash](../docs/research/t40-clash.md) |
| `t40-igusa` | 1 | Igusa transitivity for leaf T40 (IgusaTransitive iff X0Transitive and TateMuN), in Contrib/RLeaf (T40, IgusaSL2, IgusaX0, IgusaLocal); log only. | ported → `ZInQKernel/Contrib/RLeaf/T40.lean` | [t40-igusa](../docs/research/t40-igusa.md) |
| `t40-tate` | 12 | Proves the Tate-curve inputs TateCuspLaurent and TateMuN of T40, with Tau Ceti backport scripts, in Contrib/RLeaf (TateCusp*). | ported → `ZInQKernel/Contrib/RLeaf/TateCusp.lean` | [t40-tate](../docs/research/t40-tate.md) |
| `t5-torsion` | 19 | t5-torsion: T5 reduced to `deg [n] = n^{2g}` (plus separability in characteristic p); T26 follows from T5; every use of T5 in the H proof follows from T35 |  | [t5-torsion](../docs/research/t5-torsion.md) |
| `tau-n1n2` | 2 | Reduces the Neron leaves N1 and N2 to three literal leaves and two glue Props (n1_n2_of_leaves); neron-lg continues with the two glue Props. | task | [tau-n1n2](../docs/research/tau-n1n2.md) |
| `tc-license` | 3 | Apache-2.0 compliance of the vendored Tau Ceti code (modification notes and a diff check). | task | [tc-license](../docs/research/tc-license.md) |
| `tc-port` | 8 | Vendors Tau Ceti into Contrib/TauCeti (closure lists, build and axiom checks); provenance in ThirdParty/TauCeti/NOTICE. | ported → `ZInQKernel/Contrib/TauCeti` | [tc-port](../docs/research/tc-port.md) |
| `tc-survey` | 4 | Survey of the open leaves of the H decomposition against Tau Ceti, with a comparison file. | task | [tc-survey](../docs/research/tc-survey.md) |
| `ts-hecke` | 19 | Settles or reduces the five Hecke Props under CoverModelOfHecke (prop-ts-glue Part C), continued by hecke-rest: HeckeRestAll.lean holds the TSHecke.lean of before Step 11 and proves the leftover targets against the older, stronger HeckeFibreSizes. Step 11 exists only here. | task | [ts-hecke](../docs/research/ts-hecke.md) |
| `ts-kummer` | 7 | Proves the six Kummer pieces and, in Step 7, its own KummerCompositum (`TsKummer.kummerCompositum_proof`); kummer-comp copies its Step-6 file and proves KummerCompositum independently. The KummerTS.lean on main has a forward reference and no recorded compile; the fixed file and report are on the unmerged wip/ts-kummer, which the frontier checker reads. | superseded; superseded by scratch/kummer-comp | [ts-kummer](../docs/research/ts-kummer.md) |
| `ts-sn` | 7 | Proves SNSpecialize, so SpecNonMeeting is a theorem (TSSN.lean over prop-ts-glue); frontier.md also lists the proof at a prop-ts-glue commit. | task | [ts-sn](../docs/research/ts-sn.md) |
| `twist-descent` | 14 | Proves kf-glue's TwistDescent (bundle field 33, scratch TwistDescent.lean) and GaloisDescentMor; the Mathlib-only Galois descent is Contrib/TwistDescent/GaloisDescent.lean. | task → `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean` | [twist-descent](../docs/research/twist-descent.md) |
| `tyz-318` | 6 | tyz-318: TYZ Lemma `torsion2` (`Lemma318Literal HHprime`) reduced to one glue Prop (`√2 ∉ ℍ'_n`); no leaf left |  | [tyz-318](../docs/research/tyz-318.md) |
| `tyz-321` | 5 | tyz-321: TYZ Lemma 3.21(1) (`Lemma321Five`) proved from tyz-cm's Shimura-reciprocity leaf alone |  | [tyz-321](../docs/research/tyz-321.md) |
| `tyz-35` | 7 | tyz-35: `Thm35First ℓ tyzZ` reduced to TYZ Theorem 3.3 (with Lemma 3.14) for the pinned CM points |  | [tyz-35](../docs/research/tyz-35.md) |
| `tyz-5b` | 12 | Route K on published theorems: Tian-Yuan-Zhang row 5b for the slot curves, with checks. | task | [tyz-5b](../docs/research/tyz-5b.md) |
| `tyz-chain` | 2 | tyz-chain: the TYZ side in one importable module |  | [tyz-chain](../docs/research/tyz-chain.md) |
| `tyz-cm` | 27 | Works on the CM leaf of the TYZ genus package (CMFieldOfDefinition, TYZSigmaFixesZn); the Shimura modules were committed to Contrib/TYZGenus, and the dir keeps drafts and eta-quotient numerics. | ported → `ZInQKernel/Contrib/TYZGenus/ShimuraMain.lean` | [tyz-cm](../docs/research/tyz-cm.md) |
| `tyz-decomp` | 3 | Decomposes the premise TYZThm35ReadingA into literature leaves plus glue; the Lean is Contrib/TYZDecomp (CurveA, Leaves). | ported → `ZInQKernel/Contrib/TYZDecomp` | [tyz-decomp](../docs/research/tyz-decomp.md) |
| `tyz-lcal` | 4 | tyz-lcal: the three L-leaves of the TYZ decomposition |  | [tyz-lcal](../docs/research/tyz-lcal.md) |
| `tyz-t1` | 12 | Closes residual doubt T1 (the constant of TYZ Theorem 3.3) with Petersson and Heegner computations. | task | [tyz-t1](../docs/research/tyz-t1.md) |
| `unif-dims` | 24 | Proves ProductUnifDims and ProductHodgeLattice from T35 and TangentDimAtOrigin, so P2 follows; Combined.lean holds the product-height, product-unif, metrization2 chain and is folded into g0-assemble3 and leaf-fold2. | canonical | [unif-dims](../docs/research/unif-dims.md) |
| `unram-roots` | 9 | Proves local-glue's UnramRoots p l from Mathlib and vendored Tau Ceti; adopted by frob-contrib as Contrib/UnramRoots. | ported → `ZInQKernel/Contrib/UnramRoots` | [unram-roots](../docs/research/unram-roots.md) |
| `unram-tate` | 5 | Proves g0-mod-field's UnramifiedSup and TateBridge (from TateModuleFree); TateBridge.lean is copied whole into frob-trace and in part into linked-tate and g8-tate, and BCPoints.lean is now Contrib/AbVarBC/Points.lean. | task → `ZInQKernel/Contrib/AbVarBC/Points.lean` | [unram-tate](../docs/research/unram-tate.md) |
| `up-cr3` | 4 | Survey of the pole-completeness side of upstream Versions 13-16 and the 214-variable proposal. | task | [up-cr3](../docs/research/up-cr3.md) |
| `up-h` | 3 | Survey of the H side of upstream Versions 13-16 and the 214-variable proposal. | task | [up-h](../docs/research/up-h.md) |
| `up-map` | 7 | Map of the upstream manuscript versions after N5 (section diffs, theorem-number tables). | task | [up-map](../docs/research/up-map.md) |
| `up-rest` | 7 | Survey of upstream Versions 13-16 against the fork's other inputs (22P, CAT, MW, compiler, size, Lean, audit). | task | [up-rest](../docs/research/up-rest.md) |
| `upstream` | 1 | List of the 925 Lean files pinned by upstream's KERNEL_CONTRACT.json (tree 9c7b60ef, upstream through PR #36), cited by frob-contrib.md; no log. | data |  |
| `v14-routes` | 3 | checks.py and its output, cited as evidence in §5.1 of docs/research/v14-routes.md; the note itself was rewritten by v14-routes2. | data | [v14-routes](../docs/research/v14-routes.md) |
| `v14-routes2` | 3 | Rewrites docs/research/v14-routes.md against the published V14 source (hunk table, statement checks). | task | [v14-routes](../docs/research/v14-routes.md) |
| `vert-witness` | 8 | vert-witness: `HeckeVertWitness` from good reduction of `Y₃` |  | [vert-witness](../docs/research/vert-witness.md) |
| `weil-pairing` | 3 | Defines polarizations and the Weil pairing over PkgI3.AbVar with the leaves T09_SymmIsogenyExists, IsogenyQuasiInverse, DivisiblePoints; folded via g12-det into g0-assemble2 and g0-assemble3. | task | [weil-pairing](../docs/research/weil-pairing.md) |
| `wk-cr3` | 7 | Reduces CR3 to well-known theorems (Literature.lean, with convention checks); lit-adopt moved the Lean into Hypotheses/CR3Literature.lean. | ported → `ZInQKernel/Hypotheses/CR3Literature.lean` | [wk-cr3](../docs/research/wk-cr3.md) |
| `wk-h` | 5 | Plan for reducing H to well-known theorems: BackToU.lean is now Hypotheses/JHeight.lean (moved by lit-adopt), with f4_cert.py supplying its certificates; Arakelov.lean (one sorry) stays in scratch. HDecomp/Assembly.lean re-proves its E3-E4 arithmetic. | ported → `ZInQKernel/Hypotheses/JHeight.lean` | [wk-h](../docs/research/wk-h.md) |
| `x0-32` | 9 | The modular curve X0(32) over Mathlib's objects (eta quotients, cusps, Fricke involution), with numerics; now Contrib/TYZGenus/X0.lean. | ported → `ZInQKernel/Contrib/TYZGenus/X0.lean` | [x0-32](../docs/research/x0-32.md) |
| `x1-belyi` | 3 | Derives X1ModelExists and BelyiX1 from five literature leaves; now HDecomp/ModCurves/X1Belyi.lean. | ported → `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean` | [x1-belyi](../docs/research/x1-belyi.md) |
| `x1-dirichlet` | 6 | Proves DirichletOfFinite and X1ModelExists for g0-mod-newform; folded into g0-assemble2 and not in the kernel. | task | [x1-dirichlet](../docs/research/x1-dirichlet.md) |
| `x6-kummer` | 14 | Proves N2 X6KummerFibre from one explicit leaf (the conic model of X6) and MobiusGlue and checks N1b; folded into g0-assemble3 (field 3) and leaf-fold2. | task | [x6-kummer](../docs/research/x6-kummer.md) |
| `zariski-conn` | 11 | zariski-conn: `ProperSmoothGenConnected` reduced to Zariski's connectedness theorem |  | [zariski-conn](../docs/research/zariski-conn.md) |
