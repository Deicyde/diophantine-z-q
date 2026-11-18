# RC53: dependency graph of the Lean proof of Theorem 5.3 (restricted converse)

Target: `ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine` (Theorem 5.3, `hyp:RC`,
`diophantine_zq.tex` L1005–1011). Proof: Sections 7–9 (L1760–5744) and Appendices E–G
(L6825–10935). Blueprint (shared top layer): `ZInQKernel/Contrib/CloudB3RC53/{Basic,Prints,Prints/CST,Nodes,Assembly}.lean`
and this file.

Assembly (no `sorry`, standard axioms):

```
restrictedConverseGenuine_of_nodes :
  Prints → BranchPackageNode → MissingAddressNode → RestrictedConverseGenuine
```

The status column below records the state when each row was written; several rows have since
advanced, and the module headers of the area files are authoritative for the current status (e.g. the
GenusOdd and Duality rows, updated below).

Status keys: **PROVED** (Lean theorem, standard axioms); **OPEN** (Lean `Prop` stated, proof
pending); **STATED-DEFS** (the manuscript statement needs objects that are not yet defined in
Lean; the row names them); **PRINT** (cited published result).

Owners. **TOP**: the top layer (this blueprint). **RC0–RC16**: the #83 team's lanes (RC0 skeleton =
`BranchPackageNode`; RC1 missing address; RC2 §7.3 symbols, seeds, addresses and App G L10508–10791;
RC3 K-split seed; RC4 moving character; RC6 limits and outer DVR; RC7 determinant clearing; RC8, RC9
printed leaves; RC10 Heegner finite cores; RC11 §7.1 and App E; RC12 App F; RC13 nonvanishing; RC15
calibration, common coordinate, central specialization, base zero; RC16 switches and (5.5)).
**Areas** of the RC53 lanes (files `CloudB3RC53/<Area>/`): **Duality** (L2761–2830, 3395–3496),
**PairedFunctional** (L3704–3880), **HeegnerCohomology** (cohomological layer of L2834–3410),
**RankCounts** ((5.1) L4458–4648, (5.7) L5207–5484), **GenusOdd** (§7 L2403–2591),
**AppGEndpoints** (App G L10151–10256, L10792–10861).

## Top level

| node | Lean | tex | depends on | owner | status |
|---|---|---|---|---|---|
| Theorem 5.3 | `restrictedConverseGenuine_of_nodes` | 1771–1776, 5666–5741 | Prints, BranchPackageNode, MissingAddressNode, the rows below | TOP | PROVED (from the two open nodes) |
| root number −1 | `RootNumberNode`, `rootNumberNode_proof` | 1792–1796 | DD Thm 1.8; rational 2-torsion of `E_ℓ` (`PoleRC`) | TOP | PROVED |
| `L(E,1) = 0` | `CentralValueZeroNode`, `centralValueZeroNode_proof` | (not a sentence of the text; used implicitly at 5734–5736, 10922–10924, from the root number −1 of 1792–1796) | functional equation at `s = 1` | TOP | PROVED |
| final deduction | `FinalRankDeductionNode`, `finalRankDeductionNode_proof` | 5734–5736, 10922–10924 | root number −1; order of a product | TOP | PROVED |
| missing address (5.10)–(5.11) | `MissingAddressNode`; `ZInQ.Manuscript.RC.Boolean.missingAddressNode` | 5666–5735 | Boolean bit degree, cube parity, Gauss lemma for `𝒪` | RC1 | PROVED (on `rc/thm53-proof-20261117`) |
| Branch 1 or Branch-2 package | `BranchPackageNode` (`FixedFieldPackage`) | 2587–2602, 2595–2715, 2718–5664, App E–G | every row below | RC0 | reduced by RC0 (`ZInQ.Manuscript.RC.branchPackageNode_of_steps`) to `Prints`, one Kummer GLUE and the 13 fields of `RCSteps`; fields OPEN. At this layer the coefficient data `C` are existential and are not tied to the genuine coordinates `ũ_x`: constant data inhabit the package as soon as `L(E^{(k)},1) ≠ 0` and `¬ ProductOrderGeTwo E k`, so, given `Prints`, `BranchPackageNode` is equivalent to Theorem 5.3. The reduction to Elliot's steps is lane RC0's `restrictedConverseGenuine_of_steps'` (now `RC.Wiring.restrictedConverseGenuine_of_leaves`), whose `RCSteps.clearing` ties `C.u x j = [tʲ] ũ_x`. |

`FixedFieldPackage` fields and their sources:

| field | meaning | tex | sources |
|---|---|---|---|
| `k`, `hk` | final companion, `L(E^{(k)},1) ≠ 0` | 2595–2600 | even unit symbol (App E, App G), HL |
| `B` | `v₂ ũ_x(0) ≤ B` at `x ≠ 0` | AppGEndpoints | (3.9) ex:sec7-final-family / ex:app-final-family; (3.4) ex:sec7-genus-lower (CST); (4.6) ex:arith-central-calibration; (4.7) ex:arith-common-coordinate |
| `cdet`, `LT`, `ClearingIdentity`, `PoleBound`, `BaseRegular` | (5.9) | RankCounts | ex:limits-fixed-field-budget (5.6)–(5.8); ex:arith-paired-functional (exponent `a`); ex:arith-common-coordinate (`η`); height-one regularity of ex:limits-uniform-lower-bound (`ũ_x ∈ Λ[1/2]`) |
| `BaseZero` | `L'(E/K,1) = 0 ⇒ ũ_0(0) = 0` | RC15 | ex:arith-base-zero: CST at conductor one; Smith reduction over the DVR `Λ_(t)`; `s₂(E/K) = 1` (2617–2628) |

`RCSteps` fields (RC0, `ZInQKernel/Contrib/OneProof/RC/Skeleton/Steps.lean`) and owners: `stages_advance`
(2491–2551) and `gz_comparison` (3.4) (2427–2439, 2713–2714): GenusOdd; `final_family` (3.9) (2695–2715,
10792–10858): AppGEndpoints; `clearing` (5.9): RC7 with RankCounts and PairedFunctional;
`lstar_ne_zero_iff`: RC11; `genus_partner`: RC13; `visibility`, `one_admissible`: RC12; `companion`:
RC2/RC11/RC13; `calibration`, `common_coordinate`, `base_zero`: RC15; `height_one`: RC16.

## Section 7 (sec:rc), L1760–2715

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| setup: modularity, parametrization `π`, root number | 1760–1797 | BCDT, Milne MF 11.19, DD | TOP | root number PROVED; `π` STATED-DEFS (`X₀(N)`, `J₀(N)`) |
| ex:sec7-even-scalar (3.2) | 1832–1966 | App E | RC11 | STATED-DEFS (`Λ`, Kato class, positive complex) |
| ex:sec7-nonvanishing | 1969–2004 | HL, BFH, Desjardins, ex:app-five-prime | RC13 | STATED-DEFS → OPEN once HL/BFH/Desjardins are stated |
| ex:sec7-typed-graph, ex:sec7-symbol | 2006–2070 | (3.2), (3.8) | RC2 | STATED-DEFS (typed residue graphs, coefficient symbols) |
| ex:sec7-coefficient-rules | 2102–2119 | ex:app-coefficient-rules | RC12 | STATED-DEFS |
| ex:sec7-realization | 2151–2142 | CRT, Dirichlet, reciprocity | RC2 | OPEN once stated (finite) |
| ex:sec7-seed-certificate | 2188–2177 | coefficient rules | RC2 | OPEN once stated (finite) |
| ex:sec7-one/two-symbol-address | 2222–2271 | ex:app-simultaneous-address | RC2 | finite cores OPEN |
| ex:sec7-even-upper (3.3b) | 2295–2318 | (3.2), seeds, Boolean bit degree | RC11 | inequality core OPEN |
| ex:sec7-rough-companion (3.3) | 2343–2401 | HL, forward rank zero, (3.3b) | RC13 | STATED-DEFS (`L_*`) |
| ex:sec7-genus-lower (3.4)–(3.6) | 2418–2458 | CST ×2, index-≤2 glue, (3.5) | GenusOdd | (3.4) PROVED (`genusLower34_of_newform`, `GenusOdd/LocalFinal.lean`) from `Prints`, lane RC8's `HasseConvergence` (GLUE) and `ModularNewform` (PRINT), and the inert clause `LocalFactorInert` (GLUE); (3.3)+(3.4)+(3.5)⇒(3.6) core PROVED (`GenusOdd/Node34.lean`) |
| fixed witness, theta forms, (3.7), (3.8) | 2460–2551 | App F, Cornut–Jetchev, CST | GenusOdd (D_w, (3.7), δ) / RC12 ((3.8)) | STATED-DEFS |
| common family (Waldspurger) | 2553–2591 | Waldspurger Cor 2 | GenusOdd | STATED-DEFS |
| Branch 1 (empty unit) | 2587–2592 | (O.8) at `D = 1` | RC0 | inside BranchPackageNode (left disjunct) |
| final companion, `s₂(E/K) = 1` | 2595–2628 | forward rank zero (Kolyvagin), isogeny `Res E → E × E^{(k)}` | RC0 | STATED-DEFS (`s₂(E/K)`) |
| ex:sec7-ksplit-seed | 2628–2655 | App G mod-8 computation; `#E_ℓ(𝔽_p)[2^∞] = 4` | RC3 | OPEN (finite, genuine: points over `𝔽_p`) |
| packet realization | 2657–2672 | grounded Laplacian minors | RC2 | finite core OPEN |
| ex:sec7-final-family (3.9) | 2674–2713 | address lemmas, (3.4), (3.8) | AppGEndpoints | STATED-DEFS; `2j_rc ≤ 4ω + C_J` inequality core OPEN |

## Section 8 (sec:arithmetic), L2718–4380

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:arith-conjugate-duality | 2761–2830 | Weil pairing; Nekovář | Duality | STATED-DEFS (Selmer complexes) |
| ex:arith-finite-heegner (4.1)–(4.2) | 2858–3410 | Serre, CCL 2.15, Elkik, Nekovář 4.1.4.1/8.1/8.6.2, Lang, Silverman | RC10 (finite cores) / HeegnerCohomology (cohomology) | STATED-DEFS (Heegner points over ring class fields, Kolyvagin classes); finite cores (H1), matrix span, (H5), (H6), (H12), (H14)–(H18), self-cup, res/cor diagonals, 3-arrow homotopy identity: OPEN |
| ex:arith-local-kummer | 3413–3468 | Milne ADT I.2.3, I.3.2–3.5; Nekovář 5.x, 6.3.4 | Duality | annihilator statement PROVED from the Milne print (`kummerAnnihilatorNode_proof`; Milne-scope form `kummerAnnihilatorNodeCharZero_of_print`); integral chain step ELLIOT (derived category) |
| (4.4) support change | 3470–3496 | Nekovář 7.8.8(ii) | Duality | STATED-DEFS |
| ex:arith-moving-character | 3500–3702 | Serre; Kummer; Chebotarev; `SL₂(ℤ₂)` | RC4 | trace bound `c_E = 16d + 21` and `SL₂(ℤ₂)` cores OPEN |
| ex:arith-paired-functional | 3705–3880 | Nekovář 6.2.5–6.2.8, 6.3.4 | PairedFunctional | STATED-DEFS |
| ex:arith-coordinate, ex:arith-central-specialization (4.5) | 3882–3986 | finite Heegner | RC15 | STATED-DEFS |
| ex:arith-central-calibration (4.6) | 3987–4140 | lem:forward-rank (Kolyvagin), Milne ADT I.7.3, Edixhoven 5.3 | RC15 | STATED-DEFS |
| ex:arith-common-coordinate (4.7) | 4142–4317 | Nekovář 6.4.1–6.4.3 | RC15 | residue identities `ē_q = t²/(1+t)`, `l̄_q = t⁴/(1+t)²` OPEN |
| ex:arith-base-zero | 4330–4373 | CST (conductor one), Smith reduction over a DVR | RC15 | STATED-DEFS for the coordinate; DVR disk lemma OPEN |

## Section 9 (sec:limits), L4382–5744

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:limits-inner-limit | 4391–4456 | homological perturbation, ultrafilters | RC6 | STATED-DEFS |
| ex:limits-residual-bound (5.1) | 4453–4648 | Milne ADT I.4.10, I.5.1, I.2.3, I.2.8; Nekovář 7.8.8(ii) | RankCounts | arithmetic `56ω(2N) + 8A + 56j + 70` OPEN |
| ex:limits-outer-evaluation (5.2)–(5.3) | 4651–4745 | ultraproducts | RC6 | "ultraproduct of `ℤ₂`-algebras is a DVR with uniformizer 2" core OPEN |
| ex:limits-kernel-detection (5.4) | 4748–4831 | kernel lemma, Goursat | RC16 | kernel lemma `(u⁴−1)b(g) = (g−1)b(z)` OPEN |
| ex:limits-derivative-switch | 4834–4907 | Nekovář 6.3.3–6.3.4 | RC16 | switch Lagrangian lemma and equal valuations (B2-a) OPEN |
| ex:limits-uniform-lower-bound (5.5) | 4909–5205 | (5.1), (5.3), (5.4), switch, (4.6) | RC16 | Schur/Cramer coordinate formula, hyperbolic sign planes, `Λ = ∩ Λ_p` cores OPEN |
| ex:limits-fixed-field-budget (5.6)–(5.8) | 5208–5484 | Nekovář 5.1.1–5.1.6 | RankCounts | bound arithmetic OPEN |
| ex:limits-fixed-field-clearing (5.9) | 5487–5645 | budget, paired functional, `η` | RC7 | `L_T(M) = 16(d_K+5)M` pole arithmetic OPEN |
| ex:limits-coefficient-transfer (5.10)–(5.11) | 5647–5741 | clearing | RC1 / TOP | `MissingAddressNode` PROVED (RC1); final deduction PROVED |

## Appendix E (app:even-source), L6825–8205

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:app-kato-system (K1)–(K16) | 6846–7356 | Kato (8.1.3), 8.9, 8.11, Prop 8.12, Thm 6.6, 9.7, 13.4, 13.5; Stacks 03Q9/03QA; Nekovář Cor 4.1.3 | RC11 | STATED-DEFS (Kato Euler system); smoothing `v₂ s_F = 2e` arithmetic OPEN |
| ex:app-even-scalar (E.3)–(E.5) | 7367–7612 | positive complex; `Q(ζ_{2^n})⁺` | RC11 | unit `1+ζ+ζ⁻¹` norm `−1` and sign-count cores OPEN |
| ex:app-central-calibration (E.6)–(E.9) | 7614–7787 | Nekovář 5.7.1.4–5.7.1.7; forward rank | RC11 | STATED-DEFS |
| ex:app-even-phase (E.10)–(E.12) | 7792–8205 | Waldspurger, Ramsey | RC11 | `T(p²)` recurrence closed form (E.12) algebra OPEN |

## Appendix F (app:odd-source), L8206–9980

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:app-detector (O.2) | 8225–8405 | DD, BFH, CST, Serre, Chebotarev | RC12 | STATED-DEFS |
| ex:app-theta-form (O.3)–(O.6) | 8409–9100 | Voight, Jetchev–Kane, Weil | RC12 | `c₀ = #GL₄(𝔽₃) = 24261120`, `v₂ c₀ = 9`, (O.6) from the `H`-recurrence: OPEN |
| ex:app-theta-comparison (O.7) | 9103–9405 | Cornut–Jetchev | RC12 | STATED-DEFS |
| ex:app-visibility (O.8) | 9407–9445 | CST (conductor one) | RC12 | STATED-DEFS (genus point) |
| ex:app-coefficient-rules (O.9)–(O.12) | 9447–9976 | Carayol, Casselman | RC12 | shell parities (O.9)–(O.11) and the (O.12) matrix identity OPEN |

## Appendix G (app:endpoints), L9981–10935

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:app-five-prime | 10001–10053 | HL | RC13 | OPEN once HL is stated |
| ex:app-rough-companion (F.1)–(F.3) | 10056–10150 | five-prime, address, (E.8), (E.11) | RC13 | STATED-DEFS |
| ex:app-odd-minimum (F.4)–(F.7) | 10152–10256 | (3.4), (3.5), (O.8) | AppGEndpoints | (F.4) inequality core OPEN |
| ex:app-nonempty-seeds (G.4a)–(G.4d), mod 8 | 10259–10500 | (O.11), (E.12) | RC3 | coefficient formulas and the mod-8 contradiction OPEN |
| ex:app-odd-stabilization | 10508–10552 | ultrafilter pigeonhole | RC2 | finite pigeonhole core OPEN |
| ex:app-simultaneous-address (G.1a) | 10554–10790 | network operators over `𝔽₂` | RC2 | grounded-Laplacian identities and the degree count OPEN |
| ex:app-final-family (3.9) | 10792–10861 | (F.6), (F.7), (O.8) | AppGEndpoints | STATED-DEFS |
| final contradiction (F.8) | 10862–10935 | as (5.10)–(5.11) | RC1 | same as MissingAddressNode |

## Printed leaves (cited results)

Stated in `Prints` (all UNVERIFIED, pending reading):

| leaf | locator as cited | used at |
|---|---|---|
| `PoleS12.BCDTThmA` | BCDT, Thm A and Introduction conds (1)–(6) | 1779 |
| `KolyvaginThm1Printed` | Kolyvagin, MPI/90-69, Thm 1, pp. 4–5 | lem:forward-rank; 2617, 4020, 5250, 7626, 7780, 8272, 10111, 10279 |
| `DokchitserThm18` | Dokchitser–Dokchitser, Crelle 658, Thm 1.8 | 1795–1797, 8249 |
| `CST.CSTThm11Split` | Cai–Shu–Tian, ANT 8 (2014), Thm 1.1 | 2428, 8268–8272, 9437–9444, 4337–4339 |

Cited, not yet stated (definitions needed in parentheses):

| print | locator as cited | needs |
|---|---|---|
| Hoffstein–Luo | MRL 4, p. 436 | root numbers of twists, splitting conditions (RC8/RC9) |
| Bump–Friedberg–Hoffstein | Invent. 102, clauses (i), (ii) pp. 543–544 | as HL (RC8/RC9) |
| Desjardins | JTNB 32, Prop 3.3 | local root numbers (RC8/RC9) |
| Milne MF | v1.31, Thm 11.19, Rem 11.18 | `J₀(N)`, `A_f` |
| Kato | Astérisque 295, (8.1.3), §8.2, 8.9, 8.11, (4.2.4), Thm 6.6, Prop 8.12, Thm 9.7, (12.2.1)–(12.2.3), §13.1, Thm 13.4(1)(2), 13.5(2), §§13.6–13.7, Cor 14.3 | zeta elements, Iwasawa cohomology |
| Cornut–Jetchev | 2010 preprint, §§3.1–3.6, Thm 3.1, Cor 3.2, Lemma 2.1(ii), §§4.9–4.10 | CM points, supersingular reduction |
| Waldspurger | JMPA 60, Prop 2, §I.3, Prop 18, Cor 2; ICM 1983 Thm 1, Prop 1 | half-integral weight forms |
| Serre | Invent. 15 (open image) | Tate module representation (RC8/RC9) |
| Cai–Chen–Liu | TAMS 370, Thm 2.15 | Heegner points over ring class fields |
| Elkik | Astérisque 183 (Manin–Drinfeld), p. 59 | cuspidal subgroup of `J₀(N)` |
| Nekovář | *Selmer complexes*, 4.1.4.1, Cor 4.1.3, 5.1–5.4, 5.7.1.4–5.7.1.7, 6.2–6.4, 7.8.8(ii), 8.1, 8.6.2.1–8.6.2.4 | Selmer complexes |
| Milne ADT | I.2.3, I.2.8, I.3.2–3.5, I.4.10, I.5.1, I.7.3 | local/global duality |
| Edixhoven | Thm 5.3, Rem 5.4.1 | Néron component groups |
| Lang 1956 | Thm 1 | `H¹` of connected groups over finite fields (RC8/RC9) |
| Silverman | IV.2.3, IV.3.2(a), X.1.4 | formal groups |
| Voight | Main Thm 14.6.1, Prop 14.6.7 | quaternion orders |
| Jetchev–Kane | arXiv:0908.3905, §§1.1–1.2, 2.5 | supersingular pairs |
| Weil | Acta 111, I.13–I.14, II.25–II.30, III Thm 6 | Weil representation |
| Carayol | Ann. ENS 19, §§0.3–0.7, Thm A | local–global compatibility |
| Casselman | Math. Ann. 201, Thm 1, Cor p. 306, Thm 4 | conductor-one representations |
| Ramsey | Ann. Inst. Fourier 56, Def 3.1, Thm 4.2, Rem 4.4 | half-integral weight algebraic model |
| Stacks | Tags 03Q9, 03QA | étale direct images |
| Howard 2012 | §1.7 (13) | cross-reference only |
