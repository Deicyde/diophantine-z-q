# RC53: dependency graph of the Lean proof of Theorem 5.3 (restricted converse)

Target: `ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine` (Theorem 5.3, `hyp:RC`,
`diophantine_zq.tex` L1005–1011). Proof: Sections 7–9 (L1760–5744) and Appendices E–G
(L6825–10935). Blueprint: `ZInQKernel/Contrib/CloudB3RC53/` on branch `cloud-b3s/rc53-blueprint`,
based on `rc/s12-descent-inputs-20261117`. Read-only inputs: the fleet's manuscript checks
`docs/research/mcheck-rc-map.md`, `mcheck-rc-app.md`, `mcheck-rc-deep.md`.

Assembly (no `sorry`, standard axioms):

```
restrictedConverseGenuine_of_nodes :
  Prints → BranchPackageNode → MissingAddressNode → RestrictedConverseGenuine
```

Status keys: **PROVED** (Lean theorem, standard axioms); **OPEN** (Lean `Prop` stated, proof
pending); **STATED-DEFS** (the manuscript statement needs objects that are not yet defined in
Lean; the row names them); **PRINT** (cited published result).

Lane labels: L1 missing address; L2 Section 8 finite algebra; L3 Section 9 linear algebra;
L4 Appendix G seeds and networks; L5 genuine definitions and printed leaves; L6 Section 7 and
Appendices E/F arithmetic; R independent review; C coordinator.

## Top level

| node | Lean | tex | depends on | owner | status |
|---|---|---|---|---|---|
| Theorem 5.3 | `restrictedConverseGenuine_of_nodes` | 1771–1776, 5666–5741 | Prints, BranchPackageNode, MissingAddressNode, the rows below | C | PROVED (from the two open nodes) |
| root number −1 | `RootNumberNode`, `rootNumberNode_proof` | 1793–1797 | DD Thm 1.8; rational 2-torsion of `E_ℓ` (`PoleRC`) | C | PROVED |
| `L(E,1) = 0` | `CentralValueZeroNode`, `centralValueZeroNode_proof` | 5740–5741 | functional equation at `s = 1` | C | PROVED |
| final deduction | `FinalRankDeductionNode`, `finalRankDeductionNode_proof` | 5736–5741 | order of a product | C | PROVED |
| missing address (5.10)–(5.11) | `MissingAddressNode` | 5666–5735 | Boolean bit degree, cube parity, Gauss lemma for `𝒪` | L1 | OPEN |
| Branch 1 or Branch-2 package | `BranchPackageNode` (`FixedFieldPackage`) | 2587–2602, 2595–2715, 2718–5664, App E–G | every row below | — | OPEN (bundles Sections 7–9) |

`FixedFieldPackage` fields and their sources:

| field | meaning | tex | sources |
|---|---|---|---|
| `k`, `hk` | final companion, `L(E^{(k)},1) ≠ 0` | 2595–2600 | even unit symbol (App E, App G), HL |
| `B` | `v₂ ũ_x(0) ≤ B` at `x ≠ 0` | 5730–5733 | (3.9) ex:sec7-final-family / ex:app-final-family; (3.4) ex:sec7-genus-lower (CST); (4.6) ex:arith-central-calibration; (4.7) ex:arith-common-coordinate |
| `cdet`, `LT`, `ClearingIdentity`, `PoleBound`, `BaseRegular` | (5.9) | 5486–5664 | ex:limits-fixed-field-budget (5.6)–(5.8); ex:arith-paired-functional (exponent `a`); ex:arith-common-coordinate (`η`); height-one regularity of ex:limits-uniform-lower-bound (`ũ_x ∈ Λ[1/2]`) |
| `BaseZero` | `L'(E/K,1) = 0 ⇒ ũ_0(0) = 0` | 4321–4373 | ex:arith-base-zero: CST at conductor one; Smith reduction over the DVR `Λ_(t)`; `s₂(E/K) = 1` (2617–2628) |

## Section 7 (sec:rc), L1760–2715

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| setup: modularity, parametrization `π`, root number | 1760–1797 | BCDT, Milne MF 11.19, DD | C | root number PROVED; `π` STATED-DEFS (`X₀(N)`, `J₀(N)`) |
| ex:sec7-even-scalar (3.2) | 1832–1966 | App E | — | STATED-DEFS (`Λ`, Kato class, positive complex) |
| ex:sec7-nonvanishing | 1969–2004 | HL, BFH, Desjardins, ex:app-five-prime | L5 | STATED-DEFS → OPEN once HL/BFH/Desjardins are stated (L5) |
| ex:sec7-typed-graph, ex:sec7-symbol | 2006–2070 | (3.2), (3.8) | — | STATED-DEFS (typed residue graphs, coefficient symbols) |
| ex:sec7-coefficient-rules | 2102–2119 | ex:app-coefficient-rules | — | STATED-DEFS |
| ex:sec7-realization | 2151–2142 | CRT, Dirichlet, reciprocity | L4 | OPEN once stated (finite) |
| ex:sec7-seed-certificate | 2188–2177 | coefficient rules | L4 | OPEN once stated (finite) |
| ex:sec7-one/two-symbol-address | 2222–2271 | ex:app-simultaneous-address | L4 | finite cores in L4 |
| ex:sec7-even-upper (3.3b) | 2295–2318 | (3.2), seeds, Boolean bit degree | L6 | inequality core OPEN |
| ex:sec7-rough-companion (3.3) | 2343–2401 | HL, forward rank zero, (3.3b) | — | STATED-DEFS (`L_*`) |
| ex:sec7-genus-lower (3.4)–(3.6) | 2418–2458 | CST ×2, index-≤2 glue, (3.5) | L5, L6 | (3.4) STATED-DEFS (genus and ring-class points, `j_gen`, `j_rc`, `L_*`); (3.3)+(3.4)+(3.5)⇒(3.6) inequality core L6 |
| fixed witness, theta forms, (3.7), (3.8) | 2460–2551 | App F, Cornut–Jetchev, CST | — | STATED-DEFS |
| common family (Waldspurger) | 2553–2591 | Waldspurger Cor 2 | — | STATED-DEFS |
| Branch 1 (empty unit) | 2587–2592 | (O.8) at `D = 1` | — | inside BranchPackageNode (left disjunct) |
| final companion, `s₂(E/K) = 1` | 2595–2628 | forward rank zero (Kolyvagin), isogeny `Res E → E × E^{(k)}` | L5 | STATED-DEFS (`s₂(E/K)`) |
| ex:sec7-ksplit-seed | 2628–2655 | App G mod-8 computation; `#E_ℓ(𝔽_p)[2^∞] = 4` | L4 | OPEN (finite, genuine: points over `𝔽_p`) |
| packet realization | 2657–2672 | grounded Laplacian minors | L4 | finite core OPEN |
| ex:sec7-final-family (3.9) | 2674–2713 | address lemmas, (3.4), (3.8) | — | STATED-DEFS; `2j_rc ≤ 4ω + C_J` inequality core L6 |

## Section 8 (sec:arithmetic), L2718–4380

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:arith-conjugate-duality | 2761–2830 | Weil pairing; Nekovář | — | STATED-DEFS (Selmer complexes) |
| ex:arith-finite-heegner (4.1)–(4.2) | 2858–3410 | Serre, CCL 2.15, Elkik, Nekovář 4.1.4.1/8.1/8.6.2, Lang, Silverman | L2 (finite cores) | STATED-DEFS (Heegner points over ring class fields, Kolyvagin classes); finite cores (H1), matrix span, (H5), (H6), (H12), (H14)–(H18), self-cup, res/cor diagonals, 3-arrow homotopy identity: OPEN in L2 |
| ex:arith-local-kummer | 3413–3468 | Milne ADT I.2.3, I.3.2–3.5; Nekovář 5.x, 6.3.4 | — | STATED-DEFS |
| (4.4) support change | 3470–3496 | Nekovář 7.8.8(ii) | — | STATED-DEFS |
| ex:arith-moving-character | 3500–3702 | Serre; Kummer; Chebotarev; `SL₂(ℤ₂)` | L2 | trace bound `c_E = 16d + 21` and `SL₂(ℤ₂)` cores OPEN in L2 |
| ex:arith-paired-functional | 3705–3880 | Nekovář 6.2.5–6.2.8, 6.3.4 | — | STATED-DEFS |
| ex:arith-coordinate, ex:arith-central-specialization (4.5) | 3882–3986 | finite Heegner | — | STATED-DEFS |
| ex:arith-central-calibration (4.6) | 3987–4140 | lem:forward-rank (Kolyvagin), Milne ADT I.7.3, Edixhoven 5.3 | — | STATED-DEFS |
| ex:arith-common-coordinate (4.7) | 4142–4317 | Nekovář 6.4.1–6.4.3 | L2 | residue identities `ē_q = t²/(1+t)`, `l̄_q = t⁴/(1+t)²` OPEN in L2 |
| ex:arith-base-zero | 4330–4373 | CST (conductor one), Smith reduction over a DVR | L3 (DVR core) | STATED-DEFS for the coordinate; DVR disk lemma OPEN in L3 |

## Section 9 (sec:limits), L4382–5744

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:limits-inner-limit | 4391–4456 | homological perturbation, ultrafilters | — | STATED-DEFS |
| ex:limits-residual-bound (5.1) | 4453–4648 | Milne ADT I.4.10, I.5.1, I.2.3, I.2.8; Nekovář 7.8.8(ii) | L3 | arithmetic `56ω(2N) + 8A + 56j + 70` OPEN |
| ex:limits-outer-evaluation (5.2)–(5.3) | 4651–4745 | ultraproducts | L3 | "ultraproduct of `ℤ₂`-algebras is a DVR with uniformizer 2" core OPEN |
| ex:limits-kernel-detection (5.4) | 4748–4831 | kernel lemma, Goursat | L3 | kernel lemma `(u⁴−1)b(g) = (g−1)b(z)` OPEN |
| ex:limits-derivative-switch | 4834–4907 | Nekovář 6.3.3–6.3.4 | L3 | switch Lagrangian lemma and equal valuations (B2-a) OPEN |
| ex:limits-uniform-lower-bound (5.5) | 4909–5205 | (5.1), (5.3), (5.4), switch, (4.6) | L3 | Schur/Cramer coordinate formula, hyperbolic sign planes, `Λ = ∩ Λ_p` cores OPEN |
| ex:limits-fixed-field-budget (5.6)–(5.8) | 5208–5484 | Nekovář 5.1.1–5.1.6 | L3 | bound arithmetic OPEN |
| ex:limits-fixed-field-clearing (5.9) | 5487–5645 | budget, paired functional, `η` | L3 | `L_T(M) = 16(d_K+5)M` pole arithmetic OPEN |
| ex:limits-coefficient-transfer (5.10)–(5.11) | 5647–5741 | clearing | L1 | `MissingAddressNode` OPEN; final deduction PROVED |

## Appendix E (app:even-source), L6825–8205

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:app-kato-system (K1)–(K16) | 6846–7356 | Kato (8.1.3), 8.9, 8.11, Prop 8.12, Thm 6.6, 9.7, 13.4, 13.5; Stacks 03Q9/03QA; Nekovář Cor 4.1.3 | — | STATED-DEFS (Kato Euler system); smoothing `v₂ s_F = 2e` arithmetic L6 |
| ex:app-even-scalar (E.3)–(E.5) | 7367–7612 | positive complex; `Q(ζ_{2^n})⁺` | L6 | unit `1+ζ+ζ⁻¹` norm `−1` and sign-count cores OPEN in L6 |
| ex:app-central-calibration (E.6)–(E.9) | 7614–7787 | Nekovář 5.7.1.4–5.7.1.7; forward rank | — | STATED-DEFS |
| ex:app-even-phase (E.10)–(E.12) | 7792–8205 | Waldspurger, Ramsey | L6 | `T(p²)` recurrence closed form (E.12) algebra OPEN in L6 |

## Appendix F (app:odd-source), L8206–9980

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:app-detector (O.2) | 8225–8405 | DD, BFH, CST, Serre, Chebotarev | — | STATED-DEFS |
| ex:app-theta-form (O.3)–(O.6) | 8409–9100 | Voight, Jetchev–Kane, Weil | L6 | `c₀ = #GL₄(𝔽₃) = 24261120`, `v₂ c₀ = 9`, (O.6) from the `H`-recurrence: OPEN in L6 |
| ex:app-theta-comparison (O.7) | 9103–9405 | Cornut–Jetchev | — | STATED-DEFS |
| ex:app-visibility (O.8) | 9407–9445 | CST (conductor one) | L5 | STATED-DEFS (genus point) |
| ex:app-coefficient-rules (O.9)–(O.12) | 9447–9976 | Carayol, Casselman | L6 | shell parities (O.9)–(O.11) and the (O.12) matrix identity OPEN in L6 |

## Appendix G (app:endpoints), L9981–10935

| node | tex | depends on | owner | status |
|---|---|---|---|---|
| ex:app-five-prime | 10001–10053 | HL | L5 | OPEN once HL is stated |
| ex:app-rough-companion (F.1)–(F.3) | 10056–10150 | five-prime, address, (E.8), (E.11) | — | STATED-DEFS |
| ex:app-odd-minimum (F.4)–(F.7) | 10152–10256 | (3.4), (3.5), (O.8) | L6 | (F.4) inequality core OPEN |
| ex:app-nonempty-seeds (G.4a)–(G.4d), mod 8 | 10259–10500 | (O.11), (E.12) | L4 | coefficient formulas and the mod-8 contradiction OPEN in L4 |
| ex:app-odd-stabilization | 10508–10552 | ultrafilter pigeonhole | L4 | finite pigeonhole core OPEN |
| ex:app-simultaneous-address (G.1a) | 10554–10790 | network operators over `𝔽₂` | L4 | grounded-Laplacian identities and the degree count OPEN in L4 |
| ex:app-final-family (3.9) | 10792–10861 | (F.6), (F.7), (O.8) | — | STATED-DEFS |
| final contradiction (F.8) | 10862–10935 | as (5.10)–(5.11) | L1 | same as MissingAddressNode |

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
| Hoffstein–Luo | MRL 4, p. 436 | root numbers of twists, splitting conditions (L5) |
| Bump–Friedberg–Hoffstein | Invent. 102, clauses (i), (ii) pp. 543–544 | as HL (L5) |
| Desjardins | JTNB 32, Prop 3.3 | local root numbers (L5) |
| Milne MF | v1.31, Thm 11.19, Rem 11.18 | `J₀(N)`, `A_f` |
| Kato | Astérisque 295, (8.1.3), §8.2, 8.9, 8.11, (4.2.4), Thm 6.6, Prop 8.12, Thm 9.7, (12.2.1)–(12.2.3), §13.1, Thm 13.4(1)(2), 13.5(2), §§13.6–13.7, Cor 14.3 | zeta elements, Iwasawa cohomology |
| Cornut–Jetchev | 2010 preprint, §§3.1–3.6, Thm 3.1, Cor 3.2, Lemma 2.1(ii), §§4.9–4.10 | CM points, supersingular reduction |
| Waldspurger | JMPA 60, Prop 2, §I.3, Prop 18, Cor 2; ICM 1983 Thm 1, Prop 1 | half-integral weight forms |
| Serre | Invent. 15 (open image) | Tate module representation (L5: statable over Tau Ceti torsion) |
| Cai–Chen–Liu | TAMS 370, Thm 2.15 | Heegner points over ring class fields |
| Elkik | Astérisque 183 (Manin–Drinfeld), p. 59 | cuspidal subgroup of `J₀(N)` |
| Nekovář | *Selmer complexes*, 4.1.4.1, Cor 4.1.3, 5.1–5.4, 5.7.1.4–5.7.1.7, 6.2–6.4, 7.8.8(ii), 8.1, 8.6.2.1–8.6.2.4 | Selmer complexes |
| Milne ADT | I.2.3, I.2.8, I.3.2–3.5, I.4.10, I.5.1, I.7.3 | local/global duality |
| Edixhoven | Thm 5.3, Rem 5.4.1 | Néron component groups |
| Lang 1956 | Thm 1 | `H¹` of connected groups over finite fields (L5: statable for elliptic curves) |
| Silverman | IV.2.3, IV.3.2(a), X.1.4 | formal groups |
| Voight | Main Thm 14.6.1, Prop 14.6.7 | quaternion orders |
| Jetchev–Kane | arXiv:0908.3905, §§1.1–1.2, 2.5 | supersingular pairs |
| Weil | Acta 111, I.13–I.14, II.25–II.30, III Thm 6 | Weil representation |
| Carayol | Ann. ENS 19, §§0.3–0.7, Thm A | local–global compatibility |
| Casselman | Math. Ann. 201, Thm 1, Cor p. 306, Thm 4 | conductor-one representations |
| Ramsey | Ann. Inst. Fourier 56, Def 3.1, Thm 4.2, Rem 4.4 | half-integral weight algebraic model |
| Stacks | Tags 03Q9, 03QA | étale direct images |
| Howard 2012 | §1.7 (13) | cross-reference only |
