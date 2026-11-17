# Frozen initial source-use reconstruction

Date: 2026-11-10. Independent preliminary non-author review for bounded, non-release helper contribution. This is not trusted-controller eligibility, Protocol_D acceptance, protected Astra acceptance, kernel replay, or acceptance of the main Diophantine theorem.

Prior exposure: task prompt and inherited generic workspace/memory context only; no previous review reports, declared target/application inventories, favorable ledgers or manuscript mappings were read. Comments inside the four permitted Lean files were visible but were not treated as evidence of application coverage. Stage A additionally read dependency pin metadata and selected actual imported Mathlib source definitions.

Prepared worktree HEAD: `37a65df0b8f815b6c10c00bdf85f01e2b0c2860f`. No Lean build, proof changes, commits, pushes or cloud activity.

## Scope and bytes

| Source | SHA-256 |
|---|---|
| `lean/Research/DerivativeSwitch/ConjugateLocalTransport.lean` | `8688eef27fcc89c02eb3ab270e5359534dc23ef16e11678bdb1dd3587e3f8b86` |
| `lean/Research/DerivativeSwitch/ConjugateLocalH1.lean` | `078ac50ae0c90c8e609a57c51c5884a25646ad7305531f1cf531617485b9078f` |
| `lean/Research/DerivativeSwitch/ActualBoundaryCup.lean` | `77bcdd2ae5283ffd6cc51062e452da4294fcd5b3d952940b588b2d5b52ecdd90` |
| `lean/Research/DerivativeSwitch/OrthogonalComparison.lean` | `bfec996b869e44c6a42fc058fbc24cc7288b1f61d0f0e7eef1f4f58f41dca1ba` |

## Dependency pins

Toolchain: `leanprover/lean4:v4.35.0`. Manifest SHA-256: `a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58`. Actual Mathlib checkout HEAD was checked and equals manifest pin. Other package revisions below are manifest declarations, not independently checked checkout revisions.

| Package | Declared revision |
|---|---|
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Cli | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

## Per-declaration source use

All declarations are under `Research.DerivativeSwitch`. Transport and H1 share namespace `ConjugateLocalTransport`; transport entries from `transportUnit` onward and H1 entries from `h1Coordinates` onward are under `LocalData`. Other files use their filename namespace. Sites are declaration-start lines. Rows list substantive visible uses, not an exhaustive elaborated constant/axiom graph. Common transport/H1 assumptions: commutative R, group G, additive commutative R-module V; H1 uses one universe and noncomputable descent. Cup assumptions: arbitrary commutative R and additive R-modules in the displayed degrees.

### ConjugateLocalTransport

Direct imports: `Mathlib.Algebra.Module.LinearMap.End`, `Mathlib.Algebra.Group.Subgroup.Basic`, `Mathlib.Tactic.Group`.

| Declaration site | Hypotheses / substantive source uses |
|---|---|
| `ConjugateLocalTransport.lean:24` `twist` | H subgroup, T representation, alpha unit character; scalar-times-action; Module.End multiplication and smul_comm establish representation. |
| `ConjugateLocalTransport.lean:34` `conjugation` | H.Normal; conj_mem and group laws establish endomorphism of H. |
| `ConjugateLocalTransport.lean:40` `IsCrossed` | Defines p(gh)=p(g)+rho(g)p(h); no continuity. |
| `ConjugateLocalTransport.lean:43` `crossed_conjugation` | hp; crossed equation twice, group cancellation, inverse action cancellation; no scalar assumption. |
| `ConjugateLocalTransport.lean:56` `crossed_pow_of_trivial` | hp and rho(x)=1; derive p(1)=0, natural induction; cast n into arbitrary commutative R. |
| `ConjugateLocalTransport.lean:70` `LocalData` | Fields tau,frobenius,transporter,finiteGenerator,inertia,ell; tau²=1, frobenius=transporter*tau, T(frobenius)=T(tau), finiteGenerator=frobenius², tame conjugation=inertia^ell, alpha finite/inertia=1, T(inertia)=1. All supplied, no arithmetic construction. |
| `ConjugateLocalTransport.lean:93` `transportUnit` | Explicit inverse alpha(transporter), independent of p; unit by construction. |
| `ConjugateLocalTransport.lean:95` `coordinates` | Evaluation pair finiteGenerator/inertia for arbitrary functions. |
| `ConjugateLocalTransport.lean:97` `tate_transporter` | tate_frobenius and frobenius_eq; multiply by T(tau inverse), map_mul/cancellation. |
| `ConjugateLocalTransport.lean:103` `twist_transporter` | twist definition and tate_transporter. |
| `ConjugateLocalTransport.lean:108` `twist_transporter_inv` | tate_transporter, T.map_mul inverse cancellation, alpha.map_inv and transportUnit. |
| `ConjugateLocalTransport.lean:117` `tate_finite` | finite_eq, tate_frobenius, tau_sq and map_pow. |
| `ConjugateLocalTransport.lean:120` `twist_finite` | twist, alpha_finite, tate_finite. |
| `ConjugateLocalTransport.lean:123` `twist_inertia` | twist, alpha_inertia, tate_inertia. |
| `ConjugateLocalTransport.lean:129` `rawConjugate` | H.Normal; function precomposition by conjugation tau; no coefficient involution. |
| `ConjugateLocalTransport.lean:131` `rawConjugate_isCrossed` | hp, conjugation homomorphism; target is (twist H T alpha).comp(conjugation H tau), not original action. |
| `ConjugateLocalTransport.lean:136` `conjugation_finite` | frobenius_eq, finite_eq, group identities and subtype extensionality. |
| `ConjugateLocalTransport.lean:146` `conjugation_inertia` | frobenius_eq, tame_eq, group identities and subtype extensionality. |
| `ConjugateLocalTransport.lean:159` `rawConjugate_finite` | hp, conjugation_finite, crossed_conjugation, twist_finite, twist_transporter_inv. |
| `ConjugateLocalTransport.lean:166` `rawConjugate_inertia` | hp, conjugation_inertia, crossed_conjugation, twist_inertia, twist_transporter_inv, crossed_pow_of_trivial; retains ell scalar. |
| `ConjugateLocalTransport.lean:177` `coordinates_rawConjugate` | hp; product of rawConjugate_finite/inertia; shared transportUnit and ell remain explicit. |
| `ConjugateLocalTransport.lean:185` `coordinates_rawConjugate_of_neg_one` | Requires exact hEll:(ell:R)=-1; coordinates_rawConjugate plus neg_one_smul/smul_neg. |
| `ConjugateLocalTransport.lean:192` `twist_conjugation_finite` | conjugation_finite, twist_finite, representation inverse cancellation. |
| `ConjugateLocalTransport.lean:197` `twist_conjugation_inertia` | conjugation_inertia, twist_inertia, map_pow and inverse cancellation. |
| `ConjugateLocalTransport.lean:204` `coordinates_add_coboundary` | No normality required; arbitrary p,v; twist_finite/inertia kill coordinate coboundaries. |
| `ConjugateLocalTransport.lean:210` `conjugate_coordinates_add_coboundary` | Normality; arbitrary p,v; rawConjugate, twist_conjugation_finite/inertia kill original coboundary after pullback. |

### ConjugateLocalH1

Direct imports: `Research.DerivativeSwitch.ConjugateLocalTransport`, `Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree`, `Mathlib.LinearAlgebra.Isomorphisms`.

| Declaration site | Hypotheses / substantive source uses |
|---|---|
| `ConjugateLocalH1.lean:26` `h1_projection_surjective` | H1_induction_on supplies representatives of actual Mathlib H1. |
| `ConjugateLocalH1.lean:31` `cocycleEvaluation` | Linear evaluation at arbitrary x on actual cocycles₁. |
| `ConjugateLocalH1.lean:37` `cocycleEvaluation_kills_kernel` | hx:rho x=1; H1π_eq_zero_iff gives coboundary witness v; evaluate rho x v-v. |
| `ConjugateLocalH1.lean:49` `h1Evaluation` | hx; liftOfSurjective using h1_projection_surjective and cocycleEvaluation_kills_kernel. |
| `ConjugateLocalH1.lean:55` `h1Evaluation_projection` | hx; LinearMap.equivOfSurjective_apply computes descended evaluation. |
| `ConjugateLocalH1.lean:61` `cocyclePullback` | gamma group endomorphism; mem_cocycles₁_iff and gamma.map_mul; target cocycles for rho.comp gamma. |
| `ConjugateLocalH1.lean:69` `cocyclePullback_kills_kernel` | H1π_eq_zero_iff in both carriers; same v witnesses pulled-back coboundary. |
| `ConjugateLocalH1.lean:81` `h1Pullback` | liftOfSurjective; source H1(Rep.of rho), target H1(Rep.of(rho.comp gamma)); uses projection surjectivity and kernel lemma. |
| `ConjugateLocalH1.lean:88` `h1Pullback_projection` | LinearMap.equivOfSurjective_apply computes pullback on representatives. |
| `ConjugateLocalH1.lean:100` `h1Coordinates` | Original twist carrier; h1Evaluation at finiteGenerator/inertia using twist_finite/inertia. |
| `ConjugateLocalH1.lean:105` `h1Coordinates_projection` | Product of h1Evaluation_projection. |
| `ConjugateLocalH1.lean:112` `conjugateH1Coordinates` | H.Normal; conjugate representation carrier; evaluations use twist_conjugation_finite/inertia. |
| `ConjugateLocalH1.lean:118` `conjugateH1Coordinates_projection` | Product of h1Evaluation_projection on conjugate carrier. |
| `ConjugateLocalH1.lean:127` `h1_local_transport` | H.Normal and exact hEll; H1_induction_on, both coordinate projection lemmas and h1Pullback_projection reduce to coordinates_rawConjugate_of_neg_one. mem_cocycles₁_iff and add_comm align cocycle ordering. |

### ActualBoundaryCup

Direct imports: `Mathlib.LinearAlgebra.Isomorphisms`.

| Declaration site | Hypotheses / substantive source uses |
|---|---|
| `ActualBoundaryCup.lean:28` `LocalCupData` | Linear d0,d1,dt and cup10/01/11/20/02; supplied Leibniz10 dt cup10=cup20(d1 l,q)-cup11(l,d0 q), Leibniz01 dt cup01=cup11(d0 q,l)+cup02(q,d1 l). No d²=0 field. |
| `ActualBoundaryCup.lean:45` `closed_cup_differential` | hl:d1 l=0; leibniz10 and linear zero laws give cup11(l,d0 q)=-dt cup10(l,q). |
| `ActualBoundaryCup.lean:54` `pure_boundary_correction` | hl and hcycle:localCondition=localGlobal+d0 q; bilinearity and closed_cup_differential. |
| `ActualBoundaryCup.lean:63` `traced_pure_boundary` | hl,hcycle; linear trace with htrace:forall x,trace(dt x)=0; pure_boundary_correction. |
| `ActualBoundaryCup.lean:73` `traced_left_boundary` | hl for second slot; leibniz01 and htrace kill first-slot boundary. |
| `ActualBoundaryCup.lean:82` `traced_right_boundary` | hl for first slot; closed_cup_differential, map_neg and htrace. |
| `ActualBoundaryCup.lean:89` `traced_change_left` | hm:d1 m=0; bilinearity and traced_left_boundary; no closedness demanded of l. |
| `ActualBoundaryCup.lean:97` `traced_change_right` | hl:d1 l=0; bilinearity and traced_right_boundary; no closedness demanded of m. |

### OrthogonalComparison

Direct imports: `Mathlib.Algebra.Homology.Homotopy`, `Mathlib.Tactic.Abel`.

| Declaration site | Hypotheses / substantive source uses |
|---|---|
| `OrthogonalComparison.lean:21` `fibreD` | Additive groups/maps; third component loc(g)-inc(u)-dL(l), degreewise definition only. |
| `OrthogonalComparison.lean:27` `fibreComparison` | Maps (g,u,l) to (g,a(u),l+h(u)); supplied additive a,h. |
| `OrthogonalComparison.lean:32` `fibreComparison_commutes` | ha:dV a0=a1 dU; hh:inc-inc′ a0=dL h0+h1 dU; unfolds degreewise maps, Prod.ext, map_add, abel. |
| `OrthogonalComparison.lean:55` `fibreComparison_global` | Definitional unchanged global coordinate; G0 need not be additive. |
| `OrthogonalComparison.lean:60` `fibreComparison_sign_change` | Negate local coordinate: -(comparison(g,u,-l)).local=l-h(u); abel. G0 need not be additive. |
| `OrthogonalComparison.lean:76` `inverse_preserves_global_homotopy` | Actual HomologicalComplex in preadditive category; supplied j,k,p,q, hj:j≫q=p, hk:Homotopy(k≫j)(id D); hk.compRightId q and associativity. |
| `OrthogonalComparison.lean:83` `inverse_preserves_global_homology` | Same hj,hk; D/G HasHomology i; preceding homotopy and Mathlib Homotopy.homologyMap_eq. |
| `OrthogonalComparison.lean:91` `inverse_preserves_local_homotopy` | Same hj,hk plus chain map loc:G→L; preceding homotopy.compRight loc. |
| `OrthogonalComparison.lean:98` `inverse_preserves_local_homology` | Same hj,hk,loc; D/L HasHomology i; local homotopy.homologyMap_eq. |

## External dependency inspection

The following actual source bytes were inspected selectively (not a recursive re-verification of Mathlib). Paths are relative to the checked Mathlib root stated above.

| Dependency | Sites and role | SHA-256 |
|---|---|
| `Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` | 276 cocycles kernel; 304 cocycle equation; 411 coboundary range; 965–995 actual H1, projection, kernel characterization and representative induction | `4d9db7af5a24f317e22537418481858f178d1cb58bce4a25f64699a36b31c8e4` |
| `Mathlib/LinearAlgebra/Isomorphisms.lean` | 159–172 noncomputable quotient-kernel descent and representative computation | `fa74ae549f0a2e0fe1f7d98aa94950490c7a7a086ab4c50134cf6db1713c54fe` |
| `Mathlib/Algebra/Homology/Homotopy.lean` | 198–221 composition of genuine homotopies; 942–945 induced homology-map equality | `d14897fc5e2a101ee2205957e1172aba81bf986349be2e12e013a3b7e77d1923` |

## Frozen boundaries and unresolved application questions

- Original versus conjugate coefficients are genuinely distinct types in H1 pullback/coordinates. No equality of those representations and no extra coefficient involution is proved or assumed. The raw transport proof precedes quotient descent.
- Finite-stage arithmetic congruences, Artin-ring constructions, continuity, common tame quotient, actual Frobenius/inertia realization, and verification of LocalData fields are absent here. `hEll` is exact equality in R, not a proved congruence or an inverse-limit claim. Applicability to such a quotient needs external evidence.
- BoundaryCup uses the cycle equation associated with third differential `-loc + inc - d q`. OrthogonalComparison defines the opposite loc/inc convention `loc - inc - d l`, with `q=-l` explaining the switch. The sign-change lemma is a coordinate identity, not construction of either full Selmer cone or an equivalence between them.
- Cup lemmas require explicit closedness in the paired direction and a supplied trace killing every dt boundary. They construct neither cup maps nor trace, global trace compatibility, cup products on actual Galois complexes, duality or an adjunction. No nondegeneracy/normalization follows.
- Orthogonal comparison assumes inclusion homotopy equations degreewise, then separately assumes actual chain maps j,k,p,q and a right-inverse homotopy `k≫j ~ id D`. It does not construct k or hk, prove their existence from orthogonality, or join the degreewise calculation to a specific Selmer complex. No left inverse is needed by these conclusions.
- No determinant comparison, normalized derivative functional, global arithmetic theorem, or main Diophantine theorem is derived in these bytes. No claim of finite computation or Lean replay is made.
- Stage B must test declared inventories against these precise assumptions/dependencies and inspect application evidence for each external obligation. Eligibility or protocol compliance beyond this source reconstruction remains for the controlling process.

Freeze: this document is the initial Stage A inventory. Subsequent reconciliation must be recorded separately and preserve these bytes.
