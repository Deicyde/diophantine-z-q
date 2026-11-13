# Which prerequisites of H and CR₃ exist in the Lean libraries Trough tracks?

Task: BRIEF.md in this directory (Jack, 11-11: "Do any of the prerequisites we need exist in
Libraries like TauCeti?"). Written 2026-11-11 under load ≈ 460, read-only: no Lean, no builds.

## Verdict

**H: the bottom of the tree exists, the top does not.** Every refereed theorem that carries the
weight of Theorem 4.1 is absent from every tracked library:

- Faltings 1983;
- Faltings heights and the isogeny bounds of Gaudron–Rémond, Javanpeykar, Bost and Pazuki;
- p-adic Hodge theory (Scholze, Berger, Saito);
- Pan's Fontaine–Mazur theorem and Carayol;
- Shimura's `A_f` and the Galois representations of newforms;
- the canonical model of the discriminant-6 Shimura curve and Shimura reciprocity;
- semistable reduction and Néron–Ogg–Shafarevich for abelian varieties.

What does exist, and is proved:

- the number-field and local-field layer: class field theory, the Hasse principle for `Br`,
  Chebotarev, upper ramification groups (Tau Ceti);
- purity of the branch locus and Abhyankar's lemma (Axiom's Stacks);
- the newform bookkeeping of step C9 (Tau Ceti);
- Skolem–Noether (Tau Ceti);
- Néron–Ogg–Shafarevich for elliptic curves only (Tau Ceti).

Anthropic's FLT proof has the nearest thing to H's middle layer: abelian surfaces with
quaternionic multiplication, Néron models, polarised abelian schemes, Tate modules of
Jacobians. All of it is proved, but built only to the strength Ribet's level lowering needs.

By step, roughly:

- 5 of H's 36 steps have every cited supplier formalized (B1, B2, and the elementary steps B3,
  F2, F4; for B2 the identification `H²(G_ℚ, ±1) = Br(ℚ)[2]` was not located);
- 10 have part of it;
- 21 have none.

**CR₃: none of the deep inputs exists.** These are absent everywhere:

- TYZ's genus periods and genus points;
- Waldspurger and Yuan–Zhang–Zhang;
- Gross–Zagier and Heegner points;
- Bump–Friedberg–Hoffstein, Kolyvagin;
- modularity of CM curves (Deuring/Shimura);
- analytic continuation and root numbers of `L(E, s)`.

What exists (Mordell–Weil, 2-Selmer groups and descent, genus theory, ring class fields, a large
newform library with Atkin–Lehner signs and "sign −1 ⇒ positive analytic rank") covers the
Lean-statement side, which the fork already proves itself (Rédei, Mordell–Weil, RK9). The
nearest-to-complete chain, C4 plus D1, still lacks the link from `L(C_d, s)` to a newform
(Deuring).

## Sources, pins and what "status" means

| Library | Pin read | How it was read |
| --- | --- | --- |
| Tau Ceti | survey at the 11-08 head (299 255 declarations, `tauceti-map/survey-data/survey.jsonl.gz`); Trough pin `a6027b1d` | keyword scan of names and docstrings (`scan_tc.py`); 13 headline names confirmed in the source at `a6027b1d` with `gh api` |
| Mathlib | local checkout `mathlib4-wikilean-authority` at `e861750` (2026-09-08); Trough pin `9bac2d06` (11-09) | `git grep` and file docstrings at `e861750`; directory listings at `9bac2d06` show no new files in these areas except `ModularForms/OrderAtInfty.lean` |
| Anthropic FLT | `6e837e75` (Trough `data/anthropic-flt`) | file tree (45 945 files) by name, the README, two files read |
| Imperial FLT | `a3210204` (Trough blueprint) | blueprint TeX, file tree, four files read |
| Stacks (Axiom) | `5ed82d14` (Trough `data/stacks`) | every tag record: tier, `sorry`, EGA/SGA references |
| Lean Pool | `2b205bf9` (Trough `data/lean-pool`) | project records |
| Formal Conjectures | `2055e5ad` (Trough) | problem records |
| ATLAS | `Deicyde/atlas-lean@a3690dd2` (Trough `data/atlas`) | article records |
| openai/math | `HEAD` on 11-11 (catalog head `4eaee875`; "planned" in Trough) | file tree and formalization catalogue only |
| Formal Frontier, PNT+, PFR, CFSG, Equational Theories, physlib, cslib, Foundation, Analysis I, StrongPNT | catalog descriptions | none is on topic beyond foundations (see the end) |

Status words:

- **proved**: a sorry-free theorem in a library whose build audits the axioms (Tau Ceti allows
  only `propext`, `Classical.choice`, `Quot.sound`, per `scripts/Axioms.lean`; Anthropic FLT's
  README says no module contains `sorry` or `axiom`; Lean Pool records `sorry: false`).
- **proved (unreviewed)**: StacksFrontier, which is sorry-free with standard axioms but has no
  human review of the statements.
- **proved (special case)**: the cited theorem only in a restricted form, named in the row.
- **statement only**: `sorry`, `theorem_wanted`, a `Prop`-valued definition, or Imperial FLT's
  `knownin1980s` axiom.
- **definitions only**: the objects exist, the theorem does not.

Unless the row says otherwise, Tau Ceti files are the module path with `.lean`, for example
`TauCeti/NumberTheory/ClassFieldTheory/Global/Brauer/SumFormula.lean`.

## 1. H = `ZInQ.SixContactMin` (steps of `docs/research/h-trust.md` §1)

| Step(s) | Prerequisite | Where it exists | Status |
| --- | --- | --- | --- |
| A1, A3, B1 | Quaternion algebras over ℚ, orders, Skolem–Noether | **Mathlib** `QuaternionAlgebra` (`ℍ[R,a,b,c]`), `Mathlib/Algebra/Quaternion.lean`: definitions. **Tau Ceti** `TauCeti.skolemNoether` (`…Algebra.CentralSimple.SkolemNoether`); `TauCeti.hilbertSymbol_eq_one_iff_nonempty_algEquiv_matrix` (split ⇔ Hilbert symbol 1); `TauCeti.BrauerGroup.quaternionClass_eq_one_iff`; `TauCeti.BrauerGroup.invMap_brauerGroupEquivBr_quaternionClass_eq_half_iff` (local invariant 1/2). **Imperial FLT** `IsQuaternionAlgebra` (`FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean`, 0 sorries); totally definite algebras over totally real fields (`FLT/AutomorphicForm/QuaternionAlgebra/`). **Anthropic FLT** orders `Λ ⊆ ℍ[ℚ,a,b]`, maximal and Eichler orders (`CerednikDrinfeld` namespace, e.g. `…CSTower…isEichlerOrder…`) | Skolem–Noether **proved**; splitting criteria **proved**; local normalizers of maximal orders (Vignéras, A3) **not found** |
| A2, A7, A10, F1 | Discriminant-6 curve: Atkin–Lehner quotient, branch data, Baba–Granath's Igusa vector, González–Rotger, theta constants | nothing; no hits for Igusa invariants or theta constants in any library | **not found** |
| A4 | `Y₃` as fine moduli scheme over ℚ of QM abelian surfaces with level-3 structure: canonical models (Shimura, Deligne), uniqueness of the polarization, neatness | **Anthropic FLT** `CerednikDrinfeld.QM.FakeEllipticCurve` with `FullLevel m` (`Definitions/Def_CerednikDrinfeld_QMFineModuli.lean`), plus `QMCoarseModuli`, `QMCanonicalPol`, `QMIsogeny`, `QMRigidification` (1 063 files in `CerednikDrinfeld.QM`), and Čerednik–Drinfeld uniformization (`Def_CerednikDrinfeld_MumfordUniformization.lean`). **openai/math** `OAI/AlgebraicGeometry/PELModuli/` (integral model, CM points) and `AbelianModuli/HilbertConstruction/` (polarized, level), not examined | Anthropic: the moduli problem **proved (special case)**: built for p-adic uniformization in Ribet's step. Whether it yields `Y₃` over ℚ for discriminant 6, level 3 is not checked. Canonical-model theorem over ℚ **not found** |
| A5 | Lemma PR(i): Zariski–Nagata purity (SGA 1 X 3.1), Abhyankar's lemma (SGA 1 XIII 5.3), Shimura reciprocity at CM points (Lemma NV) | **Stacks** Tag 0BMB `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne`, purity in every dimension (`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/AnyDimension.lean`; its record cites SGA 1 X 3.1); Tag 0EYG `AlgebraicGeometry.isEtaleLocallyStandardTamelyRamified_of_isTamelyRamifiedInCodimensionOne`, Abhyankar for a regular divisor (`…/Abhyankar/RegularDivisorUnconditional.lean`). **Tau Ceti** `TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_ringKrullDim_le_two` (purity, regular local rings of dimension ≤ 2, `…RingTheory.RegularLocalRing.Purity`); `TauCeti.Place.ramificationIdx_restrict_sup` (Abhyankar for function fields, Stichtenoth 3.9.1) | purity and Abhyankar **proved (unreviewed)** in Stacks, **proved** in dimension ≤ 2 in Tau Ceti; Shimura reciprocity **not found** |
| A6, A8, C6 | Grothendieck's semistable reduction for abelian varieties (SGA 7 IX 3.6); Serre–Tate / Néron–Ogg–Shafarevich; Mumford's `rank Hom ≤ 4 dim A dim A'`; Minkowski's lemma | Elliptic curves only, **Tau Ceti**: `WeierstrassCurve.hasGoodReduction_iff_tateModuleGaloisRepresentation_eq_one`, `…hasPotentialGoodReduction_iff_finite_image_tateModuleGaloisRepresentation`, `…HasPotentialGoodReduction.hasGoodReduction_iff_isUnramified_divisionField` (`…EllipticCurve.TateModule.*`, `…MinimalModel.PotentialGoodReduction`). **ATLAS** `MetaMathlibExt.good_reduction_torsion_unramified` (good ⇒ unramified). Jacobians in **Anthropic FLT** `GoodReductionJacobian.*` (about 560 files). **Stacks** Tag 0CDN `Stacks.Models.semistableReduction` (curves) | elliptic curves **proved (special case)**; curves **proved (unreviewed)**; abelian varieties **not found**. No SGA 7 IX 3.6 in the Stacks SGA references |
| A9 | Polarizable complex tori are abelian varieties; GAGA; rigidity `Hom(A,B) = Hom(A_K,B_K)` | **Tau Ceti** `TauCeti.AlmostComplexStructure.isRiemannForm_iff_isPolarization` (Riemann forms = polarizations of weight-one Hodge structures); `TauCeti.AlgebraicGeometry.AbelianVariety.Hom.*` with a 4-declaration `Hom.Rigidity` module | Riemann forms **proved**; GAGA and Riemann's theorem **not found** |
| Basic | Abelian varieties, isogenies, polarizations, Tate modules | **Tau Ceti** `TauCeti.AlgebraicGeometry.AbelianVariety` (proper geometrically integral group scheme), Hom group, `End`, `IsIsogeny` (finite surjective), `IsAlbanese` (288 declarations). **Anthropic FLT** `AlgebraicGeometry.PolarisedAbelianScheme`, `RiemannForm` (Rosati compatibility), Jacobian Tate modules `Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean` (rank `2g`), Weil pairing. **openai/math** `OAI/AlgebraicGeometry/AbelianScheme/` (Frobenius kernel, isogeny quotients, Tate comparison, Cartier duality) | Tau Ceti: **definitions only** plus foundational lemmas. Anthropic: Jacobians **proved (special case)**. Tate modules, polarizations and Poincaré reducibility of a general abelian variety: **not found** |
| C1, C10 | Tate action of `G_{L'}`; reduction of isogenies through the Néron mapping property; independence of ℓ; Chebotarev; Brauer–Nesbitt | **Anthropic FLT** Néron models (`Definitions/Def_AlgebraicGeometry_NeronModelUniquenessUpToIsomorphism.lean`, `…NeronModelEndomorphismExtension.lean`). **Tau Ceti** Chebotarev `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` (`…Chebotarev.PrimeCounting.FrobeniusPrimeCount`) | Chebotarev **proved**; Néron models **proved (special case)**; Brauer–Nesbitt and Mumford §19 Thm 4 **not found** (also not in Mathlib at `e861750`) |
| C2, E1, E4 | Faltings 1983 (semisimplicity, Tate conjecture, Hom theorem, height variation) | **ATLAS** `…FaltingsWanted…Faltings.faltings` is the Mordell conjecture, not these, and is a `theorem_wanted` | **not found** |
| C3, C4, C8 | p-adic Hodge theory: de Rham comparison (Scholze, Faltings, Tsuji), Berger, Hodge–Tate weights of eigenforms (Saito, Scholl), Tate's theorem on Hodge–Tate characters | **Tau Ceti** perfectoid tilts (`TauCeti.Perfectoid.uniformTilt`), almost mathematics, Fargues–Fontaine foundations (`TauCeti.FarguesFontaine.spaY`, `spaX`); complex Hodge structures (`TauCeti.Hodge.*`, completed roadmap). **Stacks** crystalline cohomology chapter (122/124 tags: divided powers, crystalline site) | foundations only; `B_dR`, Hodge–Tate and de Rham representations, pst, every comparison theorem: **not found** |
| C5 | Betti–étale comparison (SGA 4 XI) | **Stacks** étale cohomology chapter (451/497 tags: proper and smooth base change, Galois cohomology, Brauer groups); no SGA 4 XI reference in any tag record | **not found** |
| C7 | Pan, Fontaine–Mazur in the residually reducible case | none | **not found** |
| C8 | Deligne–Serre (weight one has finite image); Kronecker–Weber | **Tau Ceti** `TauCeti.ClassFieldTheory.kroneckerWeber` (`…ClassFieldTheory.ClassFields.KroneckerWeber`). **Anthropic FLT** uses a "Deligne–Serre lifting lemma" (mod-p eigenform lifting, not the finite-image theorem) | Kronecker–Weber **proved**; Deligne–Serre Thm 4.1 **not found** |
| C9 | Twists of eigenforms; newforms and strong multiplicity one (Li, Miyake 4.6.19); Galois conjugates of newforms are new; Li's Fricke formula / Atkin–Li; Shimura's `A_f` and the `K_f`-linear Eichler–Shimura relation | **Tau Ceti** `ModularForm.qExpansion_twist_coeff`, `CuspForm.heckeTCuspNat_twist_eq_smul` (twist of an eigenform is an eigenform); `HeckeRing.GL2.Newform.primitiveTwist`, `…level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist` (strong multiplicity one across levels), `HeckeRing.GL2.finrank_cuspFormsNewEigenspace_le_one` (Miyake 4.6.13); `TauCeti.conj_mem_cuspFormsNew`; `HeckeRing.GL2.Newform.atkinLehnerPseudoEigenvalue` (Atkin–Li) (all `…NumberTheory.ModularForms.*`). **Lean Pool** `flt-eichler-shimura`: `HeckeEis.exists_eichlerShimura_heckeEquivariant` (the Eichler–Shimura *isomorphism* with cohomology for Γ₀(N)), `WeierstrassCurve.tateModuleRep_charpoly_frobenius` (`X² − a_ℓX + ℓ` for E/ℚ). **Anthropic FLT** `ModularCurve.mTorsionGaloisRep` (`Definitions/Def_HeckeGalois_EichlerShimura.lean`): mod-𝔪 Galois action on Hecke torsion of a Jacobian | newform bookkeeping **proved**; Eichler–Shimura isomorphism **proved**; Shimura's `A_f`, `V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`, and ρ_f for a newform **not found**; the Anthropic piece is **proved (special case)**, mod 𝔪 only |
| D1, D3, D4 | Ramification groups in upper numbering, Herbrand function, the subgroup formula, Artin–Swan conductor, the different | **Tau Ceti** (completed roadmap "Local fields and ramification"): `TauCeti.LocalFieldsRamification.upperRamificationGroup`, `…map_restrictNormalHom_upperRamificationGroup` (Herbrand's theorem), `…psiNat`, `…artinConductorExponent`, `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one` (Hilbert's different formula). **Mathlib** decomposition and inertia groups only (`RingTheory/Valuation/RamificationGroup.lean`; higher groups are a TODO) | **proved** for characters and finite Galois extensions; Serre's different bound `δ ≤ e − 1 + e·v_p(e)` (D1) not located; conductors of ℓ-adic representations and the Weil–Deligne conductor of `V^∨` **not found** |
| D2 | Raynaud's criterion (Silverberg–Zarhin); unipotent inertia at semistable reduction | none for abelian varieties; Tau Ceti `WeierstrassCurve.IsSemistable` (elliptic) | **not found** |
| D5 | Carayol, `v_p(N)` = conductor exponent | none | **not found** |
| B2 | `H²(G_ℚ, ±1) = Br(ℚ)[2]`; Hasse principle; reciprocity | **Tau Ceti** `TauCeti.ClassFieldTheory.brLocalization_injective` (Albert–Brauer–Hasse–Noether), `…sumLocalInv_brLocalization_eq_zero` (sum formula), `…range_brLocalization` (exactness), `…hilbertProductFormula`, `…h2MuEquivZMod` (local `H²(F, μ_n) ≅ ℤ/n`); global CFT (`…globalAbelianExistence`, `…globalClassFieldCorrespondence`). **Stacks** Brauer groups 25/33 tags. **Mathlib** `BrauerGroup` (definition only, `Algebra/BrauerGroup/Defs.lean`) | **proved** |
| E2, E3, F3 | Faltings height; Javanpeykar's bound for `J₁(N)`; Gaudron–Rémond; Bost; Pazuki's theta height | none | **not found** |
| F2, F4 | Weil heights, Northcott, rational root theorem | **Mathlib** `Height.mulHeight`, `logHeight₁`, Northcott for number fields (`NumberTheory/Height/NumberField.lean`), naive height on elliptic curves (`NumberTheory/Height/EllipticCurve.lean`). **Tau Ceti** `Height.mulHeightAff`, `TauCeti.absoluteLogHeightAff`, `WeierstrassCurve.Affine.Point.canonicalHeight`, `…abs_canonicalHeight_sub_naiveHeight_le` | **proved**: enough for the elementary steps F2 and F4 |
| A5, background | Étale fundamental group (SGA 1) | **Tau Ceti** `TauCeti.FiniteEtaleScheme.instGaloisCategoryOfConnectedSpace…`, `…instIsFundamentalGroupFiber`, `…mapAutFiber`. **Stacks** Fundamental groups of schemes, 132/136 tags (SGA 1 X 1.4, 2.1, 3.1-3.9 and XIII 4.x references). **Mathlib** Galois categories (`CategoryTheory/Galois/`) | **proved** (Stacks: unreviewed) |

## 2. CR₃ = `ZInQ.RouteK.Rank.CertifiedRankTYZClRk` (steps of `docs/research/cr3-trust.md` §1)

| Step(s) | Prerequisite | Where it exists | Status |
| --- | --- | --- | --- |
| B9, C4, D1-D3 | `L(E, s)`: definition, Euler product, analytic continuation, functional equation, root number | **Mathlib** `WeierstrassCurve.LFunction` (`AlgebraicGeometry/EllipticCurve/LFunction.lean`): definition. **Tau Ceti** `WeierstrassCurve.isMultiplicative_LFunction` (Euler product), `…analyticOrderAt_ne_top_of_isContinuationOn` (a continuation, if given, vanishes to finite order). **Formal Conjectures** `HasseWeil.exists_hasAnalyticContinuation` (`Wikipedia/HasseWeil.lean`) | Euler product **proved**; continuation **statement only** (open in FC's framing); root number of `C_d` (Birch–Stephens) **not found** |
| C4 | Root number −1 ⇒ odd order of vanishing | **Tau Ceti**, for newforms: `HeckeRing.GL2.Newform.IsSelfDual.neg_one_pow_analyticRank` (root number = (−1)^analytic rank), `…analyticRank_pos_of_I_zpow_mul_frickeSign_ne_one`, `CuspForm.frickeCompletedL_functional_equation` (Hecke's functional equation), `HeckeRing.GL2.Newform.atkinLehnerSign_eq_one_or_neg_one` (`…ModularForms.LFunction.*`, `…AtkinLehner.Sign`) | **proved for newforms**; applying it to `C_d` needs D1 |
| D1 | Modularity of CM curves (Deuring, Shimura 1971); conductor `32d²` | **Tau Ceti** `TauCeti.CMAction`, `WeierstrassCurve.gaussianIntCMAction` (ℤ[i] acting on `y² = x³ + x`); Hecke characters with infinity type (`TauCeti.GlobalNumberFields.HeckeCharacter.infinityType`, `…IsAlgebraic`); Hecke L-functions of finite-order ray class characters only (`TauCeti.LFunctions.heckeLFunctionC`); conductors of elliptic curves (`WeierstrassCurve.algorithmicConductor`, Tate's algorithm). **Anthropic FLT** `WeierstrassCurve.modularity_of_semistableModel` (semistable models only; `C_d` is additive at 2). **Lean Pool** `ModularCurve.x0_modularPolynomialPresentation` (function field of `X₀(N)`). **Formal Conjectures** `ModularityConjecture.modularity_conjecture` | CM modularity **not found**; Anthropic's modularity is **proved (special case)**, not applicable; FC **statement only** |
| B3, F5 | CM and class field theory for imaginary quadratic fields: ring class fields, `H'_d`, Cox Lemma 9.3 | **Tau Ceti** `TauCeti.ClassFieldTheory.ringClassField`, `…isAbelianGalois_ringClassField`, `…ringClassArtinEquiv` (Pic(O) ≅ Gal), `…finrank_hilbertClassField` (degree = class number), `TauCeti.BinaryQuadraticForm.posDefProperClassEquivGal`, `…hilbertClassPolynomial` (degree, roots = singular moduli, separable), `TauCeti.NumberField.classNumber_eq_one_of_mem_heegnerDiscriminants` (class number one). **ATLAS** `MetaMathlibExt.stark_heegner_theorem` | ring class fields **proved**; the main theorem of CM (`j(τ)` generates the ring class field) and the dihedral structure over ℚ **not found** |
| B4-B6, D3 | Heegner points; Gross–Zagier; generalized GZ (Yuan–Zhang–Zhang) | "Heegner" occurs only as class-number-one discriminants (Tau Ceti) | **not found** |
| B1, B2 | Waldspurger's period formula; TYZ's genus periods | none | **not found** |
| D2 | Nonvanishing of quadratic twists (Bump–Friedberg–Hoffstein, Friedberg–Hoffstein) | **Tau Ceti** has quadratic twists of curves (`WeierstrassCurve.quadraticTwist`, classification) and of newforms, no nonvanishing theorem | **not found** |
| B4, B9 | Kolyvagin's Euler systems; Coates–Wiles; Rubin | none | **not found** |
| B5-B8 | TYZ genus points, torsion lemmas 3.16 and 3.18, Theorem 3.6 | none | **not found** |
| E3 (fork) | Mordell–Weil | **Tau Ceti** `WeierstrassCurve.Affine.fg_point_of_numberField` (`…EllipticCurve.MordellWeil.FinitelyGenerated`), weak Mordell–Weil `…finiteIndex_range_nsmulAddMonoidHom_two`, Néron–Tate pairing and regulator | **proved** (the fork already has `RouteK.Rank.fg_points`) |
| E2, E3 (fork) | Selmer groups, 2-descent, Sha | **Tau Ceti** `WeierstrassCurve.selmerGroup`, `WeierstrassCurve.sha`, `…finite_selmerGroup`, `WeierstrassCurve.Affine.pow_rank_le_card_selmerGroup₂` (`2^rank · #E[2] ≤ #Sel₂`), `…finite_selmerGroup₂`, the 2-descent map (`…EllipticCurve.GaloisCohomology.*`, `…MordellWeil.RankBound`) | **proved** (the fork defines its own `Sel2` through coverings) |
| A4, all | Congruent numbers; Tunnell; TYZ | **Formal Conjectures** `CongruentNumber.Tunnell_odd`, `…Tunnell_even` (necessary direction), `…not_congruentNumber_1` (`Wikipedia/CongruentNumber.lean`). **Tau Ceti** `TauCeti.CurveX3SubX` (`y² = x³ − x`: points of order two, reduction) | FC **statement only** (`sorry`); TYZ **not found** |
| A1, A2, E1 | Class groups of quadratic fields; genus theory; Rédei | **Mathlib** `ClassGroup`, finiteness for number fields. **Tau Ceti** `TauCeti.Multiquadratic.narrowTwoRank_eq_ncard_ramifiedPrimes_sub_one` (Gauss genus theory), `…isGenusField_candidateGenusField`, `…genusCharFunNarrowClassGroupHom`, `TauCeti.ClassGroup.twoRank`; ring-class reciprocity for binary forms | genus theory **proved**; Rédei's 4-rank formula **not found** (the fork proves `RouteK.Redei.redeiFormula` itself) |
| B9 (frame) | BSD statement | **Tau Ceti** `WeierstrassCurve.BirchSwinnertonDyerConjecture`, `TauCeti.BirchSwinnertonDyerConjecture` (`Prop`s), with `bsdQuotient`, Tamagawa numbers, real period, regulator. **Formal Conjectures** `Millennium/BSD.lean` | **statement only** (the quotient's ingredients are definitions) |

## 3. Summary

### How much of each tree exists

**H.** The steps fall into three layers.

- **Present, proved.** Number fields and local fields:
  - global class field theory, Kronecker–Weber, ring class fields (Tau Ceti);
  - the Hasse principle and sum formula for `Br`, Hilbert reciprocity (Tau Ceti);
  - Chebotarev (Tau Ceti);
  - upper-numbering ramification, Herbrand, Artin conductor exponents (Tau Ceti);
  - Skolem–Noether (Tau Ceti);
  - heights with Northcott (Mathlib).

  Scheme theory, all from Axiom's Stacks: purity of the branch locus, Abhyankar's lemma, the
  étale fundamental group, base change in étale cohomology. Modular forms: newforms, twists,
  strong multiplicity one, Atkin–Lehner/Atkin–Li, Galois conjugation of newforms (Tau Ceti), and
  the Eichler–Shimura isomorphism (Lean Pool). Elliptic curves: Tate modules, Néron–Ogg–Shafarevich
  (Tau Ceti).
- **Present only in a special case.** Abelian varieties beyond definitions, Néron models,
  polarised abelian schemes, QM abelian surfaces with level structure, Jacobian Tate modules,
  mod-𝔪 Eichler–Shimura: all in Anthropic's FLT, built to the strength Ribet's level lowering
  needs. openai/math (in the catalog, not yet mapped) has PEL moduli, abelian moduli and
  abelian-scheme Tate comparison that I did not examine.
- **Absent everywhere.**
  - Faltings 1983;
  - Faltings heights and GR14, Javanpeykar, Bost, Pazuki (Part E, F3);
  - p-adic Hodge theory beyond perfectoid and Fargues–Fontaine foundations (C3, C4, C8);
  - Pan (C7) and Carayol (D5);
  - Galois representations of newforms and Shimura's `A_f` (C9);
  - Betti–étale comparison (C5);
  - semistable reduction, Raynaud's criterion and Néron–Ogg–Shafarevich for abelian varieties
    (A6, D2);
  - the discriminant-6 Shimura curve: canonical model over ℚ, Shimura reciprocity, Baba–Granath,
    González–Rotger, Igusa invariants and theta constants (A2-A4, A7, A10, F1).

By step: about 5 of 36 have every cited supplier formalized (B1, B2, and the elementary B3, F2,
F4), about 10 in part (A1, A4, A5, A9, C8, C9, C10, D1, D3, D4), and about 21 not at all.

**CR₃.** Only the shell exists.

- **Present:** Mordell–Weil, Selmer groups and 2-descent, genus theory, ring class fields,
  newform L-functions with functional equation, Atkin–Lehner signs and analytic-rank parity,
  BSD as a statement.
- **Absent:** every deep step on the TYZ + Gross–Zagier route: B1-B9, D1, D2, D3, the root
  number of `C_d`, and the analytic continuation of `L(C_d, s)`.

What is present duplicates the Lean side the fork already proves (Part E of cr3-trust).

### The longest nearly complete chains

1. **B1-B2, the scalar descent of H.** Every cited theorem is in Tau Ceti: Skolem–Noether,
   `Br(ℚ)` local–global, the sum formula, Hilbert reciprocity, and local `H²(F, μ_n) ≅ ℤ/n`. Only
   N5's own cocycle bookkeeping and the identification `H²(G_ℚ, ±1) = Br(ℚ)[2]` remain to be
   written.
2. **A5, Lemma PR(i).** Purity (Stacks 0BMB, any dimension) and Abhyankar for a regular divisor
   (Stacks 0EYG) are the two named scheme-theoretic inputs, both proved (unreviewed). Missing:
   the model `Y₃ → P¹_j` itself, and Shimura reciprocity for Lemma NV.
3. **C9, the newform bookkeeping.** The twist is an eigenform, strong multiplicity one across
   levels picks the newform, conjugates stay new, and Atkin–Li pseudo-eigenvalues exist: all in
   Tau Ceti. Missing: Shimura's `A_f` and the `K_f`-linear Eichler–Shimura relation. Lean Pool's
   Eichler–Shimura isomorphism and Anthropic's mod-𝔪 version are the nearest material.
4. **D1 and D3-D4, local ramification.** Upper numbering, Herbrand, the quotient formula, Artin
   conductor exponents and Hilbert's different formula are in Tau Ceti. Missing: conductors of
   ℓ-adic representations and Carayol (D5).
5. **CR₃'s C4 + D1.** "Sign −1 ⇒ positive analytic rank" is proved for self-dual newforms in
   Tau Ceti, and `L(E, s)` exists as an Euler product. The single missing link is `L(C_d, s) =
   L(f, s)` for a newform `f` (Deuring/Shimura, or `C_d` as the twist of `X₀(32)`). Even with it,
   C4 also needs `𝓛(n) ≠ 0` from TYZ, which is absent.

### The biggest missing pieces, in order of size

1. **Galois representations of modular forms with local–global compatibility**: Shimura's `A_f`,
   Eichler–Shimura for ρ_f, Carayol, and Pan's Fontaine–Mazur theorem (H, Part C).
2. **p-adic Hodge theory**: `B_dR`, Hodge–Tate and de Rham representations, Scholze or
   Faltings/Tsuji comparison, Berger, Saito (H, C3-C4, C8).
3. **Arithmetic of abelian varieties in general**: Tate modules, Néron models, SGA 7 semistable
   reduction, Faltings 1983, Faltings heights and isogeny estimates (H, Parts A and E).
4. **Shimura curves**: the canonical model of the discriminant-6 curve, Shimura reciprocity at
   CM points, the Baba–Granath/Igusa equations (H, A2-A4, A7, A10, F1).
5. **The analytic theory of `L(E, s)` for CM curves, and everything built on it**: Deuring,
   root numbers, Heegner points, Gross–Zagier, Waldspurger/YZZ, Bump–Friedberg–Hoffstein, TYZ
   (CR₃, Parts B and D).

## 4. Libraries checked with nothing on topic, and libraries outside Trough

- **Formal Frontier** (40 libraries): foundations only. Continuous group cohomology after NSW,
  finite étale algebras, Iwasawa modules, profinite groups, quadratic algebras (class number of
  ℚ(√−5)), norm forms, restricted products. None states a prerequisite above.
- **PNT+, StrongPNT, PFR, Equational Theories, CFSG, physlib, cslib, Foundation, Analysis I**:
  off topic by their catalog descriptions; not scanned.
- **Imperial FLT** (`a3210204`): Galois-representation and deformation frameworks
  (`FLT/Deformations/`), hardly ramified representations, quaternion automorphic forms with Hecke
  operators, the Tate curve. Its 1980s inputs use `axiom knownin1980s`
  (`FLT/Assumptions/KnownIn1980s.lean`), and `FLT/Assumptions/Mazur.lean` has 4 sorries or
  axioms, so those results are statement only. Nothing above beyond the rows already cited.
- **Outside Trough.** `lana-agents/elliptic-curves` (Apache-2.0, sorry-free, a dependency of
  openai/math) works on reduction of elliptic curves. By its README, Néron–Ogg–Shafarevich is
  only half done there, so it adds nothing to Tau Ceti. Lean Pool's `flt-eichler-shimura` comes
  from `loefflerd/KN-scratch`.

## Caveats

- Tau Ceti was scanned at the 11-08 survey, three days before Trough's pin. The 13 headline
  names were confirmed at the pin; other names may have moved.
- Mathlib was read at 09-08 plus the pin's directory listings. A Mathlib file added after 09-08
  under an existing directory with an unrelated name would be missed.
- The Anthropic FLT rows rest on file names plus two files read. Its QM moduli, Néron models and
  Jacobian results may be more general than "special case" suggests. The next check is to read
  `Def_CerednikDrinfeld_QMModuliProps.lean` and the representability theorems it feeds, to see
  whether they give `Y₃` over ℚ.
- openai/math was read only as a file tree at its current HEAD. Its README says not every
  result is formalized; I did not check `sorry` there.
- "Not found" means no keyword hit in names or docstrings (Tau Ceti, ATLAS, Lean Pool, Formal
  Conjectures, Stacks records), no file-name hit (Anthropic and Imperial FLT, openai/math), or
  no `git grep` hit (Mathlib). The keyword lists are in `scan_tc.py` and `scan_atlas.py`.

Scratch in this directory: `scan_tc.py` with its output `tc-hits/` (one TSV per topic),
`mods.py`, `scan_atlas.py`, `tc-modules.txt`, `tc-roadmaps*.{json,txt}`,
`tc-hits/aflt-tree.txt`, `tc-hits/iflt-tree.txt`, `tc-hits/oai-tree.txt`.
