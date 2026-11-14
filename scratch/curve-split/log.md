# curve-split results log

Rows: H-79 GenusX1Field, H-81 NormalCurveSmoothQ, H-82 GeomConnectedOfConstantFieldQ (Contrib/CurvesG),
H-85 CurveBijIso (scratch/model-glue/ModelGlue6.lean), H-83 ShimuraGoodReduction
(scratch/vert-witness/VertWitness.lean), H-41 x0Transitive (Contrib/RLeaf/IgusaX0.lean).

## H-41 X0Transitive
- `scratch/curve-split/X0Split.lean`: `CurveSplit.x0Transitive_of_igusaSL2X : IgusaSL2X → X0Transitive`,
  `x0Transitive_of_igusaGL2 : IgusaGL2 → X0Transitive`. COMPILED (lake env lean, 5 s), axioms standard. VERIFIED.
- Leaves already in kernel (ZInQKernel/Contrib/RLeaf/IgusaSL2.lean): IgusaSL2X (geometric part of Igusa 1959),
  IgusaGL2 (Igusa 1959). The modular-equation form (Lang Ch.5 §2 Thm 3) cannot be stated over Mathlib 4.35:
  no j-function / modular polynomial in Mathlib (grep of NumberTheory/ModularForms: VERIFIED absent).

## H-82 GeomConnectedOfConstantFieldQ
- `scratch/curve-split/CurvesGSplit.lean`: `CurveSplit.geomConnectedOfConstantFieldQ_of_zariski :
  ZariskiConn.ZariskiConnectedness.{0} → GeomConnectedOfConstantFieldQ`. COMPILED, standard axioms. VERIFIED.
- Leaf: kernel's `ZariskiConn.ZariskiConnectedness` (EGA III₁ 4.3.1 + 4.3.4, locators UNVERIFIED).
- Glue proved: `appTop_bijective_of_constantField` (Γ(X,𝒪) integral over ℚ by Mathlib
  `isIntegral_appTop_of_universallyClosed`, embeds in function field, ℚ alg. closed in F ⇒ Γ = ℚ);
  then `ZariskiConn.app_bijective_of_appTop_bijective`. Normality hypothesis unused. No finiteness leaf needed.

## H-81 NormalCurveSmoothQ
- `CurveSplit.normalCurveSmoothQ_of_regularSmooth : RegularSmoothPerfect → NormalCurveSmoothQ`. COMPILED,
  standard axioms. VERIFIED.
- New leaf `RegularSmoothPerfect` (Stacks 00TV, ⇐ direction, tag UNVERIFIED): k perfect, S finite type k-algebra,
  q prime, S_q regular (Mathlib IsRegularLocalRing) ⇒ ∃ g ∉ q, Algebra.Smooth k S_g.
- Glue proved: `isRegularLocalRing_stalk_of_normal` (stalk = Dedekind domain ⇒ regular, Mathlib instance),
  `mem_smoothLocus_of_regular` (leaf applied on affine charts with k = Γ(Spec ℚ, ⊤)), Mathlib
  `smoothLocus_eq_top_iff`, `smoothOfRelativeDimension_one` (Contrib.Dim stalk dimension at a closed point).

## H-85 CurveBijIso (in progress)
- `scratch/curve-split/CurveBij.lean` (CurveBijIso copied verbatim from ModelGlue6.lean L2954, ns ModelGlue).
- Part A COMPILED: `CurveSplit.curveBijIso_of_closed : CurveBijIsoClosed → CurveBijIso` (fpqc descent of
  isomorphisms along Spec ℚ̄ → Spec ℚ, Mathlib `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`,
  Stacks 02L4; ℚ̄-points of S ↔ sections of S_ℚ̄). Standard axioms. VERIFIED.
- Part B COMPILED: `CurveSplit.curveBijIsoClosed_of_leaf : BijToNormalIsIso → CurveBijIsoClosed`, hence
  `CurveSplit.curveBijIso_of_leaf : BijToNormalIsIso → CurveBijIso`. Standard axioms. VERIFIED (lake env lean).
- Leaf `BijToNormalIsIso`: k alg. closed char 0, X, Y integral separated finite type over k, Y normal
  (IsNormalScheme), f bijective on k-points ⇒ IsIso f. Springer LAG Cor. 5.2.8 / Borel AG.18.2-18.4 /
  Humphreys 4.6 (numbers UNVERIFIED; printed form "separable" vs "birational" needs a human check).
- Glue proved (all Mathlib + Contrib.Dim + SmoothFibre + copies of curve-glue's isDomain_of_dim_one and
  irreducibleComponent_eq_of_isDomain_stalk): stalks at closed points of smooth curves are DVRs; smooth over a
  field ⇒ reduced; components of a smooth curve are disjoint and open; non-closed point of a dim ≤ 1 Jacobson
  space is generic in a component; `bijective_of_closedPoints` (topology); `closedPoint_facts` (Mathlib
  pointEquivClosedPoint); restriction over a component; IsZariskiLocalAtTarget for isomorphisms.

## H-79 GenusX1Field
- Finding (VERIFIED by reading consumers): T34/DimJ1Genus is only used via `LeafModCurves.dim_J1_le`
  (dim J₁(N) ≤ N²), in `javanpeykarJ1` and TailD E2 (scratch/g0-assemble2/olean). The equality is not needed.
- Equality's sources (Shimura 1971 §6.7, Prop 1.40) concern Γ₁(N)\ℍ* as a compact Riemann surface: no Lean
  definition in Mathlib 4.35 (checked: NumberTheory/ModularForms has no quotient Riemann surface / genus).
- `scratch/curve-split/GenusBound.lean` COMPILED (standard axioms): `genusX1Le_of_genusX1Field`,
  `dimJ1Le_of : DimJacobianEqGenus → GenusX1Le → DimJ1Le`, `genusX1Le_of_belyi : BelyiGenusBound →
  X0Transitive → GenusX1Le` (uses kernel `ZInQ.RLeaf.belyiX1`, `x1ConstantField_of_x0Transitive`),
  `dimJ1Le_of_belyi`.
- `BelyiGenusBound` = named GLUE (Riemann–Hurwitz bound 2g+1 ≤ d for Belyi functions), needs RH
  (Stichtenoth 3.4.13 + 3.5.1), fundamental identity (3.1.11), places are DVRs (1.1.6), genus identification.
- Part B' COMPILED: `CurveSplit.curveBijIso_of_zmt : ZMTOriginal → DegreeGeneralFibre → CurveBijIso`
  (standard axioms, VERIFIED). Leaves: `ZMTOriginal` (Mumford Red Book III.9 original form; EGA III 4.4.9:
  birational, finite fibres, Y normal ⇒ open immersion; birational via Tau Ceti `functionFieldMap`),
  `DegreeGeneralFibre` (Humphreys LAG 4.6 / Shafarevich II.6.3 / Borel AG.18.4: closed points of a general
  fibre = [K(X):K(Y)], char 0, dim X = dim Y). Numbers UNVERIFIED.
- `BelyiGenusBound` PROVED (COMPILED, standard axioms): `CurveSplit.belyiGenusBound_of_leaves :
  RiemannHurwitzQj → FundamentalIdentityQj → PlacesAreDVR → BelyiGenusBound`; and
  `CurveSplit.dimJ1Le_of_textbook : DimJacobianEqGenus → RiemannHurwitzQj → FundamentalIdentityQj →
  PlacesAreDVR → X0Transitive → DimJ1Le`. Leaves over Mathlib ValuationSubring: places (`Place F`), e_P =
  index of U_P·ℚ(j)ˣ in Fˣ, deg P = dim_ℚ κ(P). Sources Stichtenoth 3.4.13+3.5.1 (+ genus identification),
  3.1.11, 1.1.6 (numbers UNVERIFIED).
- Glue lemmas: ramIdx_eq_one (uniformizer from ℚ(j) ⇒ e=1), polyIdeal (prime, ≠ ⊥ via minpoly argument),
  exists_monic_irreducible_mem, place_cases (Belyi ⇒ unramified outside j=0,1728,∞), sum estimate.
- Part C COMPILED: `CurveSplit.zmtOriginal : ZMTOriginal` PROVED from Mathlib's
  `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` (Stacks 03GW) + new `isIso_fromNormalization`
  (relative normalization of a normal Y along a birational morphism is Y: `algebraMap_integralClosure_bijective`,
  `isIntegrallyClosed_of_normal`). Hence `CurveSplit.curveBijIso_of_degree : DegreeGeneralFibre → CurveBijIso`.
  Standard axioms. VERIFIED. H-85 now rests on ONE leaf, DegreeGeneralFibre.
- Part D COMPILED: `CurveSplit.curveBijIso : CurveBijIso` PROVED WITH NO LEAF (standard axioms, VERIFIED).
  Key steps: `bijective_of_unramifiedAt` (finite flat injective over a domain, unramified at a prime q alone
  over p with trivial residue extension ⇒ iso; via Mathlib localRingHom_{in,sur}jective_of_primesOver_eq_singleton,
  rankAtStalk_isBaseChange, rankAtStalk_eq_of_le_of_finite_of_flat, algebraMap_bijective_of_rankAtStalk),
  `isDedekindDomain_sections` (smooth integral curve ⇒ Γ over affine is Dedekind ⇒ flat), Mathlib
  `Algebra.isUnramifiedAt_bot` (char 0 generic point), Jacobson ⇒ unramified maximal ideal, Nullstellensatz
  (finite_of_finite_type_of_isJacobsonRing + IsAlgClosed.ringHom_bijective_of_isIntegral),
  `app_bijective_of_finite_bijective`, `isIso_of_finite_bijective`, `restrict_isIso_noleaf`.
- Verbatim check of CurveBijIso block against ModelGlue6.lean: VERIFIED (python substring test True).
- `CurveSplit.exists_uniformizer` PROVED (places containing j are DVRs: integral closure of ℚ[j] is Dedekind,
  R ⊆ 𝒪_P, 𝔭 = R ∩ 𝔪_P ≠ 0, uniformizer of R_𝔭 (Localization.subalgebra.ofField)). Hence
  `CurveSplit.belyiGenusBound_of_rh_fi : RiemannHurwitzQj → FundamentalIdentityQj → BelyiGenusBound` and
  `dimJ1Le_of_rh_fi : DimJacobianEqGenus → RiemannHurwitzQj → FundamentalIdentityQj → X0Transitive → DimJ1Le`.
  COMPILED, standard axioms. PlacesAreDVR no longer needed.

## H-83 ShimuraGoodReduction
- Not splittable into published-form leaves today (no abelian schemes over a base in Mathlib/kernel; a leaf over
  QMFamily would be stronger than the source). Analysis in report §3.6.
- `scratch/curve-split/ShimuraGR.lean` COMPILED: verbatim copy of pIdeal…ShimuraGoodReduction, CMObjectsExist,
  cmObjectsExist_of_R1R2fp (verbatim check True); `CurveSplit.shimuraGoodReduction_of_noGuard : R1R2fp →
  ShimuraGoodReductionNoGuard → ShimuraGoodReduction` (guard clause redundant). Standard axioms.
