# p1-quot3 results log

Base: wip/p1-quot3 = 19793c5d (p1-quot2). Merged origin/wip/dcy3-used (36240662, includes leaf-fold23: field
mumfordGroupLaw, DCY3Used.y3Connected_of_leaves) as 6abfc715 (clean).
Build tree: copy of ~/dzq-wt/p1-quot2/.lake/build and lean/.lake/build (19793c5d), then lake build of the merged tree.

## Findings
- VERIFIED (read): Mathlib `Algebra.Smooth.of_formallySmooth_fiber` (RingTheory/Smooth/Fiber.lean L238): flat + finitely
  presented + every fibre `I.Fiber S` formally smooth over `I.ResidueField` => smooth.
- VERIFIED (read): vendored FLT `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`
  (CloudW03NeronSurj/Vendor/Theorems): smooth over a UFD domain => localizations at primes are normal domains.
- VERIFIED (read): Mathlib `Algebra.IsInvariant` (RingTheory/Invariant/Defs.lean), `Algebra.IsInvariant.isIntegral`.
- VERIFIED (read): chain textbook field `CurveSplit.RegularSmoothPerfect` (TailR L1471, Stacks 00TV, `<=` direction).
- VERIFIED (read): `ZariskiConn.ZariskiConnectedness` is already a kernel leaf (Contrib/ZariskiConn/Basic.lean).

## Compile log
- Build of the merged tree (DeligneComponentsY3Used, QuotientP1Printed): OK (6 min; TailZ23..TailZ40 rebuilt).
- scratch/p1-quot3/Invariants.lean (Mathlib only): `exists_algebraMap_mem_notMem` (norm trick), `localRingHom_injective`,
  `dvd_of_dvd_atPrime`, `isDomain_isIntegrallyClosed_atPrime` (normality of all localizations descends from C to
  D = C^G, finite G, no condition on |G|): compiles, 0 errors (VERIFIED).
- Invariants.lean extended: `smooth_of_invariants_field` (perfect field, C smooth of dim <= 1, D = C^G finite type
  => D smooth; uses the copied RegularSmoothPerfect and the vendored FLT normality of smooth algebras),
  `reynolds`, `exists_retraction`, `tensorAut`, `smooth_of_invariants` (R noetherian with perfect residue fields,
  B smooth over R with fibres of dim <= 1, |G| invertible in R, A = B^G of finite type => A smooth over R; flat as a
  retract of B, fibres by base change of invariants via the Reynolds operator, Mathlib
  `Algebra.Smooth.of_formallySmooth_fiber`): compiles, 0 errors (VERIFIED).
- Helper module ZInQKernel/Contrib/OneProof/QuotientP1/TameInvariants.lean generated from Invariants.lean (namespace
  QuotientP1Proof.TameQuot): `lake build` OK (VERIFIED). Added `perfectField_residueField`, the dimension lemmas
  `ringKrullDim_of_isStandardSmoothOfRelativeDimension`, `ringKrullDim_tensor_eq_one/le_one` (pullbackSpecIso and
  Contrib/Dim), `fibre_invariants`, `ringKrullDim_fibre_eq`.
- scratch/p1-quot3/Scheme.lean (imports TameInvariants and QuotProper): action of G on Γ(X, q⁻¹V) (`sect`, `action`),
  `invariant_setup`, `smooth_appLE`, `relDim_eq_one`, and
  `HDec.MCRGlue.TameQuotScheme.tameQuotientSmoothRelDim_of_regularSmoothPerfect : RegularSmoothPerfect →
  TameQuotientSmoothRelDim`: 0 errors; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
  => Task part (1) done: TameQuotientSmoothRelDim proved from the chain's textbook field regularSmoothPerfect, no new leaf.
- Contribution modules: ZInQKernel/Contrib/OneProof/QuotientP1/TameQuotSmooth.lean (from Scheme.lean; adds
  HDec.MCRGlue.tameQuotientSmoothRelDim_of_regularSmoothPerfect (hRS : CurveSplit.RegularSmoothPerfect) and
  tameQuotientSmooth_of_regularSmoothPerfect) and ZInQKernel/Contrib/OneProof/QuotientP1Smooth.lean
  (HDec.MCRQuot.quotientP1Coordinate_of_fields4; HeckeIrreducible via DCY3Used.y3Connected_of_leaves from
  mumfordGroupLaw + shimuraMainThmIDeligneY3AbU): `lake build` OK (VERIFIED).
- #discharges (scratch/p1-quot3/Discharges.lean -> discharges_out.txt): "DISCHARGES [OpenGlue7.quotientP1Coordinate]
  by HDec.MCRQuot.quotientP1Coordinate_of_fields4", still assumes LichtenbaumProjective, FiniteQuotientExists,
  SmoothModelOfP1, EdixhovenFixedSmooth2 + 6 chain fields (regularSmoothPerfect, mumfordTorsionAlgClosed,
  mumfordGroupLaw, shimuraMainThmIDeligneY3AbU, uniformizationLeafAll, gagaMorphism); axioms standard (VERIFIED).
- autofold.json (fields4; leaves lichtenbaumProjective, finiteQuotientExists, smoothModelOfP1 (consequence),
  edixhovenFixedSmooth2): --dry-run WITHOUT --allow-rise accepted: "strict count: 46/10 on 56 -> 49/10 on 59;
  strictest 45/11 -> 48/11" (GLUE unchanged, net 0; p1-quot2 was +1). Generated module (FoldDry.lean, line 1
  stripped) compiles; sixContactMin_of_open30 axioms standard (VERIFIED).

## L4 analysis
- VERIFIED (read): `ZariskiConn.ZariskiConnectedness_proof : ZariskiConnectedness` is a theorem
  (Contrib/CloudW02Connectedness/Basic.lean L47); `ZariskiConn.appTop_bijective_of_generic` (ZariskiConn/Basic.lean L65).
- Code-search survey of Contrib/CloudW07JacobiansCurves (declarations read in source by the survey agent, not
  compiled here): isLocallyConstant_eulerCharFiber, eulerChar_unit_eq_one_sub_genus, subsingleton_H_one_twist,
  isRelativeEffectiveCartier_ker_of_section, nonempty_iso_dual_zeroLocus, zeroLocus_finrank,
  hFiber_zero_eq_degree_add_one_sub_genus, isFiniteLocallyFreeInDegree_of_positive_fibres, homOfSections,
  exists_hom_twistRestrict exist; missing: genus 0 + degree-1 pencil => iso to P^1, fibrewise iso criterion,
  named arithmeticGenus(P^1) = 0.
- L4 stays GLUE (consequence); no printed statement located (SPECULATIVE candidates in report §5.3).

## L4 bypassed (no new leaf)
- Helpers (all `lake build` OK, no sorry; generated from scratch/p1-quot3/L4A..L4E.lean):
  QuotientP1/P1ModelA (Γ(P¹ by charts over ℚ) = ℚ; Γ(𝒵) = ℤ_(p); geometric connectedness via the proved Zariski
  connectedness theorem; integral fibres; generic point ξ of the special fibre; codim ≤ 1 points),
  P1ModelB (extension of sections over codim ≥ 2, from the vendored extension theorem),
  P1ModelC (chart lemmas; the generic coordinate extends: extend_of_isInteger, isUnit_germ_of_third (the third
  section forces a unit at ξ), exists_extensions, exists_toP1),
  P1ModelD (P¹ over any affine base by charts, from p1-quot's P1Scheme),
  P1ModelE (chart rings are polynomial rings: transcendence of the reduced coordinate; the map to P¹_{ℤ_(p)} has
  finite fibres hence is finite; exists_p1Coordinate).
- ZInQKernel/Contrib/OneProof/QuotientP1Model.lean (from L4F.lean): coordinateFromSectionsGen_of (glue C2 without
  L4's coordinate), quotientP1Coordinate_of_printed3, quotientP1Coordinate_of_fields5: build OK; axioms standard
  (VERIFIED).
- #discharges (Discharges5.lean -> discharges5_out.txt): "DISCHARGES [OpenGlue7.quotientP1Coordinate] by
  HDec.MCRQuot.quotientP1Coordinate_of_fields5", still assumes LichtenbaumProjective, FiniteQuotientExists,
  EdixhovenFixedSmooth2 + 6 chain fields; axioms standard (VERIFIED).
- autofold.json (fields5; leaves lichtenbaumProjective, finiteQuotientExists, edixhovenFixedSmooth2, all published):
  --dry-run: "strict count: 46/10 on 56 -> 49/9 on 58; strictest 45/11 -> 48/10" => the fold PAYS -1 (VERIFIED).
  Generated module (FoldDry.lean) compiles; sixContactMin_of_open30 axioms standard (VERIFIED).
