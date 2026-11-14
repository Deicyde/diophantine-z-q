# av-split results log

Base cba8157f (wip/av-split). Build artifacts: copied .lake/build from ~/dzq-wt/leaf-fold6 (same ZInQKernel sources as cba8157f; `git diff --stat cba8157f HEAD -- ZInQKernel` empty there); lake replays them.

## 03:20 T5Isog.lean (rows H-25, H-54)
- `lake env lean scratch/av-split/T5Isog.lean`: compiles, 56 s. VERIFIED.
- `AvSplit.torsionStructure_of_mumford : MumfordTorsionAlgClosed → PkgI2.TorsionStructure.{0}`; axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- `AvSplit.isogenyQuasiInverse_of_milne : MilneIsogenyQuasiInverse → WeilPairing.IsogenyQuasiInverse`; axioms standard. VERIFIED.
- Row H-54 text copied verbatim from scratch/g0-assemble2/parts/a35_g12det.lean L400-404 (diff with scratch/leaf-fold5/Leaves5.lean L49753-49755: identical). VERIFIED.
- Universe: TorsionStructure is universe-polymorphic (`K : Type u`); proved at u = 0 (AbVarBC infrastructure is at Type). Note for integration.

## 03:25 T35.lean (row H-38)
- compiles; `AvSplit.uniformizationExists_of_mumford : MumfordUniformizationC → ZInQ.LeafPush2.UniformizationExists`, axioms standard. VERIFIED.
- `AvSplit.mumford_of_uniformizationExists` (converse; the leaf is the row at K = ℂ, σ = id). VERIFIED.
- Proof: A_ℂ = A.baseChange ℂ via σ.toAlgebra; dim (AbVar.dim_baseChange); points via AbVarBC.bcPt; (bcPt p).left = p.left ≫ pullback.fst; cEvalAt via Scheme.Hom.comp_appLE.

## T4.lean (row H-24)
- `AvSplit.T4.henselian_of_isAlgClosed` (valuation subring of an alg. closed field is a HenselianLocalRing): compiled, standard axioms. VERIFIED.
- `AvSplit.T4.reductionTorsionBijective_of : MulEtaleAbelianScheme → UnramifiedSectionsEq → HenselEtaleLift → PkgI2.ReductionTorsionBijective.{0}`: compiled, standard axioms. VERIFIED.
  Proved pieces: valuative criterion lifts (iota_comp_injective/surjective, Mathlib), G : A(K̄) ≃* 𝒜(K̄/O) via mapPullbackAdj (G_injective/surjective, multiplicative), isRed_iff, rho_inj (from leaves a, b), rho_surj (from leaf a + GLUE HenselEtaleLift + henselian).
- Open GLUE: `HenselEtaleLift` (scheme form of Hensel); plan: prove from leaf `StacksHenselEtaleSection` (Stacks 04GG ring form).
- 03:45 `AvSplit.T4.henselEtaleLift_of_stacks : StacksHenselEtaleSection → HenselEtaleLift`: compiled, standard axioms. VERIFIED. (affine opens U ∋ f(a₀ s), V ⊆ f⁻¹U; ptRing from AbVarBC.Tangent; S = R ⊗_{Γ(U)} Γ(V) étale (Mathlib Algebra.Etale.baseChange); q = ker(S → κ); res ∘ τ = χ.)
- `AvSplit.T4.reductionTorsionBijective_of_leaves : MulEtaleAbelianScheme → UnramifiedSectionsEq → StacksHenselEtaleSection → PkgI2.ReductionTorsionBijective.{0}`: compiled, standard axioms. VERIFIED. Row H-24 DONE (three published-form leaves, no glue).

## HomLattice.lean (row H-69)
- Finding: Birkenhake–Lange Prop. 1.2.1 (holomorphic homomorphisms of tori are ℂ-linear) is already a kernel theorem: `BPAnalytic.exists_complexLinear_lift` (ZInQKernel/HDecomp/Analytic/Hom.lean). VERIFIED (read; used below).
- `AvSplit.HomLattice.homLatticeCorr_of : UnifHoloLift → ZInQ.HomUnify.HomRealize → ZInQ.HomUnify.HomLatticeCorr`: compiled, standard axioms. VERIFIED.
- `AvSplit.HomLattice.homLinearLift_of : UnifHoloLift → HomLinearLift` (via torusMap, eΦ : ℂ^g/Λ ≃+ A(ℂ)_σ, exists_complexLinear_lift). VERIFIED.
- Open GLUE: `UnifHoloLift` (weak uniformizations: kernels discrete, induced torus maps holomorphic; needs analytic coordinates + compactness of A(ℂ)^an), `HomRealize` (GAGA content; GAGA not statable over Mathlib definitions: no analytification).

## 04:15 report draft docs/research/av-split.md
- Checked by grep: Mathlib v4.35 has no Pic / line bundles / sheaf of differentials on schemes (Mathlib/AlgebraicGeometry: Modules/{Presheaf,Sheaf,Tilde}.lean only); sheaf cohomology `CategoryTheory.Sheaf.H` (abelian groups). VERIFIED.
- H-53, H-78: reported as not splittable over Mathlib definitions (stay GLUE).

## 03:52 T4.lean: leaves (b), (c) proved from Mathlib
- `AvSplit.T4.unramifiedSectionsEq : UnramifiedSectionsEq` — proved (Mathlib `isOpenImmersion_diagonal`, separated ⇒ closed diagonal, clopen preimage, `IsOpenImmersion.lift`). Standard axioms. VERIFIED.
- `AvSplit.T4.stacksHenselEtaleSection : StacksHenselEtaleSection` — proved (Mathlib `Algebra.IsEtaleAt.exists_isStandardEtale` (Stacks 00UE), `StandardEtalePresentation`, `HenselianLocalRing.is_henselian`). Standard axioms. VERIFIED.
- `AvSplit.T4.reductionTorsionBijective_of_mulEtale : MulEtaleAbelianScheme → PkgI2.ReductionTorsionBijective.{0}`. Standard axioms. VERIFIED. Row H-24 now rests on ONE leaf.
