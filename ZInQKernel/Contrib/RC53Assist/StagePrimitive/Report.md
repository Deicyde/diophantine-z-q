# Retained actual classes, primitive kernels, and height-one regularity

## Result and scope

The primitive-kernel obstruction is removed for every specified genuine two-term realization with a nonzero actual degree-one class. The retained stage vector is not replaced by its primitive kernel vector.

The contribution also constructs `HeightOneSwitchDataPK` for a specified family of genuine continuous-cochain Selmer cones from explicit actual-class determinant comparisons and local-image geometry. It then proves integrality of every constructed stage coordinate and supplies the existing height-one process consumer. The arithmetic construction of the presentation, pairing, localizations, successors, and comparison data remains an input. This is a conditional genuine-object construction, not a completed arithmetic instance of Theorem 5.3.

The source is `GenuineRegularity.lean`, in namespace `ZInQ.Contrib.RC53Assist.StagePrimitive`. It has no new printed proposition or arithmetic axiom.

## Exact nonvanishing input

For the specified actual continuous-cochain Selmer cone

```lean
C := selCx (galoisSelData K S A M Delta)
```

and a closed actual cycle `z : C.X 1`, the required input is

```lean
hnb : ∀ b : C.X 0, C.d 0 1 rfl b ≠ z
```

This says that the actual class in degree-one cohomology is nonzero, not merely that a cochain representative is nonzero. It is the cohomological meaning of the nonzero actual class in lines 4992–4995. At a known simple-zero start, lines 4928–4934 give the nonzero retained central class. For successor stages, lines 5137–5144 give the nonzero actual derivative class by its singular localization. The arithmetic verification of those assertions is not inferred from minimality.

`genuineClassVec_ne_zero_iff` proves exactly

```lean
R.classVec z hz ≠ 0 ↔ ∀ b : C.X 0, C.d 0 1 rfl b ≠ z
```

for `R : GenuineTwoTermRealization K S A M Delta`. Over a domain, `genuineClass_not_torsion_boundary` also proves that no nonzero scalar multiple of this actual class is a boundary. Its proof uses the quasi-isomorphism from the integral two-term model and the fact that the model has no degree-zero term. Thus the nonzero actual class remains nonzero generically.

In the zero-class branch, `genuineStage_coordinate_zero_of_boundary` proves that the constructed genuine stage coordinate is zero, within the determinant/adjugate scope of the existing stage constructor. No primitive-kernel witness or switching process is required for that branch.

## How the primitive-kernel field is supplied

`genuineStage_primitiveKernel` applies `exists_primitiveKernelVector` to the actual retained stage vector `R.classVec z hz`, whose nonvanishing is proved from `hnb`. The DVR saturation theorem supplies a vector `v` and a scalar `c` with

- `D *ᵥ v = 0`;
- some residue coordinate of `v` is nonzero;
- `c ≠ 0`;
- `ι (z_stage i) = c * ι (v i)` for every coordinate `i`.

No nonzero residue coordinate of `z_stage` is assumed. The saturation theorem chooses an integral divisor of the retained vector; it does not renormalize the retained class or its paired functional.

For the constructed configuration record, `GenuineStageData.primitiveKernel` is this witness. The height-one data use

```lean
primitiveKernel i := ⟨(family i).primitiveKernel hι ρ⟩
```

The exact class-retention identity is proved by `GenuineStageData.retains_class`:

```lean
R.f.f 1 1 rfl (R.b1.equivFun.symm G.stage.z) =
  G.actualClass + C.d 0 1 rfl (R.boundaryWitness G.actualClass G.class_closed)
```

The primitive vector does not occur on the right-hand side.

## Minimal realization and the same paired functional

`GenuinePresentation` contains a bounded finite-free presentation of the specified actual Selmer cone, its quasi-isomorphism, and residual cohomology ranks `n + 1` in degrees one and two, zero elsewhere. Its minimal realization is constructed by the already proved `exists_twoTermRealization_of_boundedFree`; no already two-term model is assumed.

`GenuinePresentation.realization_spec` retains the rank and minimality. `matrix_residue_zero` proves that the matrix becomes zero under a residue map killing the maximal ideal. Consequently `GenuineStageData.fiberDim_eq` identifies the computed kernel dimension with `presentation.n + 1`, and `fiberDim_residualHomology` identifies it with degree-one residual cohomology of the bounded presentation. This is the derived residue-fibre model; identification with a raw coefficient-specialized continuous-cochain Selmer cone still requires its scalar-change comparison.

The main configuration record does not accept an arbitrary closed functional. `RetainedIntegralPairing` specifies genuine conjugate and orthogonal Selmer cones, the conjugation and orthogonal comparison quasi-isomorphisms, an integral closed orthogonal lift of the same actual class with an actual boundary witness, and the Selmer cup product followed by a trace killing boundaries. Its final input is generic nondegeneracy modulo torsion, on actual cycles: an orthogonal degree-one cycle pairing to zero with every actual closed degree-two cycle has a nonzero scalar multiple that is an actual boundary.

The functional is defined by pairing with that retained orthogonal lift. `functional_closed` proves integral closedness from the cup-product Leibniz identity. `functional_nonzero_on_cycles` derives nonvanishing from generic nondegeneracy and the non-torsion actual class; it does not assume a nonzero coordinate. `GenuineStageData.coord_ne_zero` then derives generic coordinate nonvanishing. `retains_functional` proves that the stage row evaluates this same functional through the realization.

This binds the functional to the transported actual class, while leaving construction and arithmetic identification of the integral comparison, cup product, trace, and generic duality as explicit obligations.

## Genuine localizations and complete switching fields

`GenuineLocalization` is a linear map on the actual degree-one cochains, killing actual boundaries. Its matrix is derived by composing with the retained realization and basis. `class_identity` proves that its value on the retained stage vector is exactly its value on the specified actual class. `detects_actual` proves that residue-field detection of the chosen primitive kernel vector gives nonzero generic localization of that same actual class.

`GenuineSigns` carries an involution on the computed degree-one residue-fibre cohomology and the invertibility of two. Its positive and negative eigenspaces are complementary by a proved decomposition. `GenuineSignFamily.sp` and `.sm` are their dimensions; the sign-sum field is proved, not assumed as a dimension equality.

`GenuineSwitchComparison` carries the two actual-class comparison maps to the finite and singular planes. Their vector is the generic localization of the actual retained class, not an independent vector. Residue detection supplies its generic nonvanishing. Both normalized augmented-cone torsions retain the same strict factor:

```text
T_old = theta * iota(a),   T_new = theta * iota(b),   a,b in A^×.
```

`toCoordStep` constructs the existing coordinate-step consumer using `coordStep_of_commonFactor`. It derives the required coordinate nonvanishing from the genuine classes and their paired representatives. No coordinate relation is a field of the input record.

`GenuineSwitchSystem` supplies explicit successor indices and these comparisons, together with the existing geometric `QuadMixedDims`, `QuadSingleDims`, and `NonquadDims` witnesses indexed by the computed genuine fibre/sign dimensions. It assumes neither dimension drops nor regular coordinates, and has no primitive-vector field. `toData` constructs all fields of `HeightOneSwitchDataPK`:

- stage coordinates and differentials are those of the constructed genuine minimal stages;
- the primitive-kernel field is supplied by saturation of the retained actual class;
- sign sums are derived from the genuine cohomology involutions;
- coordinate steps are derived from the common strict determinant factor;
- the existing geometric dimension theorems supply the descent;
- positivity and terminal integrality are supplied by the proved primitive-kernel and two-term coordinate theorems.

`GenuineStageData.terminal_regular` independently proves integrality when the genuine presentation has residual rank one, without a switch hypothesis.

`GenuineSwitchSystem.regular` applies `regular_of_switchDataPK` and gives, for every specified configuration `i`,

```lean
∃ a : A, ι a = (family i).stage.u
```

For the actual ring `Localization.AtPrime P`, `lambdaAtPrime_dvr` proves the DVR instance from `P.height = 1`. The two height-one bridges prove `RegularAtPrime P (family i).stage.u` and apply `exists_process_of_switchDataPK` to supply

```lean
∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (i₀ : Pr.Stage),
  Pr.coord i₀ = (family i).stage.u
```

There is no free starting coordinate or process-existence hypothesis. The family interface uses a common ambient support and two specified coefficient modules. Actual support enlargements must first be compared with such an ambient presentation; these comparisons are not constructed here.

## IntegralUnit and StageConeComparison

For a supplied `GenuineSwitchComparison C`, the contribution proves

```lean
C.oldMap.IntegralUnit old_hz old_hl ↔ ∃ c : Aˣ, C.strictFactor = ι c
```

and

```lean
StageConeComparison G.stage G'.stage C.epsilon C.sigma C.J C.localization.genericVector
  ↔ ∃ c : Aˣ, C.strictFactor = ι c
```

Thus the common strict factor suffices for the coordinate step, but the literal two individual integral-unit comparisons require the extra unit-valued strict-factor certificate. The regularity proof does not assert that certificate. Actual contractible integral lifts of the two augmented comparison cones remain sufficient by the existing `integralUnit_of_contractibleLift` theorem.

## Precisely remaining arithmetic work

1. Construct the characteristic-zero scalar coefficient modules and actual local conditions over each relevant height-one localization, including their inner-limit and scalar-change comparisons. Finite coefficient rings cannot be substituted by an embedding into a characteristic-zero field.
2. Supply the actual bounded finite-free presentations, their quasi-isomorphisms to continuous-cochain Selmer cones, residual support/ranks, and generic determinant/adjugate data. The minimal realization is now constructed from these weaker inputs.
3. Verify nonzero actual cohomology at the nonzero start and at each actual derivative successor, with the same fixed multiplier and the retained finite/singular identities. Minimality alone supplies no such assertion. The zero-class branch is separate.
4. Construct the genuine integral conjugation and orthogonal comparisons, orthogonal lifts, cup products, traces, and generic nondegeneracy, retaining `D^0`, the old Kummer conditions, earlier singular conditions, and the same actual paired class.
5. Construct the actual localization maps and detecting derivative primes for the chosen primitive kernel vectors. Identify the supplied involutions and local-image witnesses with the true coefficient-specialized Selmer groups and finite/singular images, including the quadratic sign decomposition and equation (5.5a).
6. Prove the two normalized augmented-cone torsion equalities with the common strict factor from the genuine strict/relaxed Selmer triangles. These arithmetic determinant comparisons are not obtained from generic matrix comparison existence.
7. If the stronger literal `StageConeComparison` target is retained, additionally prove that the common strict factor is unit-valued, or provide compatible contractible integral lifts. Commonality and regularity alone are not asserted to give it.
8. Bind the local starting coordinates at every height-one prime to the same generic primitive coordinate, with the required support, limit, and fibre comparisons. The existing intersection/process consumer can then be used. The uniform numerical lower bound and the remaining assembly of Theorem 5.3 are not discharged by this contribution.

## Manuscript passages

The mathematical inputs and distinctions used here are the paired-functional construction, lines 3705–3774; the derivative conditions and common strict factor, lines 4864–4906; the nonzero retained start, lines 4928–4934; the minimal stage and primitive-vector selection, lines 4976–4995; the sign/dimension cases, lines 5004–5136; the actual derivative and paired-functional retention, lines 5137–5152; and terminal regularity and intersection, lines 5154–5200. No additional printed arithmetic fact is introduced.

## Verification and delivery

The final source passed an individual Lean 4.35.0 check with zero errors and zero warnings. Its mathematical declarations were also checked in a scratch copy with an identical source prefix. The successful receipt covers all 26 theorems and all 21 other named source declarations. Each of the 47 axiom reports contains exactly the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`; their universe annotations are preserved in the printed outputs.

[TheoremStatements.md](TheoremStatements.md) contains each theorem's exact printed type and exact axiom output, followed by the other named declarations. [DeclarationReceipt.txt](DeclarationReceipt.txt) is the complete successful output, without truncation. [Manifest.json](Manifest.json) records the declaration inventory, source and receipt hashes, sizes, and verification facts. The checked source SHA-256 is `dc84d78a5bc66ecdceae7dd6af52055e6fe5c2adf9666e72af74d250bd2aba44`.

Checks used six threads, the specified CPU affinity and priority, and `maxHeartbeats 800000`. No dependency build or update was run. No existing source was edited, no commit was made, and no checkout was moved. The supplied mathematical inputs were unchanged between the verification snapshots. Work was prepared against the supplied integration edition `4dab513d` and the supplied integral-stage realization sources.

Scratch checks and earlier development diagnostics are not part of the public source edition. The delivered files are the source, this report, the statement inventory, the successful receipt, and the manifest.
