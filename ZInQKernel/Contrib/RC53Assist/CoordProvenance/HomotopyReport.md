# Homotopy-aware retained comparison and the same paired functional

## Result and scope

This continuation replaces strict cochain pullback with an explicit homotopy-aware comparison. The augmentation maps retain the class and functional boundary terms. The augmented comparison cone is proved exact from the original model quasi-isomorphism, including zero-coordinate cases. Its determinant-basis transport factor is computed from the cone rather than supplied as a coordinate equality.

Comparisons are constructed through the genuine continuous-cochain Selmer complexes. The same class is lifted through the specified conjugate-orthogonal comparison, its paired functional is constructed as PD(-, zperp), and the original-basis rows are derived from that functional. A two-term core gives a constructed unique adjugate scalar and its coordinate in the original retained basis.

**The manuscript's arithmetic family and the binding of its already supplied (4.7) scalar to this construction are not completed.** The actual orthogonal and conjugation diagrams, retained finite graded models, and common coefficient realizations must still be instantiated by the arithmetic objects. No casewise restatement of the original coordinate identity is counted as discharging that arithmetic obligation.

Supplied integration base: `27579f4a`. The earlier publication and its proof files are preserved unchanged. This is a new continuation, not a correction of protected history.

## New proof files

Paths are repository-relative.

| File | Bytes | SHA-256 |
|---|---:|---|
| `ZInQKernel/Contrib/RC53Assist/CoordProvenance/HomotopyComparison.lean` | 80,122 | `e935c0c0c5049e608c608d4d4795a277c694145d6178fef3dca58949d4a9648b` |
| `ZInQKernel/Contrib/RC53Assist/CoordProvenance/IntegralFunctional.lean` | 10,144 | `0566fb27cf77b1e8164a48104041518d82eb7217ea2ffae0be177612883b0c41` |

There are 50 new theorem declarations: 42 in `HomotopyComparison` and 8 in `IntegralFunctional`. The complete theorem statements, individual axiom outputs, and declaration contexts accompany this report. The final source files contain no diagnostic commands.

## Classification following the review

`RankOneCoordinateProvenanceG` and `AcyclicCoordinateConventionG` are exactly the rank-one and acyclic restrictions of the open original-coordinate identity. Their conjunction is a correct casewise reformulation, not independent object provenance. The new construction does not take either predicate, `RelIsKMG`, `OrigCoordLink`, or a numerical original-coordinate equality as an input.

The strict `RetainedCoordinateModelG` can fail for a nonzero coboundary functional even when its cohomology tensor has coordinate zero. Requiring the functional cochain to vanish at an acyclic constituent would not repair that faithfully. The homotopy-aware augmentation below retains the actual coboundary primitive instead.

## Explicit augmented comparison

`HomotopyComparison` contains a four-term chain map f and boundary primitives b and r with

```text
f¹ z_C = z_D + d_D⁰ b,
λ_D f² = λ_C + r d_C².
```

The induced map of the original augmented complexes has degree-zero and degree-three matrices

```text
f_aug⁰ = [ f⁰  b ],       f_aug³ = [ f³  0 ].
         [  0  1 ]                [  r  1 ]
```

`class_discrepancy` proves the class boundary explicitly. `functional_on_cycles` proves equality of the functional values on corresponding degree-two cocycles. `augMap` is an actual chain map of the original augmented complexes, not the diagonal augmentation map of a strictly compatible replacement.

For a coboundary λ_C = β d_C² and target functional zero, r = -β retains the degree-three map

```text
(v, a) ↦ a - β(v).
```

The contractible-tail example has a nonzero original functional, a constructed contraction of this augmented comparison cone, and cone torsion exactly one in the specified retained basis. `tailComparison_off_diagonal`, `tailComparison_cone_torsion_ne_zero`, `tailComparison_retained_cone_basis`, and `tail_functional_ne_zero` verify this representative case directly.

## Cone exactness and determinant-basis transport are derived

`aug_cone_exact` proves exactness of the homotopy-aware augmented cone from the original four-term quasi-isomorphism. Its cycle-and-boundary proof uses the ordinary comparison cone and retains the two augmentation-line corrections. It does not require an exact augmentation, nonzero class, nonzero functional class, or a zero functional cochain at acyclic constituents.

`aug_cone_torsion_ne_zero` consequently constructs nonzero cone torsion. With the source and target basis orientations σ_C and σ_D, the transport factor is

```text
T = (-1)^(card of the odd augmented source basis) / τ(cone f_aug).
```

`coordinate_formula_of_quasiIso` proves

```text
kmCoord(C, z_C, λ_C; σ_C) = T · kmCoord(D, z_D, λ_D; σ_D).
```

T is a nonzero element of the coefficient field. It is the computed factor expressing the target tensor coordinate in the original source determinant basis. No arbitrary field-unit lift is called a power-series unit. If the actual cone basis has the canonical retained sign, `coordinate_eq_of_retained_basis` gives equality of the two standard-basis coordinates; that optional specialization is separate from the constructed general transport factor.

The source basis must be instantiated by the manuscript's retained original model basis. A bare quasi-isomorphism to genuine cochains does not identify an independently selected standard basis with that specified integral basis.

## Constructing the comparison through the genuine cochains

`exists_model_comparison` constructs f and a cochain homotopy

```text
ψ_C ≃ ψ_D f
```

for a supplied finite source model and quasi-isomorphic finite target model mapping to the same cochain complex. The proof lifts a linear family of ordinary-cone cycles one degree at a time. It does not start with f or with an equality of coordinates. `toCCHomotopy` realizes the resulting data as a Mathlib cochain homotopy, and `ModelComparison.quasiIso` proves f is a quasi-isomorphism when both model maps are.

The actual class is lifted through each model map with its retained boundary. `modelRow_value` and `modelRow_closed` derive the model row from the given actual functional and prove closedness. The functional discrepancy is computed from the degree-three component of the model homotopy:

```text
r = -L h³
```

in the original source basis. It is not an independent scalar rescaling of the functional. `actual_class_discrepancy` obtains the class primitive from the target's ordinary comparison cone.

`exists_actual_retained_comparison` assembles the same class, functional rows, original-basis matrices, homotopy-aware comparison, derived quasi-isomorphism, nonzero transport factor, and coordinate formula. None of its inputs is the coordinate conclusion.

## The same paired conjugate class and integral functional

The genuine specialization uses `galoisSelData` and `genuinePairData`: actual global and local continuous cochains, the supplied coefficient pairing, localization maps and local isotropy homotopies.

For the specified orthogonal comparison j and conjugation map c, the lifted dual class satisfies

```text
j zperp - c(z) = d bperp.
```

Its functional is exactly

```text
L(v) = tr(v ∪ zperp) = PD(v, zperp).
```

`exists_genuine_retained_PD_comparison` derives both model rows from this same functional and constructs the retained comparison between the genuine finite model maps. The left-cup-order companion is retained for the primitive-to-relaxed pairing convention; the PD(-, zperp) theorem states the manuscript's displayed order explicitly.

`IntegralFunctional` proves the lift and closed-functional construction over an arbitrary commutative coefficient ring, before scalar evaluation or passage to a fraction field. `exists_genuine_integral_paired_functional` states it on the genuine Galois Selmer complexes. No denominator or new normalization is inserted.

Alternative lifts through the same orthogonal comparison differ by an integral boundary. If zperp - zperp' = d b, their functional difference is explicitly

```text
L_zperp(v) - L_zperp'(v) = -tr(dv ∪ b).
```

Thus the paired functional class is unchanged on degree-two cohomology. This is the dual-boundary homotopy retained by the augmented map, not a demand that the functional representative vanish.

These results construct the class and functional from the supplied genuine diagrams. They do not prove that arbitrary maps j and c, arbitrary coefficient pairings or traces, or arbitrary model bases are the manuscript's arithmetic choices. That actual instantiation remains part of the obligation below.

## Constructing the scalar from the actual two-term core

For a supplied actual two-term core with nonzero adjugate, `exists_unique_adjugate_coordinate` constructs the unique u with

```text
z_D ⊗ λ_D = u · adj(D).
```

The acyclic case is included; no exact augmentation is assumed. The existing total adjugate-to-Knudsen–Mumford theorem then identifies this core scalar with the core coordinate.

`exists_actual_adjugate_coordinate` and `exists_genuine_adjugate_PD_coordinate` construct u from the same actual class and paired functional, construct the comparison and its retained basis factor, and prove

```text
kmCoord(original C, the same class and functional) = T · u.
```

This is an object-based scalar construction. It is not a proof that an independently supplied relaxed scalar from a correction record equals T u.

## What remains open precisely

1. **Actual arithmetic diagrams.** Instantiate the genuine coefficient modules, local conditions and their isotropy homotopies, actual class with its fixed multiplier, conjugation map c, orthogonal comparison j and its quasi-isomorphy, and the actual integral cup pairing and trace. The universal continuous-cochain definitions alone do not construct these arithmetic choices.
2. **Retained finite graded models and scalar realizations.** Construct the actual original and relaxed-core finite models with the retained bases and quasi-isomorphism maps ψ_C and ψ_D, compatible with the finite coefficient diagrams and sign evaluation. Supply the core's nonzero adjugate in the guarded generic patterns. The integral functional construction does not by itself provide a common completed-ring and rational-power-series realization.
3. **Binding the existing (4.7) scalar.** Prove from those actual models and coefficient diagrams that the already supplied relaxed scalar is the core adjugate scalar expressed in the original retained basis, namely T u. Do not substitute a new scalar with that definition for the existing scalar, and do not replace this construction by the two conclusion-shaped case predicates.
4. **Correct grading and interface.** The full-condition singular quotients of the manuscript are in degrees one and two and contribute det(B)^(-1). The legacy `Identification2G` coordinate interface places its new block in degrees two and three and contributes det(B). The generic four-term construction handles the correct full-condition model, but no actual adapter or graded retained comparison from the full-condition `Identification3` model to the legacy interface is supplied here. The requested legacy `RelIsKMG` and `OrigCoordLink` for the intended arithmetic family are therefore not claimed as proved.

Once these data identify the actual relaxed scalar with the constructed original-basis coordinate, the existing unit-free correction and coordinate-link reductions apply. There is no remaining need for the false premise that the correction has a power-series-unit lift.

## Mathematical sources

- ex:arith-paired-functional, TeX 3837–3862: the actual orthogonal comparison, inverse homotopies and integral paired functional.
- ex:arith-coordinate, TeX 3877–3892: the same class, paired functional and retained determinant basis; coordinate zero at an acyclic constituent.
- ex:arith-common-coordinate, TeX 4159–4194: actual primitive-to-relaxed and paired maps, retained homotopies and mapping-cone bases; Nekovář, Sections 6.4.1–6.4.3.
- ex:limits-fixed-field-clearing, TeX 5509–5516 and 5586–5617: retained determinant factors and the same transported cochains.

Every new result is proved from the existing cochain, matrix and torsion definitions. No additional printed proposition or new trusted axiom is introduced.

## Verification and complete statements

Both final proof files compiled as single files after the prerequisite build reported successful completion. The two final body compilations and the two complete declaration audits returned exit code zero without warnings or errors.

All 50 new theorem declarations have exactly the following individual axiom list, with universe annotations preserved in the accompanying raw reports:

```text
[propext, Classical.choice, Quot.sound]
```

All 79 explicit declarations were type-checked and axiom-checked, including definitions, abbreviations and structures. Every non-theorem declaration uses only a subset of the same standard axioms; some use none.

`HomotopyStatements.md` contains every exact declaration type and every individual axiom report. `HomotopyComparison.axioms.txt` and `IntegralFunctional.axioms.txt` preserve the original complete compiler output. `HomotopyManifest.json` lists byte sizes and digests, and `HomotopySHA256SUMS` covers the new delivery.

The heartbeat bound in the two final sources is 800000. Temporary diagnostic copies are removed from the delivery. No existing source, earlier published proof file, history, commit, dependency or target build was changed. No agents were spawned and no messages were sent.
