# The Hecke square root on the Y₃ route

The contribution proves `SGRDirect.heckeSqrtBranchAny_proof (hy : Y3P1j.Y3ToP1j) :
SGRDirect.HeckeSqrtBranchAny`. The fold supplies `hy` from the existing
`y3ToP1j` projection. It removes `research/heckeSqrtBranchAny` and adds no
hypotheses. The proposition itself is unchanged: for every triple
`(Y, Φ, π)` satisfying `R1fpProps`, `R1heckeProps`, and `R2fpProps`, and every
finite Galois `E/ℚ(X)` with the normalization chart, there are `c ∈ ℚˣ` and
`s ∈ E` with `s² = c(27X + 16)`.

## Fold and checks

| H open list | LEAF | GLUE, strict | GLUE, strictest | Total |
|---|---:|---:|---:|---:|
| `OpenResearchLeaves59Y3` route | 5 | 28 | 28 | 33 |
| `OpenResearchLeaves60Y3` route | 5 | 27 | 27 | 32 |

This is a net decrease of one GLUE in both columns, using the base
Y₃ fold’s classification. The Lean open-list comparison checks that
exactly the target field disappears; including pole completeness the
totals are 34 → 33.

- [Autofold spec](../../scratch/hecke-sqrt/autofold.json) and
  [kinds removal](../../scratch/hecke-sqrt/kinds-remove.tsv): remove one field,
  add no rows. The scratch renderer handles the suffixed Y₃ fold without
  editing `OneProof/Main.lean`.
- [Discharge output](../../scratch/hecke-sqrt/discharges.txt): the exact old
  field matches `heckeSqrtBranchAny_proof`, whose only assumption is the
  already listed `Y3P1j.Y3ToP1j`. The scratch check uses the regular
  `#discharges` implementation with the two Contrib bundle names also
  recognized as bundles. The excerpt keeps the new square-root theorems
  and open-list counts.
- [Dry run](../../scratch/hecke-sqrt/MainDryRun.lean): `frozenTarget`
  compiles with `OpenResearchLeaves60Y3` and the next top theorem.
  [Axiom output](../../scratch/hecke-sqrt/maindryrun-out.txt):
  `propext`, `Classical.choice`, `Quot.sound`, the same three as the
  square-root theorem. All contribution modules and scratch checks were
  checked serially with Lean 4.35.0 against the cached base.

## Proof (ON THE SPOT, provenance (c))

Work throughout on the finite chart, with `B` the integral closure of
`ℚ[X]` in `E`. Each geometric chart point is a ring map
`ψ : B → ℚ̄`. Transitivity by twists and changes of marking, and counting in
one generic fibre, show that every Galois element acts on all chart points
by such a composite. On underlying QM pairs only the outer twist survives.
The four representatives compose by xor, and a point over 1 distinguishes
them: it cannot have any of the three CM types, by the existing CM
implications. The second bit of this twist index gives a sign character.

Inertia at the kernel of `ψ` is its stabilizer. Over 0 the two negative-sign
indices are impossible by the fixed-point implications and the CM
coordinates. For the other direction, `Y3ToP1j` supplies a CM(−24) pair.
The existing `GapST.twist_of_cm` constructs the integral intertwiner
`ι(ij)φ/6` over ℂ, with `φ² = −6` in the commutant; the proof uses the
existing commutant base change and QM isomorphism descent to transport this
to ℚ̄. A unit changes the twisted marking back to the original one. The
result is a negative-sign inertia element at the point over −16/27.

The sign eigenspace gives a nonzero element with square in the base. Clear
denominators and remove square factors to get a squarefree radicand
`f ∈ ℚ[X]`. If a prime of `f` had inertia contained in the character kernel,
the ramification index below its prime in the fixed field would be 1,
by comparing the two inertia orders in the tower. The square of an
integral element of that fixed field cannot then have valuation 1 there.
The existing finite-chart ramification bounds and the positive sign over
0 exclude every prime of `f` except `X + 16/27`. Negative inertia forces
the integral eigenvector to be zero in its residue field, so `f` is
nonconstant. Squarefreeness leaves a nonzero rational multiple of
`27X + 16`. The argument uses neither the infinity chart nor a relation
between inertia generators.

## Lean declarations

The chart and character lemmas are in `HeckeSqrtAction.lean` and
`HeckeSqrtCharacter.lean`; the general sign and ramification lemmas are in
`HeckeSqrtKummer.lean`; the application is in `HeckeSqrt.lean`. All are
under `ZInQKernel/Contrib/OneProof/`. Helper names below omit the namespace
`SGRDirect.HeckeSqrt`.

| Theorem | Statement |
|---|---|
| `cm24_fixed` | With the torsion, uniformization, lattice and QM automorphism facts, each CM(−24) QM pair over ℚ̄ is isomorphic to its `rep 3` twist. |
| `fixed_level` | A QM isomorphism to the original pair after a twist gives a unit restoring the original full level class. |
| `poly_injective` | The structural map `ℚ[X] → E` is injective. |
| `Chart.point_injective`, `Chart.exists_point` | Chart points distinguish their ring maps; every geometric point with finite `π` value is obtained from a chart ring map. |
| `ringAction_apply`, `ringAction_mul` | Restriction to the integral closure agrees with the Galois action in `E` and sends products to compositions. |
| `inertia_iff_stabilizes` | Inertia at `ker ψ` is exactly the subgroup fixing `ψ` by precomposition. |
| `Chart.exists_aut` | An endomorphism preserving `π` on geometric points acts on the chart by a single Galois element. |
| `Chart.exists_hecke` | Every Galois element acts on all chart points as a fixed twist followed by a fixed marking change. |
| `trace_of_action`, `trace_rep` | A twist and a marking change give a trace on underlying QM pairs; if the twist is `rep k`, the trace is `k`. |
| `trace_mul`, `trace_unique`, `trace_index` | Traces for products compose by xor, each trace is unique, and every Galois element has the chosen trace `index`. |
| `sign_xr`, `sign_sq`, `sign_ne_zero` | The second-bit sign respects xor, has square 1 and is nonzero. |
| `trace_sign_at_zero` | At a geometric chart point over 0, inertia has sign 1. |
| `exists_inertia_trace_three` | A CM(−24) object with a fixed-pair isomorphism for `rep 3` gives a geometric chart point with an inertia element of trace 3. |
| `mem_inertia_iff`, `commutes_poly` | Mathlib's inertia subgroup agrees with `InertiaQ`; all Galois automorphisms fix the image of `ℚ[X]`. |
| `squarefree_eigenvector` | A sign character with a negative value admits a nonzero eigenvector whose square is the image of a squarefree polynomial. |
| `prime_support` | For a squarefree sign radicand, an irreducible divisor cannot have inertia contained in the character kernel at any prime above it. |
| `radicand_mem_of_neg` | If inertia has a negative-sign element, the sign radicand lies in the contracted prime. |
| `exists_at_coordinate`, `cm_objects` | The Y₃ row realizes any proposed geometric coordinate; its CM clauses give objects of all three CM types. |
| `exists_residue_hom` | A prime above a rational linear prime has a geometric point map with that kernel and the given rational coordinate. |
| `inertia_trivial_of_ramificationIdx_eq_one` | At a prime with ramification index 1 in this chart, inertia is trivial. |
| `SGRDirect.heckeSqrtBranchAny_of_y3` | The existing Y₃, torsion, uniformization, lattice, QM automorphism, rigidity and fixed-point inputs imply the original square-root proposition. |
| `SGRDirect.heckeSqrtBranchAny_proof` | The existing Y₃ row alone implies the original proposition; the other inputs are supplied by kernel theorems. |
| `HDec.HSyn.openResearchLeaves59Y3_of_60Y3` | The new research bundle implies the old bundle, filling its omitted field with the proof. |
| `HDec.HSyn.sixContactMin_of_open79_heckeSqrt` | The new research bundle with the same textbook and added bundles gives `ZInQ.SixContactMin`. |
| `ZInQ.OneProof.frozenTarget` (scratch dry run) | The new H bundles and the same pole completeness hypothesis give `ZInQ.FrozenTarget`. |

## Known issues

The citation and interpretation caveats in [the Y₃ row report](y3-p1j.md)
remain. The orders `4,6,2` refer to the elliptic orbifold orders and their
role in the torsion-free cover, rather than the ramification indices of
the fourfold `X₆ → X₆/W`. The published dictionary from the polarized
normalizer quotient to the all-components QM moduli curve, and the choice
of coordinate by the ordered CM triple, were not independently checked
here. No new source is used.

## Manuscript check

Line numbers refer to `diophantine_zq.tex`. The Lean arguments establish
the indicated consequences of inputs already in the tree; they are not a
new statement check of the published Y₃ input.

| Lines | Manuscript step | Verdict | Evidence or limit |
|---|---|---|---|
| L411–420 | Quaternion and polarization datum | unverified | The proof uses the existing Lean order and its twists. The polarization comparison is not formalized here; the Gram computation is in the earlier Y₃ row report. |
| L421–422 | The three elliptic values of the Y₃ quotient and finite branch support | gap filled | The existing CM clauses give the coordinates; `heckeBranch_of` gives index 1 away from the two finite branch values. The sign proof distinguishes the inertia at the two finite values. |
| L421–422 | Exact indices (4,6,2) for the level cover | unverified | Only the finite-chart bounds already proved in the tree are used. The exact values and printed source are not needed or independently checked. |
| L423–429 | Four-element adelic normalizer quotient `W` | unverified | The proof does not need the comparison of the adelic quotient with the group of outer automorphisms. |
| L425–440 | Action by twists, as needed to get a global sign on the finite chart | gap filled | Lean proves that the four representatives of `Aut(𝒪)/Inn(𝒪)` give a single global Galois sign, using the existing geometric fibre description. |
| L430–440 | Central ideles, the quotient on all components and the degree bound | unverified | The existing Y₃ row supplies the geometric fibre description; the proof counts one fibre using the rank of the given Galois extension. It does not verify the adelic moduli dictionary or use the numerical bound 324 here. |
| L481–500 | Stable-model action and retention of three disjoint sections with indices (4,6,2) | unverified | This is the manuscript’s tame integral-model route. The proof does not use it or check the specialization of inertia. |
| L502–508 | Integral identification of the quotient with the stated `j` coordinate | unverified | Not needed on the characteristic-zero finite chart. |
| L510–526 | Pullback normalization and the local equation `u − c = z²` | unverified | Not the route taken. This equation controls a pulled-back completed local ring and does not provide a global element of the original function field. |
