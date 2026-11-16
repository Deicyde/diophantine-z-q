# W17: actual complex exponential and its real foundations

Import `ZInQKernel.Contrib.CloudB3W17Realify.ComplexExp`.

## Main result

`CloudB3W17Realify.exists_complexExp` constructs a global analytic
additive-to-multiplicative exponential `E → G`, with value `1` and identity
manifold derivative at zero, for a finite-dimensional commutative complex
analytic self-model Lie group. Its real scalar action must be compatible with
its complex action (`IsScalarTower ℝ ℂ E`).

`exists_complexExpHom` gives the bundled `E →+ Additive G` form. Neither theorem
assumes compactness, connectedness, a local exponential, or analytic dependence
of ODE solutions on the velocity. There is no external Hausdorff hypothesis:
`LieGroup` and the existing normed-space charts supply it.

The construction uses two **fixed** canonical real flows for each complex basis
vector: `Fᵥ(z) = γᵥ(re z) · γᵢᵥ(im z)`. A proved Cauchy–Riemann derivative makes
this one-variable map holomorphic; the genuine one-variable Cauchy theorem in
local target charts makes it analytic. A finite product along complex-linear
basis coordinates then gives the global analytic exponential. Its derivative
at zero is exactly the identity by `Basis.sum_repr`.

This does **not** yet prove surjectivity, a full discrete kernel, a torus
uniformization, analytification of scheme points, general compact-group
commutativity, or either H103/H105 field. Those are separate interfaces.

## Modules and reusable results

- `ScalarRestriction` and `Realification`: same-chart scalar restriction for
  manifolds, maps and Lie groups, including `ℂ ω → ℝ ω`.
- `GlobalFlow`: completeness and uniqueness of Mathlib's actual
  `mulInvariantVectorField` on boundaryless real Banach `LieGroup I 3`, and its
  unique real one-parameter subgroup. No compactness or supplied global flow.
- `DerivRestriction`: complex/real manifold-derivative restriction in unchanged
  charts, including the reverse direction for a complex-linear candidate.
- `ComplexOneParameter`: canonical fixed-flow CR calculation and one-variable
  holomorphic-to-analytic chart upgrade.
- `ComplexExp`: finite-basis product, exact identity derivative, and bundled
  exponential homomorphism.

There are 40 checked declarations across the six modules, all with exactly
`[propext, Classical.choice, Quot.sound]`. Existing topology, charts and group
operations are retained; scalar-tower compatibility is explicit.

## Verification and source basis

Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Original base `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`; the final author branch
was rebased onto restored main `2dc949d688c407e32823c4e751679d66b2f40e65`, whose
tree is identical. No transient main WIP was used as a proof source.

The author independently compiled all six owned modules sequentially on the
dedicated node with `lake env lean -M7500 -j4`, emitting owned olean/ilean files.
All exit 0 without warnings; maximum RSS 3,305,124 KB. Exact bundled/unbundled
interfaces, finite-dimensional `Fin 2 → ℂ` usage and all 40 axiom reports were
checked. The PR supplies a fresh named build, full `#discharges`, and independent
rebuilt-pushed-commit review; the author checks alone are not that review.

Reuse is through existing Mathlib scalar restriction, canonical Lie vector
fields, local/global ODE existence and uniqueness, one-variable Cauchy analysis,
complex linear maps and finite basis calculus. No new dependency, copied
third-party library, target edit, `OneProof.Main` import in these modules,
`sorry`, new axiom, `native_decide`, or build-time syntax/macro/elaborator code.
AI-assisted original proofs, independently reviewed before PR readiness.
