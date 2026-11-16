# Global canonical invariant flow (W17 partial Lie-theory foundation)

Import `ZInQKernel.Contrib.CloudB3W17Realify.GlobalFlow`.

The exact core hypotheses are a real model `I : ModelWithCorners ℝ E H`,
`[LieGroup I 3 G]`, `[CompleteSpace E]`, `[T2Space G]`, and
`[BoundarylessManifold I G]`. No compactness, connectedness, finite dimension,
commutativity, extra axiom, or assumed global-flow premise is used.

## Main results (namespace `CloudB3W17Realify`)

```lean
theorem existsUnique_global_invariantCurve (v : GroupLieAlgebra I G) (g : G) :
  ∃! γ : ℝ → G, γ 0 = g ∧ IsMIntegralCurve γ (mulInvariantVectorField v)

theorem existsUnique_oneParameterCurve (v : GroupLieAlgebra I G) :
  ∃! γ : ℝ → G, γ 0 = 1 ∧ IsMIntegralCurve γ (mulInvariantVectorField v)

theorem existsUnique_oneParameterSubgroup (v : GroupLieAlgebra I G) :
  ∃! γ : ℝ →+ Additive G,
    IsMIntegralCurve (fun t => Additive.toMul (γ t)) (mulInvariantVectorField v)
```

`exists_global_invariantCurve` gives existence from any initial group point.
`invariantCurve_add` proves `γ (s+t) = γ s * γ t` for the identity-starting
canonical-field curve; `invariantCurve_unique` proves equality of two global
curves agreeing at any one time. `IsMIntegralCurve.continuous` from Mathlib
also gives continuity of these one-parameter curves automatically.

The canonical-field left-translation lemmas are exposed:

- `mfderiv_mul_left_invariant`: `D(L_g)_h (X_v h) = X_v (g*h)`.
- `isMIntegralCurveOn_mul_left`: a left translate of a local/set integral curve
  is a curve of the same canonical field.
- `isMIntegralCurve_mul_left`: the global variant.
- `contMDiff_invariantField`: the actual canonical vector field is `C¹`.

## Proof and scope

The vector field is **Mathlib's actual `mulInvariantVectorField`**, not a
new predicate or user-supplied flow. The derivative invariance lemma is proved
by the chain rule and associativity. A local canonical-field curve through
`1` exists by Mathlib's boundaryless real Banach-manifold ODE theorem. All
its left translates exist on the same epsilon interval, so Mathlib's
uniform-time extension theorem yields global curves through every point.
Global ODE uniqueness gives both `∃!` results. Comparing `γ(t+s)` with
`γ(s)*γ(t)` gives the subgroup law; it is then packaged as an `AddMonoidHom`.

Only two Mathlib imports are used: `GroupLieAlgebra` and
`IntegralCurve.UniformTime`. The latter imports the local existence/uniqueness
and time-translation APIs. Source: Mathlib pin
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean 4.35.0.

This is a **partial foundational edge**, not H103/H105 or Mumford closure.
No joint smooth/analytic dependence on `v`, exponential map, derivative of
an exponential, lattice/fullness, analytic graph algebraization, or general
complex uniformization is claimed. The separate completed realification
modules remain unchanged. A usage check combines them with this real theorem
for a complex analytic self-model Lie group, lowering real `ω` to `3`.

## Verification and local branch

Branch `cloud-b3/w17-real-flow`, created `--no-track` from the completed
realification commit `2e04266405cd29a3446661c0d0e2e9d7c048a5ca` (original base
`0e70c94e4a2d26838f0766cd69b39bd02f48fb85`; no accidental `a981` base).
`push.default=nothing`; no upstream; no public writes.

Sequential direct module and usage-check builds, one Lean process at a time:

```sh
lake env lean -M6144 -j4 \
  -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/GlobalFlow.olean \
  -i .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/GlobalFlow.ilean \
  ZInQKernel/Contrib/CloudB3W17Realify/GlobalFlow.lean
lake env lean -M6144 -j4 scratch/GlobalFlowCheck.lean
```

Both exit 0 without warnings. Peak module RSS about 3.26 GB.
Scratch `GlobalFlowCheck.lean` checks all three generic `∃!` interfaces,
the subgroup law, and complex analytic use through the unchanged realification
module. Full axiom output on all **11** new theorem declarations is in
`scratch/GlobalFlow-Axiom-Output.txt`; every line
reports `[propext, Classical.choice, Quot.sound]`.
No full repository build or `#discharges` field closure is claimed.

The new Lean module has no `sorry`, new axiom, OneProof.Main import, eval,
initialization, new syntax/notation, macros/elaborators or native proof shortcut.
`set_option autoImplicit false` prevents undeclared statement parameters.
