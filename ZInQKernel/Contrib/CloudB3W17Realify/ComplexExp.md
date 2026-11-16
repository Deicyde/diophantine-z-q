# Actual global analytic complex exponential (W17)

Import `ZInQKernel.Contrib.CloudB3W17Realify.ComplexExp`.

## Proved result

Namespace `CloudB3W17Realify`, exact public interface:

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup 𝓘(ℂ, E) ω G]

theorem exists_complexExp [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] :
    ∃ exp : E → G, exp 0 = 1 ∧ (∀ x y, exp (x + y) = exp x * exp y) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω exp ∧
      HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) exp 0 (ContinuousLinearMap.id ℂ E)

theorem exists_complexExpHom [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] :
    ∃ exp : E →+ Additive G,
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x => Additive.toMul (exp x)) ∧
      HasMFDerivAt 𝓘(ℂ, E) 𝓘(ℂ, E) (fun x => Additive.toMul (exp x)) 0
        (ContinuousLinearMap.id ℂ E)
```

No compactness, connectedness, externally supplied Hausdorff instance, local
exponential, analytic velocity dependence, H103, or GAGA premise is assumed.
Hausdorffness is derived internally from the Lie-group topology and chart T1.
Commutativity is an **explicit hypothesis**, not a claimed consequence of
compactness. The compatible real scalar action is genuine restriction of the
complex action. The topology and charted-space structure stay unchanged.

This is the actual analytic-exponential construction requested, not a
conditional assembly over an invented analytic ODE supplier. Its derivative
is identity in Mathlib's actual tangent/model coordinates.

## Construction and proof

1. `DerivRestriction.lean` proves both directions of `HasMFDerivAt` scalar
   restriction in identical self-model charts. The reverse direction uses
   Mathlib `HasFDerivWithinAt.of_restrictScalars`: the derivative little-o
   condition is unchanged. `mfderiv_real_apply` compares the actual derivatives.
2. `ComplexOneParameter.lean` uses the already-proved global canonical real
   flows for **two fixed velocities** `v` and `I • v`. Define
   `F_v(z) = γ_v(z.re) * γ_(I • v)(z.im)`. Both flows have actual manifold
   derivatives from their integral-curve predicates. The product chain rule,
   commutativity, invariant-field translation and scalar restriction give the
   real derivative as complex left translation applied to
   `h.re • v + h.im • (I • v) = h • v`. This Cauchy--Riemann equality is proved.
3. The complex-linear candidate real derivative is promoted to a complex
   manifold derivative. For **one-variable** maps `ℂ → G`, local target-chart
   complex differentiability upgrades to analyticity by the true domain-ℂ
   CauchyIntegral theorem. No multivariable Hartogs or analytic ODE theorem is
   used. Result `exists_complexOneParameter v` has global hom law, `C^ω`, and
   derivative `z ↦ z • v` at zero.
4. Choose a finite **complex** basis `b`. Define the exponential by a finite
   product of the fixed analytic `F_(b_i)` evaluated at complex-linear basis
   coordinates. Products and composition are analytic by the existing Lie-group
   API. The subgroup law follows factorwise. At zero all factors equal one;
   their derivatives add by the actual multiplication chain rule. The sum of
   coordinate/basis rank-one derivatives is identity by `b.sum_repr`.

Supporting proved APIs:
- `hasMFDerivAt_real`, `hasMFDerivAt_complex`, `mfderiv_real_apply`;
- `real_invariantField_eq`, `hasMFDerivAt_complexifiedFlow`,
  `contMDiff_omega_of_mdifferentiable_oneVariable`, `exists_complexOneParameter`;
- `hasMFDerivAt_mul_at_one`, `hasMFDerivAt_prod_at_one`,
  `exists_complexExp_of_basis` (conditional basis assembly, discharged in the
  unconditional public `exists_complexExp`).

## Verification and source pins

Lean 4.35.0, Mathlib **56a005855ea17e0b0958f73ec801ae140b0a1679**.
Original source base **0e70c94e4a2d26838f0766cd69b39bd02f48fb85**; dedicated
final rebuild rebased onto restored main
**2dc949d688c407e32823c4e751679d66b2f40e65**, whose tree is identical to the
original base (`062fd1b56c0ba75329a30734f55c3e6db2c21d45`). No transient `a981`
base or sources were used.

The completed ScalarRestriction, Realification and GlobalFlow modules were
not changed. Only new files were added. The private branch is
`cloud-b3/w17-complex-exp`, with `push.default=nothing` and no upstream.
No public push or GitHub write was made.

Final rebuild on **devvm54793.nha0.facebook.com** compiled all six modules
sequentially, one Lean process at a time:

```sh
for m in ScalarRestriction Realification GlobalFlow DerivRestriction ComplexOneParameter ComplexExp; do
  lake env lean -M7500 -j4 \
    -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/$m.olean \
    -i .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/$m.ilean \
    ZInQKernel/Contrib/CloudB3W17Realify/$m.lean || exit $?
done
lake env lean -M7500 -j4 /home/jackmccarthy/cloud-b3/w17/scout/ComplexExpCheck.lean
```

All module builds and the final usage/axiom check exit 0 without warnings.
Maximum module RSS: **3,305,124 KB**. Usage check RSS: **3,270,512 KB**.
Checks exercise the exact generic interfaces, bundled homomorphism form,
direct `mfderiv exp 0 v = v`, and a fixed `Fin 2 → ℂ` model specialization.

Every one of the **13 new theorem declarations** reports exactly
`[propext, Classical.choice, Quot.sound]`. Full evidence and scratch check are
under the dedicated W17 scout directory:
`ComplexExp-Axiom-Output.txt`, `ComplexExpCheck.lean`.
The new modules enable `autoImplicit false`. Dedicated prohibited-code scan
has zero matches: no sorry, new axiom, eval, initialization, new syntax/notation,
macros/elaborators, native proof shortcuts, or OneProof.Main import.

## Exact remaining scope

This does not yet prove surjectivity, discrete/full kernel, or the analytic
quotient-to-group diffeomorphism; those belong to the separate lattice author.
It also does not prove analytic manifold existence on algebraic scheme points,
proper complex-point compactness, algebraic-to-analytic connectedness, general
compact complex Lie-group commutativity, or GAGA. **No H103/H105 closure or
full Mumford theorem is claimed.** No full repository build or #discharges
closure check is represented by these module-level builds.
