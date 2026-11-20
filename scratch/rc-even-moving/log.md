# Sizing and results

VERIFIED (base declarations, in `RC/EvenExpansion/Assembly.lean` and `RC/BlocksPerU/ThetaTransform.lean`):

```lean
def MovingStepLaw (M p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ M) (phase : ℂ)
    (g : ℍ → ℂ) : Prop :=
  ∃ ξ : DirichletCharacter ℂ (M * p),
    (∀ n : ℕ, n.Coprime (M * p) → ξ n = χ n * (kronecker (p : ℤ) n : ℂ)) ∧
      HalfIntegralThreeHalves (M * p) ξ.toUnitHom (movingOp p phase g)

structure HalfIntegralThreeHalves (m : ℕ) (ξ : (ZMod m)ˣ →* ℂˣ) (g : ℍ → ℂ) : Prop where
  holo : MDiff g
  law : ∀ (γ : ↥(Gamma0 m)) (z : ℍ),
    g ((γ : SL(2, ℤ)) • z) =
      (ξ ((Gamma0Map m).toHomUnits γ) : ℂ) * thetaMultiplier γ z ^ 3 * g z
  cusps : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (cuspNorm (3 / 2) g γ)
```

The base multiplier is the quotient of actual Jacobi theta values, not an arithmetic definition.

| Tex | Existing in the tree (VERIFIED by reading) | Missing at the base |
| --- | --- | --- |
| 9497–9512 | `Vp`, `series_Vp`; Mathlib's character level change and quadratic reciprocity; nonvanishing of theta and the exact Poisson resummation. | Integral dilation conjugate; the character on units; the precise theta ratio with its sign; holomorphy and cusp bounds. |
| 9514–9542 | `Up`, `upSquare_permutation`, `upSquare_conjugation`; the existing rational-translate cusp argument and multiplier comparison at level divisible by the square of the translation denominator. | Identify the conjugation on arguments; compare the actual theta quotients for the larger bottom-left entry; transfer boundedness through positive rational affine maps and the finite sum. The old twist comparison cannot give the new exponent-one level. |
| 9543–9546 | `series_Up_sq_Vp`, `movingOp_series`, `moving_nil`, `moving_of_step`. | Close the analytic input, use stability under scalar subtraction, then iterate. |
| 9649–9655 | `evenWeightTwo` assembles once the moving and unary laws are available; `evenExpansion` transfers once its actual form and coordinates are supplied. | Discharge the moving input in a wrapper; the unary law and the constituent coordinate comparison are separate. |

VERIFIED: the earlier odd-stage `MovingSieveLaw` is also an input; it does not prove this transformation. `jacobiTheta_fourth_transform` alone cannot distinguish the required quadratic sign. `jacobiTheta_at_cusp` gives a finite quadratic sum for positive bottom-left entry; the theorem exposing that sum in the quotient is private. For the dilation one can instead center Poisson at the rational cusp b/d, and reduce to prime d by right multiplication by an integral translation (Mathlib's proved Dirichlet theorem).

VERIFIED: Lake built the base imports locally using the cache from the identical base commit. The build and direct checks run serially; a compiler lock and the host load/available memory check guard subprocesses. `Affine`, `Character`, `Matrices`, and `PrimeGauss` have passed Lake builds. The prime character is defined over the actual Dirichlet character space, and the rational affine substitution preserves both holomorphy and all cusp bounds. The finite prime-denominator Poisson calculation is an identity of actual Jacobi theta values.

VERIFIED: `thetaMultiplier_scale` passes the direct Lean check. It uses right translation to a prime denominator, computes the sign by prime Gauss sum scaling, and handles both triangular signs separately. `Vp_threeHalves` built successfully, supplying the exact character, holomorphy, and cusp bounds for the actual `Vp`.

VERIFIED: `Translate` built. Its proof uses `upSquare_conjugation` and applies the same dilation ratio twice with the same argument of the quadratic character. It proves equal theta multipliers term by term, then proves `upSquare_threeHalves` for the normalized finite sum, including all its cusp bounds.

VERIFIED: the complete `EvenMoving.Assembly` target built from the narrowed imports. `movingStep` proves the existing `MovingStepLaw` for every odd prime and level divisible by four; the analytic comparison does not need freshness. `evenMovingSieve` discharges the input in the existing good-prime induction, and the two fixed expansion wrappers have no moving-law premise. Assembly still uses the unary transformation; lattice transfer still uses the compatible embedding and the coordinates of the assembled form.

VERIFIED: the final serial Lake build of `EvenMoving.Assembly` succeeded. Direct `lake env lean -j1` checks passed on all eight new modules and `scratch/rc-even-moving/Audit.lean`. The audit covers all 48 named theorems and 20 generated private helper declarations; every reported axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`. No existing Lean or statement file changed.
