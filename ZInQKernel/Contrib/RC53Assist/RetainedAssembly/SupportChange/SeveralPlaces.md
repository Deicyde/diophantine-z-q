# Several-place residual support control

All exports are in
`ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.SeveralPlaces`.
The new source is `SeveralPlaces.lean`; earlier files are unchanged.

## Result and scope

For `G : ℕ → StageComplexFamily`, `G j i` is the actual complex after `j`
place additions at coefficient stage `i`. There is no fixed support or common
character among its parameters. The step data, coefficients, support sets and
local conditions can all vary with `i`.

`residualPackage_of_support_condition_steps` proves:

```lean
theorem residualPackage_of_support_condition_steps
    (G : ℕ → StageComplexFamily) (c : ℕ → ℕ) (k B : ℕ)
    (hbase : StageResidualPackage (G 0) B) :
    (∀ j, j < k → ∀ i [NeZero i],
      Nonempty (SupportConditionStep i (G j i) (G (j + 1) i) (c j))) →
      Nonempty (ResidualComparison (G k) (G 0)
        (6 * k + ∑ j ∈ Finset.range k, c j)) ∧
      StageResidualPackage (G k)
        (B + 6 * k + ∑ j ∈ Finset.range k, c j)
```

The output comparison is an injective map in every positive coefficient stage
and degree into the base residual group and exactly `6k + sum c` extra
coordinates. The extra coordinates are zero outside `[0,3]`. They are linear
coordinate packaging after a proved cochain estimate, not declared to be
canonical arithmetic support maps.

`movingResidualPackage_of_cochain_steps` exports the same result for a terminal
family `terminal`, with an explicit equality `G k = terminal`. Its conclusion
is written literally as:

```lean
(∀ i [NeZero i], ResidualCohomologyFinite (terminal i)) ∧
(∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
  Module.finrank (ResidueField (Acoef i))
    (residualCohomologyAt (terminal i) n) = 0) ∧
(∀ i [NeZero i] (n : ℤ),
  Module.finrank (ResidueField (Acoef i))
    (residualCohomologyAt (terminal i) n) ≤
      B + 6 * k + ∑ j ∈ Finset.range k, c j)
```

This is exactly `MovingResidualPackage Fam (...)` when
`terminal i := Fam.globalCx i`. The consumer check uses the verbatim moving
family/global-complex and residual-package definitions of the supplied
interface, without importing it.

`residualSupportControl_of_cochain_steps` returns the original
`ResidualSupportControl F R (6 * k + sum c)` type when the displayed chain
endpoints are the actual family and standard reference global complexes.
`ResidualComparison.of_onePlace` and `.to_onePlace` provide the two interface
adapters.

## Why the local-condition costs are valid

A support enlargement with the new unramified condition is compared with the
previous actual residual complex. The enlarged complex with its own truncated
condition has the same compact complex as the unramified one. The two exact
triangles yield:

```text
rank Hⁿ(new condition Selmer complex)
  ≤ rank Hⁿ(previous complex)
    + rank Hⁿ⁻¹(unramified condition)
    + rank Hⁿ(new label's condition).
```

`conditionChange_cohomology` proves this estimate and finiteness. The
coordinate exchange `swapSelCx` is a checked degreewise cochain isomorphism;
it applies the existing top exact sequence to the exchanged datum. It does
not use a dual bottom sequence as if it were the condition sequence.

Thus one must not count the full local complex a second time after removing
and reinstalling a condition. The unramified contribution is at most two.
The actual condition is allowed rank at most `4 + c_v`, giving exactly the
`6 + c_v` step allowance.

For a truncated condition with its own bound `c_v`,
`CohomologyBounds.conditionAllowance` proves the weaker `4 + c_v` allowance
without changing its inclusion or cochains. For the final retained place,
which has no imposed condition, the full condition has baseline rank at most
four and may use `c_v = 0`. The target comparison permits the canonical
relaxed contraction; it does not demand an impossible degreewise isomorphism
between the old-only complex and the complex with a contractible full-condition
factor.

## Exact cochain-step hypotheses

`SupportConditionStep i X Y c` contains:

- an inflated old-place-only datum `Dold : SelData (ResidueField (Acoef i))`;
- the full local complex `L`, unramified complex `U`, and this label's own
  condition complex `V`, over that residue field;
- the actual restriction `rq : GHom Dold.G L` and inclusions
  `ιU : GHom U L`, `ιV : GHom V L`;
- a residue-field cochain map from `gcxBaseChange ... X` to
  `selCx (withLocalCondition Dold L U rq ιU)`, and its quasi-isomorphy;
- a residue-field cochain map from `gcxBaseChange ... Y` to
  `selCx (withLocalCondition Dold L V rq ιV)`, and its quasi-isomorphy;
- unramified cohomology finite in all degrees, vanishing outside `[0,1]`,
  with rank at most two;
- the actual condition cohomology finite in all degrees, vanishing outside
  `[0,2]`, with rank at most `4 + c`.

No finiteness, range or rank bound for the new global complex is a field.
No intermediate or final global residual package is assumed in the iteration.
The only global residual input is the uniform base package with bound `B`.

## Genuine printed support map

`supportConditionStep_of_print_ur` supplies the support quasi-isomorphism from
`NekovarProp788ii K` directly over `ResidueField (Acoef i)`. At each step it
uses the canonical `galoisSupportDataUr` for `S ⊆ insert q S`, with its genuine
continuous Galois cochains and canonical unramified factorizations.

Its parameters allow an arbitrary stage-specific finite coefficient module
`M` for `GKS K S` and arbitrary actual old conditions `Δ`. Its inputs are:

1. total complexity of `K`, finite `S`, and inclusion of the dyadic places;
2. a source cochain comparison with the old datum of the canonical support
   data, and its quasi-isomorphy;
3. the exact equality of the canonical enlarged datum with
   `withLocalCondition Dold L U rq ιU`;
4. the target cochain comparison preserving this label's actual condition,
   and its quasi-isomorphy;
5. the displayed unramified and actual-condition local cohomology bounds.

There is no separate support-map quasi-isomorphism hypothesis on this route.
No nonflat tensor of a stagewise quasi-isomorphism is taken. Source and target
coefficient/support/condition dictionaries remain explicit.

The unramified bound can use the existing generic
`procyclic_cohomology_bounds` with the finite residue module of rank two.
The full-condition baseline uses the same finite local rank bound four as
the one-place arithmetic construction. Each previous derivative label retains
its own truncated condition and own bound; it is not silently changed to an
unramified, strict, relaxed or zero condition.

## What is not claimed

This is a conditional arithmetic reduction and a completed finite iteration.
It does not construct the actual moving conductor characters, a base uniform
bound for an unidentified moving base family, or the coefficient and old/local
condition cochain comparisons at each step. Those inputs must identify the
terminal complexes with the actual moving family.

If the number of added places is unbounded in the coefficient stage, the formula
alone does not give a uniform constant. The statement fixes `k` uniformly over
all positive coefficient stages.

The separate `iterate_residual_comparison` and
`residualPackage_of_comparison_steps` theorems also provide the standalone
iteration assuming residual comparisons of width `6 + c_v`. That formulation
alone is not asserted to discharge the arithmetic support comparisons.

Manuscript: `diophantine_zq.tex`, lines 2727–2741, 3483–3498, 4255–4280,
4385–4451, 4859–4873 and 4976–5135. Exact statement/axiom output and
verification are recorded separately.
