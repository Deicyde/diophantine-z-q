# A common return index in two compact groups

[`ZInQKernel.Contrib.CompactRecurrence`](../../ZInQKernel/Contrib/CompactRecurrence.lean)
exports additive and multiplicative applications of pinned Mathlib recurrence.
For arbitrary compact topological additive groups `A`, `B`, points `x`, `y`,
identity neighborhoods `U`, `V`, and `N : ℕ`,
`ZInQ.CompactRecurrence.exists_nsmul_mem_prod_gt` supplies **one** `a : ℕ` with

```text
N < a,  0 < a,  a • x ∈ U,  a • y ∈ V.
```

`ZInQ.CompactRecurrence.exists_pow_mem_prod_gt` supplies the corresponding
statement for powers in compact topological groups. The groups can be
noncommutative, have torsion, or consist only of the identity. The neighborhoods
need not be open; membership in the identity's neighborhood filter suffices.
No Hausdorff or infinite-order hypothesis is imposed. The conclusion is
arbitrarily late simultaneous returns, with no claim that every iterate converges.

These are applications of existing mathematics, originally supplied as anonymous
examples in PR #14 at `95a262a7f246da8499b91e2cfedd492ef796425e`. The current
integration moves them from the former `lean/Examples` location into the root
`z_in_q_kernel` package and gives them public names for ordinary importers.
The two proof bodies and complete statements are preserved. This is AI-assisted
work by Codex, with no claim of new mathematics or a solved open problem.

## Source and application contract

The supplying result is Mathlib's
[`mapClusterPt_one_atTop_pow`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Algebra/Group/SubmonoidClosure.lean#L53-L56),
with its `to_additive` counterpart `mapClusterPt_zero_atTop_nsmul`, at Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, using Lean 4.35.0. Its conclusion
is `MapClusterPt 1 atTop (x ^ · : ℕ → G)`, additively zero and natural multiples.
Mathlib's source credits Yury Kudryashov and is licensed under Apache 2.0.
The proof is called, not copied; upstream attribution and license apply.

| Obligation | Required input, constructed input, and connecting argument |
| --- | --- |
| Source hypotheses | The supplier requires a compact topological group. The product inherits the group, topology, compactness and topological-group instances from the two factors. Additive instances are analogous. |
| Constructed objects | The point is exactly `(x, y)` in `A × B` or `G × H`; the neighborhood is `U ×ˢ V`, justified by `prod_mem_nhds` in `Mathlib.Topology.Constructions.SumProd` (lines 303–308). |
| Domain and index coverage | The supplier concerns all natural iterates at `atTop`. `mapClusterPt_iff_frequently` in `Mathlib.Topology.ClusterPt` (lines 158–163) gives frequent membership for this product neighborhood. `Filter.frequently_atTop` in `Mathlib.Order.Filter.AtTopBot.Basic` (lines 83–84) supplies a witness at least `N + 1` for every `N : ℕ`. No restriction to a subfamily or separate coordinate indices occurs. |
| Transition and comparison maps | Product scalar multiplication and product powers are coordinatewise. The two projections preserve the **same** natural index. There is no change of normalization, scalar factor, or limit order. |
| Identity of consumed object | Membership of `a • (x,y)` or `(x,y)^a` in `U ×ˢ V` is exactly the pair of coordinate memberships returned as `hUV.1`, `hUV.2`. Both exported proofs consume that same witness `a`. |
| Coefficients and conventions | Iteration uses natural numbers. `a ≥ N + 1` implies both `N < a` and `0 < a` by the displayed natural-order lemmas. No rational or integral coefficient conversion occurs in these proofs. |
| Local conditions | `prod_mem_nhds hU hV` checks the exact identity neighborhood used by recurrence. No local-coordinate, metric-radius or punctured-neighborhood assertion is supplied. |
| Exceptional cases | Identity points and torsion are allowed: recurrence may return exactly to the identity. Noncommutativity causes no obstruction because the argument uses powers of one element of the product. Zero bound `N = 0` still gives `a ≥ 1`. No division occurs. |
| Downstream consumption | The ordinary importer in `CompactRecurrenceCheck.lean` applies each exported theorem to its complete generic statement. The conditional historical geometric use below needs additional interfaces; no current main-theorem module imports this contribution. |

This is an author-supplied contract and derivation for review, not an independent
acceptance record. It changes no accepted manuscript application or audit binding.

## Reproduction in the current package

Use the root `lakefile.toml` (`z_in_q_kernel`) and its unchanged
`lean-toolchain` and `lake-manifest.json`. Prepare the pinned dependency cache,
then run **from the repository root**:

```sh
lake exe cache get Mathlib.Topology.Algebra.Group.SubmonoidClosure
lake --wfail build \
  +ZInQKernel.Contrib.CompactRecurrence +ZInQKernel.Contrib.CompactRecurrenceCheck
lake env lean -Ddebug.skipKernelTC=false -DwarningAsError=true \
  ZInQKernel/Contrib/CompactRecurrence.lean
lake env lean -Ddebug.skipKernelTC=false -DwarningAsError=true \
  ZInQKernel/Contrib/CompactRecurrenceCheck.lean
python3 -B scripts/check_kernel_contract.py --base-ref a5937595cde3e3db00975b81e5171cdef92c801a
python3 -B scripts/check_lean.py
python3 -B scripts/check_audit_history.py --self-test
git diff --check
```

A compatible dependency cache can be reused after checking all nine git
revisions against the root manifest and verifying tracked-source cleanliness.
The importer checks the full generic exported statements and guards the printed axiom
closures of the **complete proofs** against the exact expected whitelist. Each closure is exactly `propext`,
`Classical.choice`, `Quot.sound`. The checks reuse pinned dependency artifacts;
they do not rebuild Lean, Mathlib, the accepted helper snapshot, or the entire
kernel project. The helper source check and kernel contract check have their
own structural scope and do not establish an arithmetic theorem.

The importer was written and checked by the integrator. Fresh non-author review
of this revision, exact-head required CI and the designated authenticated
`gpt-6-astra` Protocol acceptance remain separate gates. The earlier PR14 reviews
retain only their earlier revision and scope; no acceptance is carried forward
by updating their hashes.

## Conditional connection to historical HypCC

The historical intended consumer is
[`CondZQ.HypCC` in PR #6 at `7663a19635390053716f02bfcbd16b97c42bd26a`](https://github.com/elliotglazer/diophantine-z-q/blob/7663a19635390053716f02bfcbd16b97c42bd26a/lean/CondZQ/Hypotheses.lean#L109-L114),
which refers to `eq:close-complete`, lines 6109–6127 of the fixed
[`audited-baseline.tex`](../theorem-application-audit/source/audited-baseline.tex).
This comparison uses that historical argument and its definitions, not merely
its earlier verdict; it is not an integration into the current manuscript or
a current proof dependency. Its target is
`∀ n κ : ℤ, n ∉ Cset → κ ≠ 0 → ∃ a l j : ℤ, accept n κ a l j`.
For each already fixed **signed** `n` and nonzero **signed** `κ`, the required
conditions in that revision's `CondZQ.Model.accept` are

```text
1 ≤ a,  1 ≤ l,  j = n*a,
|rval a j - n| < eps l,
4 * eps l < ((4 : ℚ) ^ Bval n κ)⁻¹.
```

The abstract contribution leaves all the following interfaces unproved:

1. The actual compact topological additive groups of real points of the two
   base changes of `E/K0` under `σ₊, σ₋ : ℚ(√2) → ℝ`, including the identity.
   These are the two factors abbreviated as `E(ℝ) × E(ℝ)` in the argument.
2. One homomorphism `Φ : E(K0) →+ E_{σ₊}(ℝ) × E_{σ₋}(ℝ)` with
   `Φ(m • P0) = m • Φ(P0)` for signed integers `m`. Both coordinates must
   arise from this same `K0` point and index; unrelated real orbits do not
   identify `CondZQ.zcoord`, `eps`, or `rval`.
3. Compatibility and continuity of the local parameter `z = -x/y`, extended
   at the identity, with these embeddings; the needed nonzero denominators
   along admissible positive multiples; and strictly positive `eps l` that
   become arbitrarily small along simultaneous returns. Abstract recurrence
   permits torsion and thus supplies none of this nonvanishing.
4. For every permitted signed `n`, a punctured local limit derived from the
   derivative of `[n]` at the identity, compatible with the rational-part
   quotient defining `rval`: `rval a (n*a) → n` along those returns. This
   requires an actual local-coordinate argument.
5. Transfer of the real estimates to the exact strict rational inequalities
   in `accept`, with its particular `eps`, `rval`, and `Bval` definitions.

Conditionally on these interfaces, fix `n ∉ Cset` and `κ ≠ 0`, then choose
positive `l` with `0 < eps l` and
`4 * eps l < ((4 : ℚ) ^ Bval n κ)⁻¹`. For this fixed positive tolerance, the
ratio limit supplies a product neighborhood and any needed lower bound in
which the first strict inequality holds. Apply additive recurrence to `Φ(P0)`
to choose a common positive `a`, and set `j = n*a`. Cast the positive natural
witnesses to integers; `j` can be negative. This order keeps the tolerance and
both coordinates tied to the same actual orbit.

The historical argument supplies a conditional intended use; its realization
in this contribution is pending. This note proves neither HypCC nor the main
Z/Q theorem and claims no current-manuscript incorporation or new gap repair.
It is a focused non-release contribution. Current manuscripts, PDFs, archived
research evidence, release manifests, accepted baseline sources and the
quarantined target are unchanged, so release synchronization, a cumulative
release handoff and mirror publication are inapplicable to this patch.
