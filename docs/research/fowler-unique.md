# Fowler's Proposition 2·7: uniqueness of the order and its class number

Two quadratic orders with the same trace discriminant are isomorphic as rings, and their proper class numbers agree (**VERIFIED** in Lean). The replacement leaf `FowlerProp27PrintCanonical` states Fowler's bound using one class number `hDelta Δ` for each discriminant. Lean proves it equivalent to the existing `FowlerProp27Print` and derives the live row from it. The dry run changes one GLUE to LEAF in both counts.

## What Lean proves

All declarations below are in `HDec.CMBranch.FowlerBridges`, in
`ZInQKernel/Contrib/OneProof/FowlerUniqueDiscriminant.lean` and
`ZInQKernel/Contrib/OneProof/FowlerUnique.lean`. Write `dₖ` for `NumberField.discr k` and `f` for `O.index`. The prior theorem `toOrder_index_eq_conductor` identifies `f` with the kernel's `LeafQM.AV.conductor R`, the numerical index in the full ring of integers.

| Theorem | Statement |
|---|---|
| `quadraticAlgebra_basis_discr` | The basis `(1, ω)` of `QuadraticAlgebra ℤ a b` has trace discriminant `b² + 4a`. |
| `order_finrank_eq_two` | An order in a degree-two number field has integral rank two. |
| `order_discr_mod_four` | The trace discriminant of a quadratic order is 0 or 1 modulo 4. |
| `orders_ringEquiv_of_discr_eq` | Two quadratic orders, in possibly different number fields, are isomorphic as rings if their trace discriminants agree. |
| `fields_ringEquiv_of_order_discr_eq` | The fraction fields of two such orders are isomorphic. |
| `fields_ringEquiv_of_discr_eq` | Two quadratic number fields with the same field discriminant are isomorphic. |
| `discr_and_index_eq_of_order_discr_eq` | Equality of order discriminants implies equality of the two field discriminants and equality of the two conductor indices. |
| `index_sq_eq_discr_ediv` | `f² = O.discr / dₖ` in `ℤ`. |
| `mem_order_iff_intCast_add_index_smul` | For `x ∈ 𝓞 k`, membership in `O` is equivalent to `x = a + f • y` for some `a ∈ ℤ` and `y ∈ 𝓞 k`. |
| `mem_isImagQuadOrder_iff` | The same lattice formula for the kernel's finite-index subring, with `LeafQM.AV.conductor R` as the coefficient. |
| `map_order_of_index_eq` | A field isomorphism sends the order of index `f` in one ring of integers onto the order of the same index in the other. |
| `properClassNumber_ringEquiv` | A ring isomorphism between quadratic orders preserves `properClassNumber`, via the existing equivalences with Pic and functoriality of Pic. |
| `properClassNumber_eq_of_discr_eq` | Two quadratic orders with the same discriminant have the same proper class number. |
| `hDelta_eq_properClassNumber` | For valid `Δ = O.discr`, `hDelta Δ = properClassNumber O`. |
| `field_ringEquiv_sqrt_orderDiscr` | The fraction field of a quadratic order of negative discriminant `Δ ≡ 0, 1 mod 4` is isomorphic to `ℚ(√Δ)`. |
| `field_ringEquiv_sqrt_discr` | An imaginary quadratic field is isomorphic to `ℚ(√dₖ)`. |
| `isFundamentalDiscr_field` | The field discriminant of an imaginary quadratic field satisfies Mathlib's `Int.IsFundamentalDiscr`. |
| `fowlerProp27Print_of_canonical` | `FowlerProp27PrintCanonical → FowlerProp27Print`. |
| `fowlerProp27Print_iff_canonical` | `FowlerProp27Print ↔ FowlerProp27PrintCanonical`. |
| `fowlerProp27_of_canonical` | `FowlerProp27PrintCanonical → FowlerProp27`, the live row. |

The private lemmas used in the proof give: a basis starting with 1 in a free integral rank-two algebra; the trace discriminant `b² + 4a` for a basis with relation `ω² = a + bω`; the standard quadratic algebra presentation of each order preserving discriminant; the rational model discriminant `Δ` and nonsquareness over both `ℤ` and `ℚ` when `Δ < 0`; total complexity of that model; trace discriminant `Δ` for the canonical order; and negativity of `dₖ` from the single complex place.

For order uniqueness, Mathlib identifies each order with a standard quadratic algebra and classifies these algebras over `ℤ` by their polynomial discriminants. Identifying polynomial and trace discriminants allows that result to apply to the repository's orders. Localization of the resulting isomorphism gives the field isomorphism. The existing formula `Δ = f² dₖ` then recovers the positive index by cancellation. The proof of `O = ℤ + f·𝓞 k` is independent: project along a basis `(1, θ)` of the maximal order. The image of the order is an additive subgroup of `ℤ` of index `f` and therefore equals `fℤ`. The maximal order's discriminant is fundamental because any prime-square reduction to another valid discriminant would produce an order of smaller absolute discriminant in the same field, contradicting the square-index formula.

## Match with the print

**VERIFIED** from the recorded human reading in `docs/research/fowler-bridges.md`: p. 613 defines `h(Δ)` by the proper fractional ideal classes of the unique imaginary quadratic order of discriminant `Δ`; Proposition 2·7 on p. 615 uses `h(Δ) ≤ n` for `n > 0` and bounds `√|Δ| ≤ 2n² exp(21000n²)`. The proposition covers every negative discriminant congruent to 0 or 1 modulo 4, including the orders in fields of discriminant −3 and −4.

The canonical formulation was chosen so that `hDelta : ℤ → ℕ` matches that notation directly. For each valid negative `Δ`, it counts the proper ideal classes of the order with integral basis `(1, ω)` and `ω² = Δ / 4 + (Δ % 4)ω`. Its fraction field is imaginary quadratic and its trace discriminant is exactly `Δ`. The isomorphism and Picard comparison above prove that any other quadratic order of discriminant `Δ` has this same count. Finiteness is the prior theorem `finite_properIdealClasses`. The leaf retains the print's discriminant and positivity conditions and constants; it has no extra realization hypothesis. It does not depend on a binary form class correspondence.

## Counts and verification

| H count, 29 rows | Before: LEAF / GLUE | Dry run: LEAF / GLUE |
|---|---:|---:|
| Strict | 4 / 25 | 5 / 24 |
| Strictest | 4 / 25 | 5 / 24 |

VERIFIED: the read-only preview in `scratch/fowler-unique/autofold-output.txt` replaces `fowlerProp27` with `fowlerProp27PrintCanonical`; no fold was applied. The live `#discharges` check in `scratch/fowler-unique/discharges-output.txt` reports that `fowlerProp27_of_canonical` discharges `OpenResearchLeaves66.fowlerProp27` with only that leaf. `scratch/fowler-unique/axioms-output.txt` records 34 axiom checks (including private lemmas), all within `propext`, `Classical.choice`, and `Quot.sound`.

## Known issues

No new manuscript or source error was found. The prior report records that Cox's Lemma 7.2 gives the additive index and that equation (7.3) gives the square-index discriminant formula. These locators are inherited from that report; no new Cox or Fowler reading was done. The old `FowlerProp27Print` docstring still describes its original presentation; the new canonical statement and bridge leave it and the live assembly untouched.

## Manuscript check

| TeX lines | Verdict | Step |
|---|---|---|
| L585–586 | OK | The full geometric endomorphism order supplies a negative trace discriminant. The existing trace and sign bridges identify it with the discriminant used here. |
| L586–587 | gap filled | The separate `cmjDegree` input supplies the singular modulus degree comparison; its order class number now agrees in Lean with the canonical `h(Δ)`. |
| L588–590 | gap filled | Apply the canonical statement at `n = D`. Lean transports the proper class count for every order of discriminant `Δ` to the function in the print. |
| L592–593 | OK | The recorded reading confirms the absence of an exceptional-field exclusion; neither the leaf nor its bridge excludes a field. |
