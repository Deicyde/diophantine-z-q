# Shimura 1973, Theorem 1: quotient and Hecke glue

**Scoped stop at step (3).** The quotient comparison C = I_f J and the upgrade of clause
(ii) from primes and good prime squares to every positive index are proved in
`ZInQKernel/Contrib/OneProof/ShimuraSteps.lean`, given the independent composite operators
on the Jacobian and their Hecke laws. Every competing quotient kills I_f J, so the
constructed quotient maps to it over ℚ. The remaining geometric assertion is that
this surjective homomorphism of equal-dimensional abelian varieties is finite.

```lean
ShimuraSteps.shimuraThm1Af_of_printed :
  ShimuraThm1AsPrinted → ShimuraHeckeRelations → SameDimSurjectiveFinite →
    R16Thm1b.ShimuraThm1Af
```

Both remaining inputs are on-the-spot GLUE. `ShimuraHeckeRelations` supplies the independent
composite operators on the same Jacobian, pinned by their action on degree-zero divisor
classes, and the product laws. The source for the rational Hecke ring acting on J is
Shimura 1973, pp. 525–526 (AI page read). The triangular representatives, the identification
with the chosen model and the proof of the laws on this J are not supplied by that reading.
The tree has abstract double cosets and composite operators on modular forms; the search
found no independent composite operators on this Jacobian. The proposition uses actual
endomorphisms of J and the complex-point formula. Its pinning condition requires that
the formula characterize each operator, so an action on too few divisor classes does
not suffice.

`SameDimSurjectiveFinite` is the scoped step (3) input: for abelian varieties B and B′
over ℚ, if ψ : B → B′ is a surjective homomorphism and dim B = dim B′, then ψ is finite.
The application is the uniqueness discussion in Shimura 1973, p. 526; the finite-morphism
argument is on-the-spot. The tree has finiteness of [m] and the proper quasi-finite
criterion, as well as separate kernel and fibre tools. The missing comparison is from
equal absolute dimensions to a finite generic fibre and from there to all fibres by
translation after field extension. This is a piece of dimension and fibre theory,
without a new quotient construction or a classification of abelian subvarieties. Once
the induced map is finite, `KerConnected` for the competitor makes that map an
isomorphism, giving ν ≫ ψ = ν′. The scheme kernels then agree by pullback. This proof
does not interpret the printed uniqueness as already commuting with ν.

## What the printed statement means in Lean

| Print (AI page read pp. 525–527) | Encoding |
| --- | --- |
| A = J/C, C = ker ν (p. 525); the ideal annihilating the eigenform is intersected with End(J) (p. 526) | `printRing` keeps the two actions in End(J) × K_f. The annihilating pairs have second coordinate zero. `Sat` takes the integral operators in the rational annihilator by clearing a positive denominator. `PrintQuotient` says ν kills the image of every such operator and is universal among maps doing so. This represents the quotient by the sum of those images without adding a construction of quotient schemes. |
| (i) The quotient map | Surjectivity and the tree's `KerConnected` criterion: a surjective factorization followed by an isogeny must have an isomorphism as its second map. |
| (ii) The K_f-action intertwines every ξ_n | `PrintedClauses` uses `HeckeCompat` at every n > 0. The latter clears the denominator in the rational equation. `XiAction` identifies the independent ξ_n by the divisor-class formula. The zero index is a dummy for the induction, outside the printed quantifier. |
| (iii) Dimension; multiplicity m = 1 via q-expansions (p. 527) | `FiniteDimensional ℚ (coeffField f)` and `A.dim = Module.finrank ℚ (coeffField f)`. |
| Uniqueness up to isomorphisms over ℚ (p. 526) | For any competitor with `PrintedClauses`, there is an isomorphism over ℚ; no commuting triangle is included. |

This is the Γ₁(N) quotient portion. It omits clause (iv), for which the tree lacks
the cotangent-space dictionary, and the total Euler-factor identity, which the
quotient row does not consume. The identification of the kernel's modular curve
with the standard model still needs its existing bridge. The proposed print-form
rating is for review based on the AI page read. Shimura's 1971 book and
Diamond–Shurman are not manuscript citations for this bridge; no locator in those
books is claimed here.

## Lean statements

VERIFIED by compilation and the axiom scan. All names below are in `ShimuraSteps`.
Here a_n and χ(d) denote the weight-two coefficients and diamond eigenvalues;
K_f denotes `coeffField f`.

| Theorem | Statement |
| --- | --- |
| `xi_sq` | The independent good-prime square is T_p² − p⟨p⟩. |
| `two_primes` | Every unit class mod N ≥ 2 has two distinct prime representatives, both prime to N (Mathlib's Dirichlet theorem). |
| `coeff_coprime` | a_(mn) = a_m a_n at positive coprime indices. |
| `coeff_prime_power` | a_(p^(k+2)) = a_p a_(p^(k+1)) − pχ(p) a_(p^k), including bad primes. |
| `coeff_bad_power` | a_(p^k) = a_p^k at p dividing N. |
| `chi_mem` | χ(d) belongs to K_f for a unit d mod N, by the good-square coefficient and Dirichlet. |
| `ak_good`, `ak_mul`, `ak_bad` | The good prime-power, coprime and bad prime-power coefficient laws, respectively, in K_f. |
| `xi_mem` | A subring of End(J) × K_f containing the prime and diamond pairs contains every (ξ_n, a_n). |
| `diamond_mem` | A subring containing every (ξ_n, a_n) contains every diamond pair: the two Dirichlet primes give coprime multiples of the pair, and Bézout recovers it. |
| `closure_eq`, `end_ring_eq` | The generators give the same ring of pairs and the same integral subring of End(J). |
| `nsmul_hom_eq`, `hom_nsmul_eq_zero` | Precomposition by [m] is m-fold addition, and m > 0 cancels against zero in Hom(J,A). |
| `image_ideal_nsmul`, `image_family_sat` | For m > 0, t and mt have the same scheme-theoretic image; saturation leaves the whole image family unchanged. |
| `kills_sat_iff` | A homomorphism kills the saturated family's images iff it kills the original family's images. |
| `evK_coe`, `kernel_range` | Evaluation in K_f extends to the kernel's complex evaluation; the joint free-algebra image is the subring generated by primes and diamonds. |
| `print_annihilator_eq`, `print_images_eq` | The print's integral annihilating endomorphisms are the free-algebra image of ker(evF). Their saturated image family is the image family defining I_f J. |
| `kills_print_iff`, `isAfQuotient_of_print` | Killing the printed image family is equivalent to `KillsIf`; the printed universal property and surjectivity give `IsAfQuotient`. |
| `compat_zero`, `compat_one` | Zero and the identity satisfy the intertwining relation. |
| `common_denominator` | (mn)(u+v) = n(mu)+m(nv) in an additive commutative monoid. |
| `compat_add`, `compat_neg`, `compat_mul`, `compat_cancel` | The relation is preserved by addition, negation and multiplication; a common positive scalar can be moved into the denominator witness. |
| `diamond_compat`, `compat_all` | Prime and square intertwining imply diamond intertwining, then intertwining at every index by induction. |
| `incl_eq_zero`, `killsIf_of_clauses` | Rationalization kills no nonzero integral endomorphism; consequently a competitor kills I_f J. |
| `clauses_of_printed`, `printed_of_clauses` | In the presence of the composite Hecke laws, the all-index and the prime/square clauses imply one another. |
| `compatible_iso` | A competitor factors through the constructed quotient and, under `SameDimSurjectiveFinite`, the factor is an isomorphism compatible with the projections. |
| `shimuraThm1Af_of_printed` | The print-form Prop and the two named GLUE inputs imply the exact existing row. |

The standard-axiom check and the focused `#discharges` output are in
`scratch/shimura-steps/`. The stock command scans the exact
`R16Thm1b.ShimuraThm1Af` type in a one-row harness. A full assembly check is provided
separately: the local `Main.olean` is from `TailZ62`, while the requested base
uses `TailZ87` and the current assembly has 2,276 missing local import artifacts.
The focused check does not validate the full assembly.

## Fold status

VERIFIED by `autofold.py --dry-run`: strict and strictest are both **5 LEAF / 24 GLUE**
on 29 rows. Even granting the print-form Prop its proposed published rating
(`AI page read pp. 525-527`), the candidate would give **6 / 25** on 31 rows in
both counts. The count guard refused it. No fold was performed; the actual counts
remain 5 / 24. If the finiteness argument is proved and the Hecke bridge stays open,
the candidate would be 6 / 24 on 30 rows; discharging both bridges would give
6 / 23 on 29 rows, subject to the print-form rating.

## Known issues

- VERIFIED against the recorded AI page read: p. 526 has a misprint in the conjugate-newform
  sentence before clause (iv): the eigenvalue multiplies the conjugate form, rather than the
  original. This does not change the Euler identity.
- The reverse-generation sketch in `docs/research/r16-thm1b.md` §2 divides by a prime.
  That only directly establishes generation over ℚ. The integral proof here uses two
  different primes in the same unit class and applies Bézout.
- The total Euler identity alone does not identify the K_f-component in the Tate
  representation at the embedding used by the manuscript. This was already flagged in
  the source audit. The existing Diamond–Shurman characteristic-polynomial row is outside
  this contribution.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Check |
| --- | --- | --- |
| L768–770 | OK | After choosing a primitive newform, the manuscript supplies the Fricke proviso through its Li citation. The quotient clauses used here are independent of that proviso. |
| L770–771 | OK | The cited theorem supplies the construction and the total Euler-factor identity under the proviso (recorded AI page read). The formalized portion here is the construction. |
| L771–773 | unverified | The manuscript uses the quotient and the total Euler identity to identify a specific Tate constituent. The identity is total over embeddings; the embedding-specific argument is not supplied at these lines. The existing characteristic-polynomial route still supplies this input. |
| L770–773, step (1) C = I_f J | gap filled | The manuscript invokes the construction and skips the comparison with the tree's I_f J. The proof identifies the image families and translates the universal property, given the independently stated Hecke bridge. |
| L770–773, step (2) clause (ii) for all n | gap filled | The manuscript skips the clause-by-clause comparison. The proof upgrades the tree's prime and good-square tests to all positive indices, given the same Hecke bridge. |
| L770–773, step (3) ν-compatible uniqueness | unverified | The manuscript skips uniqueness and does not need the commuting triangle at this invocation. Annihilation and factorization are proved; the finiteness input for the induced surjection is still open. |
| L11053–11057 | OK | The bibliography names Shimura's 1973 paper and Theorem 1 and gives the DOI of the cited source. |
