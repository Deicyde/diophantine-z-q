# P4: Hasse and absolute convergence for the actual congruent-number L-function

## Status and frozen scope

**The requested mathematical statements are implemented as closed Lean theorems.**
This packet is a contribution, **not issue closure, full-project validation, an
independent acceptance, or the required protected Astra approval**. Integration
and the eligible review gate remain external. No PR, commit, push, registry,
original source, dependency pin, checker, or protocol record was changed.

The implementation is based on public main
`a5937595cde3e3db00975b81e5171cdef92c801a`, in the isolated P4 worktree on branch
`work/issue37-p4-hasse-investigation`. Lean is **4.35.0**, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib is pinned at
`56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).
The requested P4 scope comes from the assigned investigation; this note does
not assert a freshly queried GitHub issue or PR status.

All new proof declarations live in `ZInQ.Contrib.Hasse`. The two principal types
are:

```lean
LFunction_cd_prime_hasse {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (p : ℕ) [Fact p.Prime] (hpd : ¬ p ∣ 2 * d) :
    |(((shortCurve (-(d : ℚ) ^ 2)).LFunction p : ℤ) : ℝ)|
      ≤ 2 * Real.sqrt p

LFunction_cd_summable {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    {s : ℂ} (hs : (3 / 2 : ℝ) < s.re) :
    LSeriesSummable
      (fun n => (((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℤ) : ℂ)) s
```

There is **no Hasse hypothesis**, additional typeclass assertion of the bound,
new axiom, numerical certificate, or changed meaning of `LFunction` in these
types. The second theorem uses exactly the coefficients in Mathlib's
`WeierstrassCurve.LSeries`, by that definition's composition with integer casting.
Oddness and squarefreeness are the original local-model identification's
hypotheses, not assumptions used to prove the finite-field character estimate.

## Proof route and source-to-consumer derivations

Write `η` for Mathlib's integer quadratic character cast to `ℂ`, extended by
zero at zero, and `S_d = ∑x η(x³ - d²x)` over a finite field `F`.

1. **Actual affine count** (`PointCount.affine_count_eq_char_sum`). For
   characteristic different from two, the square-root fiber formula gives
   `#affine = #F + ∑x quadraticChar F (f x)`. The equivalence between the
   subtype of pairs and the sigma type of root fibers supplies domain coverage;
   the formula includes zeros and is not a nonsingular point-count assertion.
2. **Inert case** (`sum_eta_of_odd`). If `-1` is a nonsquare, negation is a
   permutation and changes every term's sign. Hence `S_d = 0`. The odd cubic
   identity holds for every `d`, even zero; it is not a claim about singular
   projective point counts. This adapts the inspected P1 argument identified below.
3. **Quartic character construction** (`Quartic.exists_quartic`). If
   `4 ∣ #F - 1`, `MulChar.exists_mulChar_orderOf` with the genuine primitive root
   `Complex.I` constructs `χ` of order **exactly four**. `χ²` is a nontrivial
   quadratic character. The cyclic unit-group generator proves uniqueness of
   nontrivial quadratic characters into `ℂ`, identifying `χ² = η`. This
   normalization is a proved equality, not a parameter assumed to exist.
4. **Complete square-map pushforward** (`CM.sum_comp_sq`). For every `f`,
   `∑x f(x²) = ∑t (1 + η(t)) f(t)`. The fiber over zero has size one and
   is explicitly included. Since `χ(x²) = η(x)`, multiplying out the pushforward
   gives the exact identity
   `S_1 = η(-1) (J(χ,η) + J(χ⁻¹,η))`.
   The sign `η(-1)` is retained; no unstated convention is needed to remove it.
5. **Twist normalization** (`CM.cubic_sum_twist`). For `d ≠ 0`, the bijection
   `x = d*u` yields `S_d = η(d) S_1`, because the cubic scales by `d³` and
   `η(d)² = 1`. Nonzero `d` is essential for this change of variable and is
   obtained from the good-prime condition in the consuming application.
6. **Jacobi norm** (`Quartic.norm_jacobiSum`). Mathlib supplies
   `J(χ,φ) J(χ⁻¹,φ⁻¹) = #F` when `χ`, `φ`, `χφ` are nontrivial and the
   target characteristic differs from the source characteristic. Complex
   conjugation is character inversion. Taking real parts gives
   `‖J(χ,φ)‖² = #F`, then the nonnegative square root gives `‖J‖ = √#F`.
   For the two sums, order four proves `χ ≠ 1`, `η ≠ 1`, `χη = χ³ ≠ 1`,
   and `χ⁻¹η = χ ≠ 1`. Both twist/sign multipliers have norm one.
   The triangle inequality therefore gives `‖S_d‖ ≤ 2√#F`.
7. **All good primes and the actual coefficient** (`PointCount`). Odd field
   cardinality is `1` or `3 mod 4`; the two preceding routes cover both.
   At `p ∤ 2d`, the field is `ZMod p`, characteristic is not two, and `d ≠ 0`.
   The existing `LFunction_cd_apply_prime_eq_sub_card` identifies the coefficient
   with `p - #affine = -S_d`. The complex norm of the integer cast is its real
   absolute value. This gives the first principal theorem.
8. **Formal Euler coefficients** (`EulerBounds`). For real `a,p` satisfying
   Hasse, construct
   `α = (a + i√(4p-a²))/2`, `β = (a - i√(4p-a²))/2`.
   Prove `α+β=a`, `αβ=p`, and `‖α‖=‖β‖=√p`. The polynomial factors formally
   as `(1-αT)(1-βT)`. Each geometric formal series is proved to be its factor's
   inverse; uniqueness of the inverse and the coefficient-map ring homomorphism
   identify the actual integer `invOfUnit` coefficients with
   `∑(i+j=k) α^i β^j`. Thus their norm is at most `(k+1)(√p)^k`.
   There is no division by `α-β`, so repeated roots and Hasse endpoints are
   covered. `coeff_inv_euler_recurrence` also derives directly from the formal
   product identity the recurrence `c_(k+2) = a*c_(k+1) - p*c_k`.
9. **Global and analytic bridge** (`Convergence`). At bad primes the frozen
   Euler polynomial is `1`, so its inverse is `1`, including coefficient zero's
   value one. The frozen factorization formula and multiplicativity, together
   with `Nat.card_divisors`, yield `‖a_n‖ ≤ τ(n)√n`; `n=0` is handled separately.
   Define `sqrtSeq n = (√n : ℂ)`. An exact divisor-sum computation proves
   `(sqrtSeq ⍟ sqrtSeq) n = τ(n)√n`, also at zero. Mathlib's rpow comparison
   proves each square-root Dirichlet series summable when `Re(s)>3/2`;
   `LSeriesSummable.convolution` makes the majorant summable. Norm comparison
   of the actual Dirichlet terms, with the same denominator and the explicit
   zero-term convention, proves the second principal theorem.

No general elliptic-curve isogeny-degree library, Gaussian-integer evaluation,
new dependency, or port from an outside proof project was required. The scoped
inspection found point/reduction/L-function APIs and division-polynomial degrees,
not a supplying isogeny-degree Hasse theorem; this is not a claim of exhaustive
absence from every Lean project. The successful CM route makes further broad
search unnecessary.

## Direct supplier inventory (author reconstruction)

The following are the substantive API applications. Their exact pinned source
files were read; the full elaborated contribution statements are in the six
Lean files and their dependency bodies were checked by the scoped audit.

- `MulChar.exists_mulChar_orderOf F h hζ`:
  `h : n ∣ Fintype.card F - 1`, `hζ : IsPrimitiveRoot ζ n` imply
  `∃ χ : MulChar F R, orderOf χ = n`. Supplier:
  `Mathlib/NumberTheory/MulChar/Lemmas.lean:143-163`.
  The application's `n=4` and `ζ=Complex.I` are proved admissible;
  `MulChar.eq_iff` at lines 26-29 supplies the generator comparison.
- `quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F)`:
  the integer root count is `quadraticChar F a + 1`, including `a=0`.
  Supplier: `LegendreSymbol/QuadraticChar/Basic.lean:211-235`.
  `quadraticChar_ne_one`, `quadraticChar_isQuadratic`, and the nonzero-value
  dichotomy supply normalization and the norm-one multipliers.
- `jacobiSum_mul_jacobiSum_inv`:
  `ringChar F' ≠ ringChar F`, `χ ≠ 1`, `φ ≠ 1`, `χ*φ ≠ 1` imply
  `jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F`.
  Supplier: `JacobiSum/Basic.lean:204-236`.
  That theorem constructs its primitive additive character and uses
  `GaussSum.lean:188-201`; the application does not assume that construction.
  `MulChar.star_apply'` supplies conjugation/inversion.
- `FiniteField.isSquare_neg_one_iff` at
  `LegendreSymbol/QuadraticChar/Basic.lean:267-277` and
  `FiniteField.odd_card_of_char_ne_two` at `FieldTheory/Finite/Basic.lean:786-795`
  are direct suppliers in `PointCount.lean:54,57`. They supply exactly the
  nonsquare hypothesis in the `3 mod 4` branch and coverage of the other odd
  cardinality branch. These are not inferred only from the quartic-character API.
- `LFunction_cd_apply_prime_eq_sub_card` (frozen project file, lines 652-659):
  odd squarefree `d`, `[Fact p.Prime]`, and `p ∤ 2d` identify the actual coefficient
  with the affine trace. `natCard_point_shortCurve_zmod` at lines 633-648
  separately justifies the infinity/nonsingularity convention at good primes.
- `LFunction_cd_apply_prime` (frozen lines 603-612) is a **direct** supplier at
  `Convergence.lean:35`, rewriting the already bounded coefficient to the actual
  Euler-polynomial trace. `cdModel_eq_shortCurve` (lines 276-277) is separately
  a direct model-identification supplier at `Convergence.lean:37`.
- `LFunction_cd_apply_prime_pow` (lines 557-599) identifies every formal local
  inverse coefficient **within the frozen supplier chain**; it is not directly
  invoked by the new Convergence body. `LFunction_cd_apply` (lines 624-630) is
  directly invoked at `Convergence.lean:56` to supply every nonzero global
  coefficient via factorization. Bad-prime polynomials and
  `cdEulerPoly_coeff_zero` are frozen definitions/lemmas, not a changed source.
  The proved `eta_inv` and Euler recurrence are reviewed extras, not artificial
  dependencies of the final convergence proof.
- `PowerSeries.mul_invOfUnit φ u h`: requires `constantCoeff φ = ↑u` and gives
  `φ * invOfUnit φ u = 1`. Supplier: `PowerSeries/Inverse.lean:99-102`.
  Here `u=1` and the actual polynomial constant term is proved to be one.
  Coefficient multiplication, map, and shifted-X identities come from
  `PowerSeries/Basic.lean`; the inverse's geometric factorization and recurrence
  are new kernel-checked connecting arguments, not informal analytic appeals.
- `Nat.card_divisors (hn : n ≠ 0)` supplies the product of the exponents plus one;
  `Nat.prod_factorization_pow_eq_self hn` supplies the prime-power product.
  Supplier: `ArithmeticFunction/Misc.lean:222-226` and the pinned factorization API.
- `LSeriesSummable_of_le_const_mul_rpow hs h`: requires `x < s.re` and
  `∃ C, ∀ n ≠ 0, ‖f n‖ ≤ C*n^(x-1)`.
  Supplier: `LSeries/Basic.lean:346-368`.
  Application: `x=3/2`, `C=1`, `f=sqrtSeq`.
  `LSeriesSummable.convolution` at `LSeries/Convolution.lean:164-167`
  consumes the two proved summabilities. The subsequent norm comparison is
  performed on the same actual `LSeries.term`, not on a different Euler product.

This is the **author's declared inventory**, not a frozen independent
source-first reconstruction. The independently commissioned preliminary review
must supply and reconcile its own inventory; neither this list nor the axiom
report supplies the required independent coverage decision.

## Nine application obligations and coverage limits

1. **Source hypotheses:** each finite-field use has `Field`, `Fintype`, and the
   stated characteristic condition. Character order/nontriviality is proved;
   the coefficient bridge retains exactly oddness/squarefreeness and good-prime
   conditions. The statements and proofs above exhibit the required comparison.
2. **Constructed objects:** the field is the actual `ZMod p`, the coefficient
   is that of `shortCurve (-(d:ℚ)^2)`, and `η` is the actual quadratic character
   cast by a ring homomorphism. A general curve's unrelated character sum is
   not substituted for this equation.
3. **Domain/index coverage:** both odd-cardinality congruence classes, all
   square-map fibers, all `k≥0`, and all positive-integer factorizations are
   covered; `n=0` is separate. The finite-field theorem does not silently drop
   the zero fiber or a prime-power exponent.
4. **Transition maps:** root fibers are identified by subtype/sigma equivalence;
   negation and multiplication by nonzero `d` are explicit bijections;
   integer-to-complex coefficient maps are ring homomorphisms. The factors
   `η(-1)` and `η(d)` and the trace sign `-S_d` are explicit.
5. **Consumed-object identity:** the frozen affine-trace and prime-power
   identities concern the same `LFunction` used in the final summability type.
   The majorant's exact Dirichlet-convolution identity is proved separately.
6. **Coefficient/normalization conventions:** characters vanish at zero,
   Jacobi sums use `1-x`, and Euler polynomials use `1-aT+pT²`.
   The formal recurrence consequently has minus sign on the `p*c_k` term.
   Integral coefficients remain integral; complex casts only estimate norms.
7. **Local conditions:** `p ∤ 2d` excludes characteristic two and `d=0 mod p`.
   At excluded bad primes the original odd-squarefree additive factor is `1`;
   the proof does not add an infinity point to singular affine counts.
8. **Exceptional cases:** zero fibers, endpoints/repeated roots, the generic
   root lemma's `p=0`, bad primes, `k=0`, `n=0`, and the Dirichlet zero-term
   convention are all explicit. `Checks.lean` consumes the generic interfaces
   and checks endpoint/zero examples. It uses no finite numerical point-count
   oracle as evidence for the universal theorem.
9. **Downstream consumption:** the finite-field bound feeds the actual prime
   coefficient, then the formal local inverse, global factorization, and actual
   Dirichlet series. No manuscript, headline premise, functional equation,
   analytic continuation, or different convergence region is discharged by this
   contribution. Those are outside this frozen component's claimed proof.

The full new proof passages are covered by the author's explanation and the
scoped kernel checks. Source-first non-author coverage, reconciliation,
composition review, integration validation, and eligible Astra approval remain
required before any protocol acceptance or issue-resolution claim. This packet
does not classify a historical manuscript omission as new mathematics; historical
Hasse justifications/audits were not exhaustively reviewed.

## Reproduction and validation

On an already provisioned checkout with the committed pinned dependencies and
cache, compile only the assigned modules in dependency order:

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/Hasse
for m in Quartic CM PointCount EulerBounds Convergence Checks; do
  lake env lean -o ".lake/build/lib/lean/ZInQKernel/Contrib/Hasse/$m.olean" \
    "ZInQKernel/Contrib/Hasse/$m.lean"
done
```

The two frozen project imports (`ShortWeierstrass` and `LFunctionCd`) must already
have their own output files; in the isolated worktree they were compiled directly
without modifying their sources. No cache download, dependency setup/update,
whole-project build, or competing build was run. The shared package source was
read-only to this contribution and its tracked-source status remained clean.

**Result:** all six new modules compile. The five mathematical modules have no
warnings; `Checks.lean` has only three cosmetic sequencing-linter sites
(`convert ... <;> norm_num`). All **26 explicitly printed** named declaration
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The six generic/example checks compile as well.

The unchanged project `scripts/audit_kernel.lean` was also run on an explicit
six-module local spec. It replayed **36 declarations / 36 raw occurrences**,
reported no skipped unsafe/partial runtime declarations, and traversed actual
transitive dependency bodies, including opaque proofs, for forbidden axioms.
Replay of the 36 selected declarations against their external base is **not** a
fresh kernel replay of every imported project/Mathlib declaration. Only the same three
standard axioms occurred; `protocol_acceptance` is **false**.
The local spec's headline and expected-type name are intentionally the same
summability theorem: its role here is scoped replay/closure checking, **not**
comparison with the repository's frozen original headline contract.
`Checks.lean` supplies the explicit expected arithmetic interfaces instead.

Local audit output (working references, not tracked review records):

- `.lake/build/p4-audit/compile.log`, SHA-256
  `71e864a25f6853d914ee6b4293108a4f1e4ae8ef8b0700e77ca15346e1684e08`.
- `.lake/build/p4-audit/spec.json`, SHA-256
  `a335bd67b0ac9cc78bffdd154e8e7145d7ebf525c587ffa39e659dbd3ec9519f`.
- `.lake/build/p4-audit/audit.json`, SHA-256
  `a38e8319cc902478e44cf82957af3d5e06dcc2902d43b9412fef144a0b7b5823`.
- `.lake/build/p4-audit/replay.log`, SHA-256
  `a6655ce992d0161df46f782f0e4e7c900ead02abae758be38e4334d45bf8a78a`.
- Unchanged auditor source SHA-256
  `673af3d23f5433cb17145e9de8cac97b40a7d513281b7c2a726fb19ca089facc`.

The new sources are intentionally untracked/uncommitted at handoff. The normal
contract checker selects **tracked** Lean modules (`git ls-files`); thus its
full tracked-module CI and frozen-headline checks are **not** claimed by this
local explicit-module audit. Integration must track all six modules and run the
required full validation on the exact candidate revision. No protected approval
is manufactured by this local report. The history-register self-test was not
triggered: no register, manuscript, application contract, or bound historical
source was changed. This focused proof contribution is not a new-record release;
TeX/PDF/release synchronization duties remain with any later release integrator.

## Frozen proof/source hashes (SHA-256, UTF-8 file bytes)

New files under `ZInQKernel/Contrib/Hasse/`:

```text
6bc5fe16753ba4f540241393544ff71d0f5cb98c61d1249576b7fb8b740f64f4  Quartic.lean
2a599960dfb7df3e4a8f69e182ae9196245cea1256b3f2269c17fb95c9373c6b  CM.lean
8e6632c70687860f21e8b21b15ab0d95b0da84f066aac5a6b048829076c814e3  PointCount.lean
518cd9612e2cdd3f980c6b57cf2248dbc2cc51ac782401a7fc8ac350974e9276  EulerBounds.lean
05a60055c4fed49b24fc9bfe4884595e751709d775967382bbc3b97947113277  Convergence.lean
d3cdad587311b894260c25908e412599b83f813777cb856feb66cd7bdb8464f4  Checks.lean
```

Inspected frozen project suppliers:

```text
7a037a4b8e200c4c51d6a27b3cd0fe12b3056572c66ae0664bfae94f67fa84d0  ZInQKernel/RouteK/Rank/LFunctionCd.lean
0d9e3891b20b9933f47196c639ef179eb1ce41b9b418d4f72ee8cfce93f4e2e1  ZInQKernel/Model/Field/ShortWeierstrass.lean
```

Inspected substantive Mathlib supplier files, relative to its pinned repository:

```text
058559d94b75d829673cc4b386760ba0e22ba046707171c8f767bd5ffcf420cd  Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean
9aacc5a0d7febe63e7fb220d5a7874e2ab52dec1ed76f1788d0d6326b7b78be3  Mathlib/NumberTheory/MulChar/Lemmas.lean
71667f6cf840cfe1b158a1589784d5e37ae3bc75dda28add400e31822b539eda  Mathlib/NumberTheory/GaussSum.lean
61bcf68c53b9a96fa829e0b8d05dc5e10e70c98137f8971e433b150e0b3dc0ee  Mathlib/NumberTheory/JacobiSum/Basic.lean
9869ecfe087cbf814b6487bc040371ebe07e2141a9d3504954800f6c21e87b63  Mathlib/RingTheory/PowerSeries/Basic.lean
40f20a3821165b734e3ad5309e26b72bf072efc0190a86f7be92c04c9032b5cb  Mathlib/RingTheory/PowerSeries/Inverse.lean
5b2a88d66820172facfab13edf2c2d8eafca43b22e6a583ea93012549d1144ae  Mathlib/NumberTheory/ArithmeticFunction/Misc.lean
7d8a7aaf776feaa8d04fd5e5287438ebc0fa219ebc2b0f6cbc85088967d7607d  Mathlib/NumberTheory/LSeries/Basic.lean
18a5bc49d7b941cef5252c113cac1dd679f9247dd4c0018b6d3cebde53a5656a  Mathlib/NumberTheory/LSeries/Convolution.lean
```

## Provenance and review roles

Implementation: an AI-assisted Metamate contributor, November 12, 2026.
The exact private run identity is retained in the non-public verification record.
Actual served model identity is not established by trusted evidence here; it is
not asserted to be an eligible Astra run. The implementation independently
constructed the CM and formal analytic bridge using the pinned APIs.

Borrowed project argument: P1 `InertPrimes/PointCount.lean` at exact public commit
`87c7160f457df93e58c4b564dfa04668576447d8`, inspected through the shared Git
object store without editing that contribution. Its SHA-256 is
`7f3f6d1a102666deec24832f3c84503b425dd06193b5fba144cb62d3e921057f`.
The negation-pairing proof is adapted to complex coefficients; the root-fiber
count uses the same inspected sigma/subtype conversion. P1's note attributes its
finite-field proof to an agentcloud implementation subagent and its integration
to its parent. This P4 packet preserves that attribution and does not claim P1's
argument as new. No P2 contribution or its approval is assumed/imported.

The new Mathlib dependencies are only imports of the existing pinned package:
no outside Lean project, excerpt library, dependency revision, or setup tree was
ported. Mathlib's inspected sources carry **Apache-2.0** notices: quadratic
characters/Gauss sums by Michael Stoll (2022), multiplicative character and
Jacobi-sum work by Michael Stoll (2024); the Jacobi file acknowledges Alexander
Spahl's bachelor-thesis code and Ireland–Rosen Section 8.3. Power-series sources
retain their own printed contributor list. These formal supplier statements,
not an uninspected textbook citation, discharge the proof dependencies here.
Lean's and all existing package notices remain in place. P1's files have no new
license notice in the inspected version; this note records reuse within the
assigned project and does not supply or invent a license or relicense it.

A separate read-only preliminary source-first review was completed by
a non-author agent on the exact six proof hashes above. The private reviewer identity
is retained in the non-public verification record. It froze its own initial reconstruction before the author inventory,
then inspected primary supplier code and reconciled the direct uses. **No
substantive mathematical objection was found to either target.** The reviewer
separately elaborated complete target-type ascriptions with standard-only axiom
reports, but did not repeat the producer's compilation or replay. Its serving
model is unknown. It is **not** eligible Astra acceptance, official coverage
acceptance, formal acceptance, or issue closure.

The complete original report and its private identity/environment records are preserved
in the non-public verification packet. A reviewer-authored public-safe projection of the
mathematical coverage, suppliers, exceptions, findings and limits accompanies the PR.
It is explicitly a projection, not a byte-identical replacement of the private original.

### Retained preliminary findings and dispositions

- **P4-R1, direct-edge/coverage-record clarification:** the reviewer identified
  direct uses of `LFunction_cd_apply_prime`, the two finite-field branching
  suppliers, and `cdModel_eq_shortCurve` missing explicit locations in the
  selected author supplier list. Their mathematical matches were checked and
  found valid; **no source repair was requested**. The supplier list above now
  records each direct use/location, distinguishes the frozen transitive
  prime-power supplier, and identifies the recurrence/`eta_inv` as unused extras.
  The reviewer's granular passage coverage remains in the linked report. This
  incorporates the documentary reconciliation without inventing a graph
  acceptance or changing any theorem.
- **P4-R2, validation-scope limitation:** the self-named expected-type local
  spec is scoped replay/axiom evidence, not independent frozen-headline contract
  validation. The existing limitation is retained above and clarified to
  distinguish transitive axiom-body traversal from replay of all imported
  declarations. The reviewer found the disclosure accurate, not a proof flaw.
- **Remaining gates:** eligible byte-bound coverage/application/composition
  review; all-six tracked-module exact-candidate validation after integration;
  protected Astra approval and downstream integration. No mathematical
  counterexample or additional unproved arithmetic premise was identified in
  this bounded preliminary review. Neither this fact nor the absence of new
  objections closes the external gates.

The reviewer examined the pre-reconciliation note at SHA-256
`4aacecb197d3d18f04e003366571f1eb9adbd7594596d0afa0ab03d82403a449`.
The present note adds the identified direct-edge records and this disposition;
its revised bytes are not represented as separately approved. All six proof
source hashes are unchanged. No source-repair-triggered related-use sweep is
claimed; the reviewer performed a bounded check of all new proof passages,
the actual frozen supplier chain, and repeated target/route summaries. Historical
whole-manuscript Hasse justifications remain outside that review's scope.
