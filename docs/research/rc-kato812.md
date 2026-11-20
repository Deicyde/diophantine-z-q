# Appendix E: the support-sensitive Kato norm

**Result.** `finite_e1_812` derives finite (E.1) from the draft
`KatoProp812Print` and the same transfer laws as `AppEK1.finite_e1`. It covers
every admissible binary family at the fixed form level, with a retained
interface for that family's (K5) smoothers. An odd prime of the fixed level
`N = N₀ ℓ` may divide the family support `F` and the full odd part `d` of a
constituent's conductor. There is no correction to (E.1): such a prime is
already in the lower omitted support and is never unused. The Lean interface
gap is filled conditional on the draft. The reading desk checked the
published norm page; the draft still requires the object comparison and
is not a LEAF.

## The draft Proposition 8.12 input

Kato, *p-adic Hodge theory and values of zeta functions of modular forms*,
Astérisque 295 (2004), Proposition 8.12, p. 186: **read (AI reading of the
published PDF)**. The repository audit
[kato-carayol.md](../theorem-application-audit/evidence/kato-carayol.md),
§§2–3, records a reading of the original page, including the support
difference and the exponents. The following table lists the draft's conditions and the
intended specialization.

| Input or conclusion | Lean statement and locator status |
| --- | --- |
| Fixed form and lattice | Elliptic `E/ℚ`, positive `N = CST.newformLevel E`, and `CST.HasCuspFormAtLevel E N`, giving a form of level `N` with the coefficients of `E`. We specialize to rational weight two, trivial nebentypus, coefficient prime 2, and `r = r' = 1`, as in tex 6835–6843 and 6904–6909. Identification with the form and lattice of the print, and the inherited restrictions on those parameters: **UNVERIFIED**, 8.1–8.2, 8.9, 8.11–8.12, pp. 179–186. |
| Same retained classes | One fixed ξ ∈ SL₂(ℤ) (or a fixed integral combination of such ξ) and the same `c,d_s` at both levels. The parameter `zAt m S : es.H m` makes the omitted support `S` explicit; the fixed symbol and construction are implicit. The known gap is identifying `es.H m` with H¹(ℤ[ζ_m,1/2], V(f)(1)), and matching the corestrictions and classes, §§8.1.3, 8.9, 8.11, pp. 180, 185–186. |
| Smoothers | Kato's `d` is the manuscript's `d_s`. The bounds `1 < c` and `1 < d_s` are the draft's own conditions. It also requires `gcd(c d_s, 6) = 1` (check §8.1, p. 180) and `prime(c d_s) ∩ S' = ∅` (Prop. 8.12). |
| Cyclotomic indices | `m,m' > 0` and `m ∣ m'`. There is no coprimality requirement between either index and `N` in the draft. |
| Omitted supports | Finite sets of primes; Lean requires primality in `S'` and `S ⊆ S'`. Require `prime(2N) ∪ prime(m) ⊆ S` and `S ∪ prime(m') ⊆ S'`. Kato's (5.1.1), p. 152, puts `prime(mN)` and the coefficient prime in `S` for ξ ∈ SL₂(ℤ); for ξ = a(A), also include `prime(A)`. |
| Norm and local factor | Corestrict `zAt m' S'` to `m`, obtaining `zAt m S` multiplied by the product over `q ∈ S' ∖ S`. The audit gives arithmetic Frobenius and the specialized factor `1 − (a_q/q) σ_q⁻¹ + q⁻¹ σ_q⁻²`, written `eulerFactor (katoP E q) (invNat _ q) (frobUnit m q)` in Lean. The conjugation and exponent convention and its specialization: **UNVERIFIED** against 8.12 p. 186 here. |

The supports `S,S'` are separate from the Euler system's exclusions `Σ`.
For the old untwisted range use `oldSigma Sbad c ds = Sbad ∪ prime(c d_s)`,
with `Sbad` containing `prime(2N)`. For (K8) the variable is the twisted
index `m`. Its exclusions are `twistedSigma E d c ds`, the union of
`prime(2N)`, `prime(c d_s)`, and `prime(d)`. In `D = 2^a d` the full odd
part is `d = |h|`, including any odd prime in `N`. The exclusions on
`m,m'` do not forbid overlap of the untwisted index `D m` with `N`.
Attribution of the old exclusion range to Kato §13.1 and Example 13.3,
pp. 224–225, is **UNVERIFIED** here; (K8)'s use of `Σ` is verified in tex.

For `m' = m q` with `S_j = Sbad ∪ prime(j)`, the multiplier is 1 if
`q ∣ m` or `q ∈ Sbad`. Otherwise, provided the smoothers avoid the upper
support, it is the single good factor above. This is
`KatoZetaInterface812.norm_mul_prime`. In particular, at `q ∣ N` the
retained norm's multiplier is 1 even if `q ∤ m`: `q` already belongs to
`S_m`. No bad local Euler polynomial occurs in the norm product for this
range. The bad local factors used later in local control are separate.

### Page checklist for the reading desk

1. Use the checked 8.12 on p. 186 and cross-check 8.1.2–8.1.3, 8.2, 8.9 and
   8.11. Confirm which restrictions on `m,m',S,S'` are direct and which are
   inherited. In particular verify that `m ∣ m'` may have
   `gcd(m',N) > 1`, including odd overlap, and check for restrictions at
   coefficient prime 2. Record (5.1.1), p. 152: ξ ∈ SL₂(ℤ) puts `prime(mN)`
   and the coefficient prime in `S`; ξ = a(A) also requires `prime(A)` in `S`.
2. Match Kato's `d` to the manuscript's `d_s` and distinguish the draft's own
   conditions `1 < c`, `1 < d_s` from the print. Check coprimality with
   6 and `S'`, any conditions involving the symbol or auxiliary level, and
   whether the equal choice `c = d_s` is allowed. Check extension to a fixed
   integral combination of `SL₂(ℤ)` symbols by linearity. Check `r,r'`,
   the form and coefficient hypotheses, and the integral lattice on which
   the norm lands.
3. Check that the factor set is `S' ∖ S`, with no separate factor at a prime
   of `N` already in `S` or for repeated powers at unchanged support.
   Check arithmetic Frobenius, inverse powers `σ_q⁻¹` and `σ_q⁻²`, powers
   `q^(−r)` and `q^(k−1−2r)`, and conjugates of the Fourier coefficient
   and nebentypus. At `k = 2, r = 1` both nonconstant terms have denominator
   `q`. Check that any prime counted by the product is unramified in the
   lower cyclotomic field and is outside the coefficient prime and form level.
4. Verify that the printed corestriction and support parameters apply to the
   same retained class and lattice after the project’s fixed lattice
   comparison. Check the distinction between the omitted supports in (K4)
   and the excluded sets of §13.1/Example 13.3 and (K8). The Lean draft uses
   the existing abstract `EulerSystemData`; the known gap is identifying its
   modules with H¹(ℤ[ζ_m,1/2], V(f)(1)) and matching the maps and classes.

## Widened interface and finite product

`KatoZetaInterface812` has `es_812` in place of `es_euler` and ties
`es.z m` to `zAt m (Sbad ∪ m.primeFactors)`. Its `norm` takes arbitrary
positive divisible levels with upper level prime to the smoothers.
`isEulerSystem` restricts to any `Sig` containing `oldSigma Sbad c ds`:
smoother primes and newly introduced primes of `Sbad` cannot occur in that
old range, because the only allowed prime of `Sig` is 2, which is already
in the lower level. `toOld` carries across the same `es`, projections,
divisibility conclusion, periods and reciprocity. Increasing `Sig` only
narrows the domain required of the reciprocity field.

`norm_at_twisted_indices` applies the untwisted norm to `Dm,Dm'` on the
(K8) range. The factors are indexed by the primes new to `m'` relative to
`m`. `dyadicNorm_812` gives a unit multiplier for two positive dyadic
exponents at the same odd part, including cofinal descent from `d·2^(a+n)`
to `d·2^n`.

For (E.1) the corestriction is from `F·2^n` to `d·2^n`.
`normSupport_eq_unused` uses `AppEK1.addedPrimes_eq_unused` to cancel
the common dyadic support and `Even.unused_disjoint_fixed` to show that
putting the form level in the lower support removes no unused primes. The
latter result uses the local squareclass hypothesis: a fixed prime
ramifies in all constituents or in none. `finiteNorm_of_kato812` therefore
provides the old `FiniteNorm` for these families when the smoothers avoid
`F`. For (K5), `smoothing_avoids_support` proves this avoidance for every
admissible family. The family type uses the actual form level.

`finite_e1_812` applies `AppEK1.finite_e1` to this norm. With the full
quadratic constituent weight (`AppEK1.constituentWeight` for
`n ≥ max(a,2)`), the linear term in the weighted factor acquires `χ(q)` and
the quadratic term acquires `χ(q)^2 = 1`. Thus the finite product is over
`q ∣ F` with `q ∤ d`, with factor
`1 − a_q χ(q) q⁻¹ σ_q⁻¹ + q⁻¹ σ_q⁻²`, exactly (K9) and (E.1).
There is no division by a transfer degree. The algebraic equality holds for
any positive common exponent and the supplied weight and maps; the cofinal
bound is where the full weight of the primitive character is defined.

**Verification.** All three new Lean modules compiled with `lake env lean`.
The [axiom check](../../scratch/rc-kato812/Check.lean) covered every new
theorem; [its output](../../scratch/rc-kato812/axioms.txt) lists only
`propext`, `Classical.choice`, and `Quot.sound`. No existing Lean module
or statement was changed.

## Known issues

- No manuscript error found in the checked norm range. The gap on the base
  was in `es_euler`: it cannot take levels whose odd part meets its fixed
  `Sig`, including common odd primes of the form level.
- This is a draft on the existing abstract cohomology interface. It does
  not construct the retained classes or their cohomological comparison.
  The finite equality still takes the two transfer laws as in the original
  finite proof. `AppEK1.FixedKatoFiniteComparison` remains open.
- The smoothers label each witness. The old fixed reciprocity scalar `s`
  is carried through unchanged; constructing a family-indexed reciprocity
  scalar and proving the infinite comparison are outside this task.

## Manuscript check

| tex lines (`diophantine_zq.tex`) | Verdict |
| --- | --- |
| 6848–6860: fixed local types, odd family support | **OK** — `BinaryFamily` has the local squareclass condition at all primes of `2N`; the family support may meet `N`. |
| 6904–6929: (K4), choice of original lattice and symbol | **unverified** — the norm uses the indicated omitted support; identification of the abstract classes with the construction remains open. |
| 6931–6939: (K5) and avoidance of `F` | **OK** — coprimality with the family support is formalized for the stated smoothers. |
| 6990–6993: `D = 2^a d`, `Σ = prime(2N d c d_s)` | **OK** — `twistedSigma` applies to the variable `m`; `d` keeps the full odd part. |
| 6994–7006: (K8), untwisted norm at `Dm,Dm'` | **gap filled** — the widened norm allows primes of `N` in `D`, conditional on the draft print; passage to the actual cohomology classes is separate. |
| 7012–7024: (K9), repeated prime powers | **OK** — the index set excludes primes already in the lower support; the audited factor normalization is used unchanged in the draft. |
| 7025–7029: repeated-two descent | **gap filled** — `dyadicNorm_812` allows the common odd conductor primes and introduces no scalar `2^a`. |
| 7034–7071: (K10), integral coefficient map | **OK** — the earlier finite algebra uses the integral weighted map; identifying its transfer with the map on actual retained classes is still a separate comparison. |
| 7074–7084: transition maps | **unverified** — the empty support difference gives the finite norm; the completed-cochain limit is outside this task. |
| 7086–7096: L7089 and (E.1) | **gap filled** — `finite_e1_812` gets exactly the manuscript product from the widened norm and the retained weighted transfer laws. The comparison with the actual classes remains open. |
| 7098–7106: (E.2), full quadratic weight | **OK** — the existing coefficient proof retains both the odd and dyadic parts. |
| 7312–7315: every unused prime is good | **OK** — `Even.unused_disjoint_fixed` derives this from the squareclasses, including for a family ramified at an odd prime of `N`. |
