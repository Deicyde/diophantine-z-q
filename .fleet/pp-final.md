# pp-final report: closing CAT (plan steps 3.4–3.5, 4 and 5)

CAT is now a theorem. The main theorem is

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactEstimate) (hPC : PoleCompleteness) (h22 : FixedPrimePattern) : FrozenTarget
```

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`, for this theorem
and for `_of_nodeCheck`, `catalogueBound8`, `effective_dirichlet` and
`norm_LFunction_one_ge_of_sq_eq_one`. `python3 scripts/check_target.py` reports
"FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean". The full
`lake build ZInQKernel` passes. There is no `sorry`, no `native_decide` and no
finite-computation hypothesis.

New code is in `ZInQKernel/Progressions/Final/`, with root `ZInQKernel/Progressions/Final.lean`,
imported from `ZInQKernel.lean`. The analytic modules (`RealLimit`, `RealBound`, `Effective`)
import Mathlib and earlier `Progressions` modules only. `Instance` also imports
`Hypotheses/PrimePattern` and `Syntax/Constants/PrimorialLiteral` (Mathlib-only).

## Leaves

| article path | Lean name | status |
| --- | --- | --- |
| progressions/real-characters/real-lower-bound.md | `ZInQ.Progressions.norm_LFunction_one_ge_of_sq_eq_one` (RealBound) | proved |
| progressions/counting/uniform-twisted-bound.md | `ZInQ.Progressions.norm_twistedSum_le_two_pow_mul` (Effective) | proved (renamed, see below) |
| progressions/effective-dirichlet.md | `ZInQ.Progressions.effective_dirichlet` (Effective) | proved |
| progressions/catalogue-instance.md | `ZInQ.catalogueBound8` (Instance) | proved |
| task step 2 (all characters) | `ZInQ.Progressions.min_le_norm_LFunction_one`, `effectiveLBound_le_norm_LFunction_one` (Effective) | proved |
| task step 5 (remove hCAT) | `Assembly.Pstar_spec_of`, `Assembly.Pstar_spec`, `Assembly.assembly`, the three main theorems in `Main.lean` | done |

## Statements as delivered

- `norm_LFunction_one_ge_of_sq_eq_one [NeZero q] (hχ2 : χ ^ 2 = 1) (hχ : χ ≠ 1) :
  1 / (40 * (q * √q)) ≤ ‖LFunction χ 1‖`. The article's `q^{3/2}` is written `q * √q`, which the
  implementation note allows. The sharper form `log((1+√5)/2) / (18 (q √q)) ≤ ‖L(1,χ)‖` is
  `log_golden_div_le_norm_LFunction_one`.
- `min_le_norm_LFunction_one (hχ : χ ≠ 1) :
  min (1/(256 (log q + 3)^7)) (1/(40 (q √q))) ≤ ‖L(1,χ)‖`, for every `q ≥ 1`. No threshold
  on `q` is needed.
- `norm_twistedSum_le_two_pow_mul (hχ : χ ≠ 1) (hx : 1 ≤ x) : ‖twistedSum χ x‖ ≤ 2^24 q^5`.
- `effective_dirichlet {q : ℕ} (hq : 2 ^ 16 ≤ q) {a : ℕ} (ha : a.Coprime q) :
  22 ≤ #{p ∈ Ioo (q ^ 2) (2 ^ q ^ 8) | p.Prime ∧ p % q = a % q}`. So `q₀ = 2^16`. The
  congruence is spelled `p % q = a % q`, as in the implementation note; this is `Nat.ModEq`
  unfolded.
- `catalogueBound8 : CatalogueBound8`. The modulus is never evaluated. Only `2^16 ≤ W` is used,
  from `13# = 30030` (kernel `decide` on `primorialB 13`) and `primorial_mono`. The instance
  goes through `catalogueBound8_of_two_pow_le`, which is stated for a variable `W ≥ 2^16`, so
  the kernel never unfolds `catalogueModulus`.

## Statement corrections and differences from the blueprint

1. **Name clash (uniform-twisted-bound).** The implementation note proposes
   `norm_twistedSum_le`, but pp-mertens already uses that name in
   `Mertens/Unconditional.lean`, for `‖S_χ(x)‖ ≤ (M² + 6q)/‖L(1,χ)‖`. The leaf is
   `norm_twistedSum_le_two_pow_mul`. It is stated for `twistedSum χ x`, which is the article's
   sum `Σ_{n≤x} χ(n)Λ(n)/n`. The proof uses `M² + 6q ≤ 15q`, not the article's `M² + 12q`,
   because pp-mertens proved the twisted-sum bound with `6q`.
2. **Catalogue instance namespace.** The implementation note proposes
   `ZInQ.Progressions.catalogueBound8`. The task asked for `ZInQ.catalogueBound8`, so the
   theorem is in namespace `ZInQ`.
3. **Route of `effective_dirichlet`.** The article goes through the uniform bound `2^24 q^5` and
   a twenty-two-primes lemma with general `y ≤ x`. That lemma is not in Lean in that form. What
   exists is pp-mertens's `twentytwo_primes_of_LFunction_lower_bound`, with `y = q^8` and
   `x = q^8·exp(5qB)`. The proof uses it with `c_q = effectiveLBound q =
   1/(2^14 (log q + 3)^7 q²)`, which is at most both character bounds, and then shows
   `q^8 exp(5q(M² + 6q)/c_q) < 2^(q^8)` for `q ≥ 2^16`. Write `t = q^{1/8} ≥ 4`. Then
   `log q ≤ 8t` (Mathlib's `Real.log_le_rpow_div`), `M ≤ 9t`, and the exponent is at most
   `2^43 t^39 < t^64/2 < q^8 log 2`. The primes come out in `(q^8, 2^(q^8))`, which is
   contained in `(q², 2^(q^8))`. The theorem statement is the article's.
4. **The residue identity** (`dedekindZeta_residue_eq_LFunction_one_mul_prod`) holds for any
   quadratic number field `K` with an integral `α`, `α² = d`, `d` not a square, `χ ≠ 1`, and
   the hypotheses of pp-idealcount's zeta factorization:
   `res_K = L(1,χ) · ∏_{p ∣ 2q} (1 − χ(p)/p)(1 − ε_p/p)⁻¹`. The article writes the reciprocal
   form `L(1,χ) = res_K ∏ (1 − ε_p/p)/(1 − χ(p)/p)`, which needs `χ(p) ≠ p`. The product form
   needs no such side condition.
5. Small arithmetic difference: the article bounds `log((1+√5)/2) > 0.48`. The proof uses
   `≥ 9/20`, which is still enough for `1/40`: `2 log φ = log 2 + log(φ²/2)`, with `φ² ≥ 13/5`
   and `log y ≥ 1 − 1/y`.

## Lemmas added beyond the leaves (namespace `ZInQ.Progressions` unless noted)

- RealLimit: `tendsto_sub_one_mul_riemannZeta_ofReal_nhdsGT`, `tendsto_LFunction_ofReal_nhdsGT`,
  `tendsto_localFactor_ofReal`, `dedekindZeta_residue_eq_LFunction_one_mul_prod`.
- RealBound: `norm_localFactor_one_le` (`‖(1 − a/p)(1 − b/p)⁻¹‖ ≤ (p+1)/(p−1)`),
  `prod_primeFactors_two_mul_le` (`∏_{p∣2q} (p+1)/(p−1) ≤ 3q`), `nine_twentieths_le_log_golden`,
  `log_golden_div_le_norm_LFunction_one`.
- Effective: `log_add_three_le_three_mul_sqrt`, `effectiveLBound` (def), `effectiveLBound_pos`,
  `effectiveLBound_le_norm_LFunction_one`, `effective_exponent_lt`, `effective_upper_lt`.
- Instance (namespace `ZInQ`): `two_pow_sixteen_le_catalogueModulus`,
  `catalogueBound8_of_two_pow_le`.

## Edits outside the directory

- `Assembly/Top/Assembly.lean`: imports `ZInQKernel.Progressions.Final.Instance`. `hCAT` is
  removed from `Pstar_spec_of`, `Pstar_spec` and `assembly`, and `catalogueBound8` is supplied
  to `Size.Pstar_target_bounds`. The size lemmas keep their `hCAT` argument.
- `Main.lean`: `hCAT` is removed from `_of_addMulBound`, `_of_nodeCheck` and the main theorem.
  The corollary `exists_bounded_integer_polynomial_defining_integers_of_catalogueBound` is
  deleted, and the module docstring is updated. `CatalogueBound`, `CatalogueBound8` and
  `catalogueBound8_of_catalogueBound` are unchanged in `Hypotheses/PrimePattern.lean`.
- `ZInQKernel.lean`: one line, `import ZInQKernel.Progressions.Final`.

## Build times

Each module was compiled alone with `lake env lean`, with Mathlib already built. Most of the
time is spent importing Mathlib; peak memory is about 7 GB:

| module | time |
| --- | --- |
| Final/RealLimit | 5.3 s |
| Final/RealBound | 8.7 s |
| Final/Effective | 8.6 s |
| Final/Instance | 9.8 s |

An incremental `lake build ZInQKernel` after the Assembly/Main edits took about 20 s.

## Problems

None open.

## Suggestions for the next agent / the lead

- **Merging with pattern-2slope.** In `Main.lean` and `Assembly.lean` the edits only delete
  `(hCAT : CatalogueBound8)` binders and their uses, and add one import line to
  `Assembly.lean`. Resolve conflicts by keeping pattern-2slope's 22P signature changes and
  dropping `hCAT`.
- **Documentation outside the blueprint.** `KERNEL_PLAN.md` (the theorem display and the status
  paragraph), `README.md` and `docs/effective-dirichlet-plan.md` still describe four
  hypotheses. They should now say three (H, PC, 22P), with CAT replaced by `catalogueBound8`.
  I did not edit them, to avoid conflicts with parallel tasks.
- **Blueprint.** Set `lean:` fields:
  - real-lower-bound: `ZInQ.Progressions.norm_LFunction_one_ge_of_sq_eq_one`;
  - uniform-twisted-bound: `ZInQ.Progressions.norm_twistedSum_le_two_pow_mul`;
  - effective-dirichlet: `ZInQ.Progressions.effective_dirichlet`;
  - catalogue-instance: `ZInQ.catalogueBound8`;
  - main-theorem and assembly-lemma: drop CAT from the hypothesis lists.
- The size chain could be tightened later, since CAT₈'s cutoff could drop: the proof gives
  primes below `exp(2^43 q^{39/8})`. It is not needed.
