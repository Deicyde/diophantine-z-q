# t21-proof: `TYZThm21At31` proved outright

**Result (VERIFIED, compiled).** The top hypothesis `hT21 : H29Split.TYZThm21At31` of `ZInQ.OneProof.frozenTarget`
(TYZ Theorem 2.1 at `n = 3`, `(d₁, d₂) = (3, 1)`) is a theorem:

```lean
theorem ZInQ.Contrib.T21Proof.tyzThm21At31 : ZInQ.Contrib.TYZDecomp.H29Split.TYZThm21At31
```

in `ZInQKernel/Contrib/OneProof/TYZThm21At31.lean`, with helper modules in `ZInQKernel/Contrib/OneProof/T21Proof/`.
The statement is unchanged and the proof adds no new leaf. `#discharges` (`scratch/t21-proof/Discharges.lean`, full output in
`scratch/t21-proof/Discharges-output.txt`):

```
DISCHARGES [hT21] by ZInQ.Contrib.T21Proof.tyzThm21At31
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
```

Effect on the single proof: one top hypothesis fewer, no new leaf. Every finite computation is checked by the kernel
with `decide +kernel`. There is no `native_decide`, `sorry`, `axiom`, `#eval` or new syntax in the new files (checked by grep).

## Route

`TYZThm21At31` says: for every admissible `τ`, every test vector `f_3` and every sign choice `ℓ` of `𝓛`,
`Σ_{t ∈ Cl_3} f_3(t) = ε · (#μ_K / 2) · ℓ(3) ℓ(1)` with `ε = ±1`, `K = ℚ(√−3)`. The proof establishes each factor
directly, without reading Theorem 2.1:

1. **The class sum is `f_3(1)`.** `Cl(𝓞_K) = 1` (`TYZLcal.pid_three`), so the sum has one term, and
   `tv_eq_of_toClassGroup_eq` moves `clLift 3 1` to `1` (`classSum_eq`).
2. **`#μ_K = 6`.** Mathlib's `IsCyclotomicExtension.Rat.torsionOrder_eq` (`torsionOrder_three`), so `w_K = 3`.
3. **`f_3(1) = ±3` for every admissible `τ` and test vector `f_3`** (`T21Proof.testVector_one`,
   `T21Proof/BrandtValue.lean`). This is a Brandt computation at `n = 3`. Let `gT` be the function that is `−3` on the
   double coset `B^×H` of `1` (`H = ⟨U_3, ℚ̂^×⟩`) and `1` off it. The three invariances of `InPiZ` hold by construction.
   Among TYZ's 8 representatives, `gT` is `−3` exactly at `t = 0` and at the partner `t*(s)`:
   * membership: an explicit element of `R̂_3^×` (`partner_mem`, `Brandt2.lean`);
   * non-membership of the other six classes: a local invariant (`twoRep_ne`, `Brandt.lean`). At every odd `p` the
     element lies in `ℚ_p^× O_{B,p}^×`. A global content argument (`GlobalStep.lean`) writes it as `q·n` with
     `nrd n = 2^k`. A 2-adic mod-4 obstruction then rules it out, checked over the 24 Hurwitz units and 8 sign
     patterns by `decide +kernel` (`Finite.lean`).
   So both orthogonality sums vanish and `gT ∈ π_ℤ^{U_3}`. A test vector generates `π_ℤ^{U_3}`, so `gT = c·f_3`.
   Since `gT` takes the value `1`, `c = ±1`, hence `f_3(1) = ±3`. Cross-check (python, `classes.py`): for each of the 8 `τ`
   the classes in `B^×H` are exactly `{0, t*}`, which matches `scratch/h29-fix/brandt.py`.
4. **`ℓ(1), ℓ(3) = ±1`.** `ℓ(m) ∈ ℤ` with `ℓ(m)² = 𝓛(m)²` (`IsLcalSign`), and `0 < ‖𝓛(m)²‖ < 4` at `m = 1, 3`
   (`lcalSq_one_bounds`, `lcalSq_three_bounds`) forces `ℓ(m)² = 1` (`int_eq_pm_one_of_sq`). The bounds come from
   rigorous enclosures of the two L-values:
   * `0.09 ≤ Re L(C_1, 1)`, `‖L(C_1, 1)‖ ≤ 1.26` (`lValOne_one_bounds`), and `𝓛(1)² = 4L(C_1,1)/Ω` with `Ω ≥ 2`
     (`omegaInt_ge_two`);
   * `0.14 ≤ Re L(C_3, 1)`, `‖L(C_3, 1)‖ ≤ 2.9` (`lValOne_three_bounds`), and `𝓛(3)² = √3 L(C_3,1)/Ω`
     (`2^{2·1−3} · (2/√3)Ω = Ω/√3`, with `√3 < 1.75`).

Then `f_3(1) · ℓ(3)ℓ(1) = ±3 = ±w_K ℓ(3)ℓ(1)`, and the sign is chosen case by case.

### The L-value enclosures (`T21Proof/LKernel.lean`, `LValues.lean`, `LBounds.lean`, `LUnit.lean`)

* Hecke's continuation (`Contrib/HeckeFE`, `Contrib/HeckeAll`, `Contrib/TYZChain/Lcal.lean`) gives
  `L(C_d, 1) = Σ_{j ∈ (ℤ/M)²} c_j (π/M) Λ_{j/M}(1)` with `M = 4d`. For `d = 1` this is `lValOne_one_eq` (existing);
  for `d = 3` it is the new `lValOne_three_eq`, via `isLContinuation_twChar`. The coefficients are
  `c_j = (cr_j + ci_j i)/4` with integer tables (`cU_eq`, `twChar_three_eq`, the latter using `jacobiSym 3 N = jac12 N`).
* `‖Λ_{a,b}(1) − mainL a b‖ ≤ (15.2 e^{−π} + 0.2487)/π` for `0 ≤ a, b < 1` (`norm_gaussLambda_sub_mainL_le`).
  Here `mainL` is the integral over `(1, ∞)` of the four nearest lattice terms. The rest of the theta kernel
  (geometric majorants, `e^{−3π} ≤ 1/8000`) and the dual kernel (existing `abs_sinKernel_le`, `abs_cosKernel_le`) give the error.
* The main sum's real and imaginary parts are `Σ q·E^N` with `q ∈ ℚ` and `E = e^{−π/M²}` (`re_term`, `im_term`).
  Rational enclosures `l ≤ E ≤ u` come from `1 − x ≤ e^{−x} ≤ 1/(1+x)` and `3.141592 < π < 3.141593` (`exp_bounds`).
  Termwise `loQ`/`hiQ` bounds are summed and checked by `decide +kernel`; the ten certificates check in under 10 s:

  | curve | M | l, u | Re S | Im S | W = Σ(\|cr\|+\|ci\|) | error ≤ 1.0087 W/(4M) |
  | --- | --- | --- | --- | --- | --- | --- |
  | C_1 | 4 | 0.8036, 0.836 | [0.60, 0.71] | [−0.04, 0.04] | 8 | 0.505 |
  | C_3 | 12 | 0.9781, 0.9787 | [1.49, 1.53] | [−0.02, 0.02] | 64 | 1.345 |

  Numerical cross-check (python, `scratch/t21-proof/lsplit.py`, `cert.py`; not a proof): `L(C_1,1) ≈ 0.65551`,
  `L(C_3,1) ≈ 1.51385`, i.e. `Ω/4` and `Ω/√3` with `Ω ≈ 2.62206`, so `𝓛(1)² = 𝓛(3)² = 1`.

## Leaves

No new leaf, so there is nothing to rate as printed form. The proof uses only Mathlib and project theorems that are
already proved, all with standard axioms (`#print axioms`): Hecke's continuation for `C_1`, `C_3`, the Deuring point count
for `C_1`, `pid_three`, `omegaInt_ge_two`, and the test-vector material of `TYZLemma29Mod2.lean`.

## Fold

`scripts/one_proof/autofold.py scratch/t21-proof/autofold.json --dry-run` refuses with
`not a field of the current bundles: ['hT21']`. `hT21` is a top-level argument of `frozenTarget`, and autofold folds
bundle fields only. The integrator therefore folds by hand: import `ZInQKernel.Contrib.OneProof.TYZThm21At31` in `Main.lean`,
drop the binder `(hT21 : H29Split.TYZThm21At31)`, and pass `ZInQ.Contrib.T21Proof.tyzThm21At31` where `hT21`
was used, then remove the `hT21` rows from kinds.tsv/claims.tsv and regenerate OPEN.md. This fold is checked in
`scratch/t21-proof/FoldCheck.lean`: `frozenTarget_noT21` (the frozenTarget signature without `hT21`) compiles,
with axioms `[propext, Classical.choice, Quot.sound]`.

## Files

* `ZInQKernel/Contrib/OneProof/TYZThm21At31.lean`: the theorem, `lcalSq_one_bounds`, `lcalSq_three_bounds`.
* `ZInQKernel/Contrib/OneProof/T21Proof/`:
  * Brandt side: `Hurwitz`, `Local`, `LocalPred`, `GlobalStep`, `Finite`, `BaseChange`, `Tau`, `K2`, `Brandt`,
    `Brandt2`, `BrandtValue`.
  * L-value side: `LKernel`, `LValues`, `LBounds`, `LUnit`.
* `scratch/t21-proof/`: `log.md` (results log), `Discharges.lean` and its output, `FoldCheck.lean`,
  `autofold.json`, the python checks (`classes.py`, `hurpoly.py`, `gen_units.py`, `lsplit.py`, `mainsum.py`,
  `cert.py`), `T21Reduce.lean` (the first reduction, superseded), `DecideTest.lean`, `JacTest.lean`, `AxBrandt.lean`.

Remark: Theorem 2.1 at `(3, 1)` is now a computation, not a citation. TYZ's statement at this instance is
confirmed independently of their proof.
