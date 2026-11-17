# lcal-one: `TYZLcalOne` proved outright (`L(y² = x³ − x, 1) = ¼ ∫₁^∞ dx/√(x³ − x)`); TYZ hypotheses 2 → 1

Task lcal-one, 2026-11-16. Branch `wip/lcal-one`: base `wip/leaf-fold33b` `c0f3d085`, with `origin/main` merged (no
change) and `origin/wip/tyz-genus` merged (clean). Results log: `scratch/lcal-one/log.md`.
Marks: **VERIFIED** means compiled, computed, or read in a named file. **STANDARD** means published, with an exact reference.
**SPECULATIVE** and **UNVERIFIED** (from memory) are marked where used. The TYZ source `~/tyz-src/Period7.tex` is not on this host (VERIFIED:
`ls` fails), so the TYZ line number L1082 is quoted from earlier notes (tyz-decomp, tyz-genus) and was not re-read here.
Model work, no human review.

## 0. Result

**`ZInQ.Contrib.TYZDecomp.TYZLcalOne` (`lcalSq 1 = 1`, TYZ's `𝓛(1) = 1`) is a Lean theorem.** It needs no new
hypothesis and only the standard axioms (VERIFIED, compiled):

```lean
-- ZInQKernel/Contrib/OneProof/TYZLcalOne.lean
theorem ZInQ.Contrib.LcalOne.tyzLcalOne_proof : ZInQ.Contrib.TYZDecomp.TYZLcalOne
theorem ZInQ.Contrib.LcalOne.lValOne_one :
    ZInQ.Contrib.TYZDecomp.lValOne 1 = (ZInQ.Contrib.TYZDecomp.omegaInt : ℂ) / 4
theorem ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only
    (h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC) : ZInQ.Contrib.TYZDecomp.TYZThm11Integral
```

`#discharges` output (`scratch/lcal-one/Discharges.lean`; full output in `Discharges-output.txt`; 35 open
hypotheses, 10170 theorems checked):

```
DISCHARGES [h11] by ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only
  still assumes: [ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [hL29] by ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C
  still assumes: [ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC]
  axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.LcalOne.tyzLcalOne_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Effect on the single proof.** The two TYZ hypotheses of `frozenTarget`, `h11 : TYZThm11Integral` and
`hL29 : H29Split.TYZLemma29PrintedNe3`, are replaced by tyz-genus's one printed leaf
`h21C : TYZGenusFold.TYZThm21PairsC` (TYZ Theorem 2.1, complex sign choices). That is variant B of tyz-genus with its
second leaf `TYZLcalOne` now proved. Open hypotheses go from 35 to 34 (**net −1**); the TYZ hypotheses go from 2 to 1. The fold is manual:
`h11` and `hL29` are top-level binders of `frozenTarget`, and autofold folds bundle fields only. It is compiled in
`scratch/lcal-one/FoldCheck.lean`. `frozenTarget_lcalOne` is the new body of `frozenTarget`, written out in full.
`frozenTarget_lcalOne'` is the same statement proved through the current `frozenTarget`. Both depend on
`[propext, Classical.choice, Quot.sound]` (`FoldCheck-output.txt`, VERIFIED).

Variant C of tyz-genus (`TYZThm21PairsC1`, pending a reading of TYZ Theorem 2.1 at `n = 1`) is no longer needed:
this fold reaches the same count with a leaf that has no pending reading.

## 1. The statement and its normalizations (VERIFIED, read)

* `lcalSq m = lValOne m / (2^{2k(m)−3} · omegaTYZ m)` with `omegaTYZ m = (2/√m)·omegaInt` and
  `omegaInt = ∫_{(1,∞)} dx/√(x³ − x)` (`Leaves.lean:144–244`). At `m = 1`: `k = 0`, so `lcalSq 1 = 4 L(C₁,1)/omegaInt`
  (tree lemma `TYZLcal.lcalSq_one`).
* `lValOne 1` is the value at `1` of the entire continuation of Mathlib's `LSeries` of `y² = x³ − x`. The
  continuation is unique (`lValOne_eq`), and `omegaInt > 0` (`omegaInt_pos`). So the statement is not vacuous: it
  is the exact evaluation `L(C₁, 1) = Ω/4`, i.e. `L(E, 1)/Ω_E = 1/8` for 32a2 (real period `Ω_E = 2Ω`).
* The tree's form of the continuation (`TYZLcal.lValOne_one_eq`) is
  `L(C₁, 1) = Σ_{j ∈ (ℤ/4)²} cU(j)·¼·π·Λ_{j/4}(1)`. Here `Λ_{a,b}(1) = mellin Θ_{a,b} 1 = ∫₀^∞ Θ_{a,b}`, and
  `Θ_{a,b}(x) = Σ_{p ∈ ℤ²} ((p₁+a) + i(p₂+b)) e^{−π|p+(a,b)|²x}` (`HeckeFE.hasSum_gaussTheta`).

## 2. The proof (all VERIFIED, compiled)

### Part A: `L(C₁, 1) = 2π ∫₀^∞ f(it) dt`, `f = η(4τ)²η(8τ)²` (`lValOne_one_eq_integral`)

* `latT x p = unitOf(p mod 4) · p · e^{−π N(p) x/16}` on `ℤ[i]` is absolutely summable (`summable_latT`,
  through `summable_norm_iff` on `Θ_{0,0}`).
* **Block decomposition** (`tsum_latT_block`): `Σ_p latT x p = Σ_j 4·unitOf(j)·Θ_{j/4}(x)`. It uses HeckeFE's
  `blockEquiv`, `gz_block` and `gq_block`, as in `twistedL_eq`.
* **Grouping by the norm** (`tsum_latT_eq`): `Σ_p latT x p = 4·Σ_n a_n e^{−πnx/16}` with
  `a_n = heckeCoeff 1 n`. This is the fibrewise sum over `normFiber n`, as in `LSeries_eq_twistedL`. By
  gz-theta's `etaThetaIdentity` the sum is `4 f(ix/32)`.
* Hence `Σ_j cU(j)Θ_{j/4}(x) = ¼ f(ix/32)` (`sum_cU_gaussTheta`). Integrate this over `(0,∞)`; each `Θ_{j/4}` is
  integrable there by `mellinConvergent_gaussTheta` at `s = 1`. Then rescale `x = 32t`.

### Part B: `∫₀^∞ f(it) dt = Ω/(8π)` (`integral_Fr`)

* **Realness and signs.** `Xr, Yr, Fr` are the values of x0-32's `xC, yC, fC` at `it`. They are real because
  `xC(−z̄) = conj xC(z)` (x0-32's `xC_neg_conj`, and likewise for `yC` and `fC`). We have `Fr > 0` and `Yr < 0`,
  since the eta values are real and nonzero (`etaD_ne_zero`). tyz-cm's `etaModelEquation` gives
  `Yr² = Xr³ + 4Xr`, hence `Xr > 0`.
* **Derivative** (`hasDerivAt_Xr`): `Xr' = −4π·Fr·Yr > 0`. This is `X0.EtaModelDifferential`
  (`x' = 4πi f y`, proved by gz-weil from Jacobi's derivative formula) restricted to the imaginary axis
  (`HasDerivAt.real_of_complex`). So `Xr` is strictly increasing.
* **The cusp `0`** (`tendsto_Xr_zero`): `Xr(t) → 2` as `t → 0⁺`. Here `x = 2θ₃(16τ)/θ₂(16τ)`
  (`Shimura.xC_theta`, `thetaTwo_sixteen`). The squared `S`-laws (`thetaThree_S_sq`, `thetaTwo_S_sq`) give
  `x(it)² = 4θ₃(τ')²/θ₄(τ')²` with `τ' = i/(16t)`, and `θ₃, θ₄ → 1` at `i∞` (JacobiLambda's bounds).
  So the cusp `0` maps to `(2, −4)`, a point of order 4 on 32a1.
* **The cusp `∞`** (`tendsto_Xr_atTop`): `1/x(it) = e^{−4πt}T(16it)/(2θ₃(16it)) → 0`, with `T → 2`.
* `Xr > 2` (`two_lt_Xr`: strictly increasing with limit `2` at `0⁺`).
* **Substitution** `u = x/4 + 1/x`. This is the 2-isogeny `y² = x³ + 4x → Y² = X³ − 16X`, `X = x + 4/x`, followed
  by `X = 4u`, which lands on `y² = u³ − u`. The facts used: `u > 1` (`one_lt_U`) and
  `√(u³ − u) = (x² − 4)/(8x²)·(−y)` (`sqrt_U`). Hence `u'/√(u³ − u) = 8π f(it)`.
* **FTC on `(0, ∞)`.** Put `K(u) = (Ω − ∫₁^u dv/√(v³ − v))/4` and `G = K ∘ u` (with `G(0) = K(1) = Ω/4`). Then
  `G' = −2π·Fr` (`hasDerivAt_G`), `G` is continuous at `0⁺` (`continuousWithinAt_G`) and `G → 0` at `∞`
  (`tendsto_G_atTop`, via `intervalIntegral_tendsto_integral_Ioi`). Mathlib's
  `integral_Ioi_of_hasDerivAt_of_nonpos` gives `∫₀^∞ −2π·Fr = 0 − Ω/4`.

So `L(C₁, 1) = 2π·Ω/(8π) = Ω/4` (`lValOne_one`), and `lcalSq 1 = (Ω/4)/(Ω/4) = 1` (`tyzLcalOne_proof`).
Numerical consistency (t21-proof's `lsplit.py`, not re-run): `L(C₁,1) ≈ 0.65551`, `Ω ≈ 2.62206`.

The classical argument in the task statement (`L(f,1) = −2πi∫₀^{i∞} f`, the image of the cusp `0` a torsion point,
the elliptic logarithm a rational multiple of a period) is what the Lean proof does. No enclosure is needed: the
integral is evaluated exactly along the real locus. The elliptic logarithm of `(2, −4)` on 32a1 becomes, after the
isogeny, the full real half-period of `C₁` from `u = 1` to `u = ∞`.

### What it uses (all theorems already in the tree, standard axioms)

`TYZLcal.lValOne_one_eq`, `TYZLcal.lcalSq_one`, `TYZLcal.cU` (tyz-lcal); `HeckeFE.hasSum_gaussTheta`, `blockEquiv`,
`gz_block`, `gq_block`, `normFiber`, `mellinConvergent_gaussTheta`, `unitOf`, `heckeCoeff`; `GZTheta.etaThetaIdentity`
(gz-theta); `X0.xC/yC/fC_neg_conj`, `X0.etaD_neg_conj`, `X0.etaD_ne_zero` (x0-32); `Shimura.etaModelEquation`,
`Shimura.xC_theta` (tyz-cm); `GZWeil.etaModelDifferential`, `thetaTwo_sixteen`, `thetaThree_S_sq`, `thetaTwo_S_sq`,
`thetaTwo/Three/Four_ne_zero`, `im_neg_inv_pos` (gz-weil); `JacobiLambda.norm_thetaThree_sub_one_le`,
`norm_thetaFour_sub_one_le`, `norm_thT_sub_two_le`, `thetaTwo_eq` (jacobi-lambda); `OmegaInt.integrableOn_f`,
`omegaInt_pos` (tyz-decomp); for the corollary, tyz-genus's `tyzThm11Integral_of_thm21C`.

## 3. Leaves

**No new leaf.** The only TYZ leaf left on this part of the route is tyz-genus's `TYZGenusFold.TYZThm21PairsC`
(TYZ Theorem 2.1 for every pair, complex sign choices). tyz-genus rated it **printed form, restricted, unread**:
odd classes, `n > 1`, and only the first assertion's consequence for pairs with no factor `≡ 1 (mod 8)`. That
rating is unchanged here. Its kinds row, with the flag updated to "replaces `h11` and `hL29`", is
`scratch/lcal-one/kinds-rows.tsv`. Remove the kinds rows of `h11` and `hL29`.

`TYZLcalOne` was rated by tyz-genus as a consequence of Tunnell's formula at `n = 1` and of the modular-symbol value.
It is now glue proved in Lean. Its docstring's remark that the value is "not a consequence of the known cases
of BSD" still holds, and is irrelevant now: the value is computed, not cited.

## 4. Fold (manual)

`scratch/lcal-one/fold-spec.json`. Edits to `ZInQKernel/OneProof/Main.lean`:

* add `import ZInQKernel.Contrib.OneProof.TYZLcalOne` (it imports `TYZThm11Genus`);
* replace the binders `(h11 : TYZThm11Integral)` and `(hL29 : H29Split.TYZLemma29PrintedNe3)` by
  `(h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)`;
* replace the argument `h11` by `(ZInQ.Contrib.LcalOne.tyzThm11Integral_of_thm21C_only h21C)` and `hL29` by
  `(ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21C h21C)`;
* kinds.tsv: drop the `h11` and `hL29` rows and add the `h21C` row; regenerate OPEN.md.

The resulting theorem is `frozenTarget_lcalOne` in `scratch/lcal-one/FoldCheck.lean` (compiled, standard axioms).

## 5. Files

* Contribution (new file only): `ZInQKernel/Contrib/OneProof/TYZLcalOne.lean`, 633 lines, 29 KB. It imports
  `TYZChain.Lcal`, `GrossZagierHeegner.JacobiLambdaDeriv`, `GrossZagierHeegner.WeilJacobi`, `GZTheta.EtaTheta` and
  `TYZThm11Genus`, never `Main`. It has no `sorry`, `axiom`, `native_decide` or `decide`, and no code that runs at build time (checked
  by grep). `lake build ZInQKernel.Contrib.OneProof.TYZLcalOne`: OK.
* `scratch/lcal-one/`: `LcalOne.lean` (identical copy of the module), `Discharges.lean` and its output,
  `FoldCheck.lean` and its output, `fold-spec.json`, `kinds-rows.tsv`, `log.md`.

## 6. What remains

Nothing on this target. Optional clean-ups, outside the task:
1. The consumers of `TYZLcalOne` through `TYZLcal.tyzLcalOne_of_leaves` (`TYZChain/Main.lean`,
   `X0ModuliUsed.lean`) could use `tyzLcalOne_proof` directly.
2. `H11Reduce.TunnellOddL1` and the variant-C leaf `TYZThm21PairsC1` are no longer needed on the route.
