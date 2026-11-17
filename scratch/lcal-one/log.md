# lcal-one results log

Task: prove `ZInQ.Contrib.TYZDecomp.TYZLcalOne : lcalSq 1 = 1` (Leaves.lean:266).

## Setup (2026-11-16 22:20)
- Merged origin/main (no change) and origin/wip/tyz-genus (clean).
- Copied tyz-genus's `.lake/build`; `lake build` of Lcal, JacobiLambdaDeriv, WeilJacobi, EtaTheta, TYZThm11Genus: OK (9 min).

## Normalizations (VERIFIED, read)
- `lcalSq 1 = lValOne 1 / (2^(0-3) * omegaTYZ 1)`, `omegaTYZ 1 = 2 * omegaInt`; tree lemma
  `TYZLcal.lcalSq_one : lcalSq 1 = lValOne 1 / (omegaInt / 4)`. So the target is `lValOne 1 = omegaInt / 4`,
  `omegaInt = ∫_{(1,∞)} dx/√(x³−x)` (= lemniscate constant ϖ ≈ 2.62206).
- `TYZChain.Lcal.lValOne_one_eq : lValOne 1 = Σ_{j ∈ (Fin 4)²} cU j * (1/4) * (π * gaussLambda (j/4) 1)`,
  `gaussLambda a b 1 = mellin (gaussTheta a b) 1 = ∫_{(0,∞)} gaussTheta a b`.

## Route (plan)
1. (A) `lValOne 1 = 2π ∫_{(0,∞)} fC(i t) dt`, `fC = η(4τ)²η(8τ)²` (block decomposition of the lattice
   theta kernels + grouping by the norm + gz-theta's `etaThetaIdentity`).
2. (B) On the imaginary axis `x(it)`, `y(it)` (x0-32's eta model, `y² = x³ + 4x`) are real, `y < 0`, `fC > 0`,
   `x' = −4π fC y` (x0-32 `EtaModelDifferential`, proved by gz-weil), `x → 2` as `t → 0+` (theta S-law),
   `x → ∞` as `t → ∞`. With `u = x/4 + 1/x` (the 2-isogeny `32a1 → y² = x³ − 16x`, rescaled to `C₁`):
   `u'/√(u³ − u) = 8π fC`, `u: (0,∞) → (1,∞)`. FTC on `(0,∞)` for `K(u(t))`, `K(u) = ¼∫_u^∞ dv/√(v³−v)`:
   `2π ∫ fC(it) dt = K(1) = omegaInt/4`.

## Part B compiled (VERIFIED, `scratch/lcal-one/PartB.lean`, 2026-11-16 ~23:30)
- `Xr, Yr, Fr t := re of xC, yC, fC at i t`; real by x0-32's `xC_neg_conj` etc.; `Fr > 0`, `Yr < 0` (eta values
  real nonzero), `Yr² = Xr³ + 4Xr` (tyz-cm `etaModelEquation`), `Xr > 0`.
- `hasDerivAt_Xr : Xr' = −4π Fr Yr` (from gz-weil `etaModelDifferential`), strictly increasing.
- `tendsto_Xr_zero : Xr → 2` at `0⁺` (`xC = 2θ₃(16τ)/θ₂(16τ)`, squared S-laws of WeilJacobi, `θ₃, θ₄ → 1`).
- `tendsto_Xr_atTop : Xr → ∞` (`1/x = e^{−4πt} T(16it)/(2θ₃)`, `T → 2`).
- `two_lt_Xr`, `U = Xr/4 + 1/Xr > 1`, `sqrt_U : √(U³−U) = (X²−4)/(8X²)·(−Y)`.
- `integral_Fr : ∫_{(0,∞)} Fr = omegaInt / (8π)` (FTC `integral_Ioi_of_hasDerivAt_of_nonpos` for
  `G = K ∘ U`, `K(u) = (Ω − ∫₁^u dv/√(v³−v))/4`, `G' = −2π Fr`).

## TYZLcalOne PROVED (VERIFIED, compiled, 2026-11-16 ~23:55)
- `scratch/lcal-one/LcalOne.lean`: `ZInQ.Contrib.LcalOne.tyzLcalOne : ZInQ.Contrib.TYZDecomp.TYZLcalOne`;
  `#print axioms` → `[propext, Classical.choice, Quot.sound]`.
- Part A: `tsum_latT_block` (block decomposition mod 4 of `Σ unitOf(α) α e^{−πN(α)x/16}`), `tsum_latT_eq`
  (grouping by the norm + gz-theta `etaThetaIdentity`: it is `4 f(ix/32)`), `sum_cU_gaussTheta`
  (`Σ_j cU_j Θ_{j/4}(x) = ¼ f(ix/32)`), `lValOne_one_eq_integral : lValOne 1 = 2π ∫_{(0,∞)} f(it) dt`.
- `lValOne_one : lValOne 1 = Ω/4`; `tyzLcalOne` from `TYZLcal.lcalSq_one`.

## Contribution and checks (VERIFIED, 2026-11-17 ~00:00)
- `ZInQKernel/Contrib/OneProof/TYZLcalOne.lean` (633 lines): `tyzLcalOne_proof`, `lValOne_one`,
  `tyzThm11Integral_of_thm21C_only`; `lake build ZInQKernel.Contrib.OneProof.TYZLcalOne` OK.
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ...`: OK (14237 jobs, 5 min).
- `#discharges` (`Discharges-output.txt`): `DISCHARGES [h11] by LcalOne.tyzThm11Integral_of_thm21C_only still
  assumes [TYZGenusFold.TYZThm21PairsC]`; with tyz-genus's `DISCHARGES [hL29] by tyzLemma29PrintedNe3_of_thm21C
  still assumes [TYZThm21PairsC]`; axioms standard. 35 open hypotheses.
- `FoldCheck.lean`: `frozenTarget_lcalOne` (h11, hL29 → h21C; new body written out) and `frozenTarget_lcalOne'`
  (through current frozenTarget): both `[propext, Classical.choice, Quot.sound]`. Net −1 (35 → 34), TYZ 2 → 1.
- No new leaf. grep: no sorry/axiom/native_decide/decide/#eval in the contribution.
