# gz-weil results log

Task: make gz-hl3's split of `hL3` net negative by turning `StrongWeilCurve` and `IsogenyLattice`
(Eichler–Shimura + Faltings, analytic form) into printed form or theorems, restricted to what the proof uses.

## Setup (2026-11-15 04:40 PST)
- base c118e9d2 (wip/gz-hl3). Build tree copied (reflink) from ~/dzq-wt/gz-hl3 (same ZInQKernel tree, built 11-15 04:12).

## Uses (VERIFIED, read)
- `StrongWeilCurve`, `IsogenyLattice` are used only in `eichlerShimuraParamAt_of_leaves`
  (GrossZagierHeegner.lean §5), which feeds `grossZagierHeegner_of_leaves` (all E) and
  `shimuraCMParamCd_of_leaves` (Cd.lean).
- The only consumer of hL3 in the chain is `GZDecomp.grossZagierCd_of_leaves`, at `E = C_d`,
  `d ≡ 5 mod 8` squarefree, `f` from `modular_cd`. GZStatements.Weak shows the Cd form
  `GrossZagierHeegnerCd` closes the chain (`frozenTarget_of_..._fhNonvanishingCd_grossZagierHeegnerCd`).
- So the parametrization leaf needed is exactly `ShimuraCMParamCd` (Cd.lean):
  `∀ d ≡ 5 (8) squarefree, EichlerShimuraParamAt C_d`.
- In it, `N = 32 d²` is forced (`GZStatements.level_eq_of_coeff_cd`, proved) and
  `eichler f` depends only on `coeff f n = aₙ(C_d) = heckeCoeff d n`
  (`GZStatements.LFunction_cd_eq_heckeCoeff`, proved).

## Step 1: the twist reduction (VERIFIED, compiled, `scratch/gz-weil/Twist.lean`, 04:55 PST)
- `eichlerCd d z = Σ heckeCoeff d (n+1)/(n+1) e((n+1)z)`; summable for Im z > 0 (bound |heckeCoeff d m| ≤ (2m+1)³).
- `twist_formula`: d Φ_d(z) = Σ_{a mod d} 𝓕χ_d(a) Φ₁(z + a/d)  (χ_d = (·/d), Fourier inversion on ZMod d).
- `period_identity`: γ ∈ Γ₀(32d²) ⇒ d(Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ(a)(Φ₁(γ'_a τ'_a) − Φ₁(τ'_a)), γ'_a ∈ Γ₀(32)
  (Tau Ceti intertwining lemma + reindexing a ↦ aD²).
- `jacobiChar_isPrimitive` (d odd squarefree), `dft_jacobiChar`: 𝓕χ = g·χ, `gaussD_sq`: g² = d (d ≡ 1 mod 4).
- `scalePP`, `g₂_scalePP`, `g₃_scalePP`; `isPeriodLattice_cd_iff`: IsPeriodLattice C_d L ↔ g₂ = 4d², g₃ = 0.
- `periods_cd`, `eichlerShimuraParamAt_cd`, `shimuraCMParamCd_of_modularParamC1 : ModularParamC1 → GZHL3.ShimuraCMParamCd`.
- `modularParamC1_of_leaves : WU → StrongWeilCurve → IsogenyLattice → ModularParamC1` (new leaf no stronger).
- `grossZagierHeegnerCd_of_leaves hU hP hHP hGZ hGC : GrossZagierHeegnerCd`.
- axioms: [propext, Classical.choice, Quot.sound] for all three.

## Step 2: ModularParamC1 from x0-32's EtaModelDifferential (VERIFIED, compiled, 04:50 PST)
- dev file `scratch/gz-weil/Unif.lean`; theorems C1 `hasDerivAt_eichlerCd_one` (Φ₁' = 2πi f₁),
  C3 `period_const`, C4 `weierstrassP_surjective`, C5 `local_eq` (order-of-vanishing argument),
  C6 `global_eq` (clopen in ℍ), C7 `period_mem` (identity theorem, pole at 0), C8
  `modularParamC1_of_etaModelDifferential` (lattices ((1±i)/2)L of 32a1; c = 2). Axioms standard.
- Inputs used from the kernel (proved): tyz-cm `etaModelEquation` (y²=x³+4x), `etaModelInvariant`,
  gz-theta `etaThetaIdentity` (f₁ = Σ heckeCoeff 1 n qⁿ), `etaQuot32_slash_eq` (weight 2), x0-32
  `differentiableAt_xC/yC/fC`, `yC_ne_zero`, `fC_ne_zero`; Mathlib `PeriodPair` (℘, ℘', order −2, relation).
- Only open input: `ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential` (∀ τ, HasDerivAt xC (4πi fC τ · yC τ) τ).
- Independent numerical check (VERIFIED, exact integers, `scratch/gz-weil/etadiff_check.py`, python3):
  q dx/dq = 2yf to q^113; y² = x³+4x to q^109; f = Σ heckeCoeff 1 n qⁿ to q^119.

## Step 3: integration (VERIFIED, 04:58 PST)
- `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Weil.lean` (twist step) and `.../WeilParam.lean`
  (uniformization step): `lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilParam` → success (11340 jobs).
- `scratch/gz-weil/Check.lean` → `out_check.txt`: 16 theorems, all [propext, Classical.choice, Quot.sound].
- `#discharges` (`scratch/gz-weil/Discharges.lean` → `discharges-output.txt`): 65 open hypotheses, 1412 theorems
  checked; my theorems discharge no open hypothesis directly (hL3 is stated for all E; the new leaves are
  C_d-restricted), as expected; gz-hl3's general discharge of hL3 still listed.
- `scratch/gz-weil/MainEdit.lean`: `frozenTarget_gzweil` = frozenTarget with hL3 replaced by
  (WeierstrassUniformization, X0.EtaModelDifferential, HeegnerPointRationalCd, GrossZagierFormulaCd,
  GrossConjugationCd), through gz-statements' Cd chain; compiles, standard axioms.

## Step 4: EtaModelDifferential from Jacobi's derivative formula (VERIFIED, compiled, 05:30 PST)
- New leaf `ZInQ.GZWeil.JacobiLambdaDeriv`: ∀ t, Im t > 0 → HasDerivAt (θ₂⁴/θ₃⁴) (πi (θ₂⁴/θ₃⁴) θ₄⁴) t,
  θ₂(t) = e^{πit/4} jacobiTheta₂ (t/2) t, θ₃ = jacobiTheta₂ 0, θ₄ = jacobiTheta₂ (1/2).
  Numerically VERIFIED (python3, `scratch/gz-weil/lambda_check.py`): central difference vs πiλθ₄⁴ agree to 4e-10
  at t = 0.3+0.8i, −0.2+1.1i, 0.45+0.6i. Printed locators UNVERIFIED (classical; Jacobi 1829).
- `product_star` (f₁ θ(2τ;4τ)² = 2Q θ(0;16τ) θ(8τ;16τ) θ(1/2;16τ)⁴) proved from tyz-cm/gz-theta product forms
  + `euler_BCD`; numerically VERIFIED in the form f θ₂(4τ)² = 2θ₂θ₃θ₄⁴(16τ) (error 1e-16).
- `etaModelDifferential_of_jacobiLambdaDeriv`, `shimuraCMParamCd_of_jacobiLambdaDeriv`,
  `grossZagierHeegnerCd_of_printed` in `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/WeilTheta.lean`;
  `lake build …WeilTheta` success (11341 jobs); out_check.txt: 21 theorems, all standard axioms.
- MainEdit: `frozenTarget_gzweil` (hL3 → WU, JacobiLambdaDeriv, HPR_Cd, GZF_Cd, GC_Cd) and
  `frozenTarget_gzweil'` (with EtaModelDifferential): both compile, standard axioms.
- #discharges rerun (with WeilTheta): 65 open, 1434 theorems checked, 6 discharge one (unchanged; expected).
