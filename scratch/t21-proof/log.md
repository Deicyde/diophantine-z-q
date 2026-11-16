# t21-proof log

Base 2880fef1. Build tree copied from ~/dzq-check2 (same commit).

## Step 1: reduction (T21Reduce.lean) — VERIFIED (compiles, 6 s)
`tyzThm21At31_of_glue : BrandtValueAt3 → LcalUnitOneThree → TYZThm21At31`.
- `torsionOrder_three : torsionOrder (QNeg 3) = 6` (Mathlib `IsCyclotomicExtension.Rat.torsionOrder_eq`).
- `classSum_eq`: Cl_3 subsingleton (pid_three), class sum = f 1 (tv_eq_of_toClassGroup_eq).
- `int_eq_pm_one_of_sq`: a ∈ ℤ, a² = z, 0 < ‖z‖ < 4 → a = ±1.
Glue left: `BrandtValueAt3` (∀ admissible τ, ∀ test vector f, f 1 = ±3), `LcalUnitOneThree`
(0 < ‖lcalSq m‖ < 4 at m = 1, 3).

## Step 2: Brandt side infrastructure (ZInQKernel/Contrib/OneProof/T21Proof/) — VERIFIED (each compiles)
- Hurwitz.lean: Hurwitz coordinates `hc`/`hur`, `mulH`/`starH`/`nrdH` (integer polynomials), `IsHur S`
  closure; `exists_oneI_mul` (even norm ⇒ divisible by 1+i, mod-2 decide), `eq_smul_unit_of_nrdH`
  (norm 4^m ⇒ 2^m · unit).
- Local.lean: `ev w : 𝔸ᶠ_ℚ →+* ℚ_[p_w]` via Mathlib `padicEquiv`; `piQ w`; components of qι γ, centre, ιAt.
- LocalPred.lean: `LocOK` (ℚ_p^× O_{B,p}^×), `InR ω` (ℤ_p + ℤ_p ω + 4O_{B,p}), `Loc2OK`; closure under
  products/inverses.
- GlobalStep.lean: `global_step` (γ ∈ ℚ_p^× O_{B,p}^× at all odd p ⇒ γ = q·n, nrd n = 2^k; content
  argument), `two_adic_step` (⇒ μβ ≡ X + Yω mod 4O_B with μ a unit; reduction ℤ_2 → ℤ/4).
- Finite.lean (decide +kernel, 11 s): 24 Hurwitz units; mod-4 obstruction for the 6 classes
  t ∉ {0, t*(s)} for all 8 sign patterns s; partner identity; sums of the test vector values.
- BaseChange.lean: `tauHat_integral` (τ̂(Ô_K) integral at every place; copy of Tau Ceti's private
  `exists_semilocalHom_sum_tmul_eq`). Pitfall: `attribute [local instance 2000]
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion` needed (ℚ-algebra diamond).
Cross-check (classes.py, python): for each of the 8 τ, the classes in B^×H are exactly {0, t*}
(matches scratch/h29-fix/brandt.py's −3 classes).

## Step 3: BrandtValueAt3 PROVED — VERIFIED (compiles; axioms propext, Classical.choice, Quot.sound)
`ZInQ.Contrib.T21Proof.testVector_one : AdmissibleTau 3 τ → IsTestVector 3 τ f → f 1 = 3 ∨ f 1 = -3`
(ZInQKernel/Contrib/OneProof/T21Proof/BrandtValue.lean; scratch/t21-proof/AxBrandt.lean prints axioms).
Files: Tau.lean (signs of τ, 𝓞 = ℤ[ω], τ̂(Ô_K) ⊂ ℤ_p+ℤ_pω, place 2), K2.lean (centralizer of ω at 2),
Brandt.lean (subgroup Sg, H ≤ Sg, twoRep_ne for the 6 classes), Brandt2.lean (partner ∈ R̂_3^×),
BrandtValue.lean (gT = −3·[B^×H] + 1·[else] ∈ InPiZ; generator ⇒ f(1) = ±3).
Route: g defined by membership in the double coset B^×H (invariances free); sums need exactly
{0, t*} ⊂ B^×H among TYZ's 8 representatives: positive by explicit R̂_3^× element, negative by the
local invariant (global content argument + 2-adic mod-4 obstruction, decide).

## Step 4: L-value bounds — VERIFIED (compiles; each file builds in < 15 s)
- LKernel.lean: `norm_gaussLambda_sub_mainL_le` (0 ≤ a,b < 1): ‖Λ_{a,b}(1) − mainL a b‖ ≤ (15.2e^{−π} + 0.2487)/π,
  mainL = closed form of the four nearest lattice points (a−m, b−n), m,n ∈ {0,1}; tails by geometric majorants.
- LValues.lean: `lValOne_three_eq` (L(C_3,1) = Σ_{j ∈ (ℤ/12)²} twChar 3 j (π/12) Λ_{j/12}(1), from
  `isLContinuation_twChar`); coefficient tables uRe/uIm/jac12 with `twChar_three_eq`, `cU_eq`; `re_term`.
- LBounds.lean: generic `Lsum_bounds` (M, tables cr ci, l ≤ e^{−π/M²} ≤ u, W = Σ(|cr|+|ci|), rational bounds on
  Re/Im of the main sum ⇒ ‖L − S‖ ≤ (15.2e^{−π}+0.2487)W/(4M), rl ≤ Re S ≤ rh, il ≤ Im S ≤ ih).
- LUnit.lean: certificates by `decide +kernel` (all 10 together < 10 s):
  C_1 (M = 4, l = 0.8036, u = 0.836): Re S ∈ [3/5, 71/100], Im S ∈ [−1/25, 1/25], W = 8;
  C_3 (M = 12, l = 0.9781, u = 0.9787): Re S ∈ [149/100, 153/100], Im S ∈ [−1/50, 1/50], W = 64.
  `lValOne_one_bounds`: 0.09 ≤ Re L(C_1,1), ‖L(C_1,1)‖ ≤ 1.26.
  `lValOne_three_bounds`: 0.14 ≤ Re L(C_3,1), ‖L(C_3,1)‖ ≤ 2.9.
  Cross-check (python, scratch/t21-proof/lsplit.py, cert.py): L(C_1,1) ≈ 0.65551, L(C_3,1) ≈ 1.51385
  (= Ω/4 and Ω/√3 with Ω = omegaInt ≈ 2.62206, i.e. 𝓛(1)² = 𝓛(3)² = 1).

## Step 5: TYZThm21At31 PROVED — VERIFIED
`ZInQ.Contrib.T21Proof.tyzThm21At31 : ZInQ.Contrib.TYZDecomp.H29Split.TYZThm21At31`
(ZInQKernel/Contrib/OneProof/TYZThm21At31.lean). `lcalSq_one_bounds`, `lcalSq_three_bounds`: 0 < ‖𝓛(m)²‖ < 4.
#discharges (scratch/t21-proof/Discharges.lean, output Discharges-output.txt):
  DISCHARGES [hT21] by ZInQ.Contrib.T21Proof.tyzThm21At31 / still assumes: [] / axioms: [propext, Classical.choice, Quot.sound]
No native_decide, #eval, sorry, axiom, syntax/macro in T21Proof/ or TYZThm21At31.lean (grep).

## Step 6: fold
autofold.py refuses (`not a field of the current bundles: ['hT21']`: hT21 is a top-level argument of frozenTarget,
autofold folds bundle fields only). Manual fold checked: scratch/t21-proof/FoldCheck.lean states frozenTarget
without hT21 (passing tyzThm21At31), compiles, axioms standard. Spec kept in autofold.json (no leaves).
