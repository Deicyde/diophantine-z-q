# nv-local results log

Task: prove `SGRDirect.NVLocalInertia` (ZInQKernel/Contrib/OneProof/SGRDirectNV.lean), base 56478c75.

## 2026-11-15 23:10 setup
- Build tree copied from ~/dzq-wt/sgr-direct (.lake/build, lean/.lake/build; same commit). Import of
  SGRDirectNV: 4 min cold, 7 s cached. VERIFIED.

## Analysis (paper; SPECULATIVE until compiled)
- NVLocalInertia is TRUE as stated (tame local structure at the closed point m=(p, dX-a): local tame pi_1 of
  the strict henselization minus V(p(X-b)) is Zhat'(1)^2; I_q, I_Q both inside the abelian I_P, I_P/I_Q =
  inertia of the residue field kappa(Q) at P). STANDARD (SGA 1 XIII 5.3, UNVERIFIED number).
- Full Lean proof needs Abhyankar's lemma in dimension 2 (Kummer base change by (X-b)^{1/N}, p^{1/N}, zeta_N,
  a new regular local base O[r]_{(w,r)}, purity, T2 at both divisors, base change of unramifiedness) -- not
  reachable by the deadline.
- Plan: reduce NVLocalInertia to one smaller GLUE Prop `BranchRegular` (purely local geometry of the
  normalization at the closed point, no Galois action, no arithmetic of residue fields):
  for every maximal ideal P of C = integralClosure Z[X] E over m_b there is exactly one prime Q of
  B = integralClosure Q[X] E over X-b with Q cap C <= P (unibranch), and every element of B/Q integral over Z
  is c1/c2 with c1, c2 in C, c2 notin P (the branch is normal at P).
  Then: tau in I_q fixes P, hence Q (unibranch); tau acts on kappa(Q) inside the inertia group of the prime
  P' = {c1/c2 : c1 in P} of O_kappa (normality); kappa(Q) unramified at p => tau trivial on kappa(Q)
  (|I(P'|P'_0)| = e(P'|P'_0) for the fixed field of tau, tower e(P'|p)=1).

## 2026-11-15 23:19 compiled (scratch/nv-local/Core.lean, `lake env lean`, standard axioms) VERIFIED
- `SGRDirect.NVLocal.eq_one_of_inertia_of_unram`: K number field, P prime of O_K with e(P|Z)=1, sigma in
  Aut(K) with sigma x - x in P for all x in O_K  =>  sigma = 1 (fixed field of <sigma>, card_inertia =
  ramificationIdxIn, ramificationIdx_tower).
- `primeOf`, `primeOf_isPrime`, `mem_primeOf_of_mem`, `inertia_primeOf`, `eq_one_of_primeOf`: the prime
  {y : y*psi(d2) = psi(d1), d1 in P, d2 notin P} of O_L for psi : C -> L with ker psi <= P and O_L inside the
  localization; an automorphism compatible with an action congruent to id mod P lies in its inertia.
- `zqIncl`, `galB`, `galC_mem` (plumbing).
- `BranchRegular` (def, GLUE) and `nvLocalInertia_of_branchRegular : BranchRegular -> NVLocalInertia`.
  `#print axioms`: [propext, Classical.choice, Quot.sound].

## 2026-11-15 23:25 Contrib file VERIFIED
- ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean (imports SGRDirectElkies): the Core.lean content plus
  `heckeVertWitness_of_branchRegular` (HeckeVertWitness from r1r2, t5, qmAutCard, serreRigidity3,
  alFixedPoints, elkiesX6StarPrinted, BranchRegular). `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNVLocal`
  OK (12 s).
- scratch/nv-local/Discharges.lean -> Discharges-output.txt: "#discharges: 63 open hypotheses, 1904 theorems
  checked, 7 discharge one" (none from this file, as expected: HeckeVertWitness is not an open field); all six
  listed theorems: [propext, Classical.choice, Quot.sound].
- scratch/nv-local/autofold.json (no fold; bypass as sgr-direct with branchRegular in place of nvLocalInertia).

## 2026-11-15 23:34 existence clause proved; BranchRegular restated VERIFIED
- `exists_int_mul_mem` (every y in the Q[X]-closure has k*y in the Z[X]-closure, k != 0; Mathlib
  `IsIntegral.exists_multiple_integral_of_isLocalization` with `Polynomial.isLocalization`) and
  `exists_branch` (a prime Q of B over X-b with Q cap C <= P, for P maximal over (p, dX-a): going down
  `Ideal.exists_ideal_le_liesOver_of_le` for C/Z[X], ker(Z[X] -> Q, X -> b) <= m via the chain's `mem_m_iff`,
  then Q = {y : k*y in Q_C}). Both compiled, standard axioms.
- `BranchRegular` restated without the existence clause: for every Q (prime of B over X-b, Q cap C <= P),
  (UB) every such Q' equals Q, and (N) every z in B/Q integral over Z is c1/c2 with c2 notin P.
  `nvLocalInertia_of_branchRegular` and `heckeVertWitness_of_branchRegular` recompiled.
- `lake build +ZInQKernel.Contrib.OneProof.SGRDirectNVLocal` OK; Discharges-output.txt regenerated:
  "63 open hypotheses, 1906 theorems checked, 7 discharge one" (none from this file); seven theorems with
  [propext, Classical.choice, Quot.sound].
- scratch/nv-local/NVLocal.lean = copy of the Contrib file; Core-first.lean = the first compiled version
  (old BranchRegular with existence clause).

## 2026-11-15 23:56 TameBranchNormal (general form) VERIFIED
- New GLUE Prop `TameBranchNormal` (no project definitions): R noetherian domain, m maximal, R_m regular local
  of dim 2, m = (f, g), (f) prime, p in m, L/Frac R Galois of degree < p, e = 1 at height-one P <= m with
  f, g notin P; then for every maximal P of the integral closure over m and every prime Q over (f) inside P:
  (UB) every such Q' equals Q; (N) every element of a fraction ring of S/Q integral over S/Q is a/s, s notin P.
- Compiled: `ramificationIdx_map_localization` (Mathlib's AtPrime lemma for any submonoid), `maximal_eq_span`
  (m = (dX - a, p)), `secGen_isPrimitive`, `secGen_map`, `span_secGen_eq` (Gauss), `span_secGen_isPrime`,
  `isLocalization_B` (B = (Z\0)^{-1} C), `unram_near` (from BranchData + distinctness), `branchRegular_of_tame`,
  `nvLocalInertia_of_tame`, `heckeVertWitness_of_tame`. All [propext, Classical.choice, Quot.sound].
- Contrib file rebuilt (lake, 22 s); Discharges-output.txt: "63 open hypotheses, 1923 theorems checked,
  7 discharge one" (none from this file). autofold.json: new leaf tameBranchNormal (project glue, GLUE).
