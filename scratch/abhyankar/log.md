# abhyankar results log

Target: `SGRDirect.NVLocal.TameBranchNormal` (ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean:627, from wip/nv-local 2e4ff83d).

## 2026-11-16
- 00:33 merged origin/wip/nv-local (clean, merge commit dc7718298). `lake build ZInQKernel.Contrib.OneProof.SGRDirectNVLocal` OK (VERIFIED).
- Available proved inputs (VERIFIED by #check from a scratch importing SGRDirectNVLocal, with `open HDec`):
  `TPurity3.purityGlobalDim2'` (purity, 2-dim regular local base), `TsKummer.unramBaseChange` (base change of
  unramified extensions of DVRs), `HDec.HSyn.t2_proved : PkgI2.AbhyankarDVR` (Abhyankar's lemma for DVRs, proved).
- Mathlib 4.35: `Algebra.HasGoingDown` instance for integral, torsion-free over integrally closed (VERIFIED, IntegralClosure/GoingDown.lean:49);
  `Ideal.ramificationIdx` is the length of `S_q/(q∩R)S_q` (VERIFIED, RamificationInertia/Ramification.lean:53);
  `Algebra.trace_eq_sum_embeddings` (VERIFIED).
- Assessment: statement plausibly TRUE (toric description of tame covers along a normal crossings divisor; SPECULATIVE until compiled).
- 00:56 Defs.lean (named Props: BranchConcl, TBNLocal, KummerBase, KummerUnram, EtaleBranch, BranchDescent) builds.
  Assembly.lean: `exists_kummer_field` (Ω = L(a^{1/N}, b^{1/N}) in an algebraic closure, separable, [Ω:L] prime to primes > N)
  and `tbnLocal_of_pieces : KummerBase → KummerUnram → EtaleBranch → BranchDescent → TBNLocal` COMPILED (no sorry),
  using `TPurity3.purityGlobalDim2'`.
- 01:01 `etaleBranch : EtaleBranch` COMPILED (EtaleBranch.lean): C = S'_𝔓' has maximal ideal (t,u)C
  (`Algebra.FormallyUnramified.map_maximalIdeal`), C/tC has principal maximal ideal, ū not nilpotent ⇒ DVR
  (`principal_local_structure`, adapted copy of `CurveGlueCI.isDomain_of_dim_one`).
- 01:12 `branchDescent : BranchDescent` COMPILED (Descent.lean): uniqueness by going down; normality by the
  colon ideal I' = (bS' + J) : a, prime avoidance over the finitely many primes over Q (minimal primes of QS'),
  and Tr_{Ω/L} as Reynolds operator (`trace_eq_sum_embeddings` into AlgebraicClosure L; J ↦ Q).
- 01:14 `kummerBase : KummerBase` COMPILED (KummerBase.lean).
- 01:20 `tameBranchNormal_of_local : TBNLocal → TameBranchNormal` COMPILED (Transport.lean).
- 01:20 contributor file ZInQKernel/Contrib/OneProof/Abhyankar.lean: `tameBranchNormal_of_kummerUnram : KummerUnram → TameBranchNormal`,
  `nvLocalInertia_of_kummerUnram` COMPILED. Only `KummerUnram` (step 2) remains open.
- 01:40 `kummerUnram_of_branch : KummerUnramBranch → KummerUnram` COMPILED (KummerUnram.lean, with helpers in
  KummerUnramBasic.lean: `height_under_eq_one`, `dvr_atPrime`, `unramifiedAt_of_local`; KummerUnramTame.lean:
  `tame_at` (e | N via Galois `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, residue separability),
  `unram_of_baseChange` (from `TsKummer.unramBaseChange`)). Generic height-one primes done; the (f)/(g) case is the
  new named glue `KummerUnramBranch` (T2 at A_(f)). Contributor file: `tameBranchNormal_of_branch` COMPILED.
- 01:49 `branch_e` COMPILED (KummerBranch.lean): primes of the integral closure of A₁ = A[t₁, g] in Ω₁ = L(t₁) over (t₁)
  have index 1 over A₁ (T2 = `HDec.HSyn.t2_proved` at A_(f), adapted from `TsKummer.abhyankar_core`; freeness from
  `TPurity3.normalFreeDim2`).
- 02:05 `kummerUnramBranch : KummerUnramBranch` COMPILED (KummerBranchFinal.lean: `finrank_le_of_adjoin`, `branch_final`).
  Contributor file: `Abhyankar.tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal` and
  `Abhyankar.nvLocalInertia : SGRDirect.NVLocalInertia` COMPILED, axioms [propext, Classical.choice, Quot.sound]
  (VERIFIED, scratch/abhyankar/axioms.txt). TameBranchNormal is PROVED outright: no new leaf.
- 02:25 #discharges (scratch/abhyankar/discharges.txt): "61 open hypotheses, 2376 theorems checked, 6 discharge one" — the six are
  earlier contributions; nothing of this task matches at this base (nvLocalInertia exists only after sgr-fold). VERIFIED.
- autofold spec scratch/abhyankar/autofold.json (nvLocalInertia := _root_.Abhyankar.nvLocalInertia). Dry-run at base: "not a field
  of the current bundles" (expected). Dry-run on origin/wip/sgr-fold's files (git archive into /tmp, contributor file copied, nothing
  merged): OK, strict 45/10 on 55 -> 45/9 on 54, strictest 43/12 -> 43/11; generated OpenGlue9 is an empty structure
  (EmptyBundleTest.lean compiles). VERIFIED.
- report docs/research/abhyankar.md written.
