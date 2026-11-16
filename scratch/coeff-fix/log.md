# coeff-fix results log

Base wip/coeff-ext bca51e5c; `git merge origin/main`: already up to date. Build tree copied from
~/dzq-wt/coeff-ext (same commit) 2026-11-16 07:53.

## Statements
- Target: `ZInQ.Contrib.HodgeSplit.DSThm966` (TailS.lean l.1128), field `OpenResearchLeaves26.dsThm966`.
- New leaf `DSThm966EV.DSThm966Printed` (Deligne-Serre 1974 Thm 4.1 as printed): hypothesis Tau Ceti
  `EigenformAwayFromLevel N 1` (nonzero, ε-space of diamond ops, T_n-eigen for (n,N)=1, no a_1 = 1),
  `F.χ = toUnitHom ε`, `ε (-1) = -1`; conclusion trace = `F.eigenvalue p` (T_p eigenvalue), det = ε(p).

## Findings / compile outcomes
- VERIFIED (compiled, scratch/coeff-fix/DSThm966EV.lean, 07:58): `DSThm966EV.dsThm966_of_printed`;
  glue `char_neg_one` (parity lemma, TauCeti.char_neg_one_of_mem_cuspFormCharSpace, Parity.lean:113),
  `exists_awayFromLevel` (eigenvalue ⟨p⟩ = coeff g p via Eigenform.qExpansion_coeff_eq_eigenvalue, a_1 = 1).
- Pitfall: `(⟨p, h⟩ : ℕ+)` elaborates to `Subtype.mk` at type `{n // 0 < n}`, and `rw` with
  `F.eigenvalue ?n` then fails (type mismatch at implicit transparency); use `p.toPNat h`.
- VERIFIED (read in source): consumers of dsThm965Weak are general weight: DSThm965Weak -> DSThm965 (TailZ38:83)
  -> r14DetWtGe2_of_ds (all k >= 2, TailS:1185) -> R14Det / EigenformHT (fields r14, r13, TailX:200-202),
  passed whole to TailD:137, TailA:3718, TailK:323. So `EigenformCoeffFieldFinite` is NOT restated at k = 2.
- VERIFIED (compiled, 08:00): fallback `DSThm966PrintedFull` (Tau Ceti full `Eigenform N 1`),
  `printedFull_of_printed`, `dsThm966_of_printedFull`; `dsThm966_of_printed` now via the fallback.
- Build: copying coeff-ext's .lake/build with `cp -r` (mtimes not preserved) made `lake build` recompile
  modules (TailZ22, FaltingsLemma5Lower/Reduction seen at 08:09); first attempt stopped, rerun in progress.
- VERIFIED: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DSThm966EV`
  succeeded, 13700 jobs, 6m18s (scratch/coeff-fix/build.log); frozenTarget standard axioms.
- VERIFIED: `#discharges` (scratch/coeff-fix/discharges-output.txt, full in discharges-full.txt):
  dsThm966 by DSThm966EV.dsThm966_of_printed, still assumes [DSThm966EV.DSThm966Printed]; also by
  dsThm966_of_printedFull [DSThm966EV.DSThm966PrintedFull]; dsThm965Weak by DSCoeffExt.dsThm965Weak_of_printed
  [DSThm965Printed, EigenformCoeffFieldFinite]; all standard axioms.
- VERIFIED: autofold dry run strict 34/11 on 45 -> 35/11 on 46, strictest 34/11 -> 35/11 (as coeff-ext: the
  script already counted the old dsThm966Printed LEAF); FoldCheck.lean compiles, sixContactMin_of_open36 standard axioms.
