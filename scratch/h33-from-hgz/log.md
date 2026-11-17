# h33-from-hgz log

* Read: Main.lean L130-145 (h33 enters only through `ThetaWP8.tyzThm35ReadingA_noHX ... h33`; hGZ enters only through
  `GZAlg.grossZagierFormulaCd_of_alg` -> `Heegner32.grossZagierHeegnerCd_of_printed` -> `GrossZagierHeegnerCd`). VERIFIED.
* `GrossZagierAlgOptCd` (Contrib/OneProof/GrossZagierAlgebraic.lean L110-142): trivial character, curves E' with
  a_n(E') = a_n(C_d), d ≡ 5 (mod 8) squarefree, K = Q(√D) with D odd fundamental (D ≡ 1 mod 4) and HeegnerHyp N D;
  conclusion (FG)'(1) = κ ĥ(y), κ > 0. VERIFIED (read).
* `TYZThm33` (OneProof/TYZSplit.lean L157-176): all n ≡ 5,7 squarefree, all quadratic χ of Cl_n; first clause
  (P_χ non-torsion ⇒ χ = χ_{d0,d1}); second clause m(d0) P_χ ≡ ε 2^{h2(n)} ℓ(d1) Q(d0) mod torsion, ℓ(d1)^2 = lcalSq d1. VERIFIED (read).
* TYZ proof of Thm 3.3 (Period7.tex L1865-2040): Lemma char' (root numbers, Tunnell–Saito via YZZ remarks after Thm 1.2),
  2-adic invariance (Prop. choice), Lemma multiples1 (Galois), Gross–Zagier + Kolyvagin (rank one of E(K_{d0})^-),
  explicit GZ with character χ_{d0,d1} (Thm EGZ, L3062, deduction omitted by TYZ) for L'(E_{K_n},χ,1) = L'(A_{d0},1)L(A_{d1},1). VERIFIED (read).
* Scope.lean: `not_oddDisc_Kn_of_five` (for n ≡ 5: −n, −4n are not odd fundamental discriminants),
  `not_heegnerHyp_of_common_prime`. Compiled (lake env lean, exit 0, no output), Mathlib only (verbatim copies of
  IsOddImagFundDisc, HeegnerHyp; worktree's upstream lean/ package not built, so GZDecomp.Decomp could not be imported).
* Verdict: hGZ does not imply h33 (reasons in docs/research/h33-from-hgz.md §2). No Contrib file, no fold, no #discharges.
