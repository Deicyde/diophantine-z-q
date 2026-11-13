# gz-statements results log

## 2026-11-13 step 1: restricted leaves (Contrib/GZStatements/Weak.lean)
- Read: Contrib/GZDecomp/{Scope,Decomp}.lean, docs/research/gz-decomp.md, atkin-li.md (VERIFIED read).
- Definitions checked (VERIFIED read): TC `Newform` = EigenformAwayFromLevel (eigen for all
  T_n, (n,N)=1, nonzero) + isNew (cuspFormsNew) + a₁=1 (Newforms/Newform.lean:85-111);
  `frickeSign` = choice of ε ∈ {±1} with 𝒲_N f = ε f (Newforms/Fricke.lean:221-233);
  `frickeCompletedL_sub_eq`: Λ_N(k−s) = i^k ε_N Λ_N(s) (LFunction/Sign.lean:186);
  Mathlib `WeierstrassCurve.LFunction`: Euler product over all primes of local factors of the
  MINIMAL model (EllipticCurve/LFunction.lean:41-81): genuine.
- Glue trace (VERIFIED read): FHNonvanishing used once, `hL2 N f hχ hw 4`, f from modular_cd for
  d%8=5; GrossZagierHeegner used once with E = C_d.
- Defined FHNonvanishingCd, GrossZagierHeegnerCd, GrossZagierRankCd; proved 10 theorems.
  `lake build ZInQKernel.Contrib.GZStatements.Weak` OK (VERIFIED). Axioms of all 10: [propext,
  Classical.choice, Quot.sound] (VERIFIED, scratch/gz-statements/out_check_axioms.txt).
- Finding: GrossZagierHeegnerCd and GrossZagierRankCd are implied by GZDecomp.GrossZagierCd
  (hence by Literature.GrossZagier): L3's conclusion is satisfied by any rational point of
  infinite order (VERIFIED, compiled).

## step 2: level pinning and Heegner arithmetic (Level.lean, Compat.lean)
- level_eq_of_coeff_cd: any weight-2 trivial-character newform with aₙ = aₙ(C_d) (n ≥ 1) has
  level 32 d² (from GZTheta.newformUniqueAcrossLevels + newCM). heegnerHyp_iff_of_coeff_cd,
  heegnerHyp_32_iff (elementary form). Compiled, standard axioms (VERIFIED).
- jacobiSym_neg_level: IsOddImagFundDisc D ∧ HeegnerHyp N D ⇒ (−N/|D|) = −1 (so
  ε(f⊗χ_D) = ε(f)χ_D(−N) = +1 when ε(f) = −1); coprime_of_heegnerHyp (D ≠ 0 needed: HeegnerHyp N 0
  holds vacuously-by-convention since J(p|0) = 1); jacobiSym_two_eq_one_iff: (2/|D|)=1 ↔ D ≡ 1 (8).
  Compiled, standard axioms (VERIFIED).
- check_heegner.py: 30 pairs (N, D) with HeegnerHyp, D odd fundamental: D ≡ β² mod 4N, (D,N)=1,
  Kronecker (D/p) = 1 for p | N in all 30 (VERIFIED, out_check_heegner.txt; sympy via uv offline).
- jacobiSym_prime_eq_legendreSym: (p/|D|) = (D/p) for odd primes p, D odd imaginary fund. disc.
  heegnerHyp_iff_split: HeegnerHyp N D ↔ (2∣N → D ≡ 1 mod 8) ∧ ∀ odd p ∣ N, D nonzero square mod p.
  Compiled, standard axioms; 18 declarations in Check.lean, all [propext, Classical.choice,
  Quot.sound] (VERIFIED).
