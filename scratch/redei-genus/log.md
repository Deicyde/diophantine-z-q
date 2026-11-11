# redei-genus log

## Step 4: Redei/Genus.lean (done, compiles, no sorry)
- not_dvd_absNorm_of_sup_span_eq_top, exists_mk0_coprime (via IsDedekindDomain.exists_sup_span_eq
  and Ideal.exists_isMaximal_dvd_of_dvd_absNorm').
- isSquare_normZ_mod: N(x) is a square mod q for every x : O (q | n squarefree) — no need for x ∉ 𝔭_q.
- legBit_absNorm_span, legBit_absNorm_mul, not_dvd_absNorm_mul, legBit_absNorm_eq_of_mk0_eq.
- chiBit, chiBit_mk0, chiBit_mul; chi (dite on Squarefree n, MonoidHom.mk'), chi_mk0.
- chi_ramIdeal_self (p = q, via span_omega), chi_ramIdeal.
- Fix: `⟨span{a}, by rw [hM]; exact (J*M).2⟩` timed out (defeq unfolding); use coe_mul rewrite with
  mk0_eq_one_iff (J*M').2 instead.

## Step 5: Redei/Dirichlet.lean (done, compiles, no sorry)
- prod_ite_bit_eq, jacobiSym_finsetProd_right (general helpers).
- exists_absNorm_eq_of_isSquare (trichotomy; inert case: (m+ω)(m−ω) ∈ pO, σ-stability, p | 2m).
- ne_two_of_mem_primeFactors, exists_chi_eq: reuses exists_prime_slot_bits (Slots/Dirichlet.lean:
  residues, CRT, Nat.forall_exists_prime_gt_and_zmodEq) with ℓ ≡ 1 or 3 mod 8 according to Σε;
  J(−n|ℓ) = χ₄(ℓ) J(ℓ|n) via jacobiSym.neg and quadratic_reciprocity_one_mod_four(').
- Fixes: legendreSym.to_jacobiSym lives in namespace jacobiSym; rw with n = ∏ q fails (motive, ε
  indexed by n.primeFactors): use congrArg.
- lake build ZInQKernel.RouteK.Redei: OK.

## chi_prod_ramIdeal (Genus.lean) and final checks
- chi_prod_ramIdeal: χ_q(Π_p [𝔭_p]^{e_p.val}) = Σ_p R_{qp} e_p.
- Checked in a scratch file (deleted) against origin/wip/redei-amb 07213a89 Ambiguous.lean:
  chi_psi := by rw [psi_apply, ← chi_prod_ramIdeal n hn hsq q e]; simp only [toAdd_ofAdd, ambigClass_eq hn hsq]
  compiles.
- lake build ZInQKernel: OK (9914 jobs). #print axioms: propext, Classical.choice, Quot.sound only.
