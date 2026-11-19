# Response to Protocol B round 1 — PR #158

**Target PR:** [elliotglazer/diophantine-z-q#158](https://github.com/elliotglazer/diophantine-z-q/pull/158).
**Reviewed head:** `a7ec3f361499d7872e9f1b1d6ba4d4ff516c5eec` (Version 20 parent `54a4e576f1c8c577f33b0b97a2cedb5ca96af642`).
**Round:** [44115113273](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44115113273), [Fable report](https://github.com/elliotglazer/diophantine-z-q/pull/158#issuecomment-6952855336), [Astra report](https://github.com/elliotglazer/diophantine-z-q/pull/158#issuecomment-6952856713).
**Status of this revision:** evidence and new proofs supplied **for renewed independent review**; no reviewer acceptance or administrative override is claimed.

## F1 — Four-point sum-height source was absent

**Change:** `suppliers/effective_torsion_sums_20261117_v62.tex` now contains the entire original 271-line uniform local-principal-part proof, including Theorem 1.1 and Corollary 4.1. The new section `sec:sum-height-audit` in `paper.tex` states the exact application to the four finite source points with arbitrary two-torsion translates and zero or negative labels.

The quantitative chain is visible rather than merely cited:

```text
h(Z) >= max_i h(x(Q_i)) - 24 log M - log 864 - (1/2) log 7
h(x(Q_i)) >= m_i^2/4 - 3                   for m_i != 0
M^2 < 8 h(Z) + 456
B^2 < 40 h(Z) + 2285
h(Z) <= h(t0)+h(t1)+h(t2)+log 32
B^2 < 40 (h(t0)+h(t1)+h(t2)) + 2425
```

The first inequality comes from the supplier's positive-subset local valuation argument for all finite points, not from the old effective lemma requiring positive abscissas and four nonzero multiples of one fixed point. The source confirms no odd ramification for Q(sqrt(2)) and uses the actual m_i labels. The numeric constant 40 is load-bearing. Source hypotheses (rank-one group, canonical height, duplication estimate, fixed curve) are stated explicitly in the note. Astra's previous report located and checked this external supplier; it was not present in the PR, and Fable did not have access to its proof through the PR packet.

**Verification status:** the supplier text is now locally reviewable; acceptance of the theorem and its use remains for outside reviewers, not for the supplied finite certificates.

## F2 — Source 229-coordinate table not bound to parent 195-coordinate system

**Change:** `source/quadratic195.json` and `source/transformation195.json` are exact copies of the Version 19 public artifacts at
`research/version19/construction/inputs/jose/computation/quartic/affine_laurent195_v45/`.
The 195-row table's Git blob SHA-1 is `5d6c4a4b482a4065b87a79d03426b0dcfff0f593` and its SHA-256 is `304f94843c1a4ac94fcd5f1295fee8b532e7f0424e638314d892c556e2fbfdf9`.
The corresponding parent transformation is Git blob `2ef400134a785944ff8f602430f88e29e51a5913`.

`graft.json`, `contact-change.json`, and **`check_graft.py`** are now included. The latter is the source's independent standard-library checker adapted only to load `source/quadratic229-v62.json` (already present), rather than the unrelated final compact `quadratic.json`, and to omit a duplicated 490-kB symbolic family JSON. It reconstructs the 3,322 symbolic parameter terms; its checks still cover every one of the 168 unchanged source rows, six changed original contact rows, all 31 cloned rows, all 34 cloned coordinates, the source aggregate coefficient change and new component, both Q(sqrt(2)) abscissa components, the complete twelve contact equations and all three literal guards. It also checks the contact factorization and all row coefficients. `check.py` independently verifies the fixed N=15 source and the final normalized polynomial coefficient by coefficient, so the omitted duplicated symbolic JSON is not a missing link for the fixed polynomial.

A separate exact JavaScript BigInt audit of the authenticated source tables on 17 November checked: the 168 untouched rows match exactly; the six changed original contact IDs are 22,24,25,34,36,37; 31 copied rows and all 34 local coordinate copies are exact; the only local coordinate used by an outside source row is x86 in the aggregate; and the aggregate coefficient at x77^2 changes by +12. The 229-source rows and the final 3,312 coefficients were independently checked in the preceding audit. **The adapted Python `check_graft.py` still needs to be executed by the receiving CI/reviewers; the historical upstream source checker reports PASS in `source/original_graft_certificate.json`.**

Reproduce:
```sh
python -B check_graft.py
python -B check.py
```

## F3 — Extraction below the previous 76,176 cutoff

**Change:** the new lemma `lem:cutoff-free` in `paper.tex`, section `sec:small-prime-audit`, now proves the scalar and detector valuation assertions at *every* prime outside the **actual** small sets S and Gamma. It does not cite the old large-prime lemma as though it already covered those primes.

The proof explicitly establishes:

1. **Hypotheses at every consumed prime.** All excluded primes include 2,3,5,7; K=Q(sqrt(2)) is unramified and E has good reduction outside those. Pairwise contact differences and midpoint differences are p-units outside Gamma. The scalar polynomial has collision support in {2,3,5,7}. The scalar constant 9792 is supported on {2,3,17}.
2. **Precision uniform in small p.** At every odd unramified p other than 5, the formal logarithm satisfies ell(z)/z in 1+p^(4r) O for r=v(z)>=1: j=1 uses p!=5, and j>=2 uses v_p(4j+1)<=4j-4. No p>76176 condition is invoked.
3. **Scalar extraction.** The three scalar summands in R_s^4 W_s have valuations in 2+4Z, 1+2Z and 4Z, preventing cancellation, and the retained pole obstruction excludes negative odd valuations outside {2,3,17}. This gives v_p(Z0)>19mu/8, v_p(Z1)>9mu/4, v_p(F)>7mu/4. Formal-log ratio transport, including possible (0,0)-translation, gives v_p(a)>9mu/4. At p=149 the separate forced depth is 2N±1; the four would-be contacts are quadratic nonsquares, so 149 is absent from M_S(beta).
4. **Every detector factor.** The five actual factors have a unique minimum among the constant term and valuation classes (odd), (2 mod 4), (4 mod 8), and two distinct odd residues in the special factor. At a consumed contact, the exact trace and pole equations give ell=max(v(W_j))>-mu/2. This implies all cross/Lucas errors vanish to order >=3, the input error to order >=1, and all nonzero reciprocal ordinates have positive even valuation.
5. **The 409 denominator.** gamma=408/409 has a negative valuation at 409, **not** a unit there. Because v_p(gamma)<=0 at all primes outside Gamma, the extra negative valuation only strengthens the pole upper bound. This case is now addressed explicitly rather than silently invoking the old p-unit assertion.
6. **No relative-to-absolute jump.** One of h,h-1 is a p-adic unit. Integrality is transmitted across the comparison of the two ratios before the order-four *relative* log error is used as an *absolute* congruence. Then L1=n modulo p and (L2,L3,L4)=(a,t,b) modulo p^3; hence p|J_X and p^3|Delta at each contact. Zero ratios, torsion differences, split/inert places and the midpoint case are addressed.

The new proof is specific to the source's actual scalar and five-factor equations, and refers to the parent's P04--P07 and q198 ratio/chart theorems only at the points where their hypotheses are matched. Earlier **completeness** constructions may still demand chosen primes >76176; that does not restrict **soundness** at other primes.

**Verification status:** all elementary valuation-class computations and the input ratios have been re-derived, but the revised source-to-consumer proof requires independent review; the supporting global prime-pattern and prepared-pole existence theorems are not re-proved.

## Notes N1, N2; Astra's scope requirements

- **N1:** `check_arithmetic.py` and its original `arithmetic_certificate.json` are now included. Reproduce with `python -B check_arithmetic.py --output arithmetic_certificate_replay.json`. It certifies finite supports, constants, input nonsquares, rational interval estimates and the N=15 numerical comparison, not the number-theoretic global assertions.
- **N2:** `README.md`, `REVIEW_NOTE.md`, and `PR_DESCRIPTION.md` now explicitly distinguish the **new effective N=15 three-detector theorem** from the inherited ineffective 195-variable theorem and the mechanically equivalent compact normalization. They no longer claim that the entire N=15 result is inherited from Version 20.
- **Astra:** The pinned source-to-parent maps, full original paper, supplier note, all three polynomial JSON/TXT artifacts, both original and adapted checkers, arithmetic certificate and precise supplier proof links are now packaged together. Review of final prime-selection, progression and pole-realization hypotheses and the assembled N=15 proof is still requested. No uncompleted review item is represented as accepted.

## Constraints and next steps

This is still a **candidate-note PR**, not an official Version 21 release. It changes no old manuscript, release, current-manuscript selector, review infrastructure or Lean code. The exact diagonal map fixes x1 and preserves rational solutions; the expanded polynomial still has 229 occurring coordinates, degree four, 3,312 terms, content one, coefficient height 149^30 and canonical ASCII size 74,007 bytes (SHA-256 `45bdea1ea7876bf6ec10b5427f9403cf1f94c144fab35817aa545bcb2cea1975`).

Request a fresh Protocol B review **only for the new exact head** after the hosted finite checks conclude. The review should check F1--F3 and the outstanding Astra source-to-consumer and witness-realization scope. Independent outside reviewers decide whether the revised proofs close the original objections; no approval or override is claimed here.
