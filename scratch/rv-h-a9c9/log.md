# rv-h-a9c9 log

Scope: second review of A9 Milne paragraph (N5 L564-570) and C9 Li-Shimura sentence (N5 L768-774),
diophantine_zq.tex at commit 97cec7fd (11/5 text). rv-h-trust.md not read until own verdicts written.

## Step 1 (read)
- A9 text read: N5 L564-577. C9 text read: N5 L752-774 (with C8 context L718-767).

## Step 2: A9 centralizer computation (a9_centralizer.py, sympy+PARI, <1 min)
- B=(-1,3)_Q: hilbert symbol -1 exactly at 2,3 (p<=13), split at infinity: disc 6.
- L(B)R(B) spans M_4(Q) (rank 16): End_Q(B)=B(x)B^op. VERIFIED.
- dim_Q of commutant of right mult. R_J in M_4(Q):
  - J = sqrt10 i + j + sqrt2 k (J^2=-1, generic): 4 (= L(B)). 
  - J = 2i+j (J^2=-1 rational, k=Q(i)): 8, contains nonzero nilpotent (so M_2(Q(i))).
  - J = (3i+j+k)/sqrt3 (k=Q(sqrt-3)): 8, contains nonzero nilpotent (so M_2(Q(sqrt-3))).
  Consistent with N5 L571-577 (commutant = B (x) Z_B(J)^op, Z_B(J) in {Q, imag. quadratic k}).
- Argument (VERIFIED by reasoning): Sum b_i(x)c_i with b_i a Q-basis commutes with R_J iff
  Sum b_i(x)[c_i,J]=0 in B_R(x)B_R^op = End_R(B_R) iff all [c_i,J]=0. Z_{B_R}(J)=R[J]=C, so
  Z_B(J) is a field of degree <=2; c=a+bJ (b!=0) has min. poly x^2-2ax+a^2+b^2, disc -4b^2<0:
  imaginary. k subset B splits B, so B(x)k = M_2(k).

## Step 3: C9 Li's Fricke formula on samples (c9_li_fricke.py, PARI, ~2 min; output c9_li_fricke.out)
- Inputs: first 30 (newform, complex embedding) pairs of weight 2, nontrivial even character,
  N=13..29 (orders 2..14). Direct evaluation of q-expansions (500 terms) at 3 points:
  ratio (f|_2 W_N)(z) / fbar(z), fbar = sum conj(a_n) q^n.
- Outcome: ratio constant (spread <= 1.5e-95), |lambda|=1 (defect <= 2e-96), equal to PARI's
  mfatkineigenvalues. So f|W_N = lambda * c(f), c = complex conjugation in Aut(C): the span of the
  Aut(C)-conjugates of f is W_N-stable (numerically VERIFIED on 30 samples; theorem STANDARD:
  Li 1975 / Atkin-Li 1978 Thm 1.1).
- Remark (by reasoning): the twist of a non-normalized eigenform can vanish: g(z)=f(3z), f=11a,
  psi mod 3 -> sum psi(n)a_n(g)q^n = 0. Harmless if one twists the newform of g (a_1=1) or works
  with Hecke eigenvalue systems at p not dividing N*cond(psi).

## Step 4: sources available offline; C9 Euler-factor step
- No local copies of Milne AV notes, Li 1975, Shimura 1973 (searched ~/dzq-wt, ~/dzq, /tmp).
  Upstream audit notes (docs/theorem-application-audit/evidence/parallel-geometry-report.md
  L95-105; parallel-geometry-a011-fricke-review.md; parallel-galois-height-report.md L95-130)
  claim page-scan readings: Milne Part I Thms 2.8-2.9 printed p.14; Li p.296 paragraph before
  Lemma 6 (F|H_M = gamma F|K, any character); Shimura 1973 Thm 1 p.526: quotient A_f of J_1(N),
  field action with Hecke eigenvalues, dim = [K_f:Q] unconditional; zeta identity under the
  hypothesis that the full conjugate span is stable under h(z) -> h(-1/(Nz))/z^2.
  Status here: AUDIT-READ (upstream model audit), not checked against the sources by me.
- c9_charpoly_divisibility.py: G=Z/2xZ/2, V=1+a+b, U=ab: charpoly_U(g) | charpoly_V(g) for all g,
  but <U,V>=0. So a total Euler-factor identity alone does not give 'r_5 is a constituent';
  one needs the K_f-linear Eichler-Shimura trace (V_lambda(A_f) rank 2 over K_{f,lambda},
  tr Frob_p = a_p) or the existence of all rho_{f^sigma, iota} + Brauer-Nesbitt + Chebotarev.
  Both standard. With the K_f-linear route the Fricke condition (Li) is not needed at all.

## Step 5: own verdicts drafted (docs/research/rv-h-a9c9.md §§1-2) before reading rv-h-trust
- A9: holds as stated (R-A9-1 citation swap, R-A9-2 name descent fact).
- C9: holds after repairs R-C9-1 (Euler-factor -> constituent needs K_f-linear ES or all rho_{f^sigma}),
  R-C9-2, R-C9-3 (wording).

## Step 6: compared with rv-h-trust §2.1 (L177-186): no disagreement; rv-h-trust's open provision
(Shimura Thm 1 hypothesis) resolved. Wrote §§3-5 and .fleet/rv-h-a9c9.md.
