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
