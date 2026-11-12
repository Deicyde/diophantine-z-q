# tyz-t1 log

## Step 0
rv-tyz-inputs.md is on origin/wip/rv-tyz-inputs (not main); read via git show. T1 = constant of TYZ Thm 3.3 (L2014-2015).

## Step 1: read TYZ (L318-370 defn of L(n); L496-590 Thm 2.1; L913-1000 proof; L1163-1331 Sec 3.1, Thm 3.3; L1860-2023 proof of Thm 3.3; L2633-3090 appendix, Thms 4.2, A.9)

Sources of the constant. TYZ reduce Thm 3.3 (L2005-2010) to
  h(R_chi) = L'(E_{K_n},chi,1) / (2^{2k(n)-2h2(n)-2-a(n)} Om_{d0} Om_{d1}),  R_chi = phi(P_chi), phi: A -> E deg 2.
Values of 2^{2h2+2+a-2k}: n=5 mod 8: h2=k, a=1 -> 8; n=7: h2=k-1, a=1 -> 2; n=6: h2=k, a=0 -> 4. Depend on n mod 8 only.

A.9 (F=Q, kappa=1, [O_K^x:O_F^x]=1 for n>3) for unramified chi and Gross-Prasad test vector f:
  h(sum_{Cl_n} f(P)^t chi(t)) / (f,f) = 4 L'^{(S)}(1/2,pi,chi) / ((f',f') |D|_A^{1/2} 64 pi^3) * loc_2,
  |D|_A = adelic abs value = 1/|D| (L2788 convention "|a| adelic"), so |D|_A^{-1/2} = sqrt|D|.
  loc_2: n=5,6 (2 ramified, 2^2|N): 2(1-1/2)=1; n=7 (2 split): no factor (=1). S=(N,D) u {inf}: removes only Euler factor at 2, which is 1 (E_d additive at 2).
  L'(1/2,pi,chi) = L'(E_{d0},1) L(E_{d1},1).
(f',f') = Om^2/(2^8 pi^3) (TYZ L960-985, Om = Om_{1,inf}); Om^2 = sqrt(n) Om_{d0} Om_{d1}.
YZZ pairing (f,f) = vol(X_V)^{-1} f f^vee, vol w.r.t. dxdy/(2 pi y^2): vol X0(32) = 48/6 = 8; X_U = 2 copies of X0(32) (Gamma_U := SL2(Z) cap U = Gamma0(32), since ad=1 mod 32 forces a=d mod 8) -> 16.
  n=7: f = i0, f f^vee = 1 -> (f,f) = 1/8.
  n=5: f = f0 - f0[i] = (1-[i], 1+[i]) on the two components -> f f^vee = (1-i)(1+i)+(1+i)(1-i) = 4 -> 1/4.
  n=6: f = f0[i] = ([i],[-i]) -> 2 -> 1/8.
Result: h_A(P_chi) = (f,f) * 16 sqrt|D| L'L / Om^2:
  n=5: (1/4)*16*2 = 8 * L'L/(Om_{d0}Om_{d1});  n=7: (1/8)*16*1 = 2;  n=6: (1/8)*16*2 = 4.
Ratios 8:2:4 = TYZ's 2^{2h2+2+a-2k}. So A.9 reproduces TYZ's constant up to ONE global factor gamma0 (height normalisation YZZ vs TYZ, Manin-type constant in Om^2 = 32 pi^2 (phi,phi)), the same for all n=5,6,7 and all chi.

Odd p | n (K ramified, pi_p unramified, chi_p(uniformizer) = s = +-1 varies with chi): VERIFIED by hand that beta_p = |D|_p^{1/2} for both s:
  beta^0 = |Dd|^{1/2}(1 + s a_p/(p+1)) (Macdonald), L(1/2,pi_K x chi)^{-1} = 1 - s a_p/p + 1/p,
  product = ((p+1)^2 - a_p^2)/(p(p+1)) independent of s; times L(1,ad)(1-p^-2) gives exactly 1.
2-adic: contributing chi have chi_2 = 1 (Lemma char'), so f_n is the GP test vector for every contributing chi and L(1/2,pi_2,chi_2) is the same.

What Prop N needs (sharper than rv-tyz 2.3): write P_chi = eps c(d0,d1) 2^{h2(n)} L(d1) PP(d0). The recursion represents c PP iff c(d0,d1) = c(d0,1) for all d1 > 1 with L(d1)PP(d0) != 0 (cross-n consistency, NOT only uniformity in chi for fixed n; for n=5 it compares the n=5 test vector with the n=7 one for (7,3)). A.9 gives c(d0,d1)^2 = gamma0 for all, so c = +-sqrt(gamma0), constant: suffices (sign is the eps ambiguity).
