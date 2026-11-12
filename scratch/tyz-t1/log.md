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

## Step 2: numerical model and first test (heeg.py, t21.py, out_t21.txt)

Model (derived, n=5 mod 8): TYZ embedding sqrt(-n) -> [[-1,1/4],[-4(n+1),1]] has fixed point tau of the form [16(n+1),-8,1], disc -64n:
f0(P_n) is a Heegner point of the order Z[4 sqrt(-n)] on X0(32) (32 | A, [A/32,B,32C] primitive, B = -8 mod 64).
X_U(C) = two copies of X0(32), components <-> embeddings iota of Q(i) (det U_2 = 1+4Z_2), f0 o [i] : (x,iota) -> [iota(i)] x.
So z_n^{s_t} = (1 - psi(t) i0) x^{s_t}, psi = character of K(i)/K = K(sqrt n)/K (unramified, in the genus field).
Sum over Pic(O_4) = Cl(-64n) of chi(t) z^{s_t} = 4 P_chi mod torsion (fibre of Pic(O_4) -> Cl_n = Gal(H_{n,4}/H_n) = <s_{1+2w}, s_w^2>, z fixed by the first, z^{s_w^2} = z + tau(1)).
Hence P_chi = (S_chi - i0 S_{chi psi})/4 with S_chi = sum_{Cl(-64n)} chi(Q) phi(tau_Q), chi(Q) = genus character via a represented odd m.
n = 7: P_1(n) = sum over Cl(-n) of phi(tau_Q), Q = [A, delta, C], 32|A, delta^2 = -n mod 128.
phi = modular parametrisation of 32a1, z = sum a_k/k q^k. Precision: all PARI transcendental calls through GP strings (cypari2 calls default to 64 bits; first runs failed for that reason).
Checks built in: #classes hit = h(-64n) (16 = 16 for n=21); two Gamma0(32)-forms of one SL2(Z)-class give the same point mod Lambda (3 checks).

n = 21 = 7*3 (only contributing chars: trivial and chi_{7,3} = K(sqrt -7)):
  i0 = +i: P_psi and P_{chi_-3} torsion (Lemma char': non-contributing), 16 P_{chi_{7,3}} = -64 P_1(7) exactly mod Lambda (scan m in [-3000,3000], unique hit).
  i0 = -i: the opposite (the contributing ones torsion) -> i0 = +i is the K_2^x-invariant vector f_n of Prop 3.1.
  So P_{chi_{7,3}}(21) = -4 P_1(7) = eps 2^{h2(21)-h2(7)} L(3) P_1(7) with h2(21)=2, h2(7)=0, L(3)=1: Thm 3.3 cross-n consistency c(7,3) = c(7,1) VERIFIED at n=21.
