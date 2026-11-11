# rv-h-c8 work log

## Step 1. Sources and the step under review
- N5 = repo-root diophantine_zq.tex, sha256 cb1148cd6c77...3d792b (matches h-trust). Read N5 L690-800.
- C8 = N5 L757-768 (Tate convention, Pan 1.0.4 at l=5, twist char ψ, local algebraicity, weight
  comparison {0,-1} vs {0,1-k}, "k=2 and power zero", absorb finite char, newform f).
- h-trust §1 C8 (L416-441) read. Suppliers listed: Faltings 1987 / Scholl 1990 + Faltings 1989 or
  Tsuji 1999 / Saito 1997 (eigenform pHT); Conrad App. B -> Serre 1968 Ch. III.
- Pan Thm 1.0.4 statement and conventions: from h-a011 §1.1 / rv-h-a011 log (VERIFIED there on
  FM.tex of arXiv v2): conclusion "comes from a cuspidal eigenform up to twist", no weight, level,
  Frobenius convention in the conclusion; notation: HT weight of eps is -1, Frob_v GEOMETRIC.
  Pan's FM.tex is no longer on disk (~/gt-src gone); not re-read here.

## Step 2. Prior reviews of C8
- rv-h-trust §1.2 item 1 (L75-90): only finding = missing eigenform pHT supplier.
- Astra descent AUDIT item 6 (11/4 text): same argument; last paragraph warns: cohomological
  modular rep has weights {0,k-1}, must not be mixed with arithmetic-Frobenius pair {0,1-k}.
  ADDENDUM item 5: "comparison of {-j,1-k-j} with {0,-1}, with k at least 1, forces k=2, j=0".
- h-a011 §4: Pan's conclusion read as rho = rho_g (x) psi, psi continuous; dual-is-twist makes
  the reading Frobenius-convention-insensitive (but changes psi by det).
- Neither names: (i) which normalization of rho_g N5's {0,1-k} presupposes vs Pan's geometric
  Frobenius notation; (ii) the k=1 case; (iii) l != 5 inertia finiteness for psi; (iv) 5 | level(g).

## Step 3. Exact weight matching (scratch/rv-h-c8/weights.py, .output.txt)
- Input: k in 1..200, n in -300..300 (n = HT weight of psi), Tate convention (cyc weight -1);
  HOM normalization (arith Frob trace a_l, det eps chi^(k-1)): {0,1-k}; COH (geometric Frob trace
  a_l = Pan's Frob convention): {0,k-1}; k=1: {0,0}.
- Outcome: HOM -> only (k,n)=(2,0); COH -> only (k,n)=(2,-1), i.e. psi = finite * cyc^1.
  det check (sum of weights = -1 = HT(det r5)) holds for both. VERIFIED.
- Consequence: "k=2" is normalization-free; "power zero" holds only in HOM. N5 never fixes the
  normalization of rho_g except implicitly by writing {0,1-k}; Pan's notation is geometric Frob.

## Step 4. Normalization link to Tate modules (scratch/rv-h-c8/normalization.py, .output.txt)
- 11a1, 37a1, 389a1, first 25 good primes: newform a_l = ellap = l+1-#E(F_l) (0 mismatches),
  i.e. trace of arithmetic Frobenius on V_p(E) = a_l(f): HOM normalization is the Tate-module
  one. VERIFIED (sample).
- S_2^new(13, chi order 6): 1 eigenform, coefficients in Q(zeta_6); conj(a_l)=conj(chi(l))a_l
  exactly for 24 primes l<100: fbar = f (x) chi^-1 is a Galois conjugate of f, so COH-normalized
  rho_f^vee (x) cyc = rho_fbar also lies in V(A_f). VERIFIED (sample).
