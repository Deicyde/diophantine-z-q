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

## Step 5. 11/4 vs N5 for C8
- git show 09c0c3f3:diophantine_zq.tex (sha256 bfc4192d..., = Astra's text); diff of 11/4
  L731-745 with N5 L757-771: only change in C8 = "Local algebraicity [conrad App. B]" added before
  "class field theory"; C9's Li-Shimura sentence replaces "Thus". VERIFIED (agrees with rv-h-trust).

## Step 6. Argument checks (as arguments, no computation)
- psi in Hom(rho_g, rho): if rho = rho_g (x) psi, id gives a G-stable line rho_g^vee (x) rho_g (x) psi
  ⊃ psi. Hom of HT (resp. dR) reps is HT (resp. dR); subobjects too (Fontaine). HT suffices for
  both uses (Tate/Sen local algebraicity needs HT only; the comparison uses HT weights only).
- l != 5: psi(I_l) ⊂ image of Z_l^x (local CFT) in O_E^x; Hom_cont(Z_l, O_E^x) has finite image
  (O_E^x virtually pro-5); unramified a.e. + G_Q^ab = Zhat^x (Kronecker-Weber) => psi chi^n has
  finite order. N5's "finite inertia at every other prime" is this, uncited (elementary).
- Robust form of the comparison: only |difference of HT weights of rho_g| = k-1 is needed for
  k=2; the value of the cyclotomic power depends on normalization (Step 3).
- k=1: {0,1-k} = {0,0} is right, but the supplier is Deligne-Serre 1974 (finite image) + Sen/Tate
  (finite image => HT weight 0), not Faltings/Scholl/Saito (k>=2). Pan's intro statement does not
  restrict k.
- 5 | level(g) possible: T = S ∪ supp M_S(u) (N5 L528) depends on u; Part D (L814-830) treats p=5 like any p in T (correction: use of r_3 at 5 is because l != p is needed, not evidence);
  g = f (x) finite twist. Supplier must cover p | N: Saito 1997 does (pst, all N); Scholl motive +
  Scholze 2013 Cor 1.8 (already a C3 leaf) + Fontaine closure do; Scholl + Faltings 1989 crystalline
  covers only 5 ∤ N; Tsuji 1999 needs de Jong 1996 alterations (Kuga-Sato not semistable at p|N).
  Whether Faltings 1987/1989 cover bad reduction: UNVERIFIED (no source access).
- Downstream: C9/C10 use r_5 = rho_f^HOM (Tate module of A_f), f weight 2 newform. In HOM
  normalization "power zero" gives exactly this; in COH, psi = eta*chi and rho_g^COH (x) chi =
  rho_g^HOM (x) eps_g^-1 (k=2), absorbed into the finite twist: same conclusion.
- Other uncited items in N5 L740-790: "duality preserves the conductor" (L774; standard);
  Eichler-Shimura a_p = trace (C9/C10); Kronecker-Weber; HT closure under Hom/sub.

## Step 7. Deliverables
- docs/research/rv-h-c8.md written: verdict "holds after repairs R1-R5" (R1 normalization, R2 k=1
  Deligne-Serre, R3 5|N supplier coverage, R4 minor uncited items, R5 h-trust bookkeeping).
- .fleet/rv-h-c8.md written. No files under ZInQKernel/, blueprint/ or other notes edited.
- No Lean run was needed or started.
