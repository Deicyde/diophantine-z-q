# h-b1 work log

## Step 1 (reading)
- Read h-map.md (origin/wip/h-map), its scripts, N5 L377-580 and L796-857.
- Uses of the integral model in N5: L441-534 (construction, tame quotient, Kummer form
  u-c=z^2), L524-532 (K unramified outside T; "proper model ... good reduction outside S"),
  L563-566 (good reduction of every conjugate outside T), L847-850 (p>R good reduction).
  L814 (v|3) uses only Raynaud's criterion (Silverberg-Zarhin Thm 3.5) over L_v(A[5]):
  no integral model needed there.
- Finding F1: "p not dividing |G| and branch locus etale mod p => no vertical ramification"
  is FALSE for a general cover over Q: y^2 = p*j*(27j+16) (group Z/2, branch points 0,-16/27
  distinct mod p) specializes at j=1 to Q(sqrt(43p)), ramified at p. Beckmann's theorem lists
  "no vertical ramification" as a separate hypothesis (bad-prime set), so B1 as written in h-map
  has a gap at exactly this point. To be checked by script.
- Replacement idea R1 (no vertical ramification at p>=5, p not dividing |Gal|): work over Z_p^sh.
  Purity => branch locus in D u V(p). Abhyankar at P_i = (b_i mod p): if the residue field of
  M over b_i is unramified at p, then the vertical inertia I_V lies in the cyclic inertia I_i
  of order e_i. Fibres over b_i are CM points (E_i = Q(i), Q(sqrt-3), Q(sqrt-6), maximal orders
  as Z[x] for the elliptic x), defined over class fields of E_i unramified outside {2,3}
  (Shimura reciprocity for the canonical model, level K_3). So |I_V| | gcd(4,6,2)=2; if 2, then
  I_V = 2-part of I_inf and = I_{-16/27}; their images in W = Gal(X_6/X_6^*) = (Z/2)^2 are
  <w_inf> and <w_{-16/27}>, distinct (Riemann-Hurwitz for a connected (Z/2)^2 cover of P^1
  branched at 3 points). Contradiction, so I_V = 1.
- (ii) Potentially good reduction: Grothendieck semistable reduction; B (dim 4, division) acts
  on the character group of the toric part (rank <= 2) => rank 0. Then A[3] rational + Serre's
  lemma + Neron-Ogg-Shafarevich.

## Step 2 (computation: scratch/h-b1/b1_checks.py -> b1_checks.output.txt; ~1 min CPU)
- A: reproduces h-map identities; disc/resultants of F,G,H supported on {2,3,5}; LC primes 7, 11·13;
  branch-point differences supported on {2,3}; H has no rational root (disc 10800, 43200, 43200
  non-squares), G no real root => J(u) is never a branch value for u in Q \ C. VERIFIED.
- B: |(O/3O)^*| = 72, image of Zhat^* = {±1} (order 2), with the two local normalizer indices 2:
  |Gamma'| = |N/(A_f^* K_3)| = 4·72/2 = 144 = 2^4·3^2 (h-map's "divides 4·72" refined; 144 <= 324).
  The local indices are STANDARD (division algebra: B_p^*/Q_p^*O_p^* = Z/2), not computed.
- C: elliptic elements in O: x4 (trd 2, nrd 2, disc -4), x6 (trd 3, nrd 3, disc -3), mu (trd 0,
  nrd 6, disc -24), x^e central for e = 4,6,2; Z[x] maximal in each CM field (fundamental
  discriminants), so E_i ∩ O is maximal; Atkin-Lehner images w2, w3, w6, pairwise distinct. VERIFIED.
- D: counterexample F1 for p in {331,337,347,349,353}: p | disc Q(sqrt(43p)). VERIFIED.
- E: 30 samples (contact / G-root / H-root / negative / generic; primes 331..5000): inertia order
  e/gcd(e,m) predicted by tame specialization equals the M_S(u) parity criterion in all 30. VERIFIED.
