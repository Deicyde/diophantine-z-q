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
