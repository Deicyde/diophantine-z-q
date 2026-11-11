# rv-barrier log

Task: adversarial review of Theorem G (docs/research/el-gadget.md §1, column form, E1/E2)
and Lemma G (docs/research/el-special.md §4, C3/C5).

## Step 1. Read both notes (done)
Objects under review:
- TG-a dichotomy, TG-b transfer, TG-c fibres with F_m-points, Theorem G, column form, Stein remark,
  global-soundness paragraph (el-gadget §1); column property (§2).
- Lemma G, Cor 1-4, scope paragraph (el-special §4); C3 (route M), C5 (Cor 2).

## Step 2. The soundness the barriers assume (inspection of Lean, no Lean run)
- `PoleSoluble B` (ZInQKernel/Hypotheses/Pole.lean:52): rational zero of `polePoly`; witnesses
  bits b (b²=b), e, z, r1, r2, w with r1² = A(A²-e²), r2² = A(A²z⁴-e²H²), w·eHz = 1, A = mB,
  H = A(A-B²), m = product of (1-2b0)...(1+12b5) (a unit at p ∤ 2730).
- Fibre over B: conic in (e,r1), and over each e a genus-1 quartic in (z,r2). Not RC: consistent with
  Theorem G (no contradiction from the existing gadget).
- Soundness proof `poleSystem_no_negative_odd_valuation` (Multiplication/Certificate/Parity.lean:93)
  uses only padicValRat identities (min rule, parity of 2v(y)); the same argument works verbatim for
  Q_p-witnesses. So the current soundness is LUS with p0 = 13 (p ∤ 2730). VERIFIED (inspection).
- `pole_step` (Assembly/Local/TestDivisibility.lean:225) consumes only `¬(v_p(B)<0 ∧ odd)` at p > 13.

## Step 3. Proof audit (paper; details go to the note)
Theorem G:
- (G-a)(ii)=>(i) needs a smooth proper model over Z[1/N] on which f is a morphism to P^1 and div(1/f)
  has no vertical part; then even multiplicities => 1/f = u h^2 locally (regular => locally factorial).
  OK after resolution + spreading out. (i)=>(ii) Lang-Weil + Hensel + Chebotarev: OK. Points may land in
  the boundary of an open X: avoided because the germ is not inside the boundary. OK.
- (G-b)/(G-c): GHS is a theorem over function fields of curves over alg. closed fields, not over
  Qbar((s)). Repair: replace the formal germ by an algebraic curve Gamma (general complete intersection
  through a general point of the odd component C, transversal to C); then GHS over Qbar(Gamma) gives a
  section, no Artin approximation/Eisenstein needed (evaluate the section at Q_p-points of Gamma with
  t = p, p split in the field of definition). This is exactly el-special's Lemma G argument.
- "RC generic fibre" must mean: geometrically integral generic fibre whose smooth proper model is RC;
  GHS gives a point of the proper model; to land in the (open, possibly singular) gadget fibre use
  density of sections (Kollar-Miyaoka-Mori + GHS: X(K) Zariski dense for smooth proper RC X over
  K = k(curve), k alg. closed char 0). Counterexample to the loose reading: affine cone over a plane
  cubic minus vertex is "rationally chain connected" via the vertex only; with a guard removing the
  vertex the fibre has no RC model. Repair = the definition above.
- Stein remark: "soundness lives on square-class conditions" is an overreach; the finite part can be any
  finite cover with even ramification along the bad divisor (e.g. z^4 = f, non-abelian covers).
  The genus>=1 conclusion survives.
- Global paragraph: premise "smooth proper RC X" is false for the real total space (the data space
  contains points of E/K0, so X fibres over a non-RC base). Conditional exclusion of global soundness
  needs fibration-method conjectures over a base with abelian-variety factors, not just CT's RC
  conjecture. Scope gap.
- Column property: "bad at one p-integral q => bad at all q" correct: v(R0) odd >= 1 and q p-integral
  gives v(a)=0 (maximal v(R)); v(R0) < 0 gives v(B) <= v(R) < 0 for every q. OK.
Lemma G:
- gamma0 in C5 is at q = infinity, i.e. outside affine P; proof only needs gamma0 smooth on the closure
  of Gamma (Hensel on the closure, gamma with t = p is not a boundary point). Repair: state it so.
- Cor 1 needs the same RC definition + density repair; Tsen part needs a smooth point (degenerate
  quadric whose only point is the vertex).
- Cor 3 "uniform" = a Q-variety W -> P dominant with RC generic fibre and a P-morphism W -> Y. Families
  over finite covers of P (algebraic, multi-valued formulas; thin sets) are not covered.

## Step 4. E1 rerun (scratch/rv-barrier/e1_rerun.py, independent code)
Inputs: 30 primes (every other prime in [331,1000)), B = c/p (c<40), m in first 16 divisors of 2730;
G5 with B = R0/p^2, R0 = c p. Outcome: G1 witnesses at exactly the 10 sampled primes p = 1 mod 4
(0 mismatches with the Hilbert-symbol prediction (-1/p)); G2, G3, G5 witnesses at 30/30 primes.
Matches el-gadget E1 (28/59, 59/59). VERIFIED.

## Step 5. E2 rerun (scratch/rv-barrier/e2_rerun.py, independent code, tests in K0 = Q(sqrt2))
Inputs: 30 bad data (10 each with v_p(R0) = 1, 3, -1; p = prime(70..300); one test with v_p = -1..-3),
20 q each with p-power denominators up to p^4 and p-divisible numerators. Outcome: 600/600 pairs bad.
(el-gadget sampled only v_p(R0) = 1 with rational tests.) Column property VERIFIED on the sample;
the paper argument in Step 3 covers all cases.

## Step 6. C3 rerun (scratch/rv-barrier/c3_rerun.py, independent code)
(a) 30 random (B, m0, lambda): explicit witnesses on C_beta (torsion) and C_{beta m(m-B)} with
x in beta Q*^2: 30/30. (b) 30 random (p in prime(67..400), B = c/p, lambda with v_p(lambda) in -3..3):
max v_p(k) = -1, so v_p(m) <= -2 < v_p(B). Paper proof of (b) for all lambda: v_p(g) = -1, v_p(beta) = 1,
v(1/(beta l)) = -1 - v(l) and v(l) have different parity, so v(t) = min(...) <= -1, v(k) <= -1.
VERIFIED. Route M is a rational (RC) family over the B-line: its failure is the case Lemma G predicts.

## Step 7. C5 rerun (scratch/rv-barrier/c5_rerun.py, independent code)
Inputs: 30 = p in {10007, 100003, 1000033} x c in C x M in {0,1,2,3} (cycled), random q0 and D_j in Q(sqrt2).
Outcome: v_p(B) = 15 - 52M for M >= 1 and v_p(B) = -11 for M = 0, 30/30 matches. VERIFIED.
New: M = 0 (q fixed, p-integral) already gives an odd pole (order 11) along n = c + lam, so Cor 2 does not
need q -> infinity; gamma0 = (n = c, q0, D) is then a point of the affine P itself (removes the
boundary-point repair for Cor 2). Model check: tests C_j = D_j/F as in TestDivisibility.lean (hC).
