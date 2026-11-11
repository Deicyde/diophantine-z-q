# rv-h-b1 work log

Object under review: origin/wip/h-b1 (commit d7d8d78f) docs/research/h-b1.md, scratch/h-b1/.
Manuscript: diophantine_zq.tex in this worktree (last touched 97cec7fd, "November 5"), = N5.

## 1. Inputs read
- h-b1.md (363 lines), scratch/h-b1/b1_checks.py and its saved output (sections A-E).
- N5 L377-570 (Theorem 4.1 setup, integral model L441-507, pullback L509-523, K and A L524-530,
  conjugates and W_0 L532-566), N5 L800-857 (L814 Raynaud step, L847-850 p > R).
- N5 L436-438 itself already says Y_3 "with all its determinant components"; N5 L475-477 says
  the b11 quotient "represents exactly the full-three moduli problem, so its generic fiber is Y_3".

## 2. Rerun of scratch/h-b1/b1_checks.py
- Copied verbatim to scratch/rv-h-b1/b1_checks_rerun.py; ran with ~/pyenv/bin/python -I (0.7 s CPU).
- Output scratch/rv-h-b1/b1_checks_rerun.output.txt is byte-identical to h-b1's saved output.
- What the script does NOT check: maximality of O (asserted in N5 L405); local normalizer
  index 2 (printed as "standard"); completeness of the list of elliptic types in M9 (it only
  finds one element of each wanted (trd,nrd)); §E computes inertia FROM the Prop. TS formula, so
  it checks the case analysis of PR(i) steps 2-3, not Prop. TS itself.

## 3. Uses of good reduction / the model in N5 (grep, lines < 1200)
- grep "integral model|proper model|good reduction|stable model|X_{35}|universal abelian|
  smooth projective|semistable|potentially good": hits L443, 464, 473-474, 483, 529, 558,
  596 (CM elliptic curve, unrelated), 740 (p-adic Hodge, unrelated), 753, 781, 817, 849.
- Locator error in h-b1 §5 (and in the task text): the conjugate good-reduction sentence is
  N5 L557-558, not L563-566 (L563-566 is the Milne Hodge-endomorphism paragraph).
- h-b1 §5 omits two downstream uses: L753 ("unramified outside T ∪ {ℓ}, since there ... A has
  good reduction") and L781 ("L_v/Q_p unramified and A has good reduction", p ∉ T ∪ {3,5}).
  Both are uses of the L529-530 statement at primes outside T; Lemma PR(ii) covers them
  (3 ∈ S ⊂ T). So h-b1's "nothing downstream of L530 uses the integral model" is true in
  substance (they use only the L529-530 conclusion) but the table is incomplete.
- L814: adjoins A[3] (A[5] at p = 3) and applies Raynaud's criterion [Silverberg-Zarhin 3.5]
  for semistability: no model used. CONFIRMED h-b1's claim.
- L848-849 "the surface has good reduction" for p > R: p may lie in supp M_S(u) ⊂ T, so this
  needs good reduction also where K ramifies; PR(ii) (all v ∤ 3) gives it.

## 4. scratch/rv-h-b1/rv_checks.py (run once, 1.2 s CPU; output rv_checks.output.txt)
- R1: det(trd(e_r e_s)) = -36, Hilbert symbols (2,-3)_p = -1 exactly at p = 2,3 => O maximal of
  disc 6 (N5 L405 claim VERIFIED). mu = 2j+ij has mu^2 = -6; Trd(mu^-1 x ybar) matrix equals N5's
  displayed matrix, det 1 (VERIFIED).
- R2: all elliptic normalizer types (primitive x in O, nrd | 6, finite order mod Q^*), box [-6,6]^4:
  (|t|,n) = (0,1) D=-4 W:1; (0,3) D=-12 but Q(x)∩O = Z[zeta_3] D=-3, W:w3; (0,6) D=-24 W:w6;
  (1,1) D=-3 W:1; (2,2) D=-4 order 4 W:w2; (3,3) D=-3 order 6 W:w3. (0,2) (D=-8) absent:
  Q(sqrt-2) does not embed in B because 3 splits in it (STANDARD embedding criterion).
  => every elliptic CM order in O is maximal, discriminants {-3,-4,-24}, supported on {2,3}.
  Stronger than M9: step 2 of NV needs only conductor prime to p, which holds for EVERY
  elliptic point, independent of which branch value carries which type.
- R3: chi(O^1/±1) = -1/3 = 4 * chi(2,4,6) = 4 * (-1/12). RH: X_6 -> P^1_j (deg 4, e=2,2,2) g=0;
  component of Y_3 -> P^1_j (deg 72, e=4,6,2) g=4, agreeing with index 18 torsion-free subgroup
  of O^1/±1 (2g-2 = 18/3 = 6).
- R4: |(O/3O)^*| = 72, |(O/3O)^1| = 36, |Gamma'| = 144 = 2^4 3^2, two geometric components
  (pi_0 = (Z/3)^*), each of degree 72 over P^1_j. M3 VERIFIED (local normalizer index 2 is STANDARD).
- R5: F1 = y^2 = p j(27j+16) is the quadratic twist by p of y^2 = j(27j+16), whose j=1 fibre
  Q(sqrt 43) (disc 172) is unramified at p. Residue fields of F1 over its branch points are Q.
  So F1 shows: (a)-(c) of Beckmann do not imply (d), and unramified branch fibres (NV step 2)
  do not imply (d) either; F1 has I_0 = I_{-16/27} = whole group, which NV's step 4 excludes for Y_3.
- R6: no elliptic power x^k (non-central) lies in Q^* K_3: ramification index at an elliptic point
  = order in B^*/Q^* (consistent with neatness, N5 L468-470).

## 5. Step-by-step check of Prop. TS and Lemma NV (paper review; no computation)
- Prop. TS. Normalization Z is finite (R = Z_(p)^sh is excellent). Z normal over the regular
  2-dim P^1_R => flat; unramified at codim-1 points off D => étale there; purity (SGA 1 X 3.1)
  => étale off D. Case 1: section misses D => pullback finite étale over strictly henselian R =>
  split => K_{j0} ⊂ k_p, unramified. Case 2: Spec R -> P^1_R factors through O^sh_{P_i}; local
  model ⊔ O^sh[z^{1/e_i}] (Abhyankar with only D_i through P_i, after NV); z -> p^m w, w ∈ R^*
  has an e_i-th root => fibre ∏ k_p(p^{1/(e_i/g)}), g = gcd(e_i,m). HOLDS.
- NV step 1: tameness along V(p): e prime to p and residue extension of F_p-bar(j) separable
  because its degree divides 144. HOLDS.
- NV step 2: G(A_f) = G(Q)_+ K_0 (strong approximation for B^1, nrd(K_0) = Zhat^*, Q^*_{>0}Zhat^*
  = A_f^*) => each point over b_i is in the Gamma'-orbit of some [tau,1]. Reciprocity: art(s) fixes
  [h,1] when r(s) ∈ K_3; r(s) ∈ prod_{l≠3} O_{E,l}^* ⊂ K_3 because Q(x)∩O is maximal at every l
  (R2). So E(y0) ⊂ ray class field of conductor 3^∞ of E, Q(y0) unramified at p >= 5. HOLDS.
  Needs only conductor prime to p (R2 shows all elliptic CM orders maximal anyway).
- NV step 3: I_P (P over P_i) = Galois group of O^sh_{Z,P} over O^sh_{P_i} (residue field of P_i is
  F_p-bar). Kummer model (O^sh[z^{1/n},p^{1/n}])^H: unique branch over z=0; with I_Q = image of
  mu_n×1, [I_P:I_Q] = residue degree of that branch over k_p. Closure of Q_i is Spec A', A' local
  finite birational over R (k(Q_i) = k_p by step 2) => strictly henselian, unibranch => degree 1
  => I_P = I_{Q_i}. Going-down (Z flat) gives a vertical prime q ⊂ P; I_q ⊂ I_P (σ ≡ id mod q
  => mod P). HOLDS.
- NV step 4: from (∞, e=6) and (-16/27, e=2): |I_V| | 2. If I_V = <g>, g ~ g_∞^3 maps to σ_∞,
  g ~ g_{-16/27} maps to σ_{-16/27}; W abelian => σ_∞ = σ_{-16/27}, contradicting g(X_6) = 0
  (R3: three distinct nontrivial generators). Images of inertia = inertia (char 0 horizontal
  divisors; k_p(X_6) = Q(X_6) ⊗ k_p is a field since X_6 is geometrically connected). HOLDS.
  Robust to the Baba-Granath labelling: any pair of branch points works (order-4 point:
  g_0^2 maps to 1, so pairing it with either other point also gives a contradiction).
- F1 (R5) has I_0 = I_{-16/27} = Z/2: the W-step is exactly what fails there. Consistent.

## 6. Independent check on the W-layer (rv_checks.py R7; 30 samples, p in [5,400), < 1 s)
- Source of the model: docs/research/rv-h-cm.md §2 (Elkies §3.1-3.2 constants c0 = -1, c1 = 3,
  rederived there by reciprocity): with t = 1 + 27j/16, Q(X^6) = Q(j)(sqrt(-(27j+16)), sqrt(j)).
  Constants are {-1,3}: X_6 -> P^1_j has no vertical ramification at p >= 5. This is independent
  confirmation of NV's conclusion on the W-quotient (Elkies fixes c0,c1 by conductors of X_0^*(l)).
- R7: for 30 (j0,p) (meet 0 / meet -16/27 / meet ∞ / generic, multiplicity 1-4), nfdisc of the
  actual biquadratic fibre field vs Prop. TS prediction (ramified iff odd contact multiplicity,
  e = 2 on this layer): 30/30 agree.
- Limitation: on the 144-layer (full Y_3) no explicit model is available here, so NV's conclusion
  above the W-layer rests on the proof alone (reviewed in §5, holds).
- rv-h-cm §1.3 also confirms the labelling j = 0, ∞, -16/27 <-> D = -4, -3, -24 with W-stabilisers
  w2, w3, w6, matching R2.

## 7. Deliverables
- docs/research/rv-h-b1.md (verdict table, sections 1-9, repairs list §8); N5 locators in it
  rechecked by grep (L414-416 matrix, L423-424 K_3, L434-435, L454-459, L466-470, L476-477,
  L557-558, L753, L781, L849).
- .fleet/rv-h-b1.md. Task complete; no Lean run was needed.
