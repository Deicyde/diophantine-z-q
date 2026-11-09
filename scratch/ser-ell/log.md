# ser-ell log (audit of nt-h §4.2, route 1)

## Step 0 (setup)
- No earlier log; fresh start from nt-h commit 9411a69.
- Read nt-h.md §4 and manuscript lines 404-870 (descent, rho_l, conductor bounds, transfer).
- Literature access: only arXiv. Khare-Wintenberger Invent. 178 (2009) I and II are NOT on arXiv
  (API search: only math/0412076, the 2004 preprint, which has no Invent numbering).
  Serre 1987 Duke, Raynaud 1974, Faltings 1983, Zarhin 1985, MW95, Carayol 1989: not on arXiv.
- Downloaded (to /tmp, untrusted, read only): Gee, "Serre's modularity conjecture" (arXiv 1402.7197,
  Luxembourg notes); Buzzard-Diamond-Jarvis arXiv 0810.2106 (v5); Dieulefait survey arXiv 0712.1317;
  KW preprint math/0412076; Zywina arXiv 1910.14171.

## Step 1 (first pass, all seven steps)
Preliminary verdicts (to be refined):
- S1 residual irreducibility: CORRECT as mathematics (End(A_{L'}) = O since O maximal and all
  endomorphisms are over L c L'; O/l = M2(F_l) for l not dividing 6; semisimple + scalar commutant of
  the multiplicity space W gives absolute irreducibility; Jordan-Hoelder gives (rbar|G_{L'})^ss = W (x) k).
  Citation: Zywina Thm 2.4 (MW95) to be read.
- S2 oddness: CORRECT (r(c) eigenvalues 1,-1 distinct mod l > 2).
- S3 weight: CORRECT after repairs. nt-h's text works over O_{L_v}, but on G_L the representation is
  the Tate action twisted by beta^{-1}; the Tate action holds on G_{L'} (L' unramified at l since beta
  is unramified outside T). Missing: lattice -> subquotient step; descent to Z_l unnecessary because
  k(rbar) depends only on rbar|I_l and I_{L'_w} = I_l. Determinant claim needs an argument.
- S4 level: CORRECT, more simply: manuscript's bounds apply verbatim to rbar (upper groups above U_0
  act trivially on T_l(A) hence on A[l]); no need for "reduction does not increase conductor"
  (attribution to Serre 1987 §1.2 doubtful anyway).
- S5 KW strong form: primary UNCHECKED (not readable). Secondary: Gee 1402.7197 says weak form
  proved by "Khare, Wintenberger, and Kisin" [KW I, KW II, Kisin Invent 178 (2009) 587-634], and
  weak => strong known for F = Q (Ribet, Edixhoven/Fontaine/Deligne, ...). Dieulefait 0712.1317
  line 280: Kisin's 2-adic results "cover also the remaining cases of Serre's conjecture, i.e. the
  cases of even level". FINDING: nt-h cites KW only; N(rbar) may be even (2 in T, beta may ramify
  at 2, A may be bad at 2), so Kisin 2009 must be in the citation.
- S6 pigeonhole: CORRECT once one pigeonholes over pairs (f, conjugate embedding) and notes t_p is
  integral at every prime (trace of a compact-group representation) -- nt-h's "with all their
  Galois conjugates" covers this.
- S7 conclusion: CORRECT; downstream needs only a common constituent with J1(N_f), N_f <= QM^2.

## Step 2 (sources and computations)
- Zywina arXiv 1910.14171, Theorem 2.4 (label T:MW; numbering recomputed from the TeX counters:
  Prop 2.1, Thm 2.2 Faltings, Prop 2.3, Thm 2.4 MW): for l >= c max([L:Q], h(A))^gamma, A[l] is a
  semisimple F_l[G_L]-module and End(A_L) (x) F_l = End_{G_L}(A[l]); proof cites MW95 §1 Cor 1, 2.
  VERIFIED as Zywina's statement. Step 1 citation fixed.
- BDJ arXiv 0810.2106v5: Conjecture 3.12 (W(rho) = modular weights, for modular rho) and Theorem 3.15
  (it holds for K = Q; proof via Deligne/Fontaine (Edixhoven Thms 2.5, 2.6), Mazur's principle,
  Edixhoven 4.5, Gross). Table in the proof: b = 1 (cyclotomic quotient) case, W contains V_{0,1}
  (weight 2) unless tres ramifiee; irreducible case b = 1 gives {V_{0,1}, V_{0,l}}. Also: "If rho is
  modular of weight 2 and level prime to l then rho|G_{Q_l} arises from a finite flat group scheme".
  Numbering is the arXiv v5 numbering (computed from counters: 3.12, 3.15).
- Gee 1402.7197 (§ on statement): weak Serre proved by Khare, Wintenberger AND Kisin
  [Invent 178 (2009) 485-504, 505-586, 587-634]; weak => strong known for Q (Deligne, Fontaine,
  Edixhoven; p = 2 cases by KW+Kisin).
- Dieulefait 0712.1317, line 280: Kisin's characteristic-2 lifting results "cover also the remaining
  cases of Serre's conjecture, i.e., the cases of even level". => citation gap in nt-h step 5.
- checks.py (own code, no nt-h import), output checks.output.txt:
  A. O = Z[i,(1+j)/2] closed, det Trd-Gram = -36 => reduced disc 6, O/l = M2(F_l) for l not | 6.
  B. Serre's recipe on all Raynaud e=1 inertia types with det = omega: weight 2 always
     (l prime in [5,120)); tres ramifiee would give l+1; det 1 or omega^2 would give l or l+2.
     (Orientation sub-etale/quotient-connected splits over Z_l^ur, so it is in the 'ss' cases.)
  C. det rbar|I = omega*eta, eta quadratic, in {1, omega, omega^2}: eta|I = 1 forced iff l > 3.
- Manuscript lines 858-966 re-read: transfer uses only "common constituent of V(A) and V(J1(N))"
  and N <= QM^2. Constants unchanged under route 1: CORRECT.
- Convention: f vs fbar (Hecke T_p vs T_p^*, homology vs cohomology) harmless: the pigeonhole set
  and the constituents of V_l(J1(N_f)) are closed under f -> fbar.

## Step 3: findings list (for the report)
F1 (moderate, citation/trust base): step 5 needs Kisin, Invent 178 (2009) 587-634, for even N(rbar);
   2 is always in T and nothing makes N(rbar) odd. Also the strong form's level/weight optimization
   (Ribet 1990, Carayol 1989, Diamond 1995, Edixhoven 1992, Mazur's principle) belongs to the
   citation unless KW's published statement already has level N(rbar), weight k(rbar) (UNCHECKED).
F2 (minor): step 3 argues over O_{L_v}; on G_L the representation is the Tate action twisted by
   beta^{-1}|G_L. Must use L' (unramified at l since beta unramified outside T) or I_l directly.
F3 (minor): step 3 "finite flat over Z_l" via "Raynaud §3.3 uniqueness": descent unneeded (k depends
   on rbar|I_l only, I_l = I_{L'_w}); what is needed is Raynaud's inertia-exponent theorem (§3.4)
   and "finite flat => peu ramifiee"; plus lattice -> subquotient closure.
F4 (minor): determinant claim unproved in nt-h; repair = check C (l > 3) or crystalline det.
F5 (minor): step 4 cites "Serre 1987 §1.2" for a(rbar) <= a(r) (attribution doubtful, UNCHECKED);
   unnecessary: the manuscript's bounds apply verbatim to rbar.
F6 (minor): step 6 bookkeeping: pigeonhole over pairs (f, embedding), t_p integrality.
F7 (minor, framing): "no p-adic Hodge theory left" / "one theorem from 2009": KW and Kisin use
   p-adic Hodge theory internally; the removal of A009/A010/Conrad is a removal of direct uses only.
