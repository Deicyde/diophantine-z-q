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
