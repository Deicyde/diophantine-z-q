# pn-fix log

Task: apply docs/research/rv-pn-encoding.md (TB-1, F1, F2, nits) and docs/research/tyz-t1.md (T1) to
ZInQKernel/Hypotheses/TYZInputs.lean and ZInQKernel/RouteK/PropN.lean.

Start: branch wip/pn-fix at b0ad93ec (integrate-w26). lemmaN2 is already proved (no sorry) on this base,
so the new witness for L n = 0 will be sorry-free (the review's caveat 3 no longer applies).

## Step 1 (TB-1, F2: docstrings of TYZInputs.lean)
- Module docstring: TYZInputs = printed consequences + two standard unprinted facts (Hecke's
  continuation for I7; F4, [i] defined over Q(i), for the type of β). F5 kept only as the
  alternative route, credited to Prop 3.2(1) (L1255-1256) + Cox Lemma 9.3, "TYZ do not print it".
- GenusData: M = Z[i]-span in A(H'_n) of A[(1+i)^3] and Z(e) (e | n, e = 5, 7); Z(e) in A(H'_n) via
  L1321 (e = 5) and L2558 (e = 7, nit I1-Z7-docstring). β = restriction of one lifting β' (F2 argument).
- TYZInputs docstring: Hecke's continuation named (CM, not proved in TYZ); β uses F4; integrality
  phrase per nit L-integrality-thm12 (Theorem 1.2 dropped).
- Line locators fixed (I1-lines, TB-2): L1309-1310 -> L1308; L1325-1330 -> L1325-1329; L1328, L1329;
  Thm 3.3 L1299-1311 -> L1299-1309; Thm 3.5 L1356 -> L1354; L2506-2508 -> L2506-2507;
  L2514-2516 -> L2514-2515.
- Also (step 4 nits, same file): eps_53 cites multiples1 (L1919-1921), L2105-2108, and notes lemmaN2
  needs it (nit F4); beta_seven notes exact form needs integer g (g-beta7-mod4/TB-4/F3); LemmaTwoEight
  docstring is a congruence with the m = 3 w_K remark (i2-b1).
- strip_compare vs HEAD: code identical. lake build ZInQKernel.Hypotheses.TYZInputs: OK.

## Step 2 (F1: witness for L n = 0)
- Added to Witness (PropN.lean): Pw_congr, Pw_fst, Sw, Pw_eq_sub, Sw_fst, Φw (= λ ∘ pr₂), Φw_Zw,
  Φw_Sw (the key identity), witnessData₀ (Z := update Zw n (Sw L n), P := update (Pw L) n 0),
  genusData_nonempty_iff_parities (for L 1 = 1, L n = 0: Nonempty (GenusData L n) ↔ the two parities;
  → is lemmaN2 + finalStep) and genusData_nonempty_of_parities (the task's theorem, via the iff).
- The review's construction worked as stated. One adjustment: k = −N/2 − x.re + x.im (2i ≡ −2 mod 2+2i);
  the review's −x.im differs by a multiple of mk 4 = 0, so either works. The (2+2i)-multiple is
  ⟨−x.im, a/2⟩. Not sorry-dependent: lemmaN2 is proved on this base.
- tyzInputs_iff (review fix item 5) not added (outside step 2's list); the docstring says so.
- Witness section docstring rewritten; module docstring lists the new theorems.
- print_axioms.lean: +3 lines (genusData_nonempty_iff_parities, genusData_nonempty_of_parities,
  Pw_congr) → 91 entries, all [propext, Classical.choice, Quot.sound] (scratch/pn-fix/print_axioms.txt).
- lake build ZInQKernel: OK (9925 jobs), no warnings in the new code.

## Step 3 (T1)
- TYZInputs.lean module docstring: T1 bullet now records tyz-t1's result (Thm 3.3 holds as printed;
  constant independent of d₁ for fixed d₀, from Thm A.9 L3062-3077, checked on 30 n / 73 pairs via
  Heegner points on X₀(32)); external residue = Thm A.9 (YZZ made explicit by TYZ, deduction omitted
  L3079). "Reviews" paragraph updated; mentions genusData_nonempty_iff_parities.
- PropN.lean module docstring: same T1 statement; cites rv-pn-encoding.
