# mcheck-rc-map (fleet note)

Report: `docs/research/mcheck-rc-map.md`. Checks: `scratch/mcheck-rc-map/checks.py`, output in
`checks.out` (43/43 PASS). Log: `scratch/mcheck-rc-map/log.md`.

**Result.** Sections 7-9 (tex L1760-5744) were read in full and mapped step by step. As far as the map
shows, Theorem 5.3 (RC) follows from the cited prints plus Elliot's own steps. No step was found wrong,
so there is no error verdict and no verdict file. The skeleton:

- w = -1 comes from 2-parity [dd].
- The odd theta coefficient a_M(D) is the Kummer image of the genus point (Cornut-Jetchev), so a
  visible coefficient gives a simple zero (CST 1.1, (O.8)).
- Branch 1 (empty unit): D=1 is visible, which gives RC.
- Branch 2: the binary family (3.9) gives a uniform upper bound B at x != 0. Determinant clearing (5.9)
  and the Boolean missing-address argument (5.11) then rule out u~_0(0) = 0. The base-zero lemma (CST,
  conductor one) turns this into L'(E/K,1) != 0, so ord L(E,s) = 1.

**GZ/TYZ.** No TYZ anywhere in sections 7-9 or Appendices E-G. GZ enters only as CST Thm 1.1 (four
uses: (3.4), the witness D_w, (O.8), base-zero) and Kolyvagin Thm 1 (lem:forward-rank). Nothing needs a
GZ/TYZ argument beyond a print. Sections 8-9 contain Elliot's own 2-adic Heegner/Kolyvagin machinery
(finite descent L2834-3393; switches and the uniform bound (5.5) at L4747-5205). That is his own work
to check, not a citation.

**Part 2.** The opening reduction ends at L1823 (the dependency-order paragraph). Every step is OK.
Locators for BCDT, Milne MF and DD are UNVERIFIED (no network). One presentation gap is filled: the
outline omits the empty-unit branch and does not say where the Selmer hypothesis enters (w = -1 and
s_2(E/K) = 1). As a supplement I checked the branch split and the final contradiction (5.10)-(5.11);
both are OK.

**Open / next.**
- K3: (3.4) relies on CST 1.1 having no c-dependent factor other than c sqrt abs(disc K). That needs
  checking against the print; an extra 2^{omega(c)} would break the 4 omega balance.
- K2: the highest-value next reads are ex:limits-uniform-lower-bound (L4909-5205),
  ex:arith-finite-heegner (L2834-3393) and the unread Appendices E-G (about 4,100 lines).
- K6: leftover "proof fragment / baseline line" tex comments (L2832, L3923, L4975) are worth showing to
  Elliot.
