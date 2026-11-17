# mcheck-rc-app (fleet note)

Report: `docs/research/mcheck-rc-app.md`. Checks: `scratch/mcheck-rc-app/checks.py`, output in
`checks.out` (15/15 PASS). Log: `scratch/mcheck-rc-app/log.md`.

**Result.** I read Appendices E-G (tex L6825-10935) in full, in order, and mapped them in the
mcheck-rc-map row format, with a new "used in" column. With the appendices mapped, Theorem 5.3 (RC)
follows, as far as the map shows, from the cited prints plus Elliot's own steps. No error verdict, so no
verdict file. Each appendix result that sections 7-9 use is proved from earlier results and prints, and
the order of choices is not circular:

- even source, then rough companion, then (F.4);
- then the odd minimum delta_o (F.5)-(F.7);
- then the coefficient rules, the address construction and the family (3.9).

Checked numerically:

- v2 s_F = 2e;
- the norm -1 unit;
- E_q(0) = #E^h(F_q)/q;
- the (E.12)/(O.6) recurrences and closed forms;
- the shell parities (O.10);
- c_0 = |GL_4(F_3)|, v2 = 9;
- (O.12) and the trace identity;
- the F_2 network matrices;
- the mod-8 seed computation H[p^3] = eta^2 (a_p - 1)(a_p - p - 1)/4, plus the order-4 2-part of E_l(F_p).

**Largest own steps in the appendices:**

- odd theta forms and the unaveraged comparison (O.7) (App F, about 1,000 lines);
- the uniform Kato class and central normalization (K1)-(K3), (K14) (about 510 lines);
- the coefficient rules (O.9)-(O.12) (about 530 lines);
- the positive complex and calibration (E.3)-(E.9);
- the address networks (G.1a).

These were read once for structure, not certified line by line.

**GZ/TYZ.** No TYZ anywhere. In the appendices, CST 1.1 appears only at conductor one: the witness
D_w (L8269-8276) and (O.8) (L9437-9444). Both uses are qualitative (height zero if and only if
L' = 0). Cornut-Jetchev (reduction of CM points) is cited and is not a height formula. Nothing needs a
GZ/TYZ argument beyond a print.

**K3** (the only quantitative GZ use, (3.4) at L2427-2439). The report lists what CST 1.1 must say:

- (a) an unaveraged sum over Pic(O_c);
- (b) the same parametrization, so its constants cancel;
- (c) a factor c sqrt|disc K| u^2 2^{mu}, with u = 1 and mu = 0 here, and no other c- or K-dependence;
- (d) ĥ absolute, not normalized over H_c;
- (e) Heegner hypothesis and (c,N) = 1.

Odd factors are harmless, because c and disc K are odd. Any factor whose v2 grows with omega(c)
breaks (3.4) in both directions. Examples are 2^{omega(c)}, prod(p+1), #Pic(O_c), or an average.
Recollection (UNVERIFIED): CST's denominator is u^2 sqrt|Dc^2| with 2^{-mu(N,D)}, which is consistent.
This still needs one look at the print.

**Flagged tex comments:** L2832-2833 ("proof fragment", on ex:arith-finite-heegner; worth showing to
Elliot), and baseline-line notes at L3923, 4975, 7428, 7789-7790, 8222-8223, 8407.
