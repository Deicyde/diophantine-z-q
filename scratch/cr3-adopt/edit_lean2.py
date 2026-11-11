def edit(p, pairs):
    s=open(p).read()
    for a,b in pairs:
        assert s.count(a)==1, (p, a[:70])
        s=s.replace(a,b)
    open(p,'w').write(s)

edit('ZInQKernel/RouteK/Rank5b/Row5b.lean',[
("""**Trust statement.** CR₃^5b is not proved in Lean. It follows from Tian–Yuan–Zhang
(Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*, Asian
J. Math. 21 (2017), no. 4, 721–774: Theorem 3.5 and the argument of the proof of Theorem 3.5(2) in
§3.3, as completed in `docs/research/nt-tyz.md` §4, through Smith's row 5b)
together with Gross–Zagier–Kolyvagin, as follows (`docs/research/tyz-5b.md` §§1, 3):""",
"""**Trust statement.** CR₃^5b is not proved in Lean. Lean derives it from
`Rank.CertifiedRankTYZClRk` (through `CertifiedRankTYZ` and `certifiedRank5b_of_certifiedRankTYZ`;
see `docs/research/cr3-trust.md`). It follows from Tian–Yuan–Zhang
(Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*, Asian
J. Math. 21 (2017), no. 4, 721–774: Theorem 3.5 and the argument of the proof of Theorem 3.5(2) in
§3.3, as completed in `docs/research/nt-tyz.md` §4, Proposition N, through Smith's row 5b)
together with Gross–Zagier with an auxiliary imaginary quadratic field, as follows
(`docs/research/tyz-5b.md` §§1, 3):"""),
("""* Gross–Zagier and Kolyvagin (manuscript Lemma 5.5): `rank C_n(ℚ) = 1`;
* then `dim C_n(ℚ)/2C_n(ℚ) = 2 + 1 = 3 = dim Sel₂(C_n)`, so the Kummer map is onto `Sel₂(C_n)`""",
"""* Gross–Zagier (Invent. Math. 84 (1986)), over an imaginary quadratic field with the Heegner
  hypothesis and `L(C_n^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein): `rank C_n(ℚ) ≥ 1`; Kolyvagin's
  published papers enter only inside Tian–Yuan–Zhang, and the manuscript's Lemma 5.5 is not used;
* then `dim C_n(ℚ)/2C_n(ℚ) = 2 + rank ≥ 3 = dim Sel₂(C_n)`, so the Kummer map is onto `Sel₂(C_n)`"""),
])

edit('ZInQKernel/RouteK/Selmer/Covering.lean',[
("""`rank C_d(ℚ) ≥ 1` (and then to `rank = 1`, `Ш[2] = 0`). This is provided by either of:

* Kriz's 2-converse theorem""",
"""`rank C_d(ℚ) ≥ 1` (and then to `rank = 1`, `Ш[2] = 0`). Lean derives CR₃^Sel from
`Rank.CertifiedRankRk` (`Rank.certifiedRankSel_of_certifiedRankRk'`, with RK9 and Mordell–Weil
proved), and that from `Rank.CertifiedRankTYZClRk`; see `docs/research/cr3-trust.md`. The positive
rank is provided by:

* for exactly the 2-adic shape `d ≡ 5`, `|a| ≡ 7 (mod 8)` assumed here, Tian–Yuan–Zhang
  (Asian J. Math. 21 (2017): Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3, as
  completed in `docs/research/nt-tyz.md` §4, Proposition N), which gives
  `ord_{s=1} L(C_d, s) = 1`, and Gross–Zagier (Invent. Math. 84 (1986)) with an auxiliary
  imaginary quadratic field (Bump–Friedberg–Hoffstein; `docs/research/pc-audit.md` RK7), which
  gives `rank C_d(ℚ) ≥ 1`; Kolyvagin's published papers enter only inside Tian–Yuan–Zhang.
  Tian–Yuan–Zhang's hypothesis is reached through Corollary 4.4 and Theorem 3.6 of
  `docs/research/tyz-5b.md` (`RouteK.Rank5b.det_M5b_eq_one`, `RouteK.Rank5b.det_M5b_eq_T5b`) and
  Rédei's formula (`RouteK.Redei.redeiFormula`), all proved in Lean.
* Kriz's 2-converse theorem, an alternative route that is not needed (a preprint;
  `docs/research/nt-tyz.md` §5.1): Kriz's 2-converse theorem"""),
("""  giving `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0`;
* or, for exactly the 2-adic shape `d ≡ 5`, `|a| ≡ 7 (mod 8)` assumed here, Tian–Yuan–Zhang
  (Asian J. Math. 21 (2017): Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3, as
  completed in `docs/research/nt-tyz.md` §4, Proposition N), which gives
  `ord_{s=1} L(C_d, s) = 1`, and Gross–Zagier–Kolyvagin, which gives `rank C_d(ℚ) = 1` and
  `Ш(C_d)` finite (`docs/research/tyz-5b.md`); then `dim Sel₂ = 3 = 2 + 1` forces `Ш[2] = 0`.
  Tian–Yuan–Zhang's hypothesis is reached through Corollary 4.4 and Theorem 3.6 of
  `docs/research/tyz-5b.md` (`RouteK.Rank5b.det_M5b_eq_one`, `RouteK.Rank5b.det_M5b_eq_T5b`) and
  Rédei's formula (`RouteK.Redei.redeiFormula`), all proved in Lean.
""","""  giving `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0`.
"""),
])

edit('ZInQKernel/RouteK/Rank5b/Sec3/TYZ.lean',[
("""  (Proposition N; reviewed in `docs/research/rv-nt-tyz.md`). For squarefree `n ≡ 5 (mod 8)`: if""",
"""  (Proposition N; reviewed in `docs/research/rv-nt-tyz.md` and `docs/research/rv-prop-n.md`).
  For squarefree `n ≡ 5 (mod 8)`: if"""),
("""  satisfies the Heegner hypothesis and has `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein;
  Murty–Murty); `C_d` is modular""","""  satisfies the Heegner hypothesis and has `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein);
  `C_d` is modular"""),
("""Under `d % 8 = 5` and `Squarefree d`, `CertifiedRankTYZ` is equivalent to `CertifiedRank5b` by
Theorem 3.6 (review: `docs/research/rv-cr5b-sec3.md`). -/""",
"""Under `d % 8 = 5` and `Squarefree d`, `CertifiedRankTYZ` is equivalent to `CertifiedRank5b` by
Theorem 3.6 (review: `docs/research/rv-cr5b-sec3.md`). Lean derives it from
`Rank.CertifiedRankTYZClRk` (`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`,
`Rank.certifiedRankTYZ_of_certifiedRankTYZRk'`); see `docs/research/cr3-trust.md`. -/"""),
])

edit('ZInQKernel/RouteK/Rank5b/Sec3/RedeiStatement.lean',[
("""  and with `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein or Murty–Murty;""",
"""  and with `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein;"""),
])

edit('ZInQKernel/RouteK/RankVariants.lean',[
("""  `RouteK.Rank.CertifiedRankRk` (Kriz's 2-converse, or Tian–Yuan–Zhang with Gross–Zagier);""",
"""  `RouteK.Rank.CertifiedRankRk` (Tian–Yuan–Zhang with Proposition N, and Gross–Zagier with an
  auxiliary field; Kriz's 2-converse is an alternative that is not needed);"""),
("""  formula `RouteK.Rank5b.RedeiFormula` is proved, `RouteK.Redei.redeiFormula`).
-/""","""  formula `RouteK.Rank5b.RedeiFormula` is proved, `RouteK.Redei.redeiFormula`). Lean derives
  every other form of CR₃ from it; the trust statement is `docs/research/cr3-trust.md`.
-/"""),
])

edit('ZInQKernel/RouteK/Rank5b.lean',[
("""point; a consequence of Tian–Yuan–Zhang and Gross–Zagier–Kolyvagin) and 22P, there is an integer""",
"""point; a consequence of Tian–Yuan–Zhang with Proposition N, and Gross–Zagier with an auxiliary
field, see `docs/research/cr3-trust.md`) and 22P, there is an integer"""),
("""CR₃^5b implies CR₃^Sel by tyz-5b Corollary 4.4 (`RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b`,
proved in Lean from Proposition 0). -/""",
"""CR₃^5b implies CR₃^Sel by tyz-5b Corollary 4.4 (`RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b`,
proved in Lean from Proposition 0). The variant without 22P is
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b`
(`RouteK/Rank5bSec3.lean`). -/"""),
])

edit('ZInQKernel/Main.lean',[
("""  `d ≡ 5 (mod 8)` and classes `|a| ≡ 7 (mod 8)`; it follows from Proposition 0 with Kriz's
  2-converse and the corank lemma, or with Tian–Yuan–Zhang and Gross–Zagier–Kolyvagin (see its
  docstring).""",
"""  `d ≡ 5 (mod 8)` and classes `|a| ≡ 7 (mod 8)`; it follows from Proposition 0 with
  Tian–Yuan–Zhang, Proposition N and Gross–Zagier with an auxiliary field (see its docstring and
  `docs/research/cr3-trust.md`; Kriz's 2-converse is an alternative that is not needed)."""),
("""(equivalently `rank C_d(ℚ) ≥ 1`). This follows from Kriz's 2-converse theorem with the corank
lemma, or from Tian–Yuan–Zhang with Gross–Zagier–Kolyvagin. Proposition 0""",
"""(equivalently `rank C_d(ℚ) ≥ 1`). This follows from Tian–Yuan–Zhang with Proposition N and
Gross–Zagier with an auxiliary field (`docs/research/cr3-trust.md`); Kriz's 2-converse theorem
with the corank lemma is an alternative that is not needed. Proposition 0"""),
])

edit('ZInQKernel/RouteK/RankInf.lean',[
("""(`certifiedRankInf_iff_certifiedRankRk`) and rests on the same literature (Kriz's 2-converse with
the corank lemma, or Tian–Yuan–Zhang with Gross–Zagier; see `CertifiedRankRk`).""",
"""(`certifiedRankInf_iff_certifiedRankRk`) and rests on the same literature (Tian–Yuan–Zhang with
Proposition N, and Gross–Zagier with an auxiliary field; see `CertifiedRankRk`)."""),
])

edit('ZInQKernel/RouteK/RankDL.lean',[
("""(`certifiedRankDLRk_of_certifiedRankTYZRk`), and so rests on the same literature (Kriz's 2-converse
with the corank lemma, or Tian–Yuan–Zhang with Gross–Zagier); any statement""",
"""(`certifiedRankDLRk_of_certifiedRankTYZRk`), and so rests on the same literature (Tian–Yuan–Zhang
with Proposition N, and Gross–Zagier with an auxiliary field; `docs/research/cr3-trust.md`); any
statement"""),
])
