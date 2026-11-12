import sys
p = 'docs/research/h-trust.md'
s = open(p).read()
def rep(old, new):
    global s
    n = s.count(old)
    if n != 1:
        sys.exit(f'count {n} for: {old[:80]!r}')
    s = s.replace(old, new)
N = '*Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).*'

# header status
rep("""for the two Lean hypotheses (§3). The work log and the rerun outputs are in `scratch/h-trust/`.""",
"""for the two Lean hypotheses (§3). The work log and the rerun outputs are in `scratch/h-trust/`.

Locator audit (task loc-adopt, 2026-11-12). The primary-source audit `docs/research/locators.md`
(AI agents with web access, not a human review) corrected several citations used here. Dated notes
in A2, A5, A7, A10, C4, C7, C8, D2, D5, E2-E4, F1, F3 and §2.5 record them. Where a correction
may affect an argument rather than a citation (A2/A5's use of ramification orders, A10's use of
the CM count) the note says so and the argument is left unchanged: a separate review task checks
those.""")

rep("""     not Props 3.7-3.10), Lin–Yang 2020 (eq. (3), Lemma 3, eqs. (13)-(14), Examples 29-30; not
     eq. (2)), Igusa 1967 and Lauter–Naehrig–Yang 2015, read through""",
"""     not Props 3.7-3.10), Lin–Yang 2020 (eq. (3), Lemma 3, eqs. (13)-(14), Examples 29-30; not
     eq. (2); the discriminant-6 example is arXiv v1 Example 29, locator audit 2026-11-12, see
     F1), Igusa 1967 and Lauter–Naehrig–Yang 2015, read through""")

# A2
rep("""  - Lin–Yang 2020, Example 30. VERIFIED in arXiv v1 by h-v14; the journal number is UNVERIFIED.
  - Independent check of the elliptic-point data: rv-h-cm §2.3 derives Elkies' twist constants
    from Shimura reciprocity at the three elliptic points.
- *Status:* **[R]**.""",
"""  - Lin–Yang 2020, Example 30. VERIFIED in arXiv v1 by h-v14; the journal number is UNVERIFIED.
  - Independent check of the elliptic-point data: rv-h-cm §2.3 derives Elkies' twist constants
    from Shimura reciprocity at the three elliptic points.
- """ + N + """
  - Lin–Yang: the discriminant-6 example of arXiv:1807.00466v1 is **Example 29** (pp. 20-21);
    v1's Example 30 treats discriminant 14. h-v14 verified the content in v1 but had not
    compared the number (h-v14 row L719). The journal number (Math. Z. 295 (2020), 775-819) is
    still UNVERIFIED. Baba–Granath Prop. 3.6 (p. 742) prints the invariant tuple and is an
    alternative supplier (read by the audit; not a verification of the Lin–Yang citation).
  - Baba–Granath, read by the audit in the journal: Thm 2.1 (p. 737), Lemma 3.1 (pp. 739-740:
    `V/W ≅ P¹_ℚ`, the three distinguished images rational), §3 (p. 739), the elliptic-order table
    of §3.1 (p. 740), Prop. 3.9 and Thm 3.10 (p. 744), Cor. 3.11 (p. 745). The audit did not
    locate the 2005 preprint.
  - **Branch data.** The audit finds that `4, 6, 2` are the elliptic (orbifold) orders of the
    uniformization by the normalizer group, and that the finite degree-4 map `V → V/W`
    (`V = X₆`) has ramification index **2** at each of `0, ∞, −16/27`. The Content line above,
    "indices `4, 6, 2`", is therefore correct only as orbifold orders (or as indices of a cover
    uniformized by a torsion-free group), not as indices of `X₆ → X₆/W`. Thm 2.1 and Lemma 3.1
    alone do not fix the numerical normalization of `j`. The steps that use these indices (A5
    through h-b1's M4, which applies them to `Y₃ → P¹_j`) may be affected; the argument is not
    changed here (see the A5 note), and a separate review checks it.
- *Status:* **[R]**.""")

# A5
rep("""- *Status:* **[M]** (rv-h-b1 §§2-5: Prop. TS, Lemma NV, M1-M10 and Lemma PR(i) hold as stated;
  its repairs 1-6 are applied in h-b1). Its inputs are [R] and [S].""",
"""- *Status:* **[M]** (rv-h-b1 §§2-5: Prop. TS, Lemma NV, M1-M10 and Lemma PR(i) hold as stated;
  its repairs 1-6 are applied in h-b1). Its inputs are [R] and [S].
- """ + N + """ h-b1's table entry M4 gives the branch points and
  indices of `Y₃ → P¹_j` as `(0,4)`, `(∞,6)`, `(−16/27,2)` and cites Baba–Granath and Lin–Yang;
  Lemma NV step 2 uses that the inertia group over a branch point is cyclic of order `e_i` (M4).
  The audit shows that Baba–Granath's degree-4 cover `X₆ → X₆/W` has index 2 at each branch value
  and that `4, 6, 2` are orbifold orders. For the Galois cover `Y₃ → P¹_j` (group of order
  dividing 144, M3) the index over an elliptic point is the order of the stabilizer, which would
  equal the orbifold order if the level-3 group is torsion-free modulo the centre (neat, A4):
  SPECULATIVE, not checked here. So M4 may need a different supplier (the elliptic-order table,
  Baba–Granath §3.1, p. 740, with neatness of `K₃`) rather than a wrong number; whether the
  argument is affected is for the separate review. Prop. TS and M5-M8 use only that the branch
  values are `0, ∞, −16/27` and that `J(u)` is not one of them, which the audit does not touch.
  The argument is not changed here.""")

# A7
rep("""  - The Igusa vector: Lin–Yang 2020, eqs. (13)-(14) and Examples 29-30, through
    `scratch/h-v14/igusa_check.py` (rerun, identical).""",
"""  - The Igusa vector: Lin–Yang 2020, eqs. (13)-(14) and Examples 29-30, through
    `scratch/h-v14/igusa_check.py` (rerun, identical). (Locator audit, 2026-11-12: the
    discriminant-6 example is v1's Example 29; Example 30 is discriminant 14. Alternative
    supplier of the tuple: Baba–Granath Prop. 3.6, p. 742. Baba–Granath Thm 2.1 was read by the
    audit, p. 737. The bracket is weighted-projective.)""")

# A10
rep("""  - Vignéras LNM 800 for the embedding condition (UNVERIFIED).
- *Repairs.* rv-h-cm R1-R5 must be applied when the CM paragraph is replaced.""",
"""  - Vignéras LNM 800 for the embedding condition (UNVERIFIED).
- """ + N + """ González–Rotger read by the audit in arXiv v1, v2 and
  the journal: Prop. 5.6 (journal p. 943; v1/v2 p. 15), Thm 5.8 (pp. 943-944), Thm 5.12
  (p. 946). Prop. 5.6 counts `#CM(R) = 2^{#{p | D(R)N(R)}}·h(R)` on `X₀(D,N)`; only a single
  specified orientation branch has `h(R)` points, and `(f,6) = 1` does not remove the factor
  (maximal order of discriminant −19: `h = 1`, four CM points). The fields of definition hold on
  the paper's `X₀(D,N)`, not automatically on `Y₃` or on the image in the full Atkin–Lehner
  quotient (at discriminant −24 the quotient value −16/27 is rational, while the ring class
  field has degree 4). The h-decomposition's former leaf R5 ("`#CM(R) = h(R)`") was wrong and is
  corrected there. The NoCM argument as written in h-cm (§5, and rv-h-cm §3) uses the count
  `2^b·h(𝔬)`, `b` the number of `p | 6` inert in `K` (rv-h-cm: Prop. 5.6 with `N = 1`), which
  appears to be this count (read here in h-cm.md; not re-derived). Whether the uses of the count
  and of the fields (which live on `X₀(6,1)`, while the fibre lies on `Y₃` over the quotient)
  are correct is left to the separate review; the argument is not changed here.
- *Repairs.* rv-h-cm R1-R5 must be applied when the CM paragraph is replaced.""")

# C4
rep("""  rv-h-a011 §3.2. In the author's published version it is Théorème 0.7 (= Corollaire 5.22)
  (ASTRA-READ: descent ADDENDUM item 3).
- *Status:* **[R]**.""",
"""  rv-h-a011 §3.2. In the author's published version it is Théorème 0.7 (= Corollaire 5.22)
  (ASTRA-READ: descent ADDENDUM item 3).
- """ + N + """ Both texts read: arXiv v3 Thm 0.6 (p. 6), Thm 5.19
  (pp. 56-57); published version (author-hosted copy) Thm 0.7 (p. 6), Cor. 5.22 (p. 52);
  Springer pagination unread. arXiv v3's Theorem 0.7 is a different statement. No dimension,
  oddness, residual or odd-`p` hypothesis; conclusion potentially semistable.
- *Status:* **[R]**.""")

# C7
rep("""- *Policy.* This is repair R2 of rv-h-a011: the leaf is Pan's stated theorem. The works cited
  inside its proof (Skinner–Wiles 1999/2001, Kisin, Hu–Tan, Khare–Wintenberger) are not leaves.""",
"""- *Policy.* This is repair R2 of rv-h-a011: the leaf is Pan's stated theorem. The works cited
  inside its proof (Skinner–Wiles 1999/2001, Kisin, Hu–Tan, Khare–Wintenberger) are not leaves.
- """ + N + """ arXiv v2 Thm 1.0.4 (p. 5) with Conj. 1.0.1 (p. 2) and
  the conventions (pp. 6-7) read; the JAMS number and page remain UNVERIFIED. At `p = 3` the
  local residual exception (semisimplification not `η ⊕ ηω`) must be kept; there is no such
  proviso at `p = 5`, so C7 is unaffected. Pan uses geometric Frobenius and cyclotomic HT weight
  −1; the arithmetic-Frobenius traces used in C8 require dualization and an adjusted twist (as
  C8's normalization paragraph already does).""")

# C8: add after the Kato bullet? find status line of C8
i = s.find('**C8. The twist and the weight**')
j = s.find('- *Status:*', i)
k = s.find('\n', j)
# insert note before status line
s = s[:j] + "- " + N + """ Kato, Astérisque 295 (2004), was read by the audit:
  §§9.2-9.4, especially (9.2.2), pp. 187-188, with §§6.3, 8.3, §§11.3-11.4 and §14.10.2-3
  (p. 240). It is the all-level supplier for cusp forms and newforms: no `p ∤ N` restriction,
  bad reduction handled by semistable models over finite extensions, `p = 2` included; the
  cohomological realization dualizes to the Tate weights `{0, 1−k}`. General eigenforms need the
  old/new reduction; Eisenstein series need a separate construction; weight one is outside it.
  Saito 1997 stays UNVERIFIED (body unread). Deligne–Serre Thm 4.1 (pp. 513-514) was read, with
  Lemma 3.2 for the transfer to every semisimple realization with the same traces
  (semisimplicity cannot be dropped).
""" + s[j:]

# D2
rep("""  - Raynaud's criterion: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5, p. 406,
    `n ≥ 3` (ASTRA-READ: conductor AUDIT), or SGA 7 I, Exp. IX, Prop. 4.7 (UNVERIFIED).""",
"""  - Raynaud's criterion: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5, p. 406,
    `n ≥ 3` (ASTRA-READ: conductor AUDIT), or SGA 7 I, Exp. IX, Prop. 4.7 (UNVERIFIED).
    (Locator audit, 2026-11-12: Thm 3.5 read, but the extracted display could not confirm that
    the printed threshold includes `n = 3`; UNVERIFIED at the boundary, which A6 uses with
    `n = 3`. SGA 7 was not read. Silverberg–Zarhin Thm 3.4 cites the semistable reduction theorem
    as SGA 7 IX **Prop.** 3.6.)""")

# D5
rep("""- *To check (UNVERIFIED).* That Théorème (A) covers `F = ℚ` at every `p ≠ ℓ`, including
  `p | N`; see the statement in §0 of the paper. Fallback: Langlands, *Modular forms and
  ℓ-adic representations*, LNM 349 (1973), together with Carayol's §0 remarks (SPECULATIVE).""",
"""- *To check (UNVERIFIED).* That Théorème (A) covers `F = ℚ` at every `p ≠ ℓ`, including
  `p | N`; see the statement in §0 of the paper. Fallback: Langlands, *Modular forms and
  ℓ-adic representations*, LNM 349 (1973), together with Carayol's §0 remarks (SPECULATIVE).
- """ + N + """ §§0.3-0.8 and Théorème A (pp. 409-411) read: it covers
  every finite `p` and every coefficient place of different residue characteristic, so `p | N`
  and `ℓ = 2` are covered; the extra discrete-series hypothesis is only for totally real fields
  of even degree, not `ℚ`. Still to supply: the newform conductor `a(π_p) = v_p(N)` and the
  identification of the chosen realization (contragredient and norm twists do not change the
  conductor). The check above is answered by the audit (AI), not by a human.""")

# E2
rep("""  with the original Faltings metric (ASTRA-READ: height AUDIT, whole REPORT).
- *Status:* **[R]**.

**E3.""",
"""  with the original Faltings metric (ASTRA-READ: height AUDIT, whole REPORT). (Locator audit,
  2026-11-12: read again; `h_Fal(X) ≤ 13·10⁶·g·deg_B(X)⁵` for smooth projective connected `X/ℚ̄`
  of genus `g ≥ 1`, the stable Jacobian height; no field-degree factor.)
- *Status:* **[R]**.

**E3.""")

# E3
rep("""  height AUDIT, pp. 2058-2060, 2098, 2101-2102).
- *Check.* The arithmetic is in `c1_constants.py` (rerun).""",
"""  height AUDIT, pp. 2058-2060, 2098, 2101-2102). (Locator audit, 2026-11-12: read in a typeset
  author copy: `α(g) = 1024g³`, `κ(A) = ((14g)^{64g²}[k:ℚ]max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`
  (p. 2058), pair convention (p. 2059), Thm 1.4 (p. 2060); an isogeny in each direction, each of
  degree `≤ κ(A)`, the degree for a pair being the maximum; specialize `k = K`.)
- *Check.* The arithmetic is in `c1_constants.py` (rerun).""")

# E4
rep("""  - The Faltings and Raynaud locators are UNVERIFIED.
- *Status:* **[R]**. The arithmetic is [M] (rv-h-novel step 9) and [S].""",
"""  - The Faltings and Raynaud locators are UNVERIFIED.
  - Locator audit (2026-11-12): Faltings' Lemma 5 unread (UNVERIFIED; Pazuki's Remark 2.3 points
    to p. 358); Bost's displays unreadable (UNVERIFIED from Bost); Gaudron–Rémond's use of
    `−(3/2)dim A` in the proof of their Lemma 9.1 (p. 2098) read. Conditional on a
    Deligne-normalized bound `h_D ≥ −(g/2)log(2π)`, one gets `h_F ≥ −(g/2)log(2π²) > −(3/2)g`.
- *Status:* **[R]**. The arithmetic is [M] (rv-h-novel step 9) and [S].""")

# F1
rep("""  - Lin–Yang 2020, Example 30: the divisors of `s₂ = ψ₄` and `s₅ = 2¹²3⁵χ₁₀` on the
    quaternionic locus `X`.""",
"""  - Lin–Yang 2020, Example 30 (**Example 29** in arXiv v1, pp. 20-21; v1's Example 30 is
    discriminant 14; journal number UNVERIFIED; locator audit 2026-11-12, see the F1 note
    below): the divisors of `s₂ = ψ₄` and `s₅ = 2¹²3⁵χ₁₀` on the
    quaternionic locus `X`.""")
rep("""- *Status:* **[R]+[S]**. This replaces `ly-d6` and `igusa-theta` (route B3).""",
"""- """ + N + """ The Lin–Yang locator used in this step (here and in
  `igusa_check.py`'s description) is arXiv:1807.00466v1 **Example 29**, the discriminant-6
  example; "Example 30" is v1's discriminant-14 example. Journal numbering unread. Baba–Granath
  Prop. 3.6 (p. 742) independently prints the invariant tuple. The invariant brackets are
  weighted-projective. Igusa 1967 pp. 833-834, 848 were opened by the audit but the decisive
  signs (`χ₁₀ = −2⁻¹⁴Πθ_m²`) and the `J`-conversion could not be read: UNVERIFIED; the 40-digit
  numerical checks are not a proof of the normalization. The content of F1 is unchanged.
- *Status:* **[R]+[S]**. This replaces `ly-d6` and `igusa-theta` (route B3).""")

# F3
rep("""  Cor. 1.3(2) and §§2.2-2.3, with the `log π` shift for `g = 2` (ASTRA-READ: whole REPORT).
- *Status:* **[R]**. The normalization bookkeeping (`X_D ≤ 3X`) is [M] (Astra "height").""",
"""  Cor. 1.3(2) and §§2.2-2.3, with the `log π` shift for `g = 2` (ASTRA-READ: whole REPORT).
- """ + N + """ Read in arXiv v2 (Cor. 1.3(2), p. 3; Def. 2.1,
  pp. 6-7; Def. 2.6, p. 9; Lemma 5.7, p. 20) and the journal (Cor. 1.3, pp. 21-22; metric p. 26;
  theta height p. 30; Lemma 5.7 p. 43). A consequence, not the literal corollary: the corollary
  compares the truncated heights `max(1,h_Θ)` and `max(1,h_D)` with `min` inside the logarithm,
  `C₂ = 1000r^{2g}(log r^{2g})⁵`. Its metric is Deligne's: `h_D = h_F + (g/2)log π`, i.e.
  `h_D = h_F + log π` for surfaces, so the bound must use `X_D ≥ max(1, h_D)`; for `h_F ≤ X`
  take `X_D = max(1, X + log π)`. N5's bookkeeping `X_D ≤ 3X` and the repository's hardened
  `X_D = max(1, h_F + 3)` (h-decomposition R22) both dominate this; the theta height (the
  paper's Fubini–Study height of the theta embedding) must be identified with the coordinate
  height used in F2.
- *Status:* **[R]**. The normalization bookkeeping (`X_D ≤ 3X`) is [M] (Astra "height").""")

# §2.5
rep("""repository: Pan v2 Thm 1.0.4, Berger v3 Thm 0.6/5.19, González–Rotger §5, Lin–Yang v1 Ex. 30 and
eqs. (2), (13), (14) (eq. (2) read but not used; see F1), and Scholze's introduction.""",
"""repository: Pan v2 Thm 1.0.4, Berger v3 Thm 0.6/5.19, González–Rotger §5, Lin–Yang v1 Ex. 30 and
eqs. (2), (13), (14) (eq. (2) read but not used; see F1), and Scholze's introduction.

*Locator audit (2026-11-12, `docs/research/locators.md`).* AI agents with web access read the
primary texts of: Baba–Granath (journal), Lin–Yang arXiv v1 (the discriminant-6 example is
**Example 29**, not 30), González–Rotger (arXiv v1, v2, journal; Prop. 5.6 has the orientation
factor), Silverberg–Zarhin (`m = 3` boundary unreadable), Scholze (v2, journal, corrigendum),
Berger (v3 and published), Pan v2 (JAMS number still unread), Kato 2004, Deligne exp. 355,
Deligne–Serre, Shimura 1973, Carayol (covers `p | N`, `ℓ = 2`), Javanpeykar, Gaudron–Rémond,
Pazuki (Deligne metric, `+log π`), Chia-Fu Yu 2013 (QM dichotomy). They could not read:
Shimura 1967, Kottwitz 1992, Serre–Tate 1968, Faltings 1983 (only the erratum), SGA 7, Igusa's
decisive displays, Saito 1997, Shimura 1971, Bost's displays, Lin–Yang's journal body, Pan's
JAMS text. Items 1, 2, 3 (Kato), 4 and 10 (Baba–Granath) below are answered by the audit as far
as stated in the notes of §1; they stay listed because no human has read them.""")

open(p,'w').write(s)
print('ok')
