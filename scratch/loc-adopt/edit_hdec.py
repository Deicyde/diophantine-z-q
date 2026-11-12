import sys
p = 'docs/research/h-decomposition.md'
s = open(p).read()
def rep(old, new):
    global s
    n = s.count(old)
    if n != 1:
        sys.exit(f'count {n} for: {old[:80]!r}')
    s = s.replace(old, new)

LA = 'locator audit (`docs/research/locators.md`, 2026-11-12, AI agents with web access; not a human review)'

# §0 list
rep("""1. Shimura 1967 / Deligne 1971 (Thm 4.21): canonical model and moduli interpretation of the
   level-3 Shimura curve of discriminant 6, with Shimura reciprocity. UNVERIFIED.""",
"""1. Shimura 1967 / Deligne 1971 (Thm 4.21): canonical model and moduli interpretation of the
   level-3 Shimura curve of discriminant 6, with Shimura reciprocity. UNVERIFIED (audit: Deligne's
   §§4.9-4.17, Thm 4.21, Cor. 5.7, Ex. 5.8 read, a qualified consequence; Shimura 1967 and
   Kottwitz unread).""")
rep("""2. Baba–Granath 2008 (Thm 2.1, Lemma 3.1): the Atkin–Lehner quotient and its branch points. Preprint read by
   a model; journal numbering UNVERIFIED.""",
"""2. Baba–Granath 2008 (Thm 2.1, p. 737; Lemma 3.1, pp. 739-740): the Atkin–Lehner quotient
   `V/W ≅ P¹_ℚ` and its three rational branch values `0, ∞, −16/27`. Journal text read by the audit.
   Corrected 2026-11-12: the degree-4 map `V → V/W` has ramification index 2 at each branch
   value; `4, 6, 2` are the elliptic (orbifold) orders of the uniformization, not indices of
   this cover.""")
rep("""3. Lin–Yang 2020 (Example 30): Igusa invariants on the quaternionic locus. arXiv v1 VERIFIED;
   journal numbering UNVERIFIED.""",
"""3. Lin–Yang 2020 (arXiv v1 **Example 29**, pp. 20-21, discriminant 6; corrected 2026-11-12: v1's
   Example 30 treats discriminant 14): Igusa invariants on the quaternionic locus. Journal
   numbering UNVERIFIED. Alternative supplier of the invariant tuple: Baba–Granath Prop. 3.6,
   p. 742 (read by the audit).""")
rep("""5. González–Rotger 2006 (Thm 5.12, Prop. 5.6): fields of definition of CM points. arXiv VERIFIED;
   journal numbering UNVERIFIED.""",
"""5. González–Rotger 2006 (Thm 5.8, Thm 5.12, Prop. 5.6; journal pp. 943-946): number and fields
   of definition of CM points on `X₀(D,N)`. Read by the audit in arXiv v1, v2 and the journal.
   Corrected 2026-11-12: Prop. 5.6 counts `2^{#{p | D(R)N(R)}}·h(R)` CM points, not `h(R)`.""")
rep("""6. Raynaud (SGA 7 IX, Prop. 4.7): semistable reduction when the m-torsion is rational, m ≥ 3.
   UNVERIFIED (Silverberg–Zarhin's form read by a model).""",
"""6. Raynaud (SGA 7 IX, Prop. 4.7): semistable reduction when the m-torsion is rational, m ≥ 3.
   UNVERIFIED (Silverberg–Zarhin Thm 3.5, p. 406, read by models; the audit could not confirm
   from the display that the printed bound includes `m = 3`, the case used).""")
rep("""8. Grothendieck (SGA 7 IX, Thm 3.6): semistable reduction theorem. UNVERIFIED.""",
"""8. Grothendieck (SGA 7 IX, Thm 3.6; Silverberg–Zarhin call it Prop. 3.6): semistable reduction
   theorem. UNVERIFIED.""")
rep("""9. Faltings 1983 (Satz 3, Satz 4): semisimplicity and the Tate conjecture for abelian varieties. Read
   by a model.""",
"""9. Faltings 1983 (Satz 3, Satz 4): semisimplicity and the Tate conjecture for abelian varieties. Read
   by a model; the audit could not open the original (only the 1984 erratum).""")
rep("""10. de Rham comparison (Scholze 2013 Cor. 1.8; or Faltings 1989, Tsuji 1999). UNVERIFIED.""",
"""10. de Rham comparison (Scholze 2013 Thm 1.6, Cor. 1.8, Thms 9.1, 9.3, and the corrigendum; or
   Faltings 1989, Tsuji 1999). Read by the audit in arXiv v2 and the journal (filtered comparison
   as printed; Tate weights a consequence).""")
rep("""11. Berger 2002 (Thm 0.7): de Rham implies potentially semistable. arXiv VERIFIED; journal
   read by a model.""",
"""11. Berger 2002 (published Thm 0.7, Cor. 5.22; arXiv v3 Thm 0.6, Thm 5.19): de Rham implies
   potentially semistable. Both texts read by the audit (published version in an author-hosted
   copy; Springer pagination unread).""")
rep("""12. Pan 2022 (JAMS, Thm 1.0.4): Fontaine–Mazur for GL₂ over ℚ, p odd. arXiv v2 statement
   VERIFIED; JAMS numbering UNVERIFIED.""",
"""12. Pan 2022 (JAMS, Thm 1.0.4): Fontaine–Mazur for GL₂ over ℚ, p odd (at `p = 3` with a local
   residual exception; none at `p = 5`, the prime used). arXiv v2 statement VERIFIED; JAMS
   numbering UNVERIFIED.""")
rep("""13. Hodge–Tate weights of eigenform representations at every level (Saito 1997, or Kato 2004). UNVERIFIED.""",
"""13. Hodge–Tate weights of eigenform representations at every level: Kato 2004 (§§9.2-9.4,
   pp. 187-188), read by the audit, covers cusp forms of every level, `p | N` and `p = 2`
   included (a consequence after dualization); Saito 1997 UNVERIFIED.""")
rep("""14. Galois representations of eigenforms (Eichler–Shimura, Deligne 1971). UNVERIFIED.""",
"""14. Galois representations of eigenforms (Eichler–Shimura, Deligne 1971). Partly read by the audit
   (Deligne exp. 355 §§3.9-3.12, Prop. 4.8, Thm 4.9); Shimura 1971 Thm 7.14 UNVERIFIED.""")
rep("""15. Deligne–Serre 1974 (Thm 4.1): weight one gives finite image. UNVERIFIED.""",
"""15. Deligne–Serre 1974 (Thm 4.1, pp. 513-514, with Lemma 3.2): weight one gives finite image.
   Read by the audit (a consequence; semisimplicity needed).""")
rep("""16. Eichler–Shimura in J₁(N) (Shimura 1971 Thm 7.9; Shimura 1973 Thm 1). UNVERIFIED.""",
"""16. Eichler–Shimura in J₁(N) (Shimura 1971 Thm 7.9, UNVERIFIED; Shimura 1973 Thm 1,
   pp. 526-527, read by the audit).""")
rep("""17. Carayol 1986 (Théorème A): local–global compatibility of the conductor. UNVERIFIED.""",
"""17. Carayol 1986 (Théorème A, pp. 409-411): local–global compatibility of the conductor. Read by
   the audit: covers `p | N` and coefficient characteristic `ℓ = 2` (`p ≠ ℓ`) for `F = ℚ`.""")
rep("""18. Javanpeykar 2014 (Thm 1.1.1): Faltings height of Jacobians of Belyi curves. Read by a model.
19. Gaudron–Rémond 2014 (Duke, Thm 1.4): explicit isogeny theorem. Read by a model.
20. Faltings 1983 (Lemma 5): variation of the Faltings height under isogeny. UNVERIFIED.
21. Bost 1996: lower bound for the Faltings height. Read by a model (as recorded by
    Gaudron–Rémond).
22. Pazuki 2012 (Cor. 1.3): theta height against Faltings height. Read by a model.""",
"""18. Javanpeykar 2014 (Thm 1.1.1, p. 90): Faltings height of Jacobians of Belyi curves. Read by the
    audit.
19. Gaudron–Rémond 2014 (Duke, Thm 1.4, p. 2060; `κ`, `α(g) = 1024g³` on p. 2058): explicit
    isogeny theorem. Read by the audit (author copy of the journal text).
20. Faltings 1983 (Lemma 5): variation of the Faltings height under isogeny. UNVERIFIED.
21. Bost 1996: lower bound for the Faltings height. UNVERIFIED in Bost (display unreadable); its
    use by Gaudron–Rémond §9 (p. 2098) read by the audit.
22. Pazuki 2012 (Cor. 1.3(2)): theta height against Faltings height. Read by the audit: a
    consequence, with Deligne's metric, `h_D = h_F + log π` for surfaces, so `X_D` must
    dominate `max(1, h_D)`; the hardened `X_D = max(1, h_F + 3)` does.""")

# §0 dated paragraph after the textbook paragraph
rep("""newforms, the Clebsch–Bolza–Igusa separation of binary sextics.

**What is in Lean today**""",
"""newforms, the Clebsch–Bolza–Igusa separation of binary sextics.

**Locator audit (loc-adopt, 2026-11-12).** The """ + LA + """ read the primary texts of most
research-level leaves; its corrections are applied in this list, in §1 (route K), in §2 and in
§6. What it changed: (i) **R2** is restated: `(4, 6, 2)` are the elliptic orders of the orbifold
uniformization; the degree-4 cover `V → V/W` has index 2 at each branch value (a degree-4 cover
cannot have index 6); (ii) **R3**'s locator is Lin–Yang arXiv v1 Example 29 (discriminant 6), not
Example 30 (discriminant 14); the journal numbering is unread; Baba–Granath Prop. 3.6 is an
alternative supplier of the tuple; (iii) **R5**: González–Rotger Prop. 5.6 has the orientation
factor `2^{#{p | D(R)N(R)}}`, so `#CM(R) = h(R)` holds only on one orientation branch (example:
`R` maximal of discriminant −19 gives four CM points with `h(R) = 1`); (iv) locators and
qualifications for R1, R6-R22, K1-K4 and T27 (Berger 0.6/0.7, Pan's `p = 3` exception and
Frobenius conventions, Kato as the all-level supplier of R13, Carayol covering `p | N` and
`ℓ = 2`, Gaudron–Rémond's constants, Pazuki's Deligne metric, Kisin 2009 Cor. 0.3 as a published
alternative to Ribet, Chia-Fu Yu 2013 Thm 1.1 for T27 with "indefinite" kept). "Read by the
audit" below means an AI agent read the primary text; it is not a human check, and the audit's
UNVERIFIED marks are kept. No leaf was added or removed and no count changed; the uses of R2's
branch data (A2, A5) and of R5's count (A10, NoCM) in the glue are being checked by a separate
review and are not changed here (h-trust, notes of 2026-11-12). The corrections are not yet
reflected in `Leaves.lean` docstrings (outside this task).

**What is in Lean today**""")

# TYZ paragraph in §0
rep("""have read states `TYZRow5b`. Theorem 1.2 of TYZ (arXiv:1411.4728v1), read literally, is false
  (d = 26565, 33117).""",
"""have read states `TYZRow5b`. Theorem 1.2 of TYZ (arXiv:1411.4728v1; Theorem 1.4 of the journal
  version, which keeps the same restriction, per the locator audit of 2026-11-12), read literally,
  is false (d = 26565, 33117).""")
rep("""  whose proof is only sketched, and the journal version (Asian J. Math. 21 (2017)) has not been
  checked.""",
"""  whose proof is only sketched. The journal version (Asian J. Math. 21 (2017)) was read by the
  locator audit (2026-11-12, AI): it renumbers Theorem 1.2 as Theorem 1.4 and keeps the
  all-factors-greater-than-one restriction, and the convolution used by Proposition N is its
  Lemma 2.9 (the notes formerly said Lemma 2.8).""")

open(p,'w').write(s)
print('ok part 1')
