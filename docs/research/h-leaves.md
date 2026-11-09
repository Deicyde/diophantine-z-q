# The reduced trust base of the six-contact estimate H

Status labels.

- **VERIFIED**: checked here against the text: the manuscript `diophantine_zq.tex` (line numbers
  refer to the frozen 11/5 source, SHA256 `cb1148cd…d792b`), the audit records in
  `docs/theorem-application-audit/`, the Lean files, or the text of a paper that was read here.
- **STANDARD**: a well-known published theorem whose statement was checked to apply. The
  reference is given.
- **SPECULATIVE**: an idea or assessment that is not proved.
- **UNCHECKED**: the source could not be read here. The step is recorded with the attribution
  that could be verified (for instance in a survey that was read), but the exact statement and
  numbering in the primary source were not checked.

Notation as in `docs/research/rs-height.md` and `docs/research/h-cm.md`: `A/K` is the fibre
surface of the proof of Theorem 4.1, `L` its Hom field (`[L:ℚ] ≤ D`), `L'` the field of the
scalar descent (`[L':ℚ] ≤ QM`), `r_ℓ` the two-dimensional representation of `G_ℚ` with
`ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` (line 730), `f` the weight-two newform of level `N`, `J = J₁(N)`.
`NoCM` is the lemma of h-cm, in the corrected form of `docs/research/rv-h-cm.md` §7.2.

Sources read for this note (besides the repository):

- E. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*,
  arXiv:1105.1230 (Comment. Math. Helv. 89 (2014)); cited as GR11. Its introduction restates the
  period theorem of Masser–Wüstholz.
- L. Pan, arXiv:1901.07166v2, Conjecture 1.0.1 and Theorem 1.0.4 (the version pinned by the
  audit, A011).
- P. Scholze, arXiv:1205.3463, introduction and the de Rham corollary.
- L. Berger, *An introduction to the theory of p-adic representations*, arXiv:math/0210184
  (in *Geometric aspects of Dwork theory*, de Gruyter 2004), §I.3, "Comparison theorems";
  cited as Berger04.
- D. Zywina, *An effective open image theorem for abelian varieties*, arXiv:1910.14171,
  Theorem 2.4 (attributed to Masser–Wüstholz) and its proof; cited as Zywina.
- R. von Känel, *Modularity and integral points on moduli schemes*, arXiv:1310.7263,
  §§1, 4; cited as vK.

Sources that could **not** be read here (no access): D. Masser and G. Wüstholz, *Periods and
minimal abelian subvarieties* and *Isogeny estimates for abelian varieties, and finiteness
theorems*, Ann. of Math. 137 (1993), 407–458 and 459–472 (MW93a, MW93b); their *Factorization
estimates for abelian varieties*, Publ. Math. IHÉS 81 (1995), 5–24, and *Refinements of the Tate
conjecture for abelian varieties*, in *Abelian varieties* (Egloffstein 1993), de Gruyter 1995,
211–223 (MW95); J.-B. Bost, Séminaire Bourbaki exposé 795, Astérisque 237 (1996); Gaudron–Rémond,
Duke 163 (2014) (GR14; known here only through audit records A005, A015, A016); Faltings 1983
(known here through A006, A008, A063); Faltings 1989; Tsuji 1999; Fontaine 1982/1983;
Coleman–Iovita 1999; Breuil 2000; Tate 1966 and 1967; SGA 7; Carayol 1986.

## Summary

- **Inventory (§1).** The proof of Theorem 4.1 (lines 404-966, with the appendix lemma at lines
  10936-11005) consumes 26 audit records: A001-A018, A061-A065, A071, A078, A079 (VERIFIED from
  `applications.json` anchors and a scan of every `\cite` in those lines). Two further external
  inputs are used without a citation or an audit record: Carayol's local–global compatibility
  (lines 852-857, "Local–global compatibility … bounds the primitive level") and the extension of
  homomorphisms of good-reduction abelian varieties (lines 781-784). Both should be recorded.
- **CM branch (§1.3).** NoCM removes A003, A004 and A005 from the proof entirely, and removes the
  H-use of A065 (its other uses, lines 1009-1016 and 1759-1769, are outside H). It removes the CM
  use of A006 and of Faltings 1983 at line 621, but A006 stays for lines 894-903. It adds
  González–Rotger §5, Vignéras (Emb) and, through González–Rotger, Shimura's reciprocity law.
- **R5.1, Masser–Wüstholz (§2).** Both uses of Faltings' finiteness theorems can switch. What the
  proof needs is qualitative: semisimplicity and the endomorphism theorem for `A/L'` at `ℓ = 3, 5`
  (A008), and the Hom theorem for `(A, J)` over `L'` (A063). These follow by Tate's 1966 argument
  from the finiteness of the `L'`-isogeny class up to isomorphism, which follows at once from the
  isogeny theorem of Gaudron–Rémond (GR14, Theorem 1.4, already a leaf as A015). This is the
  Masser–Wüstholz proof of the Tate conjecture, with GR14 in place of MW93b. The proof of the
  derivation is written out in §2.3 (VERIFIED as an argument). The large-`ℓ` mod-`ℓ` statements
  of MW95 do **not** apply at `ℓ = 3, 5`. One check is left open: that the proof of GR14
  Theorem 1.4 does not itself use Faltings' Tate theorem (§2.5).
- **R5.2, p-adic comparison (§3).** Pan's Theorem 1.0.4 needs `r₅|G_{ℚ₅}` *potentially
  semistable* with distinct Hodge–Tate weights (VERIFIED in arXiv v2). Two replacements:
  (a) the de Rham comparison for abelian varieties from Fontaine (1983), Faltings (1989) or Tsuji
  (1999) in place of Scholze; (b) better, `A` has potentially good reduction at 5 (Lemma PG,
  VERIFIED from inputs already in the base: Silverberg–Zarhin A013, Néron–Ogg–Shafarevich A061, and
  `B ⊗ ℚ₃` a division algebra), so `r₅` is potentially crystalline by the classical crystalline
  comparison for abelian varieties with good reduction. Route (b) removes Scholze (A009's main
  source) **and** Berger (A010). The primary sources of the crystalline comparison were not
  readable here (UNCHECKED; attribution VERIFIED in Berger04).
- **Further leaves (§4).** Raynaud's criterion is older than Silverberg–Zarhin (SGA 7 I, IX,
  Prop. 4.7, UNCHECKED). Several leaves cite unrefereed notes (Milne's course notes,
  Brinon–Conrad, Conrad's preprint, the Stacks project) or preprint versions of published papers
  (Baba–Granath, Buzzard, Lin–Yang); §4.4 lists published replacements. No older replacement was
  found for Pan, Javanpeykar, Pazuki, Gaudron–Rémond or the Lin–Yang/Lauter–Naehrig–Yang theta
  formula.
- **Constants (§5).** None of the changes alters a constant. `H₆(S;R)` is unchanged, and
  `SixContactEstimate` (`Hypotheses/Height.lean`, lines 89-98) and `SixContactMin`
  (`Hypotheses/HeightMin.lean`, line 36) hold as stated, with the same numerals (VERIFIED by
  reading both files).

