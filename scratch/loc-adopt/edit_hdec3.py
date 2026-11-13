import sys
p = 'docs/research/h-decomposition.md'
s = open(p).read()
def rep(old, new):
    global s
    n = s.count(old)
    if n != 1:
        sys.exit(f'count {n} for: {old[:80]!r}')
    s = s.replace(old, new)

rep("""- K4. Grothendieck: the conductor exponent of an abelian variety at `p` is independent of
  `ℓ ≠ p` (SGA 7 I, Exp. IX, UNVERIFIED), unless Carayol's Théorème (A) is checked at `ℓ = 2`.""",
"""- K4. Grothendieck: the conductor exponent of an abelian variety at `p` is independent of
  `ℓ ≠ p` (SGA 7 I, Exp. IX, UNVERIFIED), unless Carayol's Théorème (A) is checked at `ℓ = 2`.
- Locator audit (2026-11-12, `locators.md`). **K1**: Khare–Wintenberger I, Thm 1.2 read (journal
  p. 486; author copy Thm 1.2 p. 2, Hypothesis (H) and Thm 9.1 p. 18); it covers odd `p` with odd
  `N` and `p = 2`, `k = 2`, not all of Serre's cases: full coverage needs Thm 9.1, part II (which
  supplies the proofs of I's Thms 4.1 and 5.1, §10, journal pp. 581 ff.) and Kisin, Invent. Math.
  178 (2009), Thm 0.1 (pp. 587-588, read: YES for the lifting statement). CONSEQUENCE as a bundle.
  **K2**: Ribet 1992 is **(4.4)** of arXiv alg-geom/9208002v1 (p. 8; proof p. 9), the same number
  in the author copy; reprint pagination (Progr. Math. 224, pp. 241-261) confirmed, the reprint's
  theorem page unread; a CONSEQUENCE for a `ℚ`-simple `B₀` (§3 of Ribet restricts to primitive,
  `ℚ`-simple varieties; no optimality or connected-kernel conclusion). Whether the 1992 paper
  was refereed remains UNVERIFIED. **Published alternative: Kisin 2009, Cor. 0.3 (p. 588, read
  by the audit)**: a `g`-dimensional `A/ℚ` with a degree-`g` field in `End⁰_ℚ(A)` is a quotient of
  `J₁(N)^m` for some `N, m ≥ 1`; for `ℚ`-simple `B₀` some component map is nonzero, hence
  surjective, giving a quotient of `J₁(N)`. This removes the refereeing question for K2, not the
  deep Serre dependencies. **K3**: Ribet 1975/1980 original (Cor. 4.2) unread, UNVERIFIED; a
  CONSEQUENCE of the readable 1992 exposition (`ℚ`-simplicity, not absolute simplicity).
  **K4**: UNVERIFIED (SGA 7 IX §4 unread; Cor. 4.6 is the candidate cited by Ribet 1992 Lemma
  4.1). The audit read Carayol's Théorème A as covering `ℓ = 2` (R17), so K4 can be dropped on
  this route: 19 research leaves.""")

rep("""- Count: 22 − 6 (R10-R15) + 4 = **20 research leaves** (19 if Carayol covers `ℓ = 2`).""",
"""- Count: 22 − 6 (R10-R15) + 4 = **20 research leaves** (19 if Carayol covers `ℓ = 2`, which the
  locator audit of 2026-11-12 read: so 19, with K2 citable through Kisin 2009 Cor. 0.3).""")

rep("""| T27 | QM dichotomy: a quaternion division algebra in `End⁰` of an abelian surface over `k = k̄`, char 0, forces `End⁰ ≅ B` or `M₂(ℚ(√d))`, `d < 0` | no single locator (rv-leaves-b): Mumford §19 Thm 1, Cor. 2, §21 (`[D:ℚ] ∣ 2g`, char 0), §22 (Albert), with Silverman AEC III.9.4 | C |""",
"""| T27 | QM dichotomy: an **indefinite** quaternion division algebra `B` in `End⁰` of an abelian surface over `k = k̄`, char 0, forces `End⁰ ≅ B` (`A` simple) or `M₂(ℚ(√d))`, `d < 0`, `ℚ(√d)` splitting `B` (`A` not simple) | **Chia-Fu Yu, *Endomorphism algebras of QM abelian surfaces*, J. Pure Appl. Algebra (2013), Thm 1.1 (journal p. 907; arXiv:1210.1125 v1/v2 p. 1; proof Props 2.4-2.5, pp. 4-5), read by the locator audit (2026-11-12): a refereed single locator; the hypothesis "indefinite quaternion division algebra" must be kept (the broader wording "a quaternion division algebra" is not what Yu proves; whether `PkgI3.QMDichotomy` carries it is a statement check, WP13). The journal volume (217 from memory) is UNVERIFIED.** Earlier assembly (rv-leaves-b): Mumford §19 Thm 1, Cor. 2, §21 (`[D:ℚ] ∣ 2g`, char 0), §22 (Albert), with Silverman AEC III.9.4 | C |""")

rep("""- **R1. Locators.** Almost every theorem number is UNVERIFIED in the published version. Most
  worth checking before the announcement: Pan (JAMS numbering of Thm 1.0.4), Baba–Granath and
  Lin–Yang (journal numbering), Carayol (Théorème A covers `p | N` for `F = ℚ`), Javanpeykar
  (field and `g ≥ 1`), Gaudron–Rémond, Pazuki (`max(1, ·)` in `X_D`, the constant `C₂`), Faltings
  Lemma 5 in inequality form (all model readings only), and T27, the QM dichotomy, which has no single
  locator: cite Mumford §19 Thm 1, Cor. 2, §21, §22 and Silverman AEC III.9.4 together
  (rv-leaves-b), or announce it as glue over them.""",
"""- **R1. Locators.** Almost every theorem number is UNVERIFIED in the published version. Most
  worth checking before the announcement: Pan (JAMS numbering of Thm 1.0.4), Baba–Granath and
  Lin–Yang (journal numbering), Carayol (Théorème A covers `p | N` for `F = ℚ`), Javanpeykar
  (field and `g ≥ 1`), Gaudron–Rémond, Pazuki (`max(1, ·)` in `X_D`, the constant `C₂`), Faltings
  Lemma 5 in inequality form (all model readings only), and T27, the QM dichotomy, which has no single
  locator: cite Mumford §19 Thm 1, Cor. 2, §21, §22 and Silverman AEC III.9.4 together
  (rv-leaves-b), or announce it as glue over them.
  *Update (locator audit, 2026-11-12, `locators.md`; AI agents with web access).* Read in the
  primary texts: Baba–Granath (journal; R2 restated: index 2 at each branch value of `V → V/W`,
  `4, 6, 2` are orbifold orders), Lin–Yang arXiv v1 (R3 is **Example 29**, not 30; journal still
  unread), González–Rotger (R5 corrected: orientation factor `2^{#{p | D(R)N(R)}}`), Carayol
  (covers `p | N` and `ℓ = 2`), Javanpeykar, Gaudron–Rémond (constants as stated, pair degree
  the maximum), Pazuki (a consequence; Deligne's metric, `h_D = h_F + log π` for surfaces,
  `X_D ≥ max(1, h_D)`; the hardened `+3` covers it), Berger (v3 Thm 0.6, published Thm 0.7), Kato
  (R13, all levels), Deligne–Serre, Shimura 1973, Scholze, and T27 (**Chia-Fu Yu 2013, Thm 1.1**,
  a single refereed locator, with "indefinite" kept). Still UNVERIFIED after the audit: Pan's
  JAMS number (arXiv v2 read, with the `p = 3` exception), Lin–Yang's journal number, Igusa's
  signs and conversion (R4), the `m = 3` boundary of Raynaud's criterion (R6), Serre–Tate (R7),
  SGA 7 (R8, K4), Faltings 1983 (R9, R20), Bost's constant (R21), Shimura 1967, Kottwitz,
  Saito 1997, Shimura 1971, Ribet's refereeing (K2, now avoidable through Kisin 2009 Cor. 0.3)
  and Ribet 1975/1980 (K3). Two leaves were wrong as stated (R2, R5) and are corrected in §2;
  the uses in the glue are under a separate review.""")

rep("""  21-22, and R4 is stated as the transformation law, not as Igusa's identity; each derivation must
  be recorded with its proof. R1 is assembled from several statements of Shimura and Deligne.""",
"""  21-22, and R4 is stated as the transformation law, not as Igusa's identity; each derivation must
  be recorded with its proof. R1 is assembled from several statements of Shimura and Deligne.
  *Update (locator audit, 2026-11-12).* Two leaves were stronger than (indeed contradicted by)
  the published text and are corrected in §2: R2 (the indices `4, 6, 2` are orbifold orders; the
  degree-4 cover has index 2) and R5 (the CM count carries the orientation factor). Further
  qualifications to keep in the statements: T27 needs "indefinite" (Yu 2013); R14 "every
  eigenform" needs the Eisenstein (reducible) case or a cusp-form restriction; R12 needs Pan's
  `p = 3` exception and the Frobenius/dualization conventions; R16 must not inherit the Fricke
  condition of Shimura 1973's zeta clause; R22 is a consequence for `X_D ≥ max(1, h_D)`.""")

rep("""- Route K (§1): 20 research leaves.""",
"""- Route K (§1): 20 research leaves (19 if K4 is dropped, since the locator audit of 2026-11-12
  read Carayol's Théorème A as covering `ℓ = 2`).""")

open(p,'w').write(s)
print('ok part 3')
