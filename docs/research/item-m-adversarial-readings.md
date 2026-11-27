# Adversarial AI readings: item M, the Gaudron–Rémond rows over the GR1 height and EGA IV (9.7.7) (2026-11-27)

**Result.** The three rows of #219 match their printed sources, and every lens passed every row it read. R1
(`ZInQ.HeightModelM.EGAIV_9_7_7_OL`) is a direct instance of EGA IV₃, Théorème (9.7.7)(ii). R2
(`ZInQ.HeightModelM.GaudronRemondSec9LowerGR1`) is Corollaire 8.4 of Gaudron–Rémond, Comment. Math. Helv. 89
(2014), over their height of a semi-abelian model; the field the fold carries, `GaudronRemondSec9LowerGR1Weak`, is
its weakening to `h_F(A) ≥ -(3/2) dim A`, proved in Lean (`gaudronRemondSec9LowerGR1Weak_of_GR1`), and so a
consequence of the print, not the printed form (§8). R3
(`ZInQ.HeightModelM.GaudronRemondThm14GR1`) is a direct instance of Théorème 1.4 of Gaudron–Rémond, Duke Math. J.
163 (2014), over the same height. No reader found a clause stronger than the print, a missing hypothesis, or a
definition that admits models or height values the print excludes. The non-blocking points are listed in §6.

No person has read these pages. Under the maintainer's ruling of 2026-11-26 (STATEMENT-CHECKS.md, "Adversarial AI
readings"), with no human reader available, this adversarial AI reading stands in for the human reading. The
evidence stays AI-READ. R3 was read in the authors' copy, which carries the Duke pagination; the comparison with
the Duke journal text is still to be made.

The fidelity and skeptic lenses read the rows at `748c8414e`, the red team at `5cafadc3f`, which adds the weak form
and the fold check; the definitions of the three rows are the same at both, and unchanged on main at `96f3a26b7`.

## 1. Method

Three independent AI readings. Each worked from page images rendered from the PDFs at 150 dpi, not from a text
layer, and gives verbatim quotes with printed page numbers. The three readers ran on three different model families
(Claude, GPT, Gemini), so that they would not share blind spots. Each wrote its report independently, without the
pull request's description, the HeightModelM README or any report on these rows. One red-team run stopped before it
finished (an output filter cut it on the length of its quotations) and was run again; the red-team verdicts below
are from the second run.

| Lens | Task |
| --- | --- |
| Fidelity | Unfold each Lean statement and every definition it uses into atomic clauses, and map each clause to the printed text: MATCH, DIRECT INSTANCE, WEAKER or STRONGER THAN THE PRINT, MISMATCH. It also built the rows and checked their axioms (`propext`, `Classical.choice`, `Quot.sound`). |
| Skeptic | Try to break the match: hidden standing hypotheses, conventions (empty fibres, normalizations of the height and the metric), whether each Lean definition means the printed notion, vacuity, quantifiers, and what the relied-on identifications actually state. |
| Red team | Read the sources cold, before any Lean, and state what they assert. Then list every difference with the Lean and classify it. It also read the weak form. |

Sources (legal copies; SHA-256):

| Source | Copy | SHA-256 |
| --- | --- | --- |
| EGA IV₃, Publ. Math. IHÉS 28 (1966) | numdam scan PMIHES_1966__28__5_0 | `f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e` |
| EGA 0_III (in EGA III₁), Publ. Math. IHÉS 11 (1961) | numdam scan PMIHES_1961__11__5_0 | `3ed59fe81da07f1ab685ddc54a93128a364419d4ddafbc7affcd8abc8b401605` |
| EGA IV₂, Publ. Math. IHÉS 24 (1965) | numdam scan PMIHES_1965__24__5_0 | `c3e960aa1c5c37046e8892d8a3cac098e2738164136b5cdaa5d5d893f89931da` |
| EGA IV₁, Publ. Math. IHÉS 20 (1964) | numdam scan PMIHES_1964__20__5_0 | `df11afc6b6318fc491032b1239cd4af9cbc2a7c73219dcc49bf65e5ee6c13140` |
| Gaudron–Rémond (GR1), *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014), 343-403 | EMS journal file (DOI 10.4171/CMH/322) | `5afec329530089fd62d686f5e75331c91fc97fbf775ad6c4b275fc514459f31e` |
| the same article, authors' copy | downloaded for its hash and pagination only, not read | `d6b02e1adb9c8f2ab5a574bd8f8c301b5dfcfb8e14db3516bd2ae099b216ac54` |
| Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057-2108 | authors' copy with the Duke pagination and DOI 10.1215/00127094-2782528 | `6d62ddb8a0aa8f8b8f803d70060c6a26c7a6f2a00936b85867c830946cf3db12` |

Pages read: EGA IV₃ p. 79 by every lens (the skeptic also p. 54); EGA 0_III pp. 12 and 14; EGA IV₂ p. 61; EGA IV₁
p. 234 (fidelity and skeptic). GR1 pp. 351, 352 and 400 by every lens; the fidelity lens also p. 399, the skeptic
pp. 343 and 395, the red team p. 368. Duke pp. 2058, 2060 and 2062 by every lens; the fidelity lens also pp. 2059
and 2107, the skeptic pp. 2057, 2061, 2063, 2097-2098, 2100 and 2107, the red team pp. 2059, 2061, 2063 and 2101.

Both papers of Gaudron and Rémond are refereed (GR1 p. 403: "Reçu le 2 février 2012"; Duke p. 2057: "Received 4
October 2012. Revision received 4 November 2013").

## 2. R1 `EGAIV_9_7_7_OL` (EGA IV₃, Théorème (9.7.7)(ii))

| Lens | Verdict |
| --- | --- |
| Fidelity | PASS: a direct instance of (9.7.7)(ii); every clause MATCH or DIRECT INSTANCE. |
| Skeptic | PASS: no lost hypothesis; empty fibres handled as in EGA; the locus is not vacuous. |
| Red team | PASS: every difference harmless (direct instance or exact match). |

The print, p. 79:

> Soit f : X→S un morphisme de présentation finie, et soit E l'ensemble des s∈S pour lesquels X_s a l'une des
> propriétés suivantes : être : (i) géométriquement irréductible ; (ii) géométriquement connexe ; […] Alors E est
> localement constructible dans S.

The clauses, as the readers mapped them:

* **Base.** The Lean fixes `S = Spec 𝓞_L` for a number field `L`; EGA allows any prescheme. DIRECT INSTANCE.
* **Finite presentation.** EGA IV₁ (1.6.1), p. 234: "(i) f est localement de présentation finie ; (ii) f est
  quasi-compact … ; (iii) f est quasi-séparé." The Lean takes `Smooth f`, `QuasiCompact f`, `QuasiSeparated f`;
  Mathlib derives local finite presentation from smoothness. Smoothness only restricts the morphisms: DIRECT
  INSTANCE.
* **The fibre.** `f.fiber s → Spec κ(s)` is `X ×_S Spec k(s)`. MATCH.
* **Geometric connectedness.** EGA IV₂ (4.5.2), p. 61: "Si n = 1 (resp. n' ≤ 1) on dit que X est un k-préschéma
  géométriquement irréductible (resp. géométriquement connexe)", with the equivalent form "Pour toute extension K
  de k, X⊗_kK est irréductible (resp. connexe)". The Lean asks that every base change of the fibre to a field be a
  `PreconnectedSpace`. MATCH through the printed equivalence (4.5.1)-(4.5.2); the universe restriction is harmless,
  since one algebraic closure suffices.
* **Empty fibres.** EGA's `n' ≤ 1` includes `n' = 0`, and an empty space is preconnected: an empty fibre is in the
  locus on both sides. MATCH. The skeptic tested both conventions on explicit smooth maps over `Spec ℤ`.
* **Local constructibility.** EGA 0_III (9.1.2), p. 12: "une partie de X est constructible si elle appartient au
  plus petit ensemble 𝔉 de parties de X contenant toutes les parties ouvertes rétrocompactes …"; (9.1.11), p. 14:
  "pour tout x∈X, il existe un voisinage ouvert V de x tel que T∩V soit constructible dans V". Mathlib's
  `IsLocallyConstructible`, `IsConstructible` and `IsRetrocompact` are these notions. MATCH.

The proved glue `genericConnectedFibresOL_of_ega` (finiteness of the non-preconnected fibres when the generic fibre
is geometrically connected) is not part of the statement credited to (9.7.7)(ii).

## 3. The height: GR1 §2.3 and `IsGR1StableHeightOriginal`

R2 and R3 quantify over every `x` with `IsGR1StableHeightOriginal A x`. All three lenses audited this predicate
first: a definition that admitted extra models or extra values of `x` would make both rows stronger than the print.

The print, GR1 §2.3, p. 351: "Soient π : 𝒜 → Spec 𝒪_K un modèle semi-abélien de A et ε : Spec 𝒪_K → 𝒜 sa section
nulle"; the line bundle is `ε*Ω^g`, with the norm `‖s‖² = (2π)^{-g} ∫_{A_σ} |s ∧ s̄|` at each complex embedding;
Définition 2.1: "La hauteur h(A) de A est le degré d'Arakelov normalisé de ω̄_{𝒜/𝒪_K}", and "Cette définition est
indépendante des choix de K et de 𝒜". P. 352: Faltings' original definition "ne fait pas apparaître le π dans la
définition de la norme ci-dessus et donc on a h_F(A) = h(A) − (g/2) log π".

The readers' findings:

* **Model.** `GroupModel A K'` is a smooth, separated, quasi-compact group scheme over `𝓞_{K'}`, `K'/K` a finite
  extension of number fields, with a group isomorphism from its generic fibre to `A_{K'}`; `IsSemiAbelianModel`
  asks at every maximal ideal for a connected fibre that is an extension of an abelian variety by a torus, over the
  residue field and over its algebraic closure. GR1 gives no separate definition of "modèle semi-abélien"; the
  readers used the standard one. Asking for both fibre readings only narrows the predicate.
* **Commutativity.** `GroupModel` does not state it. All three lenses found that this adds no model: `A` is
  commutative, the generic fibre of `𝒜 ×_S 𝒜` is schematically dense (smooth, hence flat, over the Dedekind base),
  and `𝒜` is separated, so the two multiplication orders agree everywhere. This is an argument, not a Lean theorem.
* **Lattice.** `printedDetLattice` is the `𝓞_{K'}`-span of top wedges of `printedOmega`, an intersection of stalk
  lattices; Lean proves `theta_injective`, `omegaAt_map`, `omega_map` and `printedOmega_eq`. That this
  intersection is the module of global sections of `ε*Ω¹`, and so its top wedge that of `ε*Ω^g`, is the standard
  fact for a locally free sheaf on an integral affine base, not a Lean theorem.
* **Arakelov degree.** GR1 prints no formula for the "degré d'Arakelov normalisé". The Lean takes the standard one,
  `(log #(ω/𝓞η) − ½ Σ_τ log r_τ)/[K':ℚ]` over all embeddings. MATCH.
* **Metric.** `IsAnMetricSq` requires a measure with the holomorphic-chart density and that every such measure have
  mass `r`, so `r` is not free; the density is `2^{-g}|η ∧ η̄|` against Lebesgue measure, Faltings' original norm,
  and GR1's norm is `π^{-g} r`. So `x = h_F(A)` and `h = x + (g/2) log π`, which is p. 352. The skeptic notes that
  the signed shorthand `(i/2)^g ∫ η ∧ η̄` in a docstring is the positive density only up to the usual sign; the
  definition uses the positive density.
* **Independence.** GR1's "indépendante des choix de K et de 𝒜" applies to every accepted witness, so the print's
  bound holds for every `x` with the predicate. The Lean does not assert uniqueness and does not need it.

## 4. R2 `GaudronRemondSec9LowerGR1` and the field `GaudronRemondSec9LowerGR1Weak` (GR1, Corollaire 8.4)

| Lens | Verdict |
| --- | --- |
| Fidelity | PASS (R2): every clause MATCH; nothing stronger. |
| Skeptic | PASS (R2): no missing hypothesis; not vacuous (an explicit elliptic curve over ℚ). |
| Red team | PASS (R2 and the weak form): the constant `-3/2` is a weakening the print implies. |

The print, p. 400: "Pour toute variété abélienne A définie sur un corps de nombres, on a h(A) ≥ −(1/2)(dim A)
log(2π)", introduced as "(sans hypothèse de polarisation)"; there is no `g ≥ 1` at this locator.

The Lean puts `x + (g/2) log π` on the height side, exactly the print in `h_F`: `h_F(A) ≥ −(g/2) log(2π²)`. The
weak form `−(3/2) g ≤ x` follows because `½ log(2π²) < 3/2`; Gaudron and Rémond make the same weakening on p. 352,
and Lean proves it (`gaudronRemondSec9LowerGR1Weak_of_GR1`). The row name keeps "Sec9" from the citation in the Duke
paper's §9 (proof of Lemme 9.1, p. 2098, which cites Corollaire 8.4); the docstrings cite Corollaire 8.4, p. 400.

## 5. R3 `GaudronRemondThm14GR1` (Duke 163, Théorème 1.4)

| Lens | Verdict |
| --- | --- |
| Fidelity | PASS: every clause MATCH or DIRECT INSTANCE; the Duke journal-text comparison pending. |
| Skeptic | PASS on the authors' copy; the journal-text comparison pending. |
| Red team | PASS: every difference harmless; publisher-copy check pending. |

The print, p. 2060: "Soient K une extension de k et A' une variété abélienne définie sur k et isogène à A sur K. Il
existe un couple de K-isogénies A ⇌ A' de degré au plus κ(A)." P. 2058: "Soient donc k un corps de nombres et A une
variété abélienne sur k de dimension g ≥ 1", `α(g) = 2^{10} g³`, `κ(A) = ((14g)^{64g²}[k:ℚ] max(h_F(A),
log[k:ℚ], 1)²)^{α(g)}`, with "h_F(A) est la hauteur de Faltings stable de A (avec la normalisation originale de
Faltings, voir [GR1, paragraphe 2.3])". P. 2059: "couple d'isogénies φ₁ : A → A' et φ₂ : A' → A et l'on note
deg φ = max(deg φ₁, deg φ₂)". P. 2062: "Un morphisme φ : A → B est appelé isogénie lorsqu'il est surjectif de noyau
fini. … Le degré de φ, noté deg φ, est le cardinal de son noyau", over a field of characteristic 0.

The clauses:

* **Field.** One number field `K` carries `A`, `B` and the isogenies: the print's `K = k`. DIRECT INSTANCE.
* **Height.** The Duke paper takes its `h_F` from GR1 §2.3 (and its bibliography entry [GR1], p. 2107, is the
  *Commentarii* paper of §4), which is the predicate of §3. MATCH.
* **κ.** `grKappa g [K:ℚ] x` is the printed formula term by term, with `1024 g³ = α(g)`. MATCH.
* **Isogenies and degree.** `IsIsogenyPrinted` is a homomorphism, surjective, with finite kernel scheme, "surjectif
  de noyau fini"; `isogDeg` counts the `K̄`-points of the kernel, its order in characteristic 0 (finite étale).
  MATCH.
* **The couple.** Two separate isogenies `A → B` and `B → A`, each of degree at most `κ(A)`, is the printed couple
  with `deg = max`. MATCH.

## 6. Non-blocking points, with the reading the rows follow

1. **Commutativity** of the semi-abelian model is not part of `GroupModel`; it follows from separatedness and
   flatness by the argument of §3, not by a Lean theorem.
2. **Arakelov degree.** GR1 prints no formula for the normalized Arakelov degree; the standard one is used.
3. **Lattice and sheaf.** The stalk-built lattice and the global sheaf of differentials of GR1 are linked by the
   tree's height dictionary (`printedOmega_eq` and the lemmas before it), the last step from stalks to global
   sections being the standard fact of §3.
4. **Geometric connectedness.** EGA's notion is matched with the Lean's through the printed equivalence
   (4.5.1)-(4.5.2), not through a Lean identification.
5. **The Duke journal text** has not been compared with the authors' copy; R3 stays GLUE until it is.

## 7. What the readings do not establish

* **The evidence stays AI-READ.** No person has read these pages, and OPEN.md's count of human readings does not
  change.
* **Direction.** With R1, the GR1 rows imply the fields they replace, in Lean (`gaudronRemondSec9LowerAnSS_of_GR1Weak`,
  `gaudronRemondThm14Printed_of_GR1`, through `isGR1StableHeightOriginal_of_isAnStableHeightSS`). The converse,
  from the GR1 height to the Néron-model height, is not proved in the tree.
* **Not read:** the proofs of the three printed theorems and the results they cite; the Duke journal text.

## 8. Effect on the board

`gaudronRemondSec9LowerGR1Weak`, `gaudronRemondThm14GR1` and `egaIV_9_7_7_OL` replace `gaudronRemondSec9LowerAnSS`
and `gaudronRemondThm14Printed` in the research bundle `OpenResearchLeaves80`
(`ZInQKernel/OneProof/H/TailZ108.lean`). `egaIV_9_7_7_OL` is rated published, LEAF.
`gaudronRemondSec9LowerGR1Weak` is a consequence, GLUE: the weakening from Corollaire 8.4 is proved in Lean, but it
is an argument, so the row is not the printed form or a direct instance; a swap to Corollaire 8.4 itself is declined
as stronger (ruling of 2026-11-24, as for the replaced field). `gaudronRemondThm14GR1` is published, GLUE pending
the Duke journal text. The reading results above are unchanged by these ratings. The count of open statements goes
from 21 to 22, and the H part from 18 to 19. The strict count of the H part goes from 4/14 to 5/14, and from 4/17 to
5/17 with the three root hypotheses.
