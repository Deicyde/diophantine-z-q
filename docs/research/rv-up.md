# rv-up: adversarial verification of the upstream surveys (up-map, up-h, up-cr3, up-rest)

Status: review note (task rv-up, 2026-11-11). I re-checked the key claims of `up-map.md`,
`up-h.md`, `up-cr3.md` and `up-rest.md` in the sources themselves. Sources:
- N5 is `diophantine_zq.tex` in this worktree.
- V13, V14 and V16 are `~/upstream/manuscripts/quartic_v1{3,4,6}.tex` (commit d76bcde).
- V15 is `~/upstream/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex`.

Line numbers are physical lines, with carriage returns stripped. The step log is
`scratch/rv-up/log.md`, and the scripts and their outputs are in `scratch/rv-up/`. No Lean was
run. Nothing under `ZInQKernel/`, `blueprint/` or another note was edited. Upstream text is
paraphrased, not quoted.

Marks:
- **VERIFIED**: read in the source (version, file, lines), or computed by a script in
  `scratch/rv-up/`.
- **STANDARD**: a published theorem, cited by reference.
- **SPECULATIVE**: an inference not checked here.

## Verdicts

| # | Claim (survey) | Verdict |
| --- | --- | --- |
| 1a | The N5 statements the fork formalizes or assumes are byte-identical in V16: Thm 1.1 (now 1.3), Thm 4.1 (now 4.2) with its constants, PC with the template x+3ℓ, RC, 22P, the catalogue definition and bound, the literal cutoff (up-map) | **CONFIRMED**, with a locator correction: the constants block is N5 L391-396 = V16 L492-497, not N5 L390-400 = V16 L489-499 (§1) |
| 1b | N5 §§9-12 are byte-identical in V16 (up-map) | **CONFIRMED**: N5 L4382-6442 = V16 L5365-7425, 2061 lines |
| 1c | `lean/Frozen/BoundedIntegerPolynomial.lean` and `construction/` are byte-identical to the fork's copies (up-rest) | **CONFIRMED** for the Lean file (cmp). `construction/` matches **except `README.md`**, which up-rest itself notes; "byte-identical" holds only for the other 27 files |
| 2a | Thm 4.1's statement and constants are identical in N5 and V13-V16 (up-h) | **CONFIRMED** |
| 2b | From V14 on, upstream fixed C8, C3 and A9 (up-h) | **CONFIRMED**. All present in V14, absent in V13; V14 L505-667 = V16 L530-692 |
| 2c | C9's Euler-factor inference kept verbatim (V16 L1468-1474 = N5 L769-775), and the other kept items (up-h) | **CONFIRMED**. One off-by-one: A9's descent sentence is V16 L1275-1278 (up-h says L1274-1276) |
| 2d | Amendment h-v16-adopt is sound and changes no constant or Lean statement (up-h) | **CONFIRMED**, with two clarifications. The determinant argument is correct (§2.3). It removes the local-algebraicity leaf but not the (HT) supplier and not Kronecker–Weber. **CORRECTED** in scope: up-h never treated the Baba–Granath item that up-map handed it, so h-v16-adopt should also carry the F1 citation change of §3.5 |
| 3a | Upstream records a defect in the proof of Baba–Granath Prop. 3.7, with a counterexample to a printed sentence (up-map) | **CONFIRMED** as mathematics: the separation claim fails exactly at Weierstrass points, and the product map has degree 4 (VERIFIED, `bg37.py`, and STANDARD). The printed sentence itself was not read here (no copy of the paper) |
| 3b | Chain BG 3.7 → 3.9 → Lin–Yang eq. (2) (up-map) | **CONFIRMED as upstream's account**. Neither paper was read here |
| 3c | h-trust cites BG 2008 and LY 2020 directly; F1 lists LY eq. (2) (up-map) | **CONFIRMED** (h-trust l.89, l.691, l.797) |
| 3d | Impact on h-trust (left open by up-map, not treated by up-h) | **F1 stands without BG 3.7/3.9 and without LY eq. (2); a citation change is needed.** The repository computation never used eq. (2). The P₋₂₄ normalization is now checked independently (VERIFIED, `endo24.py`, `theta24.py`). F1 does not stand on Igusa 1967 plus computation alone: it still needs LY Example 30's divisor statements. A2, A5 and A7 do not use 3.7-3.10; narrow their locators. Exact text in §3.5 |
| 4 | 22P is justified upstream by `v15:gi-full`; V16's first correction fills a missing step there; route AP uses no inverse theorem (up-rest) | **CONFIRMED** |
| 5 | Pole side unchanged since N5; upstream has none of the fork's CR3 fixes; the two OpenAI preprints are cited for attribution only (up-cr3) | **CONFIRMED**, with two minor corrections (§5): "Tian" does occur in V16 (Cai–Shu–Tian, not TYZ), and sections of openaipointwise appear in the source catalogue as provenance labels (already so in N5) |
| 6 | The notes and scratch files quote at most a line or two of upstream text (all) | **CONFIRMED**. The longest reproduced run is 21 words (VERIFIED, `quotes.py`) |

**Most serious correction.** up-map flagged a defect, recorded upstream, in the proof of
Baba–Granath Prop. 3.7, which lies upstream of Lin–Yang's eq. (2). h-trust's leaf F1 lists that
equation as a supplier, and up-h did not take the question up.
- **Mathematics.** Unaffected. The repository's `scratch/h-v14/igusa_check.py` derives the Igusa
  vector from Lin–Yang's Example 30 and never consumes eq. (2).
- **Normalization.** The one Example 30 datum tied to the disputed CM point, P₋₂₄, is now checked
  directly: by exact endomorphism-ring linear algebra and a 40-digit theta evaluation.
- **Record.** It is wrong as it stands: F1 (and N5 L911) cite eq. (2). §3.5 gives the
  replacement text.

## 1. Item 1: statements, §§9-12, Frozen, construction

Script `scratch/rv-up/envcmp.py` (my own, independent of up-map's `extract.py`). It extracts the
environment carrying a label, or a line range, and compares the CR-stripped lines exactly.
VERIFIED:

| Statement | N5 lines | V16 lines | Result |
| --- | --- | --- | --- |
| `thm:target` (1.1 → 1.3) | 60-76 | 113-129 | identical |
| `lem:assembly` | 110-113 | 204-207 | identical |
| `prop:generator` | 268-270 | 364-366 | identical |
| catalogue definition | 238-245 | 331-338 | identical |
| H setup and constants block (`𝒞`, `M_S`, F₀ … H₆, R ≥ max(D, max S, 10¹²)) | 378-399 | 479-500 | identical |
| `thm:height` (4.1 → 4.2) | 404-409 | 707-712 | identical |
| `lem:pole` (Q_pole, E_ℓ: y² = x(x−ℓ)(x+3ℓ) at N5 986 = V16 1721) | 988-991 | 1723-1726 | identical |
| `hyp:PC` | 1001-1004 | 1736-1739 | identical |
| `hyp:RC` | 1005-1011 | 1746-1752 | identical |
| `prop:box` | 1225-1229 | 2034-2038 | identical |
| `prop:fixed-prime-pattern` (22P) | 1267-1297 | 2076-2106 | identical |
| `prop:cutoff` | 6285-6293 | 7268-7276 | identical |
| §§9-12 and the first line of §13 (limits, compiler, bridge, cutoff and size, including the catalogue bound) | 4382-6442 | 5365-7425 | identical (2061 lines) |

Further results:
- **Locator correction.** The line after the H block differs: N5's "direct modularity argument"
  becomes "the published prime-five modularity theorem". That line is not part of the
  statement. up-map's ranges for the constants block (N5 l.390-400, V16 l.489-499) are
  misaligned: the offset is +101, not +99. up-rest's ranges (N5 L389-397, V16 L491-499) are off
  by one or two. The content claim is right.
- **Pole section opening** (N5 973-1011 against V16 1705-1752). The only differences are two
  added paragraphs: the openaihtp attribution (V16 1706-1707) and the paragraph on the OpenAI
  2-converse preprints (V16 1740-1744).
- **Lean.** `lean/Frozen/BoundedIntegerPolynomial.lean` is byte-identical (`cmp`; sha256
  `0889579a…`). `lean/` has 60 files on each side, and only `README.md` differs.
- **construction/.** 28 files on each side. Only `README.md` differs: upstream retitles it as the
  original large construction and links the quartic.
- **Earlier versions (item 2a).** The same comparison passes for `thm:height`, `thm:target` and
  the 22-line H block in V13 (480-485), V14 (682-687) and V15 (707-712).

## 2. Item 2: up-h

### 2.1 (a), (b): the C8, C3 and A9 fixes (VERIFIED, V16 L505-692)

The lemma `lem:qm-modularity-descent` is stated at V16 L505-528 and proved at L530-692.
- **C3.** `F` is chosen as a finite Galois extension of ℚ (L536-537). Milne 1986 Thm 15.1(a),
  p. 129, is cited at L561, and Fontaine, Astérisque 223, Thm 3.8, p. 142, at L564-565. The
  descent runs from a finite Galois local extension `K'/ℚ₅` (L566-571). Since `F_v/ℚ₅` is
  Galois, the restriction step `F → F'` of rv-h-c3 R1 is not needed.
- **C8.**
  - Arithmetic Frobenius is used throughout. A primitive normalized constituent `f` is chosen
    by Deligne–Serre §§1.6-1.9 and Lemma 3.2 (L586-601).
  - `k = 1` is excluded through Deligne–Serre Thm 4.1 and equal Hodge–Tate weights (L604-616).
  - All levels, including `5 | N`, are covered by Kato 2004 §6.3, §9.4 p. 188 and §§5.4, 8.3
    (L618-634).
  - Kato's (14.10.2)-(14.10.3) give `det V = ε₅^{1−k}ε_f^{−1}`, hence `HT(U_f) = {0, 1−k}` and
    `det U_f = ε_f ε₅^{k−1}` (L635-650). Then `m = 0` and `k = 2` (L652-659).
  - The determinant finiteness argument is at L660-667, and Kronecker–Weber (Washington
    Thm 14.1) at L669-672.
- **A9.** Milne, *Introduction to Shimura varieties* (Clay 2005), Thms 6.7-6.8 and Cor. 6.9,
  p. 319, at V16 L1271.
- **"From V14 on."** In V14, grep finds Fontaine at L540, Kato §9.4 at L597, the determinant
  argument at L635 and Milne 2005 at L1247. None of these is in V13. V14 L505-667 is identical
  to V16 L530-692 (163 lines), and V14 §4 differs from V16 §4 in five hunks only: the `b11`
  citations.

### 2.2 (c): items kept verbatim (VERIFIED, `envcmp.py --range`)

- C9's Euler-factor inference: N5 769-775 = V16 1468-1474.
- CM branch: N5 578-631 = V16 1285-1338.
- Javanpeykar and GR transfer: N5 868-907 = V16 1589-1628.
- rv-h-novel R2: N5 828 = V16 1539. R3: N5 835-839 = V16 1546-1550.
- A9's ℂ → ℚ̄ descent sentence (R-A9-2): N5 568-571 is identical at V16 1275-1278. V16 adds a
  Galois-descent sentence at L1264-1269, but it concerns the field `L`, not the ℂ → ℚ̄ step, so
  R-A9-2 is still open upstream.
- I2 and ℓ-independence are still uncited (V16 L1486-1489).

### 2.3 (d): the determinant argument, checked

Setting: `r₅ : G_ℚ → GL₂(E)` is continuous, with `V₅(A) ⊗ E ≅ r₅|G_F ⊕ r₅|G_F`. Here `F/ℚ` is
finite Galois and `A/F` is an abelian surface. Pan's theorem gives `r₅ ≅ U_f ⊗ δ`.
1. The Weil pairing of a polarization defined over `F` makes `G_F` act on `V₅(A)` through
   `GSp₄` with multiplier `ε₅`. So `det V₅(A) = ε₅²` on `G_F` (STANDARD).
2. Hence `(det r₅)² = ε₅²` on `G_F`. So `α := det r₅ · ε₅^{−1}`, a character of `G_ℚ`, satisfies
   `α² = 1` on `G_F`. Since `[G_ℚ : G_F] < ∞`, `α` has finite image.
3. `det r₅ = det U_f · δ² = ε_f ε₅^{k−1} δ²`. With `k = 2` this gives `δ² = α ε_f^{−1}`, which
   has finite image. So `δ` has finite image: its values are roots of unity of bounded order.

The argument is sound (VERIFIED as reasoning). It needs `k = 2`, which still comes from the
comparison of Hodge–Tate weights `{m, m+1−k} = {0, −1}`. Hence:
- **Removed:** the local-algebraicity step, i.e. the `conrad-local-characters` row (Serre 1968 /
  Tate 1967), and the inertia-finiteness remark of rv-h-c8 R4.
- **Kept:** the (HT) supplier (Saito 1997, or Scholl with Scholze, or Kato 2004), and
  Kronecker–Weber to turn `δ` into a Dirichlet character (V16 itself cites Washington for it).

up-h's phrase "removes … the class-field-theory step of C8" is right only if it means the
"Hodge–Tate ⇒ finite times a power of the cyclotomic character" inference.

The other parts of h-v16-adopt:
- **C3.** Choosing `F` Galois is a free choice that N5's context allows, since `A` is defined
  over a finite extension. Fontaine's Thm 3.8 is a locator whose content was not read here.
- **A4.** The Deligne 1971 locators are at V16 L995-1101 (Thm 4.7 at L1036; Thm 4.21, Cor. 5.7
  and Ex. 5.8 at L1099; Deligne 1979 2.2.5 and 2.3.1 at L1101). They are locators only, still
  unread.
- **E4.** CMH 2014 §2.3 and Cor. 8.4 (V16 L30664, L30677; bib L39342-39346). The arithmetic
  `log(π√2) = 1.4913 < 3/2` is right. The locator has been read only by upstream's model
  reviewer.

None of these touches a constant, `SixContactMin` or any Lean statement: all four are edits to
a trust note's proof text and locators. **(d) CONFIRMED.**

## 3. Item 3: the Baba–Granath record

### 3.1 The record (VERIFIED, read)

The record is `~/upstream/research/version14/proofs/a001-moduli-current-v1/ADVERSE-CASE.md`
(14 lines), with `PROOF.md` beside it. In paraphrase:
- BG's proof of Prop. 3.7 (printed p. 743) takes the map `φ = (f₁*, f₂*) : J(C(−24)) → E₁ × E₂`
  given by the two bielliptic quotients. It concludes that `φ` is an isomorphism from the claim
  that two points with the same images under both quotient maps are equal.
- The record shows `φφ† = ([2], [2])`, so `deg φ = 4`. It gives the Weierstrass points `(±√r, 0)`
  as a counterexample to the separation claim.
- It states that this is a concern about the proof, not a claim that the statement is false.
- It notes that Lin–Yang attribute their eq. (2), the weighted Igusa formula, to BG, and that
  BG's Prop. 3.9 uses 3.7's CM calculation.
- Upstream therefore derives the normalization from Lin–Yang Example 30 instead
  (`ly-d6-normalization-v1/PROOF.md`; V16 cites it at L781, L1203, L1633).

### 3.2 The defect, checked

`scratch/rv-up/bg37.py` (output `bg37.output.txt`; VERIFIED, symbolic) takes a generic
`C: y² = f(x²)` with `f` a cubic, `σ₁(x, y) = (−x, y)` and `σ₂ = σ₁ι`.
- The points `(±s, 0)` with `f(s²) = 0` have the same image under both quotients.
- Two distinct points with equal images under both maps must satisfy `σ₁P = σ₂P`, i.e.
  `ιP = P`. So the separation claim fails exactly at the six Weierstrass points.
- Even where it holds, injectivity on curve points does not imply injectivity on `J`.

`deg φ = 4`:
- `f_{i*}f_i^* = [2]`.
- The cross terms vanish, because `σ₁` acts by +1 on `f₁*E₁` and by −1 on `f₂*E₂`.
- So `φφ† = diag([2], [2])`, which has degree 16, and `deg φ = 4`. This is STANDARD:
  Frey–Kani 1991 and Kani show that a degree-2 cover gives
  `J ≅ (E₁ × E₂)/(graph of E₁[2] ≅ E₂[2])`.

Not checked: the record's numbers for C(−24) (`disc f = 442368 = 2¹⁴·3³`, `f(0) = 1 − √2`), and
the wording of BG's printed sentence. No copy of CJM 60 is available here. The verdict "a
counterexample to a printed sentence" therefore rests on upstream's reading of the paper; the
mathematics of the counterexample is VERIFIED.

### 3.3 The chain 3.7 → 3.9 → Lin–Yang (2)

Both links come from upstream's reading: the record and `ly-d6` §1, which notes that Lin–Yang's
introduction attributes (2) to BG. Neither paper was read here, so the chain is CONFIRMED only as
upstream's account. It fits the role of the disc −24 point, the only point that fixes the
constants `c₁, c₂, c₃` (ly-d6 §2; igusa_check.py §1). The record's own caveat is correct: an
isogeny `J(C) ~ E₁ × E₂` gives the CM field `ℚ(√−6)` but not the order. Points with CM by the
orders of discriminant `−24f²` all share that field.

### 3.4 Which h-trust steps depend on BG 3.7 or 3.9 (VERIFIED by grep and reading)

No h-trust step names BG Props 3.7-3.10.

| h-trust step (line) | BG / LY input named | Depends on BG 3.7/3.9? | Stands? |
| --- | --- | --- | --- |
| Summary 2 (l.89) | "Baba–Granath 2008, Lin–Yang 2020" (unspecific) | only through F1's eq. (2) | yes, after the F1 change; narrow the wording |
| A1 (l.169-179) | LY eq. (3), Lemma 3 (Riemann-form convention) | no | yes |
| A2 (l.181-193) | BG §2.1 Thm 2.1 and "§3"; LY Ex. 30 | Not as used. The disc −24 label at the `w₆` fixed points comes from `μ² = −6` and the maximality of `ℤ[√−6]` (Ogg; upstream a001 PROOF §4), not from 3.7. But the locator "§3" covers 3.7-3.10 | yes; narrow the locator to Thm 2.1, Lemma 3.1 and the §3 datum |
| A5, Lemma NV (l.252) | `W ≅ (ℤ/2)²` (BG §3 twisting involutions) | no | yes |
| A7 (l.285-299) | BG Thm 2.1 (polarized relation); Igusa vector from LY (13)-(14) and Ex. 29-30 via igusa_check.py | no: igusa_check.py uses Ex. 30, not (2) | yes |
| **F1** (l.688-696) | **LY eqs. (2), (14), (13)**; LNY §2.2; Igusa 1967; igusa_check.py | **cites (2)**, whose ancestry is BG 3.9 ← 3.7. The computation does not use (2) | **yes, but the supplier list must change** |
| §2.5 (l.797) | "Lin–Yang v1 Ex. 30 and eqs. (2), (13), (14)" read | record only | add "(2) read, not used" |

**What F1 actually needs.** F1 states `j = 3779136·(∏z_m)⁴/(∑z_m⁸)⁵` on the quaternionic locus
`X ≅ P¹_j`, with `j` defined by its values 0, ∞, −16/27 at P₋₄, P₋₃, P₋₂₄. Write
`j_θ := 16·144⁵χ₁₀²/ψ₄⁵`. By Igusa's theta expressions for `ψ₄` and `χ₁₀`, this is F1's right-hand
side.
1. **Global shape.** LY Example 30 gives `div s₂ = P₋₃/3` and `div s₅ = P₋₃/3 + P₋₄/2`. So
   `j_θ|X` has divisor `P₋₄ − P₋₃`, which makes it `c·j` for a constant `c`. This is a
   Lin–Yang input, and the only one F1 still needs. Whether Lin–Yang derive it independently of
   BG is SPECULATIVE here: upstream's ly-d6 §1 says they do, by their own CM-intersection
   method.
2. **The constant `c`.** igusa_check.py takes it from LY's `Y′₅` data at P₋₂₄. I checked it
   without Lin–Yang and without BG:
   - `scratch/rv-up/endo24.py` (exact; PARI `matkerint` and sympy; output `endo24.output.txt`).
     Let `A = ℂ²/(ΩZ² + Z²)`, with `Ω = z·[[3,5],[5,10]]`, `5z² + 4z + 2 = 0` (the disc −24
     Heegner point of X₀(5)), and its principal polarization.
     - `End(A)` has rank 8 and is Rosati-stable.
     - It contains N5's order `𝒪 = ℤ⟨1, I, (1+J)/2, (I+IJ)/2⟩`, with Rosati involution
       `a ↦ μ⁻¹āμ` and `μ = 2J + IJ`. The embedding was found, conjugated by a normalizer
       element, and every relation was rechecked on 4×4 integer matrices.
     - The commutant of `𝒪` is the order of discriminant −24, i.e. `ℤ[√−6]`. So `A` is the
       point P₋₂₄ for N5's datum.
   - `scratch/rv-up/theta24.py` (mpmath, 40 digits; output `theta24.output.txt`). At the four
     disc −24 Heegner forms, the ten even theta constants of `Ω` give `j_θ = −16/27` to within
     2·10⁻³⁹, so `c = 1`. Lin–Yang's value `x = −6 ± 6√−3` is also confirmed.
   - Consistency check at a third CM point: at disc −19 (`5z² + z + 1 = 0`), `endo24.py` finds
     the same QM datum with commutant of discriminant −19, and `j_θ = 81/64`. This agrees with
     the value of `j(P₋₁₉)` that Lin–Yang and BG report (`theta19.output.txt`,
     `endo19.output.txt`).

**Answers.**
- **Does F1 stand without BG 3.7/3.9?** Yes. It rests on LY Example 30 (the divisor
  statements), Igusa's theta expressions (Igusa 1967; LNY §2.2), igusa_check.py, and now
  endo24.py and theta24.py for the normalization.
- **Does it stand on Igusa 1967 plus repository computation alone?** No. The global shape on `X`
  (step 1) is QM-specific and comes from LY Example 30. Igusa 1967 gives only the universal theta
  formulas.
- **The smallest repair** is citation-level: drop eq. (2), name Example 30, and point to the new
  computation for P₋₂₄.
- **Optional further step.** Removing Lin–Yang entirely would need an independent source for
  step 1. Candidates are Hashimoto–Murabayashi's explicit family (Tohoku Math. J. 47 (1995)),
  compared with the Igusa vector by computation, or Elkies' X*(6) computations (ANTS 1998).
  SPECULATIVE; not attempted.

### 3.5 Exact h-trust.md changes (proposed; not applied, since this task may not edit other notes)

1. **F1, suppliers (l.690-695).** Replace the four bullets with:
   - Lin–Yang 2020, Example 30: the divisors of `s₂ = ψ₄` and `s₅ = 2¹²3⁵χ₁₀` on the quaternionic
     locus `X`. They make `χ₁₀²/ψ₄⁵` a degree-one function on `X ≅ P¹` with zero at P₋₄ and pole
     at P₋₃. Also eqs. (13)-(14), Igusa's conversion between `ψ₄, ψ₆, χ₁₀, χ₁₂` and `J₂…J₁₀`.
   - Lauter–Naehrig–Yang 2015 §2.2 and Igusa 1967 pp. 833-834 and 848: the theta expressions of
     `ψ₄` and `χ₁₀`.
   - `scratch/h-v14/igusa_check.py` (rerun, identical). It derives the Igusa vector from
     Example 30 without eq. (2).
   - The constant at P₋₂₄ is checked without Lin–Yang's `Y′₅` data and without Baba–Granath by
     `scratch/rv-up/endo24.py` and `scratch/rv-up/theta24.py`. The first shows, exactly, that at
     the disc −24 Heegner point of `Y′₅` the principally polarized surface carries N5's QM datum
     and its commutant is `ℤ[√−6]`. The second shows that the theta expression equals −16/27
     there.
   - Not used: Lin–Yang eq. (2), cited at N5 L911. Lin–Yang attribute it to Baba–Granath, whose
     Prop. 3.9 rests on Prop. 3.7, whose printed proof has a defect recorded upstream (rv-up §3).

   Status unchanged: **[R]+[S]**.
2. **A2 (l.185).** Replace "§2.1 (Thm 2.1) and §3" with "§2.1 Thm 2.1, Lemma 3.1 and the §3
   datum (p. 739); Props 3.7-3.10 are not used. The disc −24 label at the `w₆` fixed points
   follows from `μ² = −6` and the maximality of `ℤ[√−6]`, and is confirmed by
   `scratch/rv-up/endo24.py`."
3. **Summary 2 (l.89).** Replace "Baba–Granath 2008, Lin–Yang 2020" with "Baba–Granath 2008
   (Thm 2.1, Lemma 3.1; not Props 3.7-3.10), Lin–Yang 2020 (eq. (3), Lemma 3, eqs. (13)-(14),
   Examples 29-30; not eq. (2))".
4. **§2.5 (l.797).** Add "(eq. (2) read but not used; see F1)".

The same remark applies to `h-v14.md` l.335 (A017), which cites Lin–Yang (2). Leave that note to
its owner.

## 4. Item 4: 22P, GI and route AP (VERIFIED)

- **22P upstream.** V16's proof of 22P (L2215-2228) takes GI(20) from Section `v15:gi-full`
  (L2217), together with Green–Tao's main theorem and the Möbius–nilsequence theorem. The Part
  `v15:gi-full` runs from V16 L23831 to the next Part at L30185.
- **The V15 → V16 diff.** Hunks at 40, 42, 20060-20077 (Tao–Ziegler), **26822-26842 and
  26908-26915** (horizontal normalization, inside the GI Part), 30664 and 30677 (GR), and the
  bibliography.
- **"First correction."** `research/version16/FINDINGS.json` lists `horizontal-normalization`
  first and says it was missing at the finite-cover site. So V16's first correction (in
  FINDINGS order) fills a step missing from the inverse theorem that 22P uses. up-map §4 lists
  the corrections in manuscript order (TZ first); that is not a conflict. up-rest's L26821 should
  read L26822.
- **Route AP.**
  - `ZInQ.greenTaoDense` (`ZInQKernel/External/GreenTaoDense.lean:28`) and
    `ZInQ.Density.goodPrimeDensity` (`ZInQKernel/Density/PropDFinal.lean:24`) are theorems.
    There is no `sorry` in those directories and no `axiom` declaration in `ZInQKernel/` (grep).
  - `ZInQKernel/MainGreenTao.lean:21-31` feeds them to the main theorem.
  - `aud-ap.md` l.238-239 records `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
    That was not rerun: no Lean was needed.
  - Green–Tao 2008 uses transference and Szemerédi's theorem, with no Gowers inverse theorem
    (STANDARD).

**CONFIRMED.**

## 5. Item 5: the pole side (VERIFIED)

- **Pole section.** `diff` of N5 `sec:pole` (L973-1122) against V16 (L1705-1898) gives six hunks:
  - the openaihtp attribution;
  - the OpenAI 2-converse paragraph;
  - non-CM via Fowler;
  - the Poonen–Stoll locators;
  - BCDT via Silverman C.13.6;
  - Kolyvagin pp. 430-431 and the explicit `J₁(N) → A`.

  Only the eight lines carrying those sentences are removed. The template, `lem:pole`, PC, RC,
  the descent and the point step are unchanged.
- **Proof of PC.** Points come at V16 L1887-1897: RC is applied to `n` and `nθ`, and the forward
  lemma (Kolyvagin Thm 1, L1843) gives rank 1 and finite Ш, hence `Ш[2] = 0`. Kummer exactness
  then gives points with abscissa class `β`.
- **Inputs of RC.** RC uses Kato 1999 Thm 0.8 at 2 (L2779-2785) and Ribet 1990 (L15105-15116).
- **The fork's CR3 fixes.** None appears upstream. A grep of V16 finds:
  - Kriz: 0 hits; "congruent number": 0 hits.
  - "Tian": 4 hits, all **Cai–Shu–Tian** (explicit Gross–Zagier, used in the RC chain: L3353,
    L13307, L14908, L30146; bibliography L39483), not TYZ.
  - "Smith": Smith normal form only.
  - Gross–Zagier: cited once, in the table at L13316.

  up-cr3's line 182 says that a grep for Tian and Yuan finds only Yuan2024. **Corrected:** it
  also finds Cai–Shu–Tian. The conclusion that TYZ is never cited stands.
- **The OpenAI preprints.** openaipointwise and openaigoldfeld are cited at:
  - L1741-1742: RC is a special case of each; cited for attribution and not assumed.
  - L2572-2574: the organization of the RC proof follows openaipointwise.
  - L13064-13069: in the source catalogue, entries S30, S18, S29 and S32 are identified as
    Sections 2, 4, 5 and 9 of openaipointwise. They are declared provenance labels, not
    independent assumptions.

  The catalogue rows S12, S18, S29, S30 and S32, files `*-frozen-4eaee875.tex`, are already in N5
  (L6627-6647).
  - By the manuscript's own account, then, the preprints are not logical premises, but parts of
    the RC text derive from them.
  - Whether the in-manuscript RC proof is complete without them was not checked, and does not
    matter to the fork, which does not use RC.

**CONFIRMED**, with the two minor corrections above.

## 6. Item 6: quoting (VERIFIED)

`scratch/rv-up/quotes.py` matches 8-token shingles of the four notes and every file in
`scratch/up-*/` against an upstream corpus.
- **Corpus** (`quotes.corpus.txt`): 7307 files, 362 MB. It covers every `manuscripts/*.tex`, the
  V15 snapshot, `research/version14-16`, the collaborator notes, `docs/`, p214's
  `research/quartic214` and the top-level READMEs. Files over 5 MB and the other snapshots are
  excluded. (The file list, which names paths on the build host, is not kept in the repository.)
- **Runs of 25 words or more:** none (`quotes.output.txt` is empty).
- **Runs of 12 words or more** (6-token shingles, `quotes12.output.txt`): 19 runs. The longest
  are 21 words (up-map l.162-164, a one-sentence quotation of V16 l.155-159), then 16 and
  15 words. All are bibliographic titles or single-sentence quotations, so no passage exceeds
  about a line and a half.

This note quotes no upstream passage.

## 7. Scripts (all in `scratch/rv-up/`, outputs saved)

| Script | Purpose | Output |
| --- | --- | --- |
| `envcmp.py` | environment and line-range byte comparison | log Steps 1-2 |
| `bg37.py` | the BG 3.7 counterexample and degree | `bg37.output.txt` |
| `theta24.py [A B C num den]` | eta value `x` and theta `j_θ` at Heegner points | `theta24.output.txt`, `theta19.output.txt` |
| `endo24.py bound [A B C]` | exact `End(A_Ω)`, the 𝒪-embedding with the μ-Rosati involution, the commutant discriminant | `endo24.output.txt`, `endo19.output.txt` |
| `quotes.py` | quotation scan | `quotes.output.txt`, `quotes12.output.txt` |
