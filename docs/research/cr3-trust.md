# cr3-trust: a trust statement for CR₃

Status: research note (task cr3-trust, 2026-11-11). It does for CR₃ what `docs/research/h-trust.md`
does for H. It lists the Lean forms of CR₃ that main-theorem variants take and the Lean theorems
that connect them (§0). It gives a numbered outline of the published argument for
`CertifiedRankTYZClRk`, with a supplier and a status for every step (§1). It lists what remains
outside refereed sources and Lean (§2), and it drafts the trust docstrings (§3). The work log and
the scripts are in `scratch/cr3-trust/`. The Lean files were not edited.

Base: commit `14b28b23` (`wip/bp-catchup`). Adopted by task cr3-adopt after the repairs of its
review `docs/research/rv-cr3-trust.md` (changelog at the end); Lean names and line numbers were
rechecked at commit `81bb5d8f` (`wip/cr3-adopt`).

> **Locator correction (2026-11-12, loc-adopt).** TYZ's convolution lemma (L1062–1077), cited
> below as input I2, was called "Lemma 2.8"; it is printed as **Lemma 2.9**, and Lemma 2.8 is the
> symmetry lemma (`lem2.6`). The earlier count of TYZ's shared §2 counter skipped Definition 2.7
> (L842). VERIFIED for arXiv v1 by recounting `Period7.tex`; for the journal text, per the locator
> audit `docs/research/locators.md` (AI agents, 2026-11-12). The same audit read the author-hosted
> typeset journal text (Asian J. Math. 21 (2017)): arXiv Theorem 1.2 is journal **Theorem 1.4**,
> which keeps "all `d_i > 1`", so the counterexamples `n = 26565, 33117` refute it too; journal
> Theorem 1.2 is a different result. Line numbers still refer to arXiv v1 (`Period7.tex`). No step,
> status or argument below changed; the remarks that the journal was never read are kept as
> written, with dated notes.

Sources used. All are in the repository or on fleet branches. No source outside the repository
could be read (there is no network).

- `docs/research/nt-tyz.md` (the TYZ citation, Proposition N, Lemmas N1 and N2), with its reviews
  `docs/research/rv-nt-tyz.md` and `docs/research/rv-prop-n.md` (the second written independently,
  without the TeX source). nt-tyz and rv-nt-tyz read the arXiv TeX source of TYZ, `Period7.tex` of
  arXiv:1411.4728v1 (e-print sha256 `b295b160…fed2`). That file is not stored in the repository.
- `docs/research/tyz-5b.md` and `docs/research/rv-cr5b-sec3.md` (the bits form `T5b` against TYZ's
  `(7, 3)` sum, the Gross–Zagier step, a red team of 30 curves).
- `docs/research/rv-redei.md` (`gCl`, `T5bCl` and `RedeiFormula` against TYZ's `g` and
  Proposition N, with 30 PARI checks).
- `docs/research/pc-audit.md` (records RK4, RK7, RK9), `docs/research/rv-cr3-dl.md`,
  `docs/research/d2-check.md`, and `KERNEL_PLAN.md`.
- `docs/research/rv-cr3-rank.md` (commit `aec3b570`, now merged). It reviews the three `Rk`
  statements, RK9 and Mordell–Weil.
- `docs/research/rv-cr3-trust.md`, the adversarial review of this note (verdict: adopt after
  repairs; all repairs are applied here).
- The Lean files named in §0.

Marks, as in h-trust:

- **VERIFIED**: checked in this task, against a repository note, the Lean source, or by an exact
  computation run here.
- **STANDARD**: a published theorem, cited with a locator.
- **ARXIV-READ** (after a TYZ locator): `nt-tyz` and `rv-nt-tyz` (and, where said, `rv-cr5b-sec3`)
  read that place in the arXiv v1 TeX source. That is a model's reading of the preprint. The
  journal text has been read by no one. This mark plays the role of h-trust's ASTRA-READ.
- **UNVERIFIED** (after a locator): no one in this repository has read the source at that place.
  §2.4 says where to check it.
- **SPECULATIVE**: an assessment.

Status of a step. As in h-trust, the status is local: it is the weakest of the suppliers of the
step's own argument.

- **[L] Lean-proved**: a Lean theorem, with only the axioms `propext`, `Classical.choice`,
  `Quot.sound`.
- **[R] refereed**: a theorem in a refereed journal or a standard monograph. For TYZ this means
  the statement in arXiv v1, under the assumption that the journal version (Asian J. Math. 21
  (2017)) proves the same statement. That assumption is open (§2.3).
- **[P] published but unrefereed**: a preprint. None is used on the route of §1.
- **[M] repository argument reviewed by a model only**: a repository note, with the review named.
  **[M1]** means one model review; **[M2]** means two; **[M3]** means three.
- **[U] unchecked**: a repository argument that no independent review has read.
- **[S] script**: an exact computation in the repository with its output saved.

## Summary

1. **Forms (§0).** Fourteen Lean forms of CR₃ appear in main-theorem variants. Lean proves every
   implication between them that §0.2 draws. The weakest forms are `CertifiedRankDLRk` (and the
   equivalent `CertifiedRankDLInf`) and `CertifiedRankDLAdmRk`. The form whose content is
   literature is `CertifiedRankTYZClRk`: for squarefree `d ≡ 5 (mod 8)` with odd genus sum of class
   numbers, `C_d(ℚ)` has a point of infinite order. Lean derives **every** other form from it,
   including the three with the premise `#Sel₂ = 8` (`CertifiedRankTYZ`, `CertifiedRankTYZCl`,
   `CertifiedRank5b`) and `CertifiedRankDLAdmRk`, by chains of existing theorems (§0.2).
2. **The outline (§1)** has 26 steps in five parts: the match of the Lean statement (A1-A6), the
   deep results of TYZ (B1-B9), Proposition N (C1-C4), the rank step (D1-D4), and the Lean side for
   the other forms (E1-E3).
   - 3 steps are Lean-proved: E1-E3 (Rédei's formula; Theorem 3.6, Corollary 4.4, Proposition 0;
     RK9 and Mordell–Weil).
   - 2 steps are verified here: A4 (the curve, by hand) and A6 (a computation on 30 curves).
   - 10 steps rest on refereed theorems only: B1-B9 and C4 (TYZ and its imports; TYZ read in
     arXiv v1 only).
   - 3 steps rest on refereed theorems whose exact locators are still to check: D1-D3
     (modularity of `C_d`, the auxiliary non-vanishing theorem, Gross–Zagier). D4 records the
     alternatives that are not used (Lemma 5.5 of the manuscript, Kriz).
   - 7 steps are repository arguments with model reviews: A1, A2, A3, A5 (the match of `gCl`,
     `T5bCl`, the premises and the conclusion; rv-redei, rv-cr5b-sec3, rv-cr3-rank) and C1-C3
     (Lemmas N1 and N2 and the proof of Proposition N). C1-C3 have two model reviews, rv-nt-tyz
     and rv-prop-n, both "holds"; no human review.
   - No step is unchecked.
3. **What remains outside refereed sources and Lean (§2):**
   - (a) Proposition N: Lemmas N1 and N2, the facts F3 (first half) and F5, and the proof of
     nt-tyz §4.4. New mathematics, short, reviewed twice by a model (rv-nt-tyz, rv-prop-n). This
     is the only repository *argument* on the route.
   - (b) The match of the Lean definitions with TYZ's quantities: model reviews (rv-redei §1,
     rv-cr5b-sec3 §1, rv-cr3-rank §1), plus the check of this task (§1 A1-A5).
   - (c) The journal text of TYZ: never read. Theorem 1.2 is false as printed in arXiv v1 (nt-tyz
     §1.4), so whether the journal corrected it is open (§2.3). (2026-11-12: the AI locator audit
     `locators.md` read the journal text: it is Theorem 1.4 there, with the restriction kept, so
     it was not corrected; not re-read here.)
   - (d) About 25 locators UNVERIFIED (§2.4), and the TYZ locators ARXIV-READ only.
   - (e) Exact scripts (§2.5).
4. **New computation (§1 A6).** On 30 values of `d` (3 to 5 primes, `d < 30000`) with
   `T5b d = 1`: `T5bCl d`, computed from certified class groups, is `1`; the root number is `−1`; and
   the analytic rank is `1` (numerical). An explicit non-torsion point was found on 24 of the 30
   curves; on the other 6 the generator was too large for `ellrank` and for a search of the
   2-coverings to height `10⁵`, and there `ellrank`'s lower bound `1` is not certified (it rests on
   a parity step and lists no point). rv-cr3-trust §4.2 reproduced the count and the checks on 30
   other values. A scan of all 386 squarefree
   `d ≡ 5 (mod 8)` below 30000 with 3 to 5 primes and `T5b d = 1` finds `#Sel₂(C_d) = 8` in every
   case. So the premise `#Sel₂ = 8` of the non-`Rk` TYZ forms excluded nothing in that range
   (rv-cr5b-sec3 §1.6 had left this open).
5. **Drafts (§3).** A replacement docstring for `ZInQ.CertifiedRank` and trust paragraphs for
   `CertifiedRankTYZClRk` and `CertifiedRankRk`. The current docstring of `ZInQ.CertifiedRank`
   names Kriz's preprint first and "Gross–Zagier–Kolyvagin"; the draft leads with the TYZ route,
   names Gross–Zagier with its auxiliary input, and records Kriz as an alternative that is not
   needed (nt-tyz §5.1). The drafts are applied to the Lean files by task cr3-adopt.

## 0. The Lean forms of CR₃

### 0.1 The forms

Notation: `C_d : y² = x³ − d²x`, which is `shortCurve (−d²)` over `ℚ` in Lean; `Sel2 d` is the
2-Selmer group defined by local solubility of the 2-coverings `D_{a,b}` (`Selmer/Covering.lean`);
`Loc ℚ d a b` says `D_{a,b}(ℚ) ≠ ∅`. All forms take `d : ℕ` with `d % 8 = 5` and `Squarefree d`
(so `d > 0`). VERIFIED by reading the definitions at `14b28b23`; the locations were rechecked at
`81bb5d8f`.

| Form | Definition | Premises beyond `d ≡ 5 (8)` squarefree | Conclusion |
| --- | --- | --- | --- |
| `ZInQ.CertifiedRank` | `Hypotheses/CertifiedRank.lean:50` | a squarefree divisor `a` of `d` with `\|a\| ≡ 7 (8)`; the explicit system `Σ(𝒞_d)` has 8 solutions, one with first coordinate the class of `a` | a point `(x, y)` on `C_d` with `x ≠ 0` and `x/a` a square |
| `Selmer.CertifiedRankSel` | `RouteK/Selmer/Covering.lean:385` | `#Sel₂ = 8`; a class `(a, b)` with `\|a\| ≡ 7 (8)` | every `(a, b) ∈ Sel₂` has `Loc ℚ` |
| `Rank5b.CertifiedRank5b` | `RouteK/Rank5b/Row5b.lean:209` | `#Sel₂ = 8`; `det M_5b = 1` (Smith's row-5b matrix of Legendre bits) | as above |
| `Rank5b.CertifiedRankTYZ` | `RouteK/Rank5b/Sec3/TYZ.lean:125` | `#Sel₂ = 8`; `T5b d = 1` (genus sum with Rédei bits) | as above |
| `Rank5b.CertifiedRankTYZCl` | `RouteK/Rank5b/Sec3/RedeiStatement.lean:99` | `#Sel₂ = 8`; `T5bCl d = 1` (genus sum with `#Cl²`) | as above |
| `Rank.CertifiedRankRk` | `RouteK/Rank/Statements.lean:43` | `#Sel₂ = 8`; a class with `\|a\| ≡ 7 (8)` | `C_d(ℚ)` has a point of infinite order |
| `Rank.CertifiedRankTYZRk` | `Statements.lean:59` | `T5b d = 1` | as above |
| `Rank.CertifiedRankTYZClRk` | `Statements.lean:72` | `T5bCl d = 1` | as above |
| `Rank.CertifiedRankDLRk` | `RouteK/RankDL.lean:78` | (quantifies over slot inputs `Inputs β θ p₀`) | some slot choice `D` has points of infinite order on `C_{D.d₁}` and `C_{D.d₁\|θ\|}` |
| `Rank.CertifiedRankDLAdmRk` | `RankDL.lean:190` (variant `RankDL.lean:232`) | (over admissible `B`) | a multiplier `m \| 2730`, `p₀` and a slot choice with points of infinite order on the two curves |
| `Rank.CertifiedRankInf`, `…TYZInf`, `…TYZClInf`, `…DLInf` | `RouteK/RankInf.lean:109, 120, 131, 143` | as the `Rk` form of the same name | `InfinitelyManyPoints`: `y² = x³ − d²x` has infinitely many rational solutions (no group law) |

In words:

- **`CertifiedRank`** is the original hypothesis. It is stated with the explicit system `Σ(𝒞_d)`
  built from Legendre symbols, so no Selmer group, cohomology or L-function enters it.
- **`CertifiedRankSel`** says the same in terms of the textbook Selmer group: when `Sel₂(C_d)` is
  as small as the 2-torsion and one class allows, and one class has `|a| ≡ 7`, then `Ш(C_d)[2] = 0`.
- **`CertifiedRank5b`, `CertifiedRankTYZ`, `CertifiedRankTYZCl`** replace the 2-adic condition on
  a class by the parity condition of TYZ's `(7, 3)` row, written as Smith's determinant, as Rédei's
  bits, or with TYZ's class numbers `g(d_B) = #Cl(ℚ(√−d_B))²`.
- **The `Rk` forms** conclude only positive rank, which is what the literature gives. The two TYZ
  `Rk` forms have no Selmer premise at all.
- **The `DL` forms** restrict to the two curves that pole completeness uses. They depend on the
  internal definitions `Inputs`, `Slots`, `betaOf`, `thetaOf`, `Admissible`.
- **The `Inf` forms** say "`d` is a congruent number" in the classical form, without Mathlib's
  group law.

### 0.2 The implications (all Lean-proved, VERIFIED by reading)

`A → B` means Lean proves `A → B` (so `B` assumes less). `MW` means the theorem uses Mordell–Weil
for `C_d`, proved as `RouteK.Rank.fg_points`.

```
TYZClRk ──Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk──▶ TYZRk
TYZRk   ──certifiedRankRk_of_certifiedRankTYZRk (Cor 4.4, Thm 3.6)──▶ Rk
Rk      ──certifiedRankDLRk_of_certifiedRankRk (Prop 0 at one certificate)──▶ DLRk
TYZRk   ──certifiedRankDLRk_of_certifiedRankTYZRk──▶ DLRk
DLRk    ──certifiedRankDLAdmRk_of_certifiedRankDLRk──▶ DLAdmRk
DLRk, DLAdmRk ──poleCompleteness_of_certifiedRankDLRk / …DLAdmRk (RK9, MW)──▶ PoleCompleteness
Rk      ──certifiedRankSel_of_certifiedRankRk' (RK9, MW)──▶ Sel
Rk      ──certifiedRank_of_certifiedRankRk' ──▶ CertifiedRank
TYZRk   ──certifiedRankTYZ_of_certifiedRankTYZRk' (RK9, MW)──▶ TYZ
TYZClRk ──certifiedRankTYZCl_of_certifiedRankTYZClRk' (RK9, MW)──▶ TYZCl
TYZCl  ◀──certifiedRankTYZ_iff' (Rédei's formula)──▶ TYZ
TYZ     ──certifiedRank5b_of_certifiedRankTYZ (Thm 3.6; in fact ↔)──▶ 5b
5b      ──certifiedRankSel_of_certifiedRank5b (Cor 4.4)──▶ Sel
Sel     ──Selmer.certifiedRank_of_certifiedRankSel (Prop 0)──▶ CertifiedRank
CertifiedRank ──poleCompleteness_of_certifiedRank (descent lemma)──▶ PoleCompleteness
XInf   ◀──certifiedRank{,TYZ,TYZCl,DL}Inf_iff_…Rk (MW)──▶ XRk      (X = Rk, TYZ, TYZCl, DL)
```

Locations: `Redei/FourRank.lean:363, 367`; `Rank/Statements.lean:80`; `RankDL.lean:108, 119,
174, 198, 206`; `RankVariants.lean:31-46`; `Sec3/TYZ.lean:130`; `Rank5b/Row5b.lean:214`;
`Selmer/Prop0.lean:100`; `Assembly/PoleCompleteness.lean:23`; `RankInf.lean:148-164`. The
main-theorem variants of §0.3 are at `Rank5bSec3.lean:51, 64, 77`.

So `CertifiedRankTYZClRk` implies **every** form. The premise `#Sel₂ = 8` of `CertifiedRankTYZ`,
`CertifiedRankTYZCl` and `CertifiedRank5b` is a premise of the *target*, so it only weakens them.
The chains, each a composition of existing Lean theorems (rv-cr3-trust §1.1; elaborated, with the
three standard axioms, in `scratch/rv-cr3-trust/Check.lean`; no new declaration is needed):

```
TYZClRk ─Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk─▶ TYZRk
TYZRk   ─certifiedRankTYZ_of_certifiedRankTYZRk' (RK9, MW)─▶ TYZ
TYZ     ─certifiedRank5b_of_certifiedRankTYZ─▶ 5b
TYZClRk ─certifiedRankTYZCl_of_certifiedRankTYZClRk' (RK9, MW)─▶ TYZCl
TYZRk   ─certifiedRankDLRk_of_certifiedRankTYZRk─▶ DLRk
DLRk    ─certifiedRankDLAdmRk_of_certifiedRankDLRk─▶ DLAdmRk
```

(The three `#Sel₂ = 8` forms are logically stronger than `CertifiedRankSel`, because they assert
the conclusion for more `d`; that does not conflict with the chains above.)

### 0.3 The main-theorem variants

Each takes `SixContactMin` and one form, and concludes `FrozenTarget`.

| Form | Variant (`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_…`) | File |
| --- | --- | --- |
| CertifiedRank | `…_sixContactMin_certifiedRank` | `MainGreenTao.lean:38` |
| Sel | `…_sixContactMin_certifiedRankSel` | `MainGreenTao.lean:45` |
| 5b | `…_sixContactMin_certifiedRank5b` | `RouteK/Rank5bSec3.lean:51` |
| 5b (older) | `…_certifiedRank5b` (**also takes 22P**, `FixedPrimePattern`) | `RouteK/Rank5b.lean:37` |
| TYZ, TYZCl | `…_sixContactMin_certifiedRankTYZ`, `…TYZCl` | `RouteK/Rank5bSec3.lean:64, 77` |
| Rk, TYZRk, TYZClRk | `…_sixContactMin_certifiedRankRk`, `…TYZRk`, `…TYZClRk` | `RouteK/RankVariants.lean:52-67` |
| DLRk | `…_sixContactMin_certifiedRankDLRk` | `RouteK/RankDL.lean:220` |
| DLAdmRk | `…_sixContactMin_certifiedRankDLAdmRk` | `RouteK/RankDL.lean:232` |
| Inf forms | `…_sixContactMin_certifiedRankInf`, `…TYZInf`, `…TYZClInf`, `…DLInf` | `RouteK/RankInf.lean:176-197` |

So all 14 forms have a variant with `SixContactMin` alone. The `DLAdmRk` variant goes through
`poleCompleteness_of_certifiedRankDLAdmRk`. The `5b` variant without 22P goes through
`certifiedRankSel_of_certifiedRank5b` (Corollary 4.4) and the Sel variant; the older variant in
`Rank5b.lean` still assumes 22P (VERIFIED by reading).

## 1. Numbered outline of the argument for `CertifiedRankTYZClRk`

**Statement.** For squarefree `d ≡ 5 (mod 8)` with `T5bCl d = 1`, `C_d(ℚ)` has a point of infinite
order. Here `T5bCl d = Σ_π Π_{B∈π} #Cl(ℚ(√−d_B))² (mod 2)`, over the set partitions `π` of the
primes of `d` with one block `≡ 7`, one block `≡ 3` and all other blocks `≡ 1 (mod 8)`.

**Route.** `T5bCl d` is TYZ's `(7, 3)` genus sum `T_5b(n)` for `n = d` (Part A). Proposition N
(nt-tyz §4), from TYZ's Theorem 3.5 and its supporting results (Part B), turns `T_5b(n)` odd into
`𝓛(n) ≠ 0`, hence `ord_{s=1} L(C_n, s) = 1` (Part C). Gross–Zagier gives a point of infinite order
(Part D). Part E records the Lean steps that carry the conclusion to the other forms.

TYZ means Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number
problem*, Asian J. Math. 21 (2017), no. 4, 721–774, DOI 10.4310/ajm.2017.v21.n4.a5; read only as
arXiv:1411.4728v1. Line numbers `Lnnnn` refer to its TeX source `Period7.tex`, and theorem numbers
follow its section counter (nt-tyz, header, VERIFIED there).

### Part A. The Lean statement against TYZ's quantities

**A1. `gCl n` is TYZ's `g(n)`.**
- *Content.* `gCl n = Nat.card (powMonoidHom 2).range` on `ClassGroup (𝓞 (QNeg n))`, with
  `QNeg n = ℚ(√−n)` as Mathlib's `QuadraticAlgebra ℚ (−n) 0` and `𝓞` the full ring of integers.
  So `gCl n = #Cl² = #2Cl` in additive notation, which is TYZ's `g(n)` (TYZ §1, L363, ARXIV-READ;
  TYZ use `g` only modulo 2).
- *Suppliers.* rv-redei §1.1 (model review: `𝓞` is the integral closure, not `ℤ[√−n]`; Mathlib's
  `ClassGroup` is finite, so `Nat.card` is not the junk value); rv-prop-n §1 (`T5bCl` is
  Proposition N's `T_5b` with TYZ's `g`). Rechecked here by reading `RedeiStatement.lean:33-50`
  (at `81bb5d8f`), and again in rv-cr3-trust §1.2.
- *Status:* **[M2]** (rv-redei, rv-prop-n) + VERIFIED by reading.

**A2. `T5bCl d` is TYZ's `(7, 3)` genus sum.**
- *Content.* `T5bCl` sums over `Finpartition univ` of `d.primeFactors` (set partitions, nonempty
  blocks, each counted once) satisfying `Admissible5bNat` (exactly one block `≡ 7`, exactly one
  `≡ 3`, all blocks in `{7, 3, 1} (mod 8)`), the product `Π_B gCl(d_B)` in `ZMod 2`. This is
  `T_5b(n) = Σ_{d₀≡7, d₁≡3} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)` of Proposition N, with `𝓛₁` the set-partition
  sum over class-1 blocks. Under Lemma N2 it is the coefficient sum `N = Σ_{e≡7} ℓ_e g(e)` of
  nt-tyz §4.4, and it is the bracket of TYZ L2589-2593 under the set-partition convention
  (rv-nt-tyz finding A1).
- *Suppliers.* rv-redei §1.4 (T5bCl = Proposition N's `T_5b`); rv-cr5b-sec3 §1.4 (the same for the
  bits form `T5b`, and the match with TYZ's bracket, ARXIV-READ); rv-prop-n §1. Rechecked here
  by reading `RedeiStatement.lean:52-57` (at `81bb5d8f`) and `Sec3/Defs.lean:85-88`
  (`Admissible5bNat`), and again in rv-cr3-trust §1.2.
- *Status:* **[M3]** (three model reviews: rv-redei, rv-cr5b-sec3, rv-prop-n) + VERIFIED by
  reading.

**A3. The premises.**
- *Content.* Lean: `d : ℕ`, `d % 8 = 5`, `Squarefree d`. TYZ and Proposition N: `n` positive,
  squarefree, `n ≡ 5 (mod 8)`. The same. `T5bCl d = 1` in `ZMod 2` is "`T_5b(n)` odd".
- *Suppliers.* rv-cr5b-sec3 §1.5-1.6 (edge cases: `d` prime gives `T5b = 0`; the empty partition
  cannot occur); rv-cr3-rank §1.
- *Status:* **[M2]** + VERIFIED by reading.

**A4. The curve.**
- *Content.* `shortCurve (−d²)` is `y² = x³ − d²x` over `ℚ`. TYZ's curve is `E_n : ny² = x³ − x`, and
  `(x, y) ↦ (nx, n²y)` is an isomorphism `E_n ≅ C_n` over `ℚ` (multiply `ny² = x³ − x` by `n³`). So
  `L(E_n, s) = L(C_n, s)`, and the ranks agree.
- *Suppliers.* pc-audit RK4 (translation), rv-cr3-rank §1 (`shortCurve (−d²)` everywhere, and the
  group is Mathlib's `Point.instAddCommGroup`). The isomorphism was rechecked here by hand.
- *Status:* VERIFIED.

**A5. The conclusion.**
- *Content.* `∃ P : (shortCurve (−d²)).toAffine.Point, ¬IsOfFinAddOrder P` is "`rank C_d(ℚ) ≥ 1`"
  (with Mordell–Weil; without it, it is still exactly "some point of infinite order", which is what
  Gross–Zagier's Heegner point gives). The `Inf` form says that the affine solution set is
  infinite, which for `d ≠ 0` is equivalent by `exists_infinite_order_iff_infinitelyManyPoints`.
  Gross–Zagier's point has infinite order for the classical group law, and so it does in Lean:
  Mathlib's addition on `WeierstrassCurve.Affine.Point` is the chord-tangent law (the formulas of
  Silverman, *The Arithmetic of Elliptic Curves*, III.2.3; STANDARD). The `Inf` forms avoid the
  question: `InfinitelyManyPoints d` (`RankInf.lean:32`) uses no group law.
- *Suppliers.* rv-cr3-rank §1 (merged; commit `aec3b570`), which is also the supplier of E3; the
  `Inf` definitions were read here and in rv-cr3-trust §1.2 (the equivalence is Lean-proved).
- *Status:* **[M1]** + VERIFIED by reading; the `Inf` equivalence **[L]**.

**A6. Numerical check of the whole statement (this task).**
- *Content.* `scratch/cr3-trust/tyzcl_check.py`, output `out_tyzcl_check.txt`. The inputs are 30 of
  the 386 squarefree `d ≡ 5 (mod 8)`, `d < 30000`, with 3 to 5 primes and `T5b d = 1` (every 13th).
  For each `d`, `T5bCl d` is computed from its Lean definition, with the class groups of the full
  rings of integers from `bnfinit` certified by `bnfcertify` (87 fields, unconditional). The script
  also computes the root number (`ellrootno`), the analytic rank (`ellanalyticrank`, numerical) and
  a rational point. The point comes from `ellrank`, or, when `ellrank` reports rank 1 but lists no
  point, from a search of the 2-coverings (`ell2cover`, `hyperellratpoints` to height `10⁵`,
  `scratch/cr3-trust/cover_point.py`). It is checked exactly to lie on `C_d` and to have `y ≠ 0`.
  So it lies outside `C_d(ℚ)_tors = C_d[2]` (`elltors` gives 4) and has infinite order.
  (`ellheegner` was tried first and was too slow at conductor `32·10293²`.)
- *Outcome.* No failure. `T5bCl d = 1` on all 30, so it agrees with Lean's `T5b d = 1`, as
  `T5bCl_eq_T5b'` requires. The root number is `−1` and the analytic rank is `1` on all 30, and
  `ellrank` gives the bounds `[1, 1]`. An explicit non-torsion point was found on 24 curves (23 by
  `ellrank`, 1 by the covering search). On the other 6 (`d = 10293, 15565, 18309, 21909, 26285,
  27213`) none was found: their generators are too large for these searches (searching
  `d = 10293, 15565` to height `10⁶` also found nothing). This is consistent with analytic rank 1,
  but there the point is not certified. On these 6 curves `ellrank`'s lower bound `1` is not
  certified either: it lists no point and rests on a parity step, which is not a proof of
  positive rank (rv-cr3-trust §4.2; `d = 10293` gives `[1, 1, 0, []]`).
- *Selection scan.* `scratch/cr3-trust/select.py` (`out_select.txt`): all 386 values with
  `T5b d = 1` have `#Sel₂(C_d) = 8` (Selmer group from the local images of
  `scratch/rv-cr5b-sec3/mirror.py`, which follows Lean's `Loc`). So in this range the premise
  `#Sel₂ = 8` of `CertifiedRankTYZ(Cl)` removes no `d`. Whether `T5b d = 1` forces `#Sel₂ = 8` in
  general is SPECULATIVE (it would make the premise redundant, but nothing depends on it).
- *Independent recheck.* rv-cr3-trust §4.2 (`scratch/rv-cr3-trust/indep_check.py`): `T5bCl` from
  class numbers counted by reduced forms, `#Sel₂` from PARI's `ell2cover`; the same count 386, and
  on 30 other values `#Sel₂ = 8`, root number `−1`, conductor `32d²`; no failure.
- *Status:* **[S]** (numerical in the analytic rank only).

### Part B. The deep results of TYZ (inputs I1-I7 of nt-tyz §4.2)

These are cited, not reproved. rv-nt-tyz §1 checked each statement against the TeX source
(CORRECT, with the repair B1 for I2), and read the proofs without re-verifying them (rv-nt-tyz B4).
Their status is [R] under the journal assumption of §2.3.

**B1. External inputs of TYZ.**
- *Content.* Waldspurger's period formula and the Gross–Zagier formula of Yuan–Zhang–Zhang, as
  restated in TYZ's appendix (Theorems A.3, A.8 and A.9, label `EGZ`).
- *Suppliers.* J.-L. Waldspurger, *Sur les valeurs de certaines fonctions L automorphes en leur
  centre de symétrie*, Compositio Math. 54 (1985), 173–242 (UNVERIFIED). X. Yuan, S.-W. Zhang,
  W. Zhang, *The Gross–Zagier formula on Shimura curves*, Annals of Math. Studies 184, Princeton
  (2013) (UNVERIFIED). TYZ appendix numbering ARXIV-READ (nt-tyz §1.1). Which step of TYZ uses which
  appendix theorem was not traced here (SPECULATIVE: Waldspurger for the toric periods of §2,
  Theorem 2.1; the GZ formula for Theorem 3.3).
- *Status:* **[R]**.

**B2. Genus periods: Theorem 2.1, Lemma 2.9 and Proposition 2.3 (input I2).**
- *Content.* For odd squarefree `m ≡ 1, 3 (mod 8)`: `Σ ε 𝓛(d₁)𝓛(d₂) ≡ Q(m) ≡ g(m) (mod 2)` over
  non-ordered `m = d₁d₂` with `d₂ ≡ 1`, and `𝓛(1) = 1`.
- *Suppliers.* TYZ Lemma 2.9 (L1062-1077), Proposition 2.3 (L580-586), L1082, Theorem 2.1
  (L554-560), all ARXIV-READ. rv-nt-tyz B1: at `m = 3` Lemma 2.9 and Theorem 2.1 differ by the odd
  factor `w_K = 3`, so I2 is to be quoted as a congruence; the congruence holds under either.
- *Status:* **[R]** (as a congruence).

**B3. The fields: Proposition 3.2(1) (input I6).**
- *Content.* For `d ≡ 5`, `H'_d(√2)` is the ring class field of conductor 4 of `K_d`, and `H'_d`
  its fixed field under `σ_{1+2ϖ}`.
- *Suppliers.* TYZ Prop. 3.2(1), L1253-1258, ARXIV-READ.
- *Status:* **[R]**.

**B4. Generalized Gross–Zagier: Theorem 3.3 (input I1, `ε`-classes).**
- *Content.* `P_χ` is non-torsion only for `χ = χ_{d₀,d₁}` with `d₀ ≡ 5, 6, 7`, `d₁ ≡ 1, 2, 3`, and
  then `P_χ = ε(d₀, d₁) 2^{h₂(n)} 𝓛(d₁) 𝒫(d₀)` with `ε ≡ i` on `(5, 3)` and `≡ 1` otherwise. Only
  `ε ≡ 1` on `(5, 1)`, `(7, 1)`, `(7, 3)` is used (rv-nt-tyz B3).
- *Suppliers.* TYZ Thm 3.3, L1299-1311, ARXIV-READ; its proof uses Gross–Zagier and Kolyvagin
  through the published papers (L1993, nt-tyz §5.2 item 1).
- *Status:* **[R]**.

**B5. The genus point and its recursion (input I1).**
- *Content.* `Z(n) = Σ_{t∈Φ₀} f_n(P_n)^t` and
  `P(n) := Z(n) − Σ_{n=d₀d₁, d₀≡5,6,7, d₁≡1,2,3, d₁>1} ε(d₀, d₁) 𝓛(d₁) P(d₀)` in `A(ℍ'_n)`. The
  recursion is a definition. The inclusion `ℍ'_{d₀} ⊂ ℍ'_n` for `d₀ | n`, which it needs, is a
  quoted TYZ fact, not part of the definition and not proved here (rv-prop-n §6, correction 3;
  rv-nt-tyz quotes `ℍ'_n = L_n(i)·Π_{d₀ | n, d₀ ≡ 5,6} H'_{d₀}`, L1320).
- *Suppliers.* TYZ §3.1, L1320-1327, ARXIV-READ.
- *Status:* **[R]**.

**B6. Theorem 3.5, first assertion (input I3).**
- *Content.* `P(n)` represents `𝒫(n) = 2^{−1−ρ(n)} 𝓛(n) α_n` in `A(ℍ'_n) ⊗ ℚ`; and `𝒫(n) = 0` if
  `𝓛(n) = 0` (L1295). This is the deep step.
- *Suppliers.* TYZ Thm 3.5 (label `m3`), L1353-1356, proof L2343-2380, ARXIV-READ. Not the
  part (2) and not Theorem 1.2 (journal Theorem 1.4): those are not cited (nt-tyz §1.4: Theorem 1.2
  is false as printed).
- *Status:* **[R]**.

**B7. Torsion: Lemmas 3.16 and 3.18 (input I4).**
- *Content.* `A(ℚ(i)) = A[(1+i)³]`, and `A(ℍ'_n)_tors = A[(1+i)³]` for odd `n`.
- *Suppliers.* TYZ L2182-2185 and L2230-2232, ARXIV-READ (rv-nt-tyz B4 singles out Step 3 of
  Lemma 3.18, `√2 ∉ ℍ'_n`, as read but not re-verified).
- *Status:* **[R]**.

**B8. The action of `β'`: Theorem 3.6 and Lemma 3.21(1), (4) (input I5).**
- *Content.* With `β₁ = r_∞(−1)r₂(−2)` and a lift `β'`: for `e ≡ 5`,
  `Z(e)^{β'+1} ∈ g(e)τ((1−i)/2) + ℤτ(1)`; for `e ≡ 7`, `Z(e)^{β'+1} = g(e)τ(1/2)`. One lift
  `β' ∈ Gal(ℍ'_n/ℚ)` serves all `Z(e)`, `e | n`, at once: it restricts on each `ℍ'_e` to a lift of
  `β₁`, and Lemma 3.21 holds for any lift (rv-prop-n §6, correction 2; TYZ L2495-2500).
- *Suppliers.* TYZ Lemma 3.21, L2504-2525, through Theorem 3.6 (label `CM point2`), ARXIV-READ.
- *Status:* **[R]**.

**B9. The invariant `𝓛(n)` and the root number (input I7).**
- *Content.* `𝓛(n) = 0` exactly when `ord_{s=1} L(E_n, s) > 1`; for `ord = 1` its definition uses the
  regulator of a generator of `E_n(ℚ)/tors`, so it presupposes the rank part of BSD in analytic
  rank one, for which TYZ cite Coates–Wiles, Rubin, Gross–Zagier and Kolyvagin (published papers).
  The root number of `E_n` is `−1` for `n ≡ 5, 6, 7 (mod 8)`.
- *Suppliers.* TYZ §1, L318-345, ARXIV-READ (rv-nt-tyz I7, pc-audit RK4). Root number:
  B. J. Birch, N. M. Stephens, *The parity of the rank of the Mordell–Weil group*, Topology 5
  (1966), 295–299 (UNVERIFIED; quoted by TYZ at L318-327). Kolyvagin as cited by TYZ: Math. USSR
  Izv. 32 (1989), and *Euler systems*, Grothendieck Festschrift II (1990) (L3297-3304; UNVERIFIED).
- *Status:* **[R]**.

### Part C. Proposition N (nt-tyz §4)

**C1. Lemma N1** (Theorem 1.1 in the set-partition reading: `𝓛(m) ≡ Λ(m) (mod 2)` for odd squarefree
`m ≡ 1, 3`).
- *Suppliers.* nt-tyz §4.3; rv-nt-tyz §2 (CORRECT; also checked on 360 configurations, with `𝓛`
  computed from the recursion of I2); rv-prop-n §3 (VERIFIED, own abstract check that models I2
  as a congruence only). Uses B2 only modulo 2.
- *Status:* **[M2]** (rv-nt-tyz, rv-prop-n; no human review).

**C2. Lemma N2** (the coefficients of the genus point: `P(n) = Σ_e c_n(e) Z(e)` with
`c_n(e) ≡ Λ(n/e) (mod 2ℤ[i])` for `e ≡ 5, 7`).
- *Suppliers.* nt-tyz §4.3 (proof by unwinding B5, a fixed-point-free involution and odd Fubini
  numbers); rv-nt-tyz §3 (re-derived, CORRECT; 20 440 coefficients on 360 abstract configurations,
  152 on 30 real `n`, mutation tests). Scripts: `scratch/nt-tyz/coeff_check.py`
  (`out_coeff_check.txt`, 400 trials), `scratch/rv-nt-tyz/coeff_recompute.py`, `coeff_real.py`.
  rv-prop-n §4.1 (VERIFIED, 453 abstract configurations, own code). It replaces TYZ's
  Proposition 3.4, whose statement is ambiguous and whose proof is a sketch.
- *Status:* **[M2]** (rv-nt-tyz, rv-prop-n; no human review) + **[S]**.

**C3. Proof of Proposition N** (nt-tyz §4.4: `𝓛(n) = 0` ⟹ `T_5a(n) ≡ T_5b(n) ≡ 0`).
- *Content.* From B6 and B7, `P(n)` is torsion and lies in `A(ℚ(i))`. `β'` fixes `ℚ(i)` (F3, first
  half). Write `P(n) = Σ ℓ_e Z(e) + 2X` (C2), apply `β' + 1`, use B8, and use F5 (`ℍ'_n` is Galois
  over `ℚ`, from B3 and Cox, *Primes of the form x² + ny²*, Lemma 9.3, UNVERIFIED) to put
  `X^{β'} + X` in `A(ℍ'_n)_tors`. Then `a(1−i)/2 + N/2 ∈ ℤ[i]` gives `a ≡ N ≡ 0`, with
  `N ≡ T_5b(n)`. Contrapositive: `T_5b(n)` odd ⟹ `𝓛(n) ≠ 0`.
  The `ε`-information used is only `ε ≡ ±1` on the classes `(5, 1)`, `(7, 1)`, `(7, 3)` (as in B4);
  the value at `(5, 3)` is irrelevant (rv-prop-n §2, §4.3).
- *Suppliers.* nt-tyz §4.4, F3, F5; rv-nt-tyz §4 (each step CORRECT; F4 and the second half of F3
  are not needed, B2); rv-prop-n §4.2 (each step VERIFIED given I1-I7; F4 not used, correction 1).
  Differential tests: rv-nt-tyz `propN_diff.py` (30 values, all `T_5a` or `T_5b` odd cases have
  analytic rank 1); rv-prop-n §5 (51 values: 19 with an odd sum, all of analytic rank 1; 22 of
  analytic rank 3, all with `T_5a = T_5b = 0`).
- *Status:* **[M2]** (rv-nt-tyz, rv-prop-n; no human review).

**C4. Analytic rank one.**
- *Content.* `𝓛(n) ≠ 0` gives `ord_{s=1} L(E_n, s) ≤ 1` (B9, by definition). The root number `−1`
  (B9) makes the order odd, so it is 1.
- *Suppliers.* B9.
- *Status:* **[R]**.

### Part D. From analytic rank one to a point of infinite order

**D1. Modularity of `C_d`.** `C_d` has CM by `ℤ[i]`, so `L(C_d, s)` is a Hecke L-function and `C_d`
is modular (Deuring; Shimura). The step needs a nonconstant map `X_0(N) → C_d`, which Shimura
proved for CM curves: G. Shimura, *On elliptic curves with complex multiplication as factors of
the Jacobians of modular function fields*, Nagoya Math. J. 43 (1971), 199–208 (UNVERIFIED
locator, STANDARD content). Alternatively `C_1` is `X_0(32)` and `C_d` is its quadratic twist by
`χ_d`. BCDT is not needed. Conductor `32d²` for odd squarefree `d` (STANDARD; e.g. Koblitz,
*Introduction to elliptic curves and modular forms*, GTM 97, Ch. II, UNVERIFIED locator; checked
with `ellglobalred` on 30 values in rv-cr3-trust §2.1). *Status:* **[R]**.

**D2. An auxiliary imaginary quadratic field.** There is an imaginary quadratic `K` in which every
prime dividing `32d²` splits (so `disc K ≡ 1 (mod 8)`), with the nonvanishing *central value*
`L(C_d^K, 1) ≠ 0`. The root number of the twist is `+1`, so this is consistent with the sign
(rv-cr3-trust §2.1). Suppliers: D. Bump, S. Friedberg, J. Hoffstein, *Nonvanishing theorems for
L-functions of modular forms and their derivatives*, Invent. Math. 102 (1990), 543–618; or
Waldspurger 1985; or S. Friedberg, J. Hoffstein, *Nonvanishing theorems for automorphic
L-functions on GL(2)*, Ann. of Math. 142 (1995), 385–423. Exact theorem numbers UNVERIFIED
(pc-audit RK7, rv-cr5b-sec3 §2.2), and it is to be checked that the level `N = 32d²` (even, not
squarefree) is allowed (§2.4 item 3). Not Murty–Murty (Ann. of Math. 133 (1991)): that is, by its
title and usual role, the theorem for twists with nonvanishing *derivative*, the input for
analytic rank 0 (rv-cr3-trust §2.2; its text is UNVERIFIED). Numerically, for 16 sample values a
`D` with these conditions and `L(C_d^D, 1) ≠ 0` exists with `|D| ≤ 455` (rv-cr3-trust §2.1).
*Status:* **[R]**.

**D3. Gross–Zagier.** B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent.
Math. 84 (1986), 225–320: `L'(C_d/K, 1) = L'(C_d, 1) L(C_d^K, 1) ≠ 0`, so the Heegner point
`y_K ∈ C_d(K)` has infinite order. Complex conjugation acts by `ȳ_K = −ε(C_d) y_K^σ` up to
torsion (Gross–Zagier 1986; B. Gross, *Heegner points on X_0(N)*, in *Modular forms* (Durham
1983), 1984; UNVERIFIED locators). Since `y_K` is a trace from the Hilbert class field and the
root number `ε(C_d)` is `−1`, `y_K + ȳ_K = 2y_K + (torsion) ∈ C_d(ℚ)` has infinite order. The exact
hypotheses of GZ's main theorem (on the
discriminant and the level) are UNVERIFIED; the split condition at 2 makes `disc K` odd.
*Status:* **[R]**. Kolyvagin is not needed for this step (only `rank ≥ 1` is used; pc-audit RK7,
rv-cr5b-sec3 §2.2). He enters only inside TYZ (B4, B9), through the published papers.

**D4. Alternative to D2-D3.** The manuscript's Lemma 5.5 (`lem:forward-rank`) gives
`rank = ord ≤ 1`, but it cites Kolyvagin through the MPIM preprint MPI/90-69 and BCDT (nt-tyz §5.2
item 1). It is not used on this route. Kriz's 2-converse (arXiv:2002.04767, Theorem 10.13, a
preprint) is an alternative route to `CertifiedRankRk`, not needed (nt-tyz §5.1, rv-nt-tyz §6).
*Status:* not used.

### Part E. The Lean steps to the other forms

**E1. Rédei's formula** (`RouteK.Redei.redeiFormula`, `Redei/FourRank.lean:356`), giving
`T5bCl d = T5b d` (`T5bCl_eq_T5b'`) and `CertifiedRankTYZClRk → CertifiedRankTYZRk`. Review:
rv-redei (no blocker; 30/30 PARI checks of `gBit` against `#Cl²`). *Status:* **[L]**.

**E2. Theorem 3.6 and Corollary 4.4 of tyz-5b** (`det_M5b_eq_T5b`, `det_M5b_eq_one`), Proposition 0
(`Selmer.prop0Statement`, `sel_of_selmerCertified`), giving `TYZRk → Rk → DLRk → DLAdmRk` and
`TYZ → 5b → Sel → CertifiedRank`. Reviews: rv-cr5b-sec3 (statements), rv-cr3-dl, rv-cr3-rank.
*Status:* **[L]**.

**E3. RK9 and Mordell–Weil** (`loc_of_mem_sel2_of_infinite_order`, `fg_points`): a point of infinite
order and `#Sel₂ = 8` give every Selmer class (`Rk → Sel`, `TYZRk → TYZ`, `TYZClRk → TYZCl`,
`DLRk → PoleCompleteness`); and `Inf ↔ Rk`. Review: rv-cr3-rank (merged). *Status:* **[L]**.

The axiom check at the base commit is the 59/59 standard-axioms result of the base branch (task
statement); it was not rerun here. rv-cr3-trust reran it for the chains of §0.2 and the new
variants, and task cr3-adopt reran `scripts/print_axioms.lean` (61/61; changelog).

## 2. What remains outside refereed sources and Lean

### 2.1 Repository arguments, and how many model reviews each has

| Step | Argument | Reviews |
| --- | --- | --- |
| C1-C3 | Proposition N: Lemmas N1, N2, F3 (first half), F5, the proof of nt-tyz §4.4 | **two**: rv-nt-tyz (proved after repair B1), rv-prop-n (holds as stated; presentational corrections only); no human review |
| A1 | `gCl` is TYZ's `g` | two: rv-redei §1.1, rv-prop-n §1 (and this task and rv-cr3-trust, by reading) |
| A2 | `T5bCl` / `T5b` is TYZ's `(7, 3)` sum | three: rv-redei §1.4 (`T5bCl`), rv-cr5b-sec3 §1.4 (`T5b`), rv-prop-n §1 |
| A3 | premises | two: rv-cr5b-sec3 §1.5-1.6, rv-cr3-rank §1 |
| A5 | the `Rk` conclusion | **one**: rv-cr3-rank §1 (merged; commit `aec3b570`) |
| A5 | the `Inf` conclusion | **none** besides this task's and rv-cr3-trust's reading; the equivalence with `Rk` is Lean-proved, so only the reading of `InfinitelyManyPoints` itself is at stake |
| — | `DLRk`, `DLAdmRk` say what pole completeness uses | **one**: rv-cr3-dl (`DLAdmRk` was added later; read here and in rv-cr3-trust §4.1) |

No repository argument on the route is unchecked. The model reviews are not human refereeing.

### 2.2 Published theorems used, by status

All refereed: TYZ (B1-B9, under §2.3), Waldspurger 1985, Yuan–Zhang–Zhang 2013, Birch–Stephens
1966, Gross–Zagier 1986 (with Gross 1984 for the conjugation sign), Bump–Friedberg–Hoffstein 1990
(or Waldspurger; Friedberg–Hoffstein 1995) for D2, Deuring/Shimura (Shimura 1971) for modularity of
CM curves, Kolyvagin 1989/1990 and Coates–Wiles/Rubin inside TYZ, Cox Lemma 9.3, and (for E1)
Rédei 1934, which Lean has reproved. No preprint is on the route: Kolyvagin's MPIM preprint, Kriz
and Smith are not used (§1 D4; nt-tyz §5).

### 2.3 The journal version of TYZ (open)

nt-tyz §1.1: arXiv:1411.4728 has one version, v1 (18 Nov 2014). The journal version, Asian J. Math.
21 (2017), no. 4, 721–774, could not be read. Crossref registers no erratum. Three facts make the
comparison matter:

- Theorem 1.2 of arXiv v1, read literally ("all `d_i > 1`"), is false (`n = 26565, 33117`; nt-tyz
  §1.4, confirmed by rv-nt-tyz §5). It is not cited. Whether the journal corrected it is unknown.
  (2026-11-12: per the AI locator audit `locators.md`, which read the journal text, it is journal
  Theorem 1.4 and keeps "all `d_i > 1`", so the same values refute it; not re-read here.)
- Zhang (arXiv:2111.11618) cites the journal version as "Corollary 1.3" for what is Corollary 1.4
  in arXiv v1, so the journal numbering may differ (nt-tyz §3, warning).
- Every TYZ locator of Part B is an arXiv v1 locator (ARXIV-READ). Citations should give the arXiv
  version with the label (e.g. "Theorem 3.5 (`m3`) of arXiv:1411.4728v1").

Status [R] for B1-B9 assumes that the journal text proves the same statements (Theorem 3.5 first
assertion, Lemmas 2.9, 3.16, 3.18, 3.21, Proposition 2.3, 3.2, Theorem 3.3, the recursion). If it
differs, those steps become [P] (arXiv preprint) until compared. Check: the journal text of
Theorems 1.2, 3.3, 3.5 and Lemmas 3.16-3.21; Tian's ICM 2022 article (Proc. ICM 2022, Vol. 3,
1990–2010, open access) for an authoritative restatement (nt-tyz §6, routes 3 and 4).

### 2.4 Locators not read, and where to check them

ARXIV-READ (model reading of the arXiv v1 TeX, nt-tyz/rv-nt-tyz/rv-cr5b-sec3): every TYZ locator in
Part B, TYZ's bibliography entries (L3276-3277, L3297-3304, L3316-3317), and the appendix Theorems
A.3, A.8, A.9.

UNVERIFIED, in order of weight:

1. **TYZ, journal text**, Asian J. Math. 21(4), pp. 721–774: the statements of B2-B8 (§2.3).
2. **Gross–Zagier 1986**, the main theorem (Thm I.6.3 is the usual locator; UNVERIFIED) and its
   hypotheses on `D` and `N` (check that `N = 32d²` and odd `D` with all `p | N` split are allowed).
3. **Bump–Friedberg–Hoffstein 1990 (or Waldspurger 1985; Friedberg–Hoffstein 1995)**: the
   non-vanishing theorem for the central value `L(C_d^K, 1)` with prescribed local conditions at
   the primes of `32d²` (the theorem number in each paper), and whether the level `N = 32d²` (even,
   not squarefree) is allowed. Murty–Murty 1991 is the derivative case and is not the supplier
   unless its text is found to contain a value version (rv-cr3-trust §2.2).
4. **Birch–Stephens 1966**: the root number of `y² = x³ − n²x` for `n ≡ 5, 6, 7 (mod 8)`.
5. **Waldspurger 1985; Yuan–Zhang–Zhang 2013**: the forms restated in TYZ's appendix (compare with
   TYZ Thms A.3, A.8, A.9).
6. **Kolyvagin 1989, 1990; Coates–Wiles 1977; Rubin 1987**: as cited by TYZ for the rank part in
   B9 (bibliographic only).
7. **Cox, *Primes of the form x² + ny²***, Lemma 9.3 (generalized dihedral Galois group of a ring
   class field), for F5.
8. **Deuring / Shimura** for modularity of CM curves (Shimura, Nagoya Math. J. 43 (1971),
   199–208: the map `X_0(N) → C_d`), and the conductor `32d²` (D1).
9. **Gross–Zagier 1986 and Gross 1984** (*Heegner points on X_0(N)*, Durham 1983): the relation
   `ȳ_K = −ε y_K^σ` up to torsion (D3).
10. **Rédei 1934**, J. Reine Angew. Math. 171, 55–60: no longer needed (E1 is Lean-proved).

### 2.5 Repository scripts (exact computations unless marked)

| Script | Output | Used in |
| --- | --- | --- |
| `scratch/nt-tyz/coeff_check.py` | `out_coeff_check.txt` | C2 |
| `scratch/nt-tyz/certify_counterexamples.py`, `kummer_independence.py` | `out_certify.txt`, `out_kummer.txt` | §2.3 (Theorem 1.2 false) |
| `scratch/rv-nt-tyz/coeff_recompute.py`, `coeff_real.py`, `coeff_n7.py` | `out_coeff_*.txt` | C1, C2 |
| `scratch/rv-nt-tyz/propN_diff.py` (numerical ranks), `cr3_sample.py` | `out_propN_diff.txt`, `out_cr3_sample*.txt` | C3, §0 |
| `scratch/rv-cr5b-sec3/mirror.py` | `out_mirror.txt` | A2, A3 |
| `scratch/rv-redei/gbit_check.py` | in rv-redei §1.5 | A1, E1 |
| `scratch/d2-check/` | `d2-check.md` | DL forms |
| `scratch/cr3-trust/select.py`, `tyzcl_check.py` | `out_select.txt`, `out_tyzcl_check.txt` | A6 |

None was rerun here except through the reuse of `mirror.py`'s functions in A6.

### 2.6 Residual list in one line each

Outside refereed sources and Lean, `CertifiedRankTYZClRk` rests on:

- (i) Proposition N (Lemmas N1, N2, F3, F5, nt-tyz §4.4), **two** model reviews (rv-nt-tyz,
  rv-prop-n), no human review;
- (ii) the match of `gCl` (two reviews), `T5bCl` (three), the premises (two) and the `Rk`
  conclusion (one) with TYZ's quantities, plus this task's reading, rv-cr3-trust and A6;
- (iii) the journal text of TYZ, never compared with arXiv v1 (§2.3);
- (iv) the locators of §2.4;
- (v) the scripts of §2.5.

Steps with a single model review: A5 (`Rk` conclusion, rv-cr3-rank); the `DLAdmRk` form (read here
and in rv-cr3-trust). The `Inf` reading has none besides this task and rv-cr3-trust.

## 3. Draft docstrings (lines ≤ 100 characters; repaired after rv-cr3-trust, applied by cr3-adopt)

**`ZInQ.CertifiedRank`** (`ZInQKernel/Hypotheses/CertifiedRank.lean`): replace the docstring of the
definition.

```lean
/-- **Hypothesis CR₃** (certified rank). Let `d > 0` be squarefree with `d ≡ 5 (mod 8)`, and let
`a` be a squarefree (signed) divisor of `d` with `|a| ≡ 7 (mod 8)`. If the system `Σ(𝒞_d)` of the
configuration of `d` has exactly 8 solutions (dimension 3) and one of them has first coordinate the
class of `a` (`a₀ = [a < 0]`, `a₁ = 0`, `u_p = [p ∣ a]`), then the congruent number curve
`C_d : y² = x³ − d²x` has a rational point `(x, y)` with `x ≠ 0` and `x ∈ a ℚ*²`.

**Trust statement.** CR₃ is not proved in Lean. Lean derives it from `RouteK.Rank.CertifiedRankRk`
(`certifiedRank_of_certifiedRankRk'`), and that from `RouteK.Rank.CertifiedRankTYZClRk`
(`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`).
The latter says: for squarefree `d ≡ 5 (mod 8)` with odd genus sum of class numbers `T5bCl d`,
`C_d(ℚ)` has a point of infinite order. Its proof is published mathematics, one short repository
argument, and the match of the Lean definitions with TYZ's quantities (model reviews);
`docs/research/cr3-trust.md` lists every step with its supplier:

* *Tian–Yuan–Zhang* (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), 721–774; read in arXiv:1411.4728v1 only):
  Theorem 3.5 (first assertion), Theorem 3.3, Proposition 3.2, Lemmas 2.9, 3.16, 3.18, 3.21,
  Proposition 2.3 and the recursion of §3.1. Their proofs use Waldspurger's formula and the
  Gross–Zagier formula of Yuan–Zhang–Zhang. TYZ's Theorem 1.2 (journal Theorem 1.4) is not cited: as printed (all
  `d_i > 1`) it is false (`docs/research/nt-tyz.md` §1.4).
* *Proposition N* (`docs/research/nt-tyz.md` §4; model reviews `docs/research/rv-nt-tyz.md` and
  `docs/research/rv-prop-n.md`): from these inputs, if the `(7, 3)` genus sum `T_5b(d)` is odd
  then TYZ's `𝓛(d) ≠ 0`, so `ord_{s=1} L(C_d, s) ≤ 1`, and the root number `−1` (Birch–Stephens)
  gives `= 1`. It replaces TYZ's Proposition 3.4 by a direct parity count (Lemmas N1, N2). Not
  refereed.
* *Gross–Zagier* (Invent. Math. 84 (1986)), with an imaginary quadratic field satisfying the
  Heegner hypothesis and `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein): analytic rank one gives a
  point of infinite order. `C_d` is modular since it has CM (Deuring, Shimura). Neither BCDT nor
  Kolyvagin's MPIM preprint is needed; Kolyvagin's published papers enter only inside
  Tian–Yuan–Zhang.

Everything else is proved in Lean: Rédei's formula (`RouteK.Redei.redeiFormula`, which turns
`T5bCl` into Rédei's bits `T5b`), Theorem 3.6 and Corollary 4.4 of `docs/research/tyz-5b.md`
(`RouteK.Rank5b.det_M5b_eq_T5b`, `det_M5b_eq_one`: the premises here give `T5b d = 1`),
Proposition 0 (`RouteK.Selmer.prop0Statement`: `Σ(𝒞_d)` is `Sel₂(C_d)`), Mordell–Weil for `C_d`
(`RouteK.Rank.fg_points`), and the step from a point of infinite order and `#Sel₂(C_d) = 8` to a
point in the class `a` (`RouteK.Rank.loc_of_mem_sel2_of_infinite_order`; pc-audit RK9).
Kriz's 2-converse (arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an
alternative route; it is not needed (`docs/research/nt-tyz.md` §5.1). Weaker forms that Lean also
accepts: `RouteK.Rank.CertifiedRankDLRk` and `CertifiedRankDLAdmRk` (only the curves the proof
uses). -/
```

**`RouteK.Rank.CertifiedRankTYZClRk`** (`ZInQKernel/RouteK/Rank/Statements.lean`): the trust
paragraph.

```lean
**Trust statement.** Not proved in Lean. It is Tian–Yuan–Zhang (Asian J. Math. 21 (2017),
721–774, read as arXiv:1411.4728v1): Theorem 3.5 (first assertion) with Theorem 3.3,
Proposition 3.2, Lemmas 2.9, 3.16, 3.18, 3.21 and Proposition 2.3, as completed by Proposition N
(`docs/research/nt-tyz.md` §4, model reviews `docs/research/rv-nt-tyz.md` and
`docs/research/rv-prop-n.md`; not refereed): if `T5bCl d` is odd, TYZ's `𝓛(d) ≠ 0`, and with the
root number `−1` (Birch–Stephens) `ord_{s=1} L(C_d, s) = 1`. Then Gross–Zagier (Invent. Math. 84
(1986)), with an auxiliary imaginary quadratic field (Bump–Friedberg–Hoffstein), gives a point of
infinite order. `T5bCl d` is TYZ's `(7, 3)` genus sum with `g(d_B) = #Cl(ℚ(√−d_B))²`, so no Rédei
formula is needed; TYZ's Theorem 1.2 is not cited (false as printed). Lean derives every other
form of CR₃ from it (the forms with the premise `#Sel₂ = 8` through RK9 and Mordell–Weil,
`certifiedRankTYZ_of_certifiedRankTYZRk'`, `certifiedRankTYZCl_of_certifiedRankTYZClRk'`).
Step-by-step outline: `docs/research/cr3-trust.md`.
```

**`RouteK.Rank.CertifiedRankRk`** (`ZInQKernel/RouteK/Rank/Statements.lean`): the trust paragraph.

```lean
**Trust statement.** Not proved in Lean. Lean derives it from `CertifiedRankTYZClRk`
(`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`):
the premises give `T5b d = 1` by Corollary 4.4 and Theorem 3.6 of `docs/research/tyz-5b.md`
(`det_M5b_eq_one`, `det_M5b_eq_T5b`), and Rédei's formula (`RouteK.Redei.redeiFormula`) makes
that `T5bCl d = 1`. So it rests on Tian–Yuan–Zhang as completed by Proposition N
(`docs/research/nt-tyz.md` §4; model reviews `docs/research/rv-nt-tyz.md`,
`docs/research/rv-prop-n.md`) and on Gross–Zagier with an auxiliary field, exactly as
`CertifiedRankTYZClRk` (see there and `docs/research/cr3-trust.md`). Kriz's 2-converse
(arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an alternative, not needed.
The step to "every Selmer class comes from a rational point" (pc-audit RK9) is proved in Lean
(`loc_of_mem_sel2_of_infinite_order`, with `fg_points`).
```

## 4. Next steps

- Done: rv-prop-n is read and C1-C3 are [M2]; the drafts of §3 are applied, and the docstrings of
  `CertifiedRankSel`, `CertifiedRank5b`, `CertifiedRankTYZ` and the other CR₃ forms and variants
  are aligned (task cr3-adopt); KERNEL_PLAN.md leads with the TYZ route and lists the new
  variants; the CR₃^5b variant without 22P exists (`Rank5bSec3.lean:51`).
- The network checks of §2.4, items 1-4, 8 and 9, decide whether any statement changes; the rest
  are numbering (SPECULATIVE).
- A human referee (or a reviewer with the source) confirms the three quotations Proposition N is
  sensitive to (rv-prop-n §9): the recursion's coefficient `ε(d₀, d₁)𝓛(d₁)` with `ε = ±1` at
  `(5, 1)`, `(7, 1)`, `(7, 3)`; Lemma 3.21(1), (4); Theorem 3.5's first assertion.
- Optionally drop the older CR₃^5b variant with 22P (`Rank5b.lean:37`).

## Changelog

- 2026-11-11 (task cr3-adopt). Applied every repair of `docs/research/rv-cr3-trust.md` §6:
  - Summary 1, §0.2: `CertifiedRankTYZClRk` implies every form, including `CertifiedRankTYZ`,
    `CertifiedRankTYZCl`, `CertifiedRank5b` (premise `#Sel₂ = 8`) and `CertifiedRankDLAdmRk`; the
    chains of existing theorems are given (checked in `scratch/rv-cr3-trust/Check.lean`). The false
    claim "except the three" is removed here and in the §3 draft for `CertifiedRankTYZClRk`.
  - 14 forms, not 13; §0.1 and §0.3 list the variants `…_sixContactMin_certifiedRank5b`
    (`Rank5bSec3.lean:51`) and `…_sixContactMin_certifiedRankDLAdmRk` (`RankDL.lean:232`); the
    recommendation to add the former is removed; locations rechecked at `81bb5d8f`.
  - D2: the supplier is Bump–Friedberg–Hoffstein (or Waldspurger, or Friedberg–Hoffstein 1995) for
    the central value `L(C_d^K, 1) ≠ 0`; Murty–Murty is the derivative case and is dropped as
    supplier; the level `32d²` question is added to §2.4 item 3. Same change in §2.2 and §3.
  - Review counts after rv-prop-n: C1-C3 [M2] (no human review), A1 [M2], A2 [M3]; §2.1, §2.6 and
    the Summary updated; §3 drafts cite rv-prop-n.
  - B5: the inclusion `ℍ'_{d₀} ⊂ ℍ'_n` is a quoted TYZ fact. B8: one lift `β'` serves all `Z(e)`.
    C3: the `ε`-classes used are `(5, 1)`, `(7, 1)`, `(7, 3)`.
  - D1: Shimura 1971 locator. D3: the conjugation sign `ȳ_K = −ε y_K^σ` with locators (Gross–Zagier
    1986, Gross 1984); both added to §2.4. A5: Mathlib's `Point` law is the chord-tangent law; the
    `Inf` forms avoid it. A6 and Summary 4: on the 6 curves without a found point, `ellrank`'s
    lower bound `1` is not certified. rv-cr3-rank is merged and cited as the supplier of A5 and E3.
  - §3: the "Trust statement" opening of the `CertifiedRank` draft now names the match of the Lean
    definitions (model reviews) besides the repository argument.
  - §4 updated. rv-prop-n's corrections to nt-tyz.md are recorded in a dated note at its end.
