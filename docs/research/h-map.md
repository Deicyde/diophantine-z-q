# A map of the height hypothesis H (SixContactMin): what is used, what it rests on, and routes

Status: research note (task h-map, 2026-11-11). It does for H what `cr3-map-needs.md` and
`cr3-map-literature.md` did for CR₃, and is the basis for a serious attempt on H. It rests on the
existing H notes (`rs-height`, `nt-h`, `h-leaves`, `h-v14`, `h-a011` with `rv-h-a011`, `h-cm` with
`rv-h-cm`, `ser-ell`), rechecked against the Lean tree at commit `d549dabb` and against the 11/5
manuscript `diophantine_zq.tex`. It adds one route not considered before: §3.2, route B1, which
replaces the integral model of the Shimura curve (an unpublished supplement) with Beckmann's
specialization theorem.

Marks:

- **VERIFIED**: checked here against the Lean source, the manuscript (line numbers "N5 L" are
  those of `diophantine_zq.tex`), a repository note that recorded its own check, or by an exact
  computation in `scratch/h-map/`, with the output saved beside the script.
- **STANDARD**: a published theorem, with reference. No source outside the repository could be
  read in this task, so this mark means the statement is classical and the repository notes or
  the manuscript cite it. The statement itself was not re-read here.
- **SPECULATIVE**: a proposal or an assessment, not proved.

"V14 L" refers to upstream's Version 14, which this host does not have. Facts about it are taken
from `h-v14.md`, `h-a011.md` and `rv-h-a011.md`, where they are marked VERIFIED.

## Summary

1. **What is used (§1).** The proof uses the single inequality
   `SixContactMin: h(u) ≤ H₆(D)·M_{S_mul}(u)²⁴ for all u ∈ ℚ \ 𝒞`. It is used at two
   points, and at each one the rational number `u` is an adversarial witness. The precision use
   would accept any bound that the natural-number machine can compute. The multiplication use
   needs a bound that is polynomial in `M`, with exponent below the test valuation 25, and an
   explicit constant within a tower-sized budget. Neither use can do with an ineffective
   constant or a bound on a subset of `u`. The constant and the exponent have enormous slack.
   Uniformity over all twists has none (VERIFIED).
2. **The citation chain (§2).** Lean `SixContactMin` ⇐ (Lean theorem) `SixContactEstimate` ⇐
   manuscript Theorem 4.1 ⇐ published theorems plus five upstream supplements. The weakest
   links, in order:
   - **(W1)** the manuscript's own new argument. The scalar descent to `G_ℚ`, the conductor
     bound `N ≤ QM²` and the transfer have had only AI reviews: four scoped Astra reviews and
     the repository's model notes. No human referee has read them.
   - **(W2)** the supplement `b11-integral-model`. It is unpublished and unread, and it is the
     only supplement whose content is not reproduced in this repository.
   - **(W3)** the uncited inputs: I2 (a homomorphism of abelian varieties with good reduction
     reduces) and the independence of `ℓ`. I1 (Carayol) is cited in V14, but the locator in
     Carayol 1987 is unchecked.
   - **(W4)** whether GR14's Theorem 1.4 is non-circular. The text is not on arXiv.

   The deep published inputs (Pan, or Khare–Wintenberger with Kisin; Faltings; GR14;
   Javanpeykar; Pazuki) are refereed.
3. **Routes (§3).**
   - (a) Narrowing H is already at its limit as a statement. `SixContactMin` is the one instance
     used. Weaker forms exist (any computable shape for the precision use, any exponent below 25
     and a far larger constant for the multiplication use), but none is easier to prove.
     Rating: high feasibility, very low payoff.
   - (b) Cleaning the justification is where the value is. All five supplements can go:
     - `direct-p5` goes by h-a011 (done; one review);
     - `a001`, `ly-d6` and `igusa-theta` go by published sources plus the scripts already in
       the repository (h-v14);
     - `b11` goes by the new **route B1**: Beckmann's specialization theorem, with Morita's
       potentially good reduction of QM surfaces and Serre–Tate (rating medium-high).

     I1 and I2 get textbook citations (rating high), and NoCM removes the CM branch (done; one
     review). After that, H rests on the manuscript's argument plus refereed theorems only.
   - (c) Eliminating H by redesign: very low. The cusp lemma and the affine-moduli lemma
     (nt-h §3) and the parity obstruction (rs-height R2) stand, and nothing found here changes
     them.
4. **Next tasks (§4).**
   - (T1) Write route B1 as an audit record.
   - (T2) An adversarial proof review of the manuscript's novel steps (N5 L631-857: scalar
     descent, the character β, the conductor bound at 2 and at `p > R`). This is the weakest
     link.
   - (T3) Consolidate one supplement-free trust statement for H and put it to a single review.

## 1. What the proof uses from H

### 1.1 The instance (VERIFIED, `ZInQKernel/Hypotheses/HeightMin.lean`)

`SixContactMin := ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 heightD * contactSupport
Mult.S_mul u ^ 24`. The parts:

- `𝒞 = {0,-15,-20,-24,-30,-60}`, and `h(a/b) = log max(|a|, b)`.
- `M_S(u)` is the product of the primes `p ∉ S` for which some `v_p(u-c)`, `c ∈ 𝒞`, is
  positive and odd.
- `H₆(D) = 2·10¹³·max(1, C_cm, (D^{D E₀})¹⁷)`, with `D = 324!·3^{256·324!⁴}`.
- `S_mul = S_ht ∪ 𝓗 ∪ supp(c_*)`.

It is the instance `S = S_mul`, `R = D` of the manuscript's form `SixContactEstimate`
(`sixContactMin_of_sixContactEstimate`, `ZInQKernel/Main.lean:70`). That instance is admissible
because `max S_mul ≤ D`, which follows from the proved `catalogueBound8`. Every main theorem in
`Main.lean`, `MainGreenTao.lean` and `RouteK/RankVariants.lean` takes `hH : SixContactMin` and
passes it unchanged to the two consumers below.

### 1.2 The two consumers (VERIFIED by reading the Lean proofs)

| | Precision (main-branch exactness) | Multiplication (finite box) |
| --- | --- | --- |
| Lean | `Assembly.ratHeight_le_bound_of_test` (`Assembly/Top/MainBranch.lean`) via `Compiler.Precision.sixContact_at_heightPrimes` | `Mult.slope_height_le` (`Multiplication/Soundness/ContactSupport.lean`) via `Mult.sixContact_at_Smul` (`Certificate/ConstantsProperties.lean`) |
| `u` | the value `t` of an accepted main branch, `Test n κ t` | each of the 27 slopes `t` with `SlopePred t ℓ₀ (certShifts n)` |
| what is known of `u` | `t ∉ 𝒞` and `M_{S_ht}(t) ∣ κF(n)` (`test_dvd`) | `t ∉ 𝒞` and `M_{S_mul}(t)²⁵ ∣ f = n₁n₂ − n₃` (local congruence) |
| H used as | `h(t) ≤ A0·M_{S_ht}(t)²⁴ ≤ 𝓑(n,κ) = A0·|κF(n)|²⁴`, from `M_{S_mul} ∣ M_{S_ht}` | `h(t) ≤ A_ht·|f|^{24/25}`, with `A_ht = H₆(R) ≥ H₆(D)` by monotonicity |
| conclusion | `|t − n| < e^{−𝓑}` forces `t = n` (upstream `eq_int_of_real_abs_sub_lt_exp_neg_of_height_le`) | `N² < 24A N^{48/25} + 10`, so `|nᵢ| < T = (48A)¹³` (`finite_box_of_heights`), and then the false-triple guard |

### 1.3 The slack

- **Shape, precision use** (VERIFIED). `A0` is the value of the `NExpr` `eA`
  (`Compiler/Precision/CappedTest.lean`: literals, `+`, `·`, `max`, powers and factorials;
  `eval_eA : eA.eval = A0`). The test `4ε < 4^{−𝓑}` is decided by capped arithmetic. So any
  monotone bound `Φ(M)` that an `NExpr` can express works, at the cost of a new program and a
  new decision-correctness proof (rs-height §2.2).
- **Shape, multiplication use** (VERIFIED, rs-height §2.3, nt-h §1.3). Suppose
  `h(t) ≤ A·M^e` and `M^k ∣ f`. Then `N < (48A)^{k/(2(k−e))}`. This needs `e < k`. Today
  `k = 25` and `e = 24`. Raising `k` (a new multiplication template) admits any fixed `e`. A
  bound that is super-polynomial in `M` bounds nothing.
- **Constant.** `T` enters the false-triple guard, and so the degree budget `2↑↑7` of
  `FrozenTarget` (`lean/Frozen/BoundedIntegerPolynomial.lean`: degree `< hyperoperation 4 2 7`,
  coefficients `< hyperoperation 4 2 8`). The budget is `log₂log₂log₂ T < 65536`, against about
  9013 today. So `log₂ A` could grow from `D⁷` to about `D^{2^{56000}}` (rs-height §2.3, nt-h
  §1.3; not re-derived here).
- **Effectivity** (VERIFIED as a reading). The constant must be an explicit upper bound. It is
  evaluated by the machine in the precision use and bounded in the size chapter in the
  multiplication use. "There is some `A`" with no bound on `A` gives no size bound, so a
  non-effective H (for example via Faltings' finiteness, or a Siegel-type constant) does not do.
- **Subsets of `u`** (VERIFIED, rs-height §1.4, nt-h §2.1). Each `t` is chosen by whoever
  satisfies the formula. The proof extracts only `t ∉ 𝒞` and the divisibility. A bound on
  average, outside a thin set, or with unknown finitely many exceptions does not suffice.
  Known, explicit exceptions would, but none are needed.
- **The set `S`.** `S_mul` is fixed, with about `10^{131}` primes. A bound whose constant grows
  with `max S` is fine up to the budget. The constant already contains `R^{R E₀}` with `R ≥ D`.
- **Uniformity** (VERIFIED as an argument, rs-height §2.4). With `M = 1` the bound would cap
  the height of every accepted slope, true triples included. So the bound must grow with `M`.
  The rationals with given contact support are the rational points on the `(ℤ/2)`-twists of a
  fixed curve of genus 17, and H is a uniform, effective, polynomial-in-the-twist Mordell bound
  for that family (rs-height §3.3). **This is the part with no slack.**

**Answer to "could a weaker bound do?"** Yes, there is room in the constant, in the exponent
(after a template change) and in the shape (precision use only). No, there is no room in
effectivity or in uniformity over `u`, and those two properties are the whole difficulty.

## 2. The citation chain

### 2.1 Links

| # | Link | Status |
| --- | --- | --- |
| L0 | `SixContactMin` is the hypothesis of every main theorem | Lean, kernel-checked (VERIFIED) |
| L1 | `SixContactEstimate → SixContactMin` (`Main.lean:70`, using `catalogueBound8`) | Lean theorem (VERIFIED) |
| L2 | `SixContactEstimate` is a faithful transcription of Theorem 4.1 | repository (audited transcription; h-leaves §5.2 rechecked the numerals) |
| L3 | Theorem 4.1 and its proof (frozen 11/5, N5 L377-972; Version 14 §4, V14 L448-1680) | **unpublished manuscript**. Four scoped Astra AI reviews (`docs/reviews/height-replacement/REPORT.md`: "not independent human peer review"); repository model notes h-leaves, h-v14, h-a011 + rv, h-cm + rv, ser-ell |
| L4 | published theorems that L3 cites (table 2.2) | published, refereed (statements mostly UNCHECKED here; see the notes) |
| L5 | five upstream supplements: `direct-p5-modularity`, `a001-moduli`, `ly-d6-normalization`, `b11-integral-model`, `igusa-theta` | **repository-only** (upstream). None was readable here or by the earlier notes |
| L6 | uncited inputs: I2 (`μ_σ` reduces), independence of `ℓ`, Faltings' Hom theorem at V14 L1552, the scheme theory delegated to `b11` | standard textbook facts with no citation |

### 2.2 The published leaves of L3, by proof step (from h-leaves §5.1 and h-v14 §3)

| Step (N5 lines) | Leaf | Kind | Status |
| --- | --- | --- | --- |
| Shimura datum, `P¹_j`, branch data (409-441) | Baba–Granath, Canad. J. Math. 2008; Lin–Yang, Math. Z. 295 (2020); Deligne 1971/1979 (canonical model) | moduli | refereed |
| Integral model, tame quotient (441-544) | Buzzard, Duke 1997; uncited scheme theory; **`b11`** | moduli | refereed + **repository-only** |
| Fibre field and good reduction (545-579) | Serre–Tate 1968; Milne 2005 | standard | refereed / book |
| CM branch (580-630) | Fowler; Barquero-Sanchez et al.; GR14 | analytic | refereed; **removable by NoCM** (h-cm, rv-h-cm) |
| Scalar descent (631-716) | Skolem–Noether; Milne, *Arithmetic duality theorems* I | classical | book |
| Modularity (717-796) | **Pan, JAMS 35 (2022), Thm 1.0.4** (arXiv v2 statement VERIFIED by h-a011; journal numbering UNCHECKED); Faltings 1983/1986; Scholze 2013 + erratum, or Breuil 2000 Cor. 5.3.4; Deligne–Serre, Kato, Li, Shimura | modularity | refereed |
| Conductor (796-857) | Serre, *Local fields*; Silverberg–Zarhin 1995; Silverman; Carayol 1987 (V14; 1986 Théorème (A) proposed) | local | refereed |
| Transfer (858-905) | Javanpeykar, ANT 2014; GR14 Thm 1.4 (Duke 2014); Faltings 1983 Lemma 5; Bost via GR14 §9 | Arakelov / transcendence | refereed (GR14 non-circularity open) |
| Back to `u` (906-964) | Igusa 1967; Lin–Yang; Pazuki, BSMF 2012; **`igusa-theta`**, **`ly-d6`** | explicit | refereed + repository-only (content reproduced by `scratch/h-v14/igusa_check.py`) |

### 2.3 The weakest links (SPECULATIVE ranking; the facts are VERIFIED)

1. **W1, the manuscript's new mathematics (L3).** The argument that turns a QM fibre over a field
   of degree up to `324!` into a weight-two newform of level `≤ QM²` is new text. It covers the
   sign cocycle and its splitting by a Dirichlet character, the cochain β, the absolute
   upper-numbering bound (including the dyadic paragraph), and the identification of `r₃` and
   `r₅` in one system. These steps have only AI reviews. The published theorems they call are
   individually solid.
2. **W2, `b11-integral-model`.** It is the only supplement with content that no repository
   script reproduces (h-v14 §3.2). Its job is to show that parity of the contact valuations
   means good reduction: `K` is unramified at `p ∉ S`, and `A` has good reduction there. Route
   B1 (§3.2) replaces it.
3. **W3, uncited inputs (L6).** I2 and the independence of `ℓ` are textbook facts that are used
   without a citation. Carayol is cited in V14, but with an unchecked locator.
4. **W4, GR14 Theorem 1.4.** It is used for the explicit isogeny and, if R5.1 of h-leaves is
   adopted, for the Hom and semisimplicity theorems too. Its text is not on arXiv, and its
   non-circularity with respect to Faltings is unchecked (h-leaves §2.5, h-v14 §4 item 1).
5. **W5, the remaining supplements.** `direct-p5` is superseded by h-a011. The content of
   `a001`, `ly-d6` and `igusa-theta` is reproduced by `scratch/h-v14/` scripts from published
   inputs.

## 3. Routes

Ratings give the chance of success of the stated replacement (very low, low, medium, high).
The payoff is stated separately.

### 3.1 (a) Narrowing H to what the consumers need

- **A1, done.** `SixContactMin` is the single inequality the proof uses (rs-height R1, now in
  Lean).
- **A2, consumer-shaped split.** The replacement statement is
  `H_P(Φ) ∧ H_M(e, A)`. Here `H_P(Φ)` says `h(t) ≤ Φ(M_{S_ht}(t))` with `Φ` an `NExpr`, and
  `H_M(e, A)` says `h(t) ≤ A·M_{S_mul}(t)^e` with `e < 25` and `log₂log₂log₂ (48A)^{25/(2(25−e))+1}
  < 65535`. Rating: high (a Lean refactor of the two bridge lemmas and the precision program).
  Payoff: very low. Both parts are still uniform effective Mordell for the genus-17 family, and
  no known proof gives `H_P` without `H_M`.
- **A3, a subset of `u`, or an ineffective constant.** Ruled out (§1.3). Rating: very low.
- **A4, a better exponent.** With `log(14g)` bounded by `O(log QM)` instead of `5QM⁴`, the GR14
  step gives exponent about `20 + ε` (SPECULATIVE arithmetic from N5 L880-892). That is useful
  only if some future proof loses exponent elsewhere. Payoff: none now.

### 3.2 (b) Removing the supplements and the uncited inputs

**B1 (new): integral model → Beckmann specialization.** Rating: **medium-high**. Payoff: it
removes `b11`, Buzzard 1997 and the uncited scheme theory (A002, A078), which is the
weakest-link supplement W2.

*Replacement statement* (Lemma PR). Let `S ⊇ {p ≤ 324}`, `u ∈ ℚ \ 𝒞`, `K` the Galois closure
of the fibre field of `Y₃ → P¹_j` over `j = J(u)`, and `A/K` the fibre surface. Then:

- (i) for `p ∉ S`, `K` is unramified at `p` unless some `v_p(u − c)` is positive and odd;
- (ii) `A` has good reduction at every place of `K` not above 3.

*Proof outline* (SPECULATIVE as written; ingredients STANDARD):

- (i) `Y₃ → P¹_j` is a cover over `ℚ`. Its branch points are `0, ∞, −16/27`, with ramification
  indices `4, 6, 2`, because the level-3 group is torsion-free. Its geometric monodromy group
  `G` has order dividing `4·|(O/3O)^*|`. On one component it is the group
  `Γ*/±Γ(3)` of order `72 = 2³3²` (VERIFIED count, `o3_units.py`). In any case
  `G ⊆ S_{324}`, so `p ∤ |G|` for `p > 324`.
  - The branch points stay distinct modulo every `p ≥ 5`.
  - Beckmann's specialization theorem applies. (S. Beckmann, *On extensions of number fields
    obtained by specializing branched coverings*, J. reine angew. Math. 419 (1991); the
    mechanism is Grothendieck's tame specialization, SGA 1 Exp. XIII.) For `p ∤ |G|` with the
    branch divisor étale at `p`, the specialization at `j₀ ∈ ℚ` is unramified at `p` unless
    `j₀` meets a branch point `tᵢ` modulo `p`. If it meets `tᵢ` with multiplicity `m`, the
    inertia group is generated by a conjugate of `gᵢ^m`, where `gᵢ` has order `eᵢ`.
  - For `j₀ = J(u)` and `p ∉ {2,3,5,7,11,13}` (VERIFIED, `beckmann_check.py`):
    - `J(u)` meets `0` with multiplicity exactly `2v_p(u−c)`, at the unique contact `c` with
      `v_p(u−c) > 0`. With `e = 4`, the inertia is trivial exactly when `v_p(u−c)` is even.
    - It meets `∞` with multiplicity `6v_p(G(u))`. With `e = 6`, the inertia is trivial.
    - It meets `−16/27` with multiplicity `2v_p(H(u))`. With `e = 2`, the inertia is trivial.
      The identity `J + 16/27 = 16H²/(27G⁶)` is VERIFIED.
    - If `v_p(u) < 0`, then `J(u) ≡ J(∞) = −57600/7⁶` modulo `p`. That value is not a branch
      point modulo `p`: `J(∞) + 16/27 = 2⁴11²13²/(3³7⁶)`.
  - The cover is not geometrically connected. Apply the theorem to the Galois closure over its
    constant field `k`, a regular `G`-cover. Here `k` is unramified outside `{2, 3}`
    (SPECULATIVE detail).
- (ii) Let `v ∤ 3` be a place of `K`.
  - QM surfaces have potentially good reduction at every finite place (Morita, Hokkaido Math. J.
    10 (1981); STANDARD).
  - A point of the fine moduli scheme `Y₃` gives the full level-3 structure over `K`.
  - So inertia at `v` acts on `T₃A` through a finite group that is `≡ 1 (mod 3)`, and such a
    group is trivial (Serre's lemma: the kernel of `GL_n(ℤ₃) → GL_n(𝔽₃)` is torsion-free).
  - Néron–Ogg–Shafarevich (Serre–Tate 1968, Thm 1) then gives good reduction.
  - At `v | 3`, use level 5 in the same way, as N5 L814 already does.

This is all that N5 L441-563 delivers to the rest of the proof: `K` unramified outside
`T = S ∪ supp M`, and good reduction of `A` (VERIFIED by reading N5 L524-532, L847-850). The
degree bounds `324` and `324!` use only the generic fibre. *To check:* Beckmann's exact
hypotheses (G-cover over a number field, no vertical ramification when `p ∤ |G|` and the branch
points do not meet), and the moduli interpretation of the canonical model `Y₃` over `ℚ`.

**B2, Pan applied directly** (h-a011, reviewed in rv-h-a011: "proved after the listed repairs").
Rating: high. It removes the survey sentence and `direct-p5`. Remaining action: apply the repairs
R1-R9 of rv-h-a011.

**B3, `a001` / `ly-d6` / `igusa-theta` → published sources plus repository scripts** (h-v14
§3.2: `form_check.py`, `igusa_check.py`). Rating: high. The replacement leaves are Baba–Granath
2008, Lin–Yang 2020 and Igusa 1967, read through the scripts' exact checks.

**B4, the uncited inputs.**
- I1: Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), in the direction "level ≤ conductor".
- I2: the Néron mapping property (Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2).
- The independence of `ℓ`: Mumford, *Abelian varieties*, §19.
- Faltings' Hom theorem: Faltings 1983, Satz 4.

Rating: high. Payoff: small, but it closes W3.

**B5, NoCM** (h-cm, reviewed in rv-h-cm). Rating: high, done on paper. It removes Fowler, the
CM height formula and the CM use of GR14. The numeral `H₆` is unchanged.

**B6, Serre's argument at large `ℓ`** (Khare–Wintenberger with Kisin 2009; nt-h §4, ser-ell:
"proved after repairs"). Rating: high as an alternative to Pan, but it gives no reduction in
depth. Keep it as a fallback in case Pan's numbering or text causes trouble.

**B7, GR14 non-circularity.** Rating: medium. It needs the Duke text. Fallback: Masser–Wüstholz
(Ann. of Math. 1993) for the finiteness used in Tate's argument.

**After B1-B5** (SPECULATIVE outcome, VERIFIED inventory): H rests on the manuscript's argument
(W1) plus refereed sources only:

- Pan;
- Faltings;
- Scholze, or Breuil;
- GR14;
- Javanpeykar;
- Pazuki;
- Igusa;
- Baba–Granath and Lin–Yang;
- Deligne;
- Beckmann;
- Morita;
- Serre–Tate;
- Carayol;
- Silverberg–Zarhin;
- textbooks.

No supplement is left.

### 3.3 (c) Eliminating H by redesigning its consumers

| Idea | Replacement statement | Rating | Reason |
| --- | --- | --- | --- |
| C1, S-units (Baker) | `h(t) ≪ (P_S M)^{1/3+ε}` via Stewart–Yu, given tests that force `v_p(t−c) > 0 ⇒ p ∣ K` | very low | The local tests see only `ℚ_p^×/ℚ_p^{×2}`. A test of positivity at all primes would define `ℤ[1/S₀]`, which is the theorem itself (rs-height R2, nt-h §3.4-3.5) |
| C2, elliptic or genus-2 families with Baker-type Shafarevich | an effective Shafarevich bound for elliptic curves over `ℚ` (BCDT is already a PC leaf) | very low | Cusp lemma: cusps are met at a positive density of primes for every valuation parity. Affine-moduli lemma: a parity-to-good-reduction family has a complete moduli image (nt-h §3.2, §3.6) |
| C3, per-curve Chabauty or Runge on the genus-17 twists | effective Mordell for every twist `C_d` | very low | Not uniform in the twist; Runge and elliptic logarithms bound integral points only (rs-height R3) |
| C4, change the contact set | another branched family | very low | Fewer contacts make H false (genus 1). More contacts keep the uniformity problem (rs-height R7) |
| C5, trade H for a hypothesis the proof already assumes (CR₃) | none found | very low | CR₃ concerns ranks of congruent-number curves. H is a height bound on a compact Shimura curve, and neither implies the other (SPECULATIVE) |
| C6, formalize H in Lean | the proof of §2 in Lean | very low (in this project's horizon) | It needs Pan or Khare–Wintenberger, Faltings, GR14 and Arakelov theory |

No new route to elimination was found. The structural verdict of rs-height and nt-h stands:
parity tests turn H into uniform effective Mordell on a compact Shimura curve, and the only
known proof of that goes through modularity.

## 4. The most valuable next tasks

1. **T1, route B1 as an audit record** (closes W2). *First step:* pin the exact statement of
   Beckmann's specialization theorem, Crelle 419 (1991), with all hypotheses: `G`-cover versus
   mere cover, the field of definition, and the claim that there is no vertical ramification
   when `p ∤ |G|` and the branch locus is étale. If Beckmann's own text cannot be read, use a
   restatement that can (Legrand's "specialization inertia theorem" papers on arXiv), then match
   it to `Y₃ → P¹_j` with `|G| ∣ 4·72` and branch data `(0,4), (∞,6), (−16/27,2)`. Success:
   Lemma PR (i)-(ii) proved from numbered published statements, with no reference to an
   integral model of `Y₃`.
2. **T2, adversarial review of the manuscript's novel steps** (W1). *First step:* an rv-style
   line-by-line check of N5 L631-716 (sign cocycle, Brauer step, the bound on the order of β,
   `[L':ℚ] ≤ QM`) and N5 L796-857 (the break bound, the `p = 2` paragraph for β, `N ≤ QM²`),
   recomputing every inequality. These are the parts of H that no referee has read and that no
   published theorem supplies.
3. **T3, a single supplement-free trust statement for H.** *First step:* merge B2 (with the
   rv-h-a011 repairs), B3, B4, B5 (with the rv-h-cm repairs) and T1 into one proof outline of
   Theorem 4.1, listing for each step its published supplier (theorem number and edition).
   Then send it to one review. Success: KERNEL_PLAN's H row names no supplement.

## 5. Scripts (`scratch/h-map/`; each was run and its output saved)

- `beckmann_check.py` → `beckmann_check.output.txt`. It checks exactly (sympy):
  - `G⁶ − 97200F² = H²` and `J + 16/27 = 16H²/(27G⁶)`;
  - `J(∞)` and `J(∞) + 16/27`;
  - the prime supports of the resultants and discriminants of `F, G, H`, of the contact
    differences and of `57600`, which are all contained in `{2, 3, 5}`;
  - the leading coefficients of `G` and `H`, whose primes are `7` and `11, 13`.
- `o3_units.py` → `o3_units.output.txt`. For `O = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`,
  `i² = 2`, `j² = −3`:
  - closure of `O` under products and `det` of the trace form `= 36`;
  - `|O/3O| = 81`, with `72` units and `36` units of reduced norm `≡ 1 (mod 3)`.
- `log.md`: the work log.
