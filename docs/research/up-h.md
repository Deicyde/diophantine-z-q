# up-h: the H side of upstream Versions 13–16 and the 214-variable proposal

Status: research note (task up-h, 2026-11-11). It compares N5's Theorem 4.1 (the six-contact
height estimate behind `ZInQ.SixContactMin`) with upstream's Versions 13, 14, 15, 16 and the
214-variable proposal. It then checks each repair and gap that the fork's reviews found against
those versions, and gives a verdict on what upstream changes mean for `SixContactMin` and
`docs/research/h-trust.md`. The work log is `scratch/up-h/log.md`. The script is
`scratch/up-h/checks.py`, and its output is `checks.output.txt`.

Marks:

- **VERIFIED**: read in the source named, with version and line numbers, or checked by
  `scratch/up-h/checks.py`. For a repository note it means: read in that note.
- **STANDARD**: a published theorem, with reference. No source outside the two upstream clones
  and this repository was read (there is no network), so this mark records a citation, not a
  reading of the cited work.
- **SPECULATIVE**: an assessment or a recommendation.

**Sources and line numbers.**
- "N5 L": `diophantine_zq.tex` in this worktree.
- "V13 L", "V14 L", "V16 L": `~/upstream/manuscripts/quartic_v13.tex`, `quartic_v14.tex` and
  `quartic_v16.tex` (branch `codex/version16-fable-corrections`, commit d76bcde).
- "V15 L": `~/upstream/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex`.
- "p214": `~/upstream-p214/research/quartic214/` (commit 110cf72).

All manuscript line numbers are taken with carriage returns removed, the convention of
`h-v14.md`. Offsets inside the height section (VERIFIED, `checks.output.txt` and the log):
- V13 = N5 + 76 after N5 L378, because V13 inserts a five-line preamble at L449-453.
- V15 = V16. Each is V14 + 25 up to V14 L784, and V14 + 24 from V14 L786 on.

The upstream text is cited by line, not copied.

## Summary

1. **Theorem 4.1 itself never changes (VERIFIED).** Its constants block and statement are
   identical in N5 (L378-397, L404-409), V13 (L454-473, L480-485), V14 (L454-473, L682-687), V15
   and V16 (L479-498, L707-712); see `checks.py` §2.
   - V16's headline theorem, the 292,890,231,905-variable polynomial `thm:target` (V16 L113),
     is still proved from it: "Theorem `thm:height` proves H for each of the two sets of
     constants" (V16 L219).
   - The proof changes only between V13 and V14:
     - V13's height section is N5's plus the five preamble lines.
     - V14 rewrites it (audited in `h-v14.md`).
     - V15 changes five lines: it replaces the four citations of the `b11-integral-model`
       supplement by in-manuscript sections and adds a pointer to a new Tate-module appendix.
     - **V16's height section is byte-identical to V15's** (`checks.py` §3).
2. **No version removes or weakens H for the fork's construction.**
   - The new estimates of V15/V16 and the 214 proposal are *five-contact* estimates on a
     different curve: the Shimura curve of the discriminant-210 algebra, with contacts
     `∞, 0, 1, 2401, −343/32`.
   - They serve only the quartic constructions. They give much smaller exponents (24, 19, then
     3 up to a log; 2103/1024 in p214).
   - They rest on the same architecture: QM surface, scalar descent, modularity at 5, conductor,
     height of `J₁(N)`, isogeny. They prove nothing about the six contacts
     `𝒞 = {0, −15, −20, −24, −30, −60}`.
   - No version replaces H by a finite computation or by a published theorem.
3. **Repairs (§2).** Of the gaps the fork's reviews found in N5's proof:
   - **Fixed or made moot in V14 and later (and so in V16):**
     - C8's three problems: the normalization of `ρ_g`, weight one, and levels divisible by 5;
     - C3's restriction step R1 (avoided by choosing `F` Galois) and its citation swaps R2,
       including the Fontaine exposé;
     - A9's citation of Milne's course notes (swapped to Milne 2005, Clay);
     - I1 (Carayol 1987 now cited).
   - **Kept as in N5, in every version:**
     - C9's Euler-factor inference (R-C9-1), verbatim at V16 L1468-1474;
     - A9's implicit descent step (R-A9-2);
     - rv-h-novel R1-R3 (R1 only partly addressed);
     - I2 and the independence of `ℓ` (uncited);
     - the CM branch, which NoCM replaces (byte-identical, V16 L1285-1338).
   - **Changed, in the direction the fork did not take:**
     - The integral model is now written out in the manuscript (V15/V16 §`v15:marking-descent`).
       It is Buzzard's route made explicit, not Lemma PR.
     - The modularity input is now a survey sentence plus a project supplement (Calegari ICM
       2022 with `direct-p5`), where N5 applied Pan Theorem 1.0.4 directly.
     - Three other project supplements are now cited in the height section (V16 L748, L781,
       L1203, L1633, L1647).
4. **Gaudron–Rémond (§3, VERIFIED).** V16's "two corrected Gaudron–Rémond citations" are at V16
   L30664 and L30677, in the five-contact section `v15:height`, not in Theorem 4.1's proof.
   - They move Bost's lower bound and the half-log-degree isogeny variation from the Duke paper
     to the CMH paper (*Théorème des périodes…*, CMH 89 (2014), §2.3 and Cor. 8.4).
   - Upstream records that the Duke citations of the height section (Thm 1.4 twice, §9 once;
     V16 L1322, L1599, L1616 = N5 L615, L878, L895) are kept on purpose.
   - h-trust's steps E3 and E4 cite exactly those Duke places. Nothing in h-trust is
     invalidated. The CMH places are a second locator for E4, read by upstream's V16 reviewer.
5. **Verdict (§4).**
   - The strongest upstream proof of H is V16 §4 (= V15 §4). It still assumes a survey
     statement, four unpublished project supplements, the Euler-factor inference, uncited I2
     and `ℓ`-independence, the CM branch, and the same deep published inputs.
   - h-trust's proof is already supplement-free and has C9 repaired, so it is stronger than any
     upstream version on the points where they differ.
   - **No upstream change lets the fork narrow or remove `SixContactMin`.**
   - h-trust can be shortened only marginally (SPECULATIVE):
     - C8: adopt V14's determinant argument for the finiteness of the twist. This drops the
       local-algebraicity leaf (Conrad's appendix, or its swap to Serre 1968 / Tate 1967).
     - C3: adopt the Galois choice of `F`, so that R1 is not needed.
     - Add locators: Kato 2004 §9.4 for C8 at all levels, Fontaine's exposé (Astérisque 223,
       pp. 113-184, Thm 3.8), CMH 2014 §2.3 for E4, and V16's Deligne 1971 locators for A4.

## 1. The analog of Theorem 4.1 in each version

### 1.1 Theorem 4.1 (`thm:height`) in V13-V16 (VERIFIED)

| | N5 | V13 | V14 | V15 | V16 |
| --- | --- | --- | --- | --- | --- |
| height section | L377-972 | L448-1048 | L448-1680 | L473-1704 | L473-1704 |
| statement and constants | L378-409 | identical | identical | identical | identical |
| proof | L410-966, appendix lemma L10939-11000 | = N5 (lemma at L16472) | rewritten (h-v14) | V14 with five lines changed | = V15 |
| supplement citations in the section | 0 | 0 | 10 | 6 | 6 |

Constants, in every version: `𝒞 = {0,−15,−20,−24,−30,−60}`, `F₀ = 324!`, `D = F₀·3^{256F₀⁴}`,
`G₀ = 116064000000`, `E₀ = 10(DG₀)²`, `Q_R = R^{RE₀}`, `B_cm`, `C_cm`,
`H₆(S;R) = 2·10¹³·max(1, C_cm, Q_R¹⁷)` with `R ≥ max(D, max S, 10¹²)`. Statement:
`h(u) ≤ H₆(S;R)·M_S(u)²⁴`. V15 and V16 add the sentence that the constants are unchanged
(V16 L503-504).

**The V14 → V15 change (VERIFIED, `checks.py` §3).**
- V14 L784-785, L808, L912 and L1117 cited `b11-integral-model-project`. V15 drops it at L809,
  and cites §`v15:marking-descent` instead at L832, L936 and L1141.
- V15 L894 adds the pointer "by the integral-lattice proof in Section `v15:tate-polarized`".
- The two new sections are V16 L30096-30107 (`v15:tate-polarized`: Tate modules, finiteness of
  the integral endomorphism lattice, finiteness of polarized automorphisms, from Milne 1986
  §§8, 12, 17) and V16 L30109-30122 (`v15:marking-descent`).
- `v15:marking-descent` works over `ℤ[1/30]`. In order:
  1. `X₃₅ → X₅` is finite étale.
  2. `(𝒪/5𝒪)^×` acts freely, with quotient `Y`.
  3. Smoothness, properness and projectivity descend.
  4. The universal abelian scheme, its dual and its principal polarization descend.
  5. `Y` represents the full-three moduli problem.

  The inputs are Stacks tags and BLR §§8.2 and 8.4.

**Proof architecture of V14-V16 (VERIFIED by reading; details in h-v14 §2).** The proof keeps
N5's architecture:
1. QM datum for `B = (2,−3)`.
2. Level-three curve, with degree `≤ 4·81 = 324` (V16 L822-826).
3. Integral model (Buzzard Thm 2.1 / Cor. 2.3 at V16 L835, then Deligne 1971 at V16
   L979-1101, then §`v15:marking-descent`).
4. Hom field and dichotomy (V16 L1271-1283).
5. CM branch (V16 L1285-1338).
6. Scalar descent and Brauer step (V16 L1339-1441).
7. Modularity, through the new Lemma `lem:qm-modularity-descent` (statement V16 L505-528, proof
   L530-692, scope paragraph L694-706).
8. Compatible system and conductor (V16 L1442-1571).
9. Transfer through `J₁(N)` (Javanpeykar), GR14 Duke Thm 1.4, theta height (V16 L1572-1698).

The exponent 24 and the constants come from the same places as in N5.

### 1.2 The new height estimates of V15/V16 (VERIFIED)

All three concern the quartic constructions, not `thm:target`.
- **Setting.** `S_* = {p ≤ 76176}`, `B_* = ∏_{p∈S_*} p`, `𝒟 = {0, 1, 2401, −343/32}`.
  `M₅(a)` is the product of the primes outside `S_*` with positive odd contact order at
  `∞, 0, 1, 2401, −343/32`.
- **The curve.** The proof starts from the maximal-level Shimura curve of the
  discriminant-210 quaternion algebra (genus 5) and the González–Rotger 2006 models (V16
  L7660-7680). "Theorem `thm:height` uses a different contact set" (V16 L7622).

| Label | Lines (V16) | Bound | Constant |
| --- | --- | --- | --- |
| `hyp:o8-height` | L7651 (constant L7640-7650) | `h(a) ≤ H_*·M₅(a)²⁴` | `H_* = 2(4608^165888 + 6^100)·B_*²⁴ + 128`, `log₂ H_* < 4783227` |
| `thm:quartic-height19` | L10005 | `h(a) ≤ H₁₉·M₅(a)¹⁹` | `H₁₉ = 2·2^109·210^1800·B_*¹⁹ + 128`, `log₂ H₁₉ < 2093966` |
| `v15:height:thm:contactheight` | §`v15:height`, L30186-30906 | `h(a) ≤ C₃·M₅³(1 + log M₅)`, hence `h(a) < 2^330789·M₅^{7/2}` | `C₃ = 19·4608·210^300·B_*³·log B_* < 2^330770` |

The three `log₂` bounds were rechecked numerically: about 4645521, 2093447 and 330681
(`checks.py` §5; VERIFIED). The method of `v15:height` differs from N5's transfer step in two
places:
- **An internal Jacobian-height theorem** (V16 L30247-30253). For a Belyi map split over
  `t = 2`, `h_F(Jac X) ≤ log N𝔇(C)/(2[K:ℚ]) + g·log(2/√π)`, proved from the trace-dual lattice
  of the fibre. It gives `h_F(J_H) ≤ 6·d_H·log R` (V16 L30797), linear in the degree,
  where N5 used Javanpeykar's `1.3·10⁷·N¹²` (N5 L868-876).
- **A dimension-two isogeny theorem** applied to the surface factor itself:
  Gaudron–Rémond's 2023 Theorem 1.9(1) (V16 L30672), resting on Rémond 2022 and 2017 (V16
  L30665-30668). In N5 the isogeny goes from `J` to `A × Z` (GR14 Duke Thm 1.4).

The input is the "Modular realization" lemma (V16 L30710-30733). It takes the geometric
comparison `h(a) ≤ 2·max(0, h_F(A)) + 128`, the CM alternative `h_F(A) < 854R` and the non-CM
modular data from the proof of `thm:quartic-height19`, that is, from the same kind of argument
as N5 §4, run on the discriminant-210 curve.

### 1.3 The 214-variable proposal (VERIFIED by reading p214 `proofs/height-supplier.md`, `PROOF.md`)

- **Status.** An author proposal, explicitly not accepted (height-supplier.md L3; README).
- **Setting.** Same five contacts, smaller support `S = {2,3,5,7,11,13,17,37,41,2399}`.
- **Inherited interfaces (H0, L7-30).** The geometric comparison (H0.1), the CM bound, the
  modularity-descent lemma of `quartic_v14.tex`, the conductor bound
  `N ≤ C_N R²` with `C_N = 2^68·3^16·5^16·7^4` (H0.2), and a modular-Jacobian height (H0.3).
- **Result (H4, L97-133).** `h(a) < C₂·M^{2103/1024}` with `C₂ < 2^{7557/32}`, an effective
  constant.
- **Use.** PROOF.md uses it through `h(t_j) ≤ H₂·M_j^{7/6}` and an aggregate-sum theorem whose
  constant `M2` is ineffective, so the threshold `N₀` of the family is ineffective (PROOF.md
  L33-45).
- **What it still needs.** A uniform effective contact-height bound proved by the same chain.
  The proposal changes the curve, the averaging step (the published product construction over
  `L'`, `height-averaging.md`) and the constants. It does not remove the need for the bound.

### 1.4 Answer to question 1

| Version | Removes the need for a uniform effective height bound? | Weakens what the fork's construction needs? | Proves it differently? |
| --- | --- | --- | --- |
| V13 | no | no (identical statement) | no (= N5) |
| V14 | no | no | same architecture; new modularity lemma, integral model in outline plus supplement (h-v14) |
| V15 | no | no | V14 plus the integral model written out in the manuscript; new five-contact estimates only for the disc-210 curve |
| V16 | no | no | = V15 for `thm:height` |
| p214 | no (still an effective contact bound; ineffectivity enters only later) | not applicable (another polynomial) | other curve and constants, same chain |

None of them uses a finite computation or a published theorem that covers the bound directly
(VERIFIED for the texts read; whether such a theorem exists is outside this note). The
SPECULATIVE reason, consistent with h-map §1: every version needs the bound uniformly in an
adversarial `u`, with an effective constant, and the only known route is Faltings-height
control of a modular abelian surface.

## 2. The fork's repairs and gaps against V13-V16

V13 equals N5 throughout the height section (§1.1), so its column is "kept as N5" everywhere,
with V13 line = N5 line + 76. V15 and V16 are identical there. The V14 status is the V15/V16
status unless the table says otherwise; for V14 lines subtract 25 (24 after V14 L785).

| # | Item (fork source) | N5 | V16 (= V15; V14 unless noted) | Status in V16 |
| --- | --- | --- | --- | --- |
| 1 | **Integral model**: N5's inline route through Buzzard; the `b11` supplement; the fork's Lemma PR (h-b1, rv-h-b1; h-trust A5-A6) | L443-530, inline, no supplement cited | V14: outline plus `b11` (4 citations, L784-1117). V15/V16: Buzzard Thm 2.1/Cor. 2.3 to `V₁(5)` (L835) over `ℤ[1/30]`, then Deligne 1971 (L979-1101), then §`v15:marking-descent` L30109-30122 and §`v15:tate-polarized` L30096-30107 | **Changed.** The supplement is gone and the full route is in the manuscript, but it is still Buzzard's integral model, not Lemma PR. The fork's A5-A6 are unaffected; V16 gives a readable, supplement-free fallback (reviewed by no one in this repository). |
| 2 | **A4**, the moduli identification (h-b1 §4A) | implicit at L528 | Deligne 1971 Thm 4.7 (L1036), §§4.8-4.12 (L995-1057), §4.15 (L1069), Prop. 1.15 (L1074), §§4.16-4.17 (L1082), Thm 4.21, Cor. 5.7, Ex. 5.8 (L1099); Deligne 1979 2.2.5, 2.3.1 (L1101); identification of the full-three moduli problem (L30122) | **Changed, made explicit.** Gives precise Deligne locators for the fork's A4 input 1 (h-trust's are "§§4-6", UNVERIFIED). |
| 3 | **C3**, the de Rham descent lemma (rv-h-c3 R1-R3) | L734-737, appendix L10939-11000 | Inline in the lemma, L536-572. `F` is chosen Galois over `ℚ` (L536-537), so `F_v/ℚ₅` is Galois and R1's restriction step is not needed. Milne 1986 Thm 15.1(a), p. 129 (L561), replaces the course notes. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223, pp. 113-184, Thm 3.8, p. 142 (L564-565; bibitem L39243-39247), replaces Brinon–Conrad. Scholze with erratum kept (L557-559). The appendix lemma is gone | **Fixed in substance (V14 on).** R1 avoided by choice; R2 done (with a different Milne edition); the Fontaine exposé question of rv-h-c3 R2 is settled as a citation (pp. 113-184; the content is unread here). R3 belongs to C8. |
| 4 | **C8**: `ρ_g` normalization, weight one, levels divisible by 5 (rv-h-c8 R1-R3) | L757-768 (local algebraicity via Conrad's preprint, L760-761) | L589-662. Arithmetic Frobenius, `HT(U_f) = {0, 1−k}` and `det U_f = ε_f·ε₅^{k−1}` derived from Kato's realization (L618-650). `k = 1` excluded by Deligne–Serre Thm 4.1 (L604-616). All levels, including `5 \| N`, via Kato 2004 §9.4, p. 188, with §§5.4, 8.3 (L621-634). Finiteness of the twist from determinants: `α = det r₅/ε₅`, `α² = 1` on `G_F`, `δ² = α/ε_f` (L660-667) | **Fixed (V14 on).** All three repairs are made, with Kato 2004 as the supplier where h-trust names Saito 1997 or Scholl with Scholze. The determinant argument makes the local-algebraicity step (Conrad, or Serre 1968 / Tate 1967) unnecessary. |
| 5 | **C9**, Euler-factor inference (rv-h-a9c9 R-C9-1), Galois-stability of newness and duality of the conductor (R-C9-2), "primitive" (R-C9-3) | L768-775 | L1468-1474, verbatim N5 L769-775 | **Kept as N5** in every version. The gap that R-C9-1 repairs is still in V16. Upstream's audit evidence (`docs/theorem-application-audit/evidence/descent.md` L71) supplies the constituent claim from Ribet §3, but the manuscript sentence was not changed. The lemma's own newform step (L680-683) uses Li and traces, which is consistent with R-C9-3. |
| 6 | **A9**, Milne's course notes (R-A9-1); implicit descent `ℂ → ℚ̄` (R-A9-2) | L564-570 (`milne-av`, Part I Thms 2.8-2.9) | L1271: Milne, *Introduction to Shimura varieties* (Clay Math. Proc. 4, 2005), Thms 6.7-6.8, Cor. 6.9, p. 319. L1274-1276 = N5 L568-570 | **R-A9-1 changed** (a published edition of lecture notes replaces the course notes; h-trust's Mumford / Milne 1986 swap is an equivalent alternative). **R-A9-2 kept** (still implicit). |
| 7 | **NoCM** (h-cm, rv-h-cm; h-trust A10) | L578-631 | L1285-1338, verbatim (V14 L1261-1314; V13 L654-707) | **Kept as N5.** The CM branch with Fowler, Barquero-Sanchez et al. and GR14 Thm 1.4 (L1322) is unchanged; NoCM remains the fork's replacement. |
| 8 | **Gaudron–Rémond** (h-trust E3, E4) | Thm 1.4 at L615 and L878; §9 at L895 | L1322, L1599, L1616, same keys and locators | **Kept as N5** (§3). |
| 9 | **Modularity supplier** (h-trust C7; h-a011) | Pan Thm 1.0.4 directly (L756) | Calegari, ICM 2022, p. 624, with definition pp. 611-612 (L532-535); Pan as "proof source"; `direct-p5-modularity-project` (L705) | **Changed, away from the fork.** h-trust keeps N5's direct Pan application. |
| 10 | rv-h-novel **R1** (`ω_p(−1) = χ_p(−1)`), **R2** ("If `e ≤ D`"), **R3** (cite the subgroup formula) | L688-692; L828; L835-839 | L1411-1415 rewritten (local Brauer group of order two; Milne ADT I.1.6(b), proof of II.2.1, p. 164); L1539 = N5 L828; L1546-1550 = N5 L835-839 | **R1 partly changed** (more detail, but the identity is still not stated). **R2, R3 kept.** |
| 11 | **I1**, the level equals the conductor (h-trust D5) | not cited in the H proof | Carayol 1987, §§2.1, 2.4, 4.1 (L1502-1504) | **Changed (V14 on).** Gives a second locator next to h-trust's Carayol 1986 Thm (A). |
| 12 | **I2** and the independence of `ℓ` (h-trust C10) | uncited (L784-787) | "The actual isogeny `μ_σ` extends over the local abelian schemes" (L1489-1490); independence of `ℓ` (L1492-1493); both uncited | **Kept** (uncited). |
| 13 | Supplements `a001`, `ly-d6`, `igusa-theta`, `direct-p5` (h-map W2; h-trust Summary 2) | none cited | L748, L781, L1203, L1633, L1647, L705 | **Introduced in V14 and still in V16.** h-trust's published replacements stay necessary. |
| 14 | Faltings (h-trust C2, E1, D2) | `faltings1983`, no locator | lemma: *Complements to Mordell* (Rational Points, 2nd ed. 1986), Thm 1(a)-(b), p. 204 (L546-547; bibitem L39711); main proof: `faltings1983`, no locator (L1453) | **Changed** (second published locator for semisimplicity and the endomorphism theorem). |
| 15 | Javanpeykar (E2), Pazuki and theta height (F1-F3) | L868-876, L908-964 | L1589-1628 = N5 L868-907; L1629-1698 partly new, citing `ly-d6` and `igusa-theta` | E2 **kept**; F1 changed toward supplements (h-v14 §2.5). |

## 3. Version 16's Gaudron–Rémond correction against h-trust's height steps (VERIFIED)

**What V16 changed.**
- The diff V15 → V16 changes V15 L30633 and L30646 (`gr2014`) to V16 L30664 and L30677
  (`gr-periods2014`), and adds the bibitem at V16 L39342-39346: Gaudron–Rémond, *Théorème des
  périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014) 343-403, §2.3 and
  Cor. 8.4.
- The two uses are in the proof of `v15:height:lem:surface`:
  - Bost's lower bound `h_F(E) ≥ −log(π√2)·dim E > −(3/2)·dim E` (V16 L30661-30664);
  - `h_F(A) ≤ h_F(B) + ½·log deg` for an isogeny `B → A` (V16 L30676-30677).
- Upstream's records give the reason: "Two existing inequalities cite wrong Gaudron–Rémond
  paper" (`research/version16/FINDINGS.json` L12-17). The application record
  (`APPLICATIONS.json` L27-41) ends "Bibliography correction only. Preserve gr2014 Duke key for
  Theorem1.4/Section9 applications".
- The V16 reviewer reports reading CMH §2.3 (pp. 351-352) and Cor. 8.4 (p. 400). By that
  report, the CMH height `h` satisfies `h_F = h − (g/2)·log π`, and `h ≥ −(g/2)·log(2π)` gives
  `h_F ≥ −g·log(π√2)` (`research/version16/review/current/REVIEW.md` L25-27).
- `log(π√2) = 1.4913 < 3/2` (VERIFIED, `checks.py` §5).

**h-trust's height steps against this.**

| h-trust step | h-trust supplier | N5 / V16 text | Effect of V16's correction |
| --- | --- | --- | --- |
| E3, explicit isogeny bound | GR14 Duke Thm 1.4 (ASTRA-READ pp. 2058-2060, 2098, 2101-2102) | N5 L878 = V16 L1599, Duke Thm 1.4 | none; upstream keeps Duke here on purpose |
| E4, Bost's lower bound | "through GR14 §9" (ASTRA-READ) | N5 L894-895 = V16 L1615-1616, "recorded in [Section 9]{gr2014}" | none; upstream keeps the Duke §9 locator. CMH §2.3 with Cor. 8.4 is a second locator (read by upstream's V16 reviewer, a model; read by no one here) |
| E4, height variation and additivity | Faltings 1983 Lemma 5, or Raynaud 1985 Exp. VII Cor. 2.1.3 (UNVERIFIED) | N5 L896 = V16 L1617, uncited | none; CMH §2.3 is an alternative locator for both (same caveat) |
| CM-branch use of GR14 Thm 1.4 | deleted by NoCM | N5 L615 = V16 L1322 | none |

Conclusion: the correction concerns a section that the fork does not use. h-trust's E3 and E4
remain as written. The only gain is an optional extra locator for E4.

## 4. Verdict

**The strongest upstream proof of H** (the six-contact statement the fork uses) is V16 §4,
which is identical to V15 §4 (VERIFIED). Compared with N5 it is more explicit:
- the integral model is written out;
- C8 is correct at all levels and in weight one, and the twist is shown finite;
- C3 needs no restriction step;
- Carayol and refereed or published editions are cited.

It still assumes (VERIFIED as a list of what the text cites or uses; the cited works were not
read here):
- a survey statement for modularity, Calegari ICM 2022, p. 624 (Pan as proof source), and the
  `direct-p5` map;
- four unpublished project supplements (`a001`, `ly-d6`, `igusa-theta`, `direct-p5`);
- the Euler-factor inference of C9;
- I2 and the independence of `ℓ`, both uncited;
- the CM branch (Fowler, Barquero-Sanchez et al., GR14);
- the published inputs: Scholze with erratum, Fontaine 1994, Kato 2004, Deligne–Serre, Faltings
  1983 and 1986, Shimura 1973, Li 1975, Washington, Carayol 1987, Buzzard, Deligne 1971 and
  1979, Stacks and BLR, Javanpeykar, GR14 Duke Thm 1.4 and §9, Pazuki, Lin–Yang, Baba–Granath,
  Igusa;
- reviews by models only (`no_new_whole_proof_acceptance: true`, V16 FINDINGS.json).

**Narrowing or removing `SixContactMin`: no.**
- The statement and constants are unchanged (§1.1), and `thm:target` still uses them (V16
  L219).
- The new, sharper estimates are about another curve and another contact set, and serve other
  polynomials (§1.2-1.3).
- The fork's target is the frozen N5 polynomial, whose height uses need this contact set, an
  exponent below 25 and an effective constant (h-map §1). An estimate for `𝒟` cannot be
  substituted.
- p214's ineffective threshold is a feature of its own family and cannot be imported.
- SPECULATIVE: the `v15:height` method (an internal Jacobian-height theorem plus a
  dimension-two isogeny theorem) could probably be rerun for `𝒞`, with an exponent near 3. That
  would change neither the Lean statement nor the trust base in a useful direction. It would
  replace Javanpeykar and GR14 Duke by an unpublished internal theorem and a 2023 paper with
  indirect dependencies.

**Shortening h-trust.md: marginal (SPECULATIVE recommendations, VERIFIED inputs).**
1. **C8.** Replace "a Hodge–Tate character unramified almost everywhere is finite times a
   cyclotomic power" by V14's determinant argument (V16 L660-667). Since
   `det V₅(A) = ε₅²` and `V₅(A) ⊗ E ≅ r₅ ⊕ r₅` on `G_F`, the character
   `α = det r₅ · ε₅^{−1}` has `α² = 1` on `G_F`. With `det(U_f) = ε_f·ε₅` for `k = 2`, this gives
   `δ² = α/ε_f`, so `δ` has finite image.
   - This removes the `conrad-local-characters` row of h-trust §2.4 and the class-field-theory
     step of C8. (The argument was rechecked as stated here, not by an independent review.)
   - Add Kato 2004 §9.4, p. 188, with §§5.4, 8.3 and (14.10.2)-(14.10.3), as a third
     all-levels supplier for (HT) next to Saito 1997 and Scholl with Scholze. Its locators are
     UNVERIFIED here.
2. **C3.** Choose `F` Galois over `ℚ`, as V16 L536 does. Repair R1 then becomes unnecessary.
   Replace "Astérisque 223, exposé to be checked" by Fontaine, *Représentations p-adiques
   semi-stables*, Astérisque 223, pp. 113-184, Thm 3.8, p. 142 (the citation V16 uses; the
   content is unread here).
3. **A4.** Import V16's Deligne 1971 locators (Thm 4.7, §§4.8-4.17, Prop. 1.15, Thm 4.21,
   Cor. 5.7, Ex. 5.8) and Deligne 1979 2.2.5, 2.3.1 in place of "§§4-6". This sharpens the
   locators; their content is still UNVERIFIED.
4. **E4.** Add CMH 2014 §2.3 (pp. 351-352) and Cor. 8.4 (p. 400) as a second locator for Bost's
   lower bound, additivity and isogeny variation.

**Must stay in h-trust:**
- C9's R-C9-1, which is not fixed upstream;
- A9's R-A9-2;
- NoCM;
- Lemma PR. Upstream's integral model is Buzzard's, now readable in V16; Lemma PR keeps
  Buzzard out of the base.
- rv-h-novel R2-R3;
- I2 and `ℓ`-independence;
- the policy of applying Pan directly. Upstream's Calegari route is weaker for the fork.

## 5. Scripts and log (VERIFIED: run, output saved)

- `scratch/up-h/checks.py N5 V13 V14 V15 V16` (pure Python, run with `python3 -I`; output in
  `checks.output.txt`). It prints only line ranges, counts and numbers:
  - the height-section ranges;
  - identity of the constants block and statement across the five sources;
  - the diff hunks N5→V13, V14→V15, V15→V16;
  - project-supplement citations per version;
  - `log(π√2)` and `log(2/√π)`;
  - upstream's `log₂` bounds for `H_*`, `H₁₉` and `C₃`.
- The N5 → V16 line map in the log (step 7) was produced with `scratch/h-v14/linemap.py`.
- `scratch/up-h/log.md`: passages located and comparisons made, step by step.
