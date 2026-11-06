# bp-multiplication: report

Branch `wip/bp-multiplication`, commit "Blueprint: multiplication chapter". `autoform check
blueprint`: OK (183 articles, no warnings). `autoform audit blueprint`: no finding in
`roadmap/multiplication/`, `sources/multiplication-locators.md` or my notes. The remaining
audit errors are the shared `declared-coverage-gap` rows and the `missing-source-link`
stubs of the assembly, compiler and size chapters, none of them mine.

**Push failed.** `git push origin HEAD:wip/bp-multiplication` fails: direct HTTPS to github.com
gets "Connection reset by peer", `http://fwdproxy:8080` answers "CONNECT tunnel failed, response
403", and the `gh` token in `~/.config/gh/hosts.yml` is invalid. Both commits (the chapter and
this report) exist only locally in `~/dzq-wt/bp-multiplication`; they need pushing from a host
with GitHub access.

## Articles (45 leaves, 5 containers)

Interface articles, kept at their paths with their `article_id`, `not_ready` removed:

- `multiplication/pole-obstruction.md`: lemma, cited (Lemma 5.1).
- `multiplication/multiplication-template.md`: theorem, cited (input M: for all
  $Y_1,Y_2,Y_3\in\mathbb Q^5$, Rel_multiply iff $(Y_i)=(\iota(a),\iota(b),\iota(ab))$; 35,134 witnesses).

Top level: `README.md` (container), `abscissa-parity.md` (lemma, bridged).

`local/` (formal group and truncated logarithm): `README.md`; `primes-above-p.md` (lemma,
bridged); `formal-group.md` (theorem, background); `formal-logarithm.md` (theorem,
background); `logarithm-series.md` (theorem, cited); `logarithm-coefficients.md` (lemma,
cited, FINITE); `truncation-unit.md` (lemma, bridged); `truncation-error.md` (lemma, cited:
$v(\epsilon_z)\ge28$); `dyadic-generator.md` (lemma, bridged, FINITE);
`logarithm-nonvanishing.md` (lemma, bridged); `logarithm-ratio.md` (lemma, bridged).

`certificate/` (constants and template semantics): `README.md`; `constants.md` (def, cited:
$S_{\rm ht},\mathcal H,S_b,S_{\rm mul},B_p,C_p,D_p,E_p$, $F(t)$, odd contact primes, $k_j$);
`clearing-arithmetic.md` (lemma, cited, FINITE); `constants-properties.md` (lemma, bridged);
`local-templates.md` (theorem, bridged: raw_z, raw_inverse_x, log25); `twelve-tests.md` (def,
cited); `test-group-semantics.md`, `slope-semantics.md`, `height-certificate-semantics.md`,
`multiply-unfolding.md` (theorems, bridged); `slope-predicate.md` (def, cited);
`guard-true-triples.md` (lemma, cited).

`soundness/`: `README.md`; `contact-valuations.md`, `common-group.md`,
`tests-to-congruence.md` (lemmas, bridged); `local-congruence.md` (theorem, cited:
$p^{25}\mid n_1n_2-n_3$); `contact-support.md` (lemma, bridged, uses H);
`rational-height-bounds.md` (lemma, background; already in Mathlib); `field-height-bounds.md`,
`generator-height.md`, `box-inequality.md` (lemmas, bridged); `height-constants.md` (lemma,
cited, FINITE); `finite-box.md` (theorem, cited: Proposition 6.1); `soundness.md` (theorem,
bridged).

`completeness/`: `README.md`; `shift-choice.md` (lemma, cited); `pattern-slopes.md` (lemma,
bridged, uses 22P); `sb-integrality.md` (lemma, cited); `selected-prime-precision.md`,
`weak-approximation.md`, `pole-input-positivity.md` (lemmas, bridged);
`pole-input-valuations.md` (lemma, cited); `slope-completeness.md` (theorem, bridged, uses
PC); `completeness.md` (theorem, bridged).

Every leaf has an implementation note `blueprint/.implementation-notes/<article_id>.md`
(45 notes). Locators: `blueprint/sources/multiplication-locators.md` (28 anchors).

## Which direction uses which hypothesis

- Soundness (accepted ⇒ true): H (only in `contact-support`, then `finite-box`) and MW (through
  the generator certificate: membership typing and infinite order of $P_0$). It uses the pole
  obstruction (Lemma 5.1, which is unconditional) but not PC, and it does not use 22P.
- Completeness (true ⇒ accepted): 22P (only in `pattern-slopes`), PC (only in
  `slope-completeness`), and MW (fixed-scalar semantics, guard injectivity, test-group
  semantics). It does not use H.
- CAT is not used anywhere in this chapter.

## Finite computations

| Article | Decidable statement | Size | Method |
| --- | --- | --- | --- |
| `local/logarithm-coefficients` | $16575(-1)^j\binom{2j}{j}/(4j+1)=c_j$ for $j\le6$; $16575=3\cdot5^2\cdot13\cdot17$ | 7 rational identities, < $10^6$ | `norm_num`/`decide` |
| `local/dyadic-generator` | $1641,87483,145,15465$ odd; $1160=2^3\cdot145$; $123720=2^3\cdot15465$ | tiny | `decide` |
| `certificate/clearing-arithmetic` | for $B\in\{1,4\}$, $v\in\{0,1,2\}$: $2E-C-2D>v$, $2E-C-2v=103C+8\ge4$; $52\cdot56+4=2916$, $52\cdot14+4=732$; $v_2(12)=2$, $v_3(12)=1$ | 6 cases, < $10^4$ | `decide` |
| `soundness/height-constants` | $3^{24}2^9\cdot39202\cdot676^2\cdot1000^{60}<2718^{60}$, $392\cdot27183^3<41^3\cdot10^{12}$, $2\cdot13860^2<19601^2$ | about 207 digits | kernel `decide` (GMP `Nat`), then real glue with `Real.exp_one_gt_d9`/`lt_d9` |

No constant ($c_*$, $M_0$, $\ell_0$, $R$, $A_{\rm ht}$, $T$, $H_{\rm cat}$) is evaluated; the
guard product is never expanded. No file-level check of the JSON artifacts is used.

## Extra hypotheses and large gaps

No input beyond the five hypotheses was introduced. The largest formalization gaps, which
are stated as background theorems (they are classical and elementary, so I did not make them
`def` propositions):

1. `local/formal-group` and `local/formal-logarithm` (Silverman IV.1-IV.6, VII.2.2): the formal
   group of $y^2=x^3+Ax$ over a complete discretely valued field, the formal logarithm, its
   isometry range. Mathlib v4.35.0 has only `FormalGroup` (a structure plus $\mathbb G_a$,
   $\mathbb G_m$), with nothing about elliptic curves or logarithms. Estimated 1500-3000 lines.
   The notes suggest a valuation-only route for parts 1, 3, 4 of `formal-group`, and a
   project-specific route defining the logarithm as the binomial series. If the lead wants
   these isolated as `def` propositions, the same pattern as the syntax chapter's
   `division-polynomial-multiplication` works.
2. `local/logarithm-series`: power-series computation of the invariant differential (medium).
3. `completeness/selected-prime-precision` needs the cardinality of
   `WeierstrassCurve.Affine.Point` over `ZMod p` to equal `pointCount` of
   Hypotheses/PrimePattern.lean. This is a Mathlib gap of about 100 lines.
4. `soundness/field-height-bounds`: `#synth NumberField (QuadraticAlgebra ℚ 2 0)` fails with
   plain `import Mathlib` (checked with `lake env lean`). The instance has to be provided, and
   Mathlib's `logHeight₁` must be aligned with the model chapter's normalized height
   ($h=\text{logHeight}_1/2$ on $K_0$).

## Cross-chapter dependencies and requests

- **Size chapter**: `certificate/constants-properties` needs $M_0\ge1$ (the search defining
  $M_0$ succeeds), which the manuscript proves inside Proposition 12.1 (lines 6310-6349). I
  linked `size/cutoff.md` under "Proof depends on". If the size chapter exposes the success of
  the search as a separate leaf, relink to that leaf.
- **Model chapter**: I used `model/descent/reduction-torsion.md` part 1, the reduction
  homomorphism at a split prime, at the selected primes, and the canonical height on $C$ with
  $\widehat h_E:=\widehat h_C\circ\theta$. The model chapter has no formal-group article. Its
  reduction-torsion note mentions the kernel of reduction; my `local/formal-group` could serve
  both chapters.
- **Syntax chapter**: I used the guard semantics (`syntax/templates/guard-semantics.md`), the
  fixed-scalar semantics (needs $\mathrm{val}(c_*)=c_*\ge1$) and field-pair-arithmetic part 5. The
  syntax README inventory lists raw_z, raw_inverse_x, log25, test_group, slope and
  height_certificate as this chapter's responsibility; all are covered (`certificate/`).
- The template's parameter points $P_0,P_1,P_2$ are called $Y_1,Y_2,Y_3$ in this chapter,
  because $P_0$ is the generator point.

## Manuscript issues (all handled in the articles)

1. Lemma 5.1, last sentence of the proof ("both points have abscissa in the squareclass A") is
   garbled. The contradiction is the parity of the abscissa valuation; written out in
   `pole-obstruction` and `abscissa-parity`. The hypothesis $p\ne2$ is not needed.
2. Local congruence (lines 1194-1213). The argument is written as if $p$ split; an odd contact
   prime outside $S_{\rm mul}$ may be inert in $K_0$. The argument works uniformly with
   $v_{\sigma\mathfrak p}=v_{\mathfrak p}\circ\sigma$; see `common-group` and `tests-to-congruence`.
3. "Each factor valuation is the minimum of zero and an odd integer" skips the case
   $v_p(a)<0$. There $v_p(R)=3k+4v_p(q)<k$ and may be negative. The pole obstruction forces
   $v_p(R)\ge1$, and the estimate needs $v_p(R)\le v_p(R_0)$; both are written out
   (`contact-valuations`, `common-group`).
4. "The first tests put the points in the formal group": $V_0,V_i$ lie in the formal group at
   the *conjugate* place. The full-log ratios are the rationals $z_i/h$ and
   $(z_i-c_*n_i)/(h-c_*)$, by $u\lambda(H)=\lambda([u]H)=\lambda([h]U)$; made explicit.
5. Proposition 6.1 uses $2\widehat h(P_0)>1$ without proof. It follows from
   $2\widehat h([2]R)\ge\log41-\tfrac13\log392\approx1.72$ (`generator-height`,
   `height-constants`); $\widehat h(P_0)$ means $\widehat h_C(\theta P_0)$. Also
   $|f|\le2N^2$ needs $N\ge1$, which holds because $f\ne0$; "the case $N\le4$ is immediate"
   needs $T>4$, which holds because $A_{\rm ht}\ge1$.
6. Completeness does not specify the test groups of a slope with fewer than six contact
   primes. Any $h$ with $M_0\mid h$, $h\ne0,c_*$ works; I used $h=2c_*$.
7. The inverse guards $L(z(H))\ne0$ and $L(z(V_0))\ne0$ are never justified ("all denominators
   are guarded"). They hold automatically: $L(z)=16575z\cdot$unit at the dyadic prime, where
   $P_0$ has $v_s(z)=3$ (`logarithm-nonvanishing`).
8. "The small formal subgroup in the definition of $M_0$ gives $v_p(D_{gj})\ge0$ at $S_b$" needs
   two facts: multiplication preserves the depth of the formal group, and $L(z)$ is
   $16575z$ times a unit. Expanded in `sb-integrality`.
9. The manuscript bounds $|v_p(R_0)|$ by $C_p=14B_p$; the true bound is $8B_p$. This is harmless.
   "Since $p>324$, their sum is a unit" needs only $p>12$.
10. Weak approximation: "q small at $S_b$" must mean $v_p(q)\ge C_p$ (or $>C_p/2$) so that $a$
    is a unit; $q\ne\pm R_0^{-1/2}$ is needed when $R_0$ is a rational square. Both are made
    explicit (`weak-approximation`, `slope-completeness`).
11. The condition $p\nmid d_1d_2$ of Proposition 6.2 is not used in this chapter.
12. The pole predicate's degree-75 claim (line 987) is not used by the chapter and has no leaf.
13. The identification with the reduction kernel of a minimal model (Silverman VII.2.1-2.2,
    lines 1145-1149) is not needed: everything works with the integral equation of $E$ itself.

## Open questions

- Should formal-group and formal-logarithm stay background theorems, or become `def`
  propositions flagged as explicit inputs until they are formalized?
- The size chapter has to confirm where $M_0\ge1$ is stated (see above).
