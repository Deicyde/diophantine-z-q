# rv-multiplication: adversarial review of the multiplication chapter

Branch `wip/bp-multiplication`, review commit "Blueprint: multiplication chapter (review fixes)"
on top of the writer's commits. `autoform check blueprint`: OK (187 articles, 547
dependencies). `autoform audit blueprint`: no finding in `roadmap/multiplication/`,
`sources/multiplication-locators.md` or the chapter's notes. The remaining audit errors are the
shared `declared-coverage-gap` row (coverage/README.md) and the `missing-source-link` stubs of
the assembly, compiler and size chapters, none of them in this chapter.

**Push failed, as it did for the writer.** `git push origin HEAD:wip/bp-multiplication` fails:
direct HTTPS gets "Connection reset by peer", `fwdproxy:8080` answers "CONNECT tunnel failed,
response 403", and the `gh` token in `~/.config/gh/hosts.yml` is invalid. All commits (the
writer's two and my two) exist only locally in `~/dzq-wt/bp-multiplication` and need pushing
from a host with GitHub access.

## What I checked

I re-read lines 960-1020 and 1123-1759 of `diophantine_zq.tex`, the construction generator
`construction/multiplication-certificate.js`, the syntax templates the chapter relies on
(test_group, slope, height_certificate, multiply, guard, pole), the five hypothesis files, and
the model articles the chapter links (generator point, special primes, canonical-height bounds,
height of 2R, reduction-torsion). Then I checked every article of the chapter step by step:

- **Constants and formulas**, all against the manuscript and the generator: $L$ and its
  coefficients (recomputed), $d^2=11243-7950s$, $P_0$ and its dyadic valuations, $k_j$, the
  normalizations $R_0(t-1)^2$ and $R_0^{25}(t-1)^{26}$, $\Theta=2\sum_g(\omega_g)_0$, the
  shift points $c_*G,c_*Y_i$, the witness count $3+4\cdot6+35106+1=35134$, $B_p,C_p,D_p,E_p$,
  $\ell_0=12P_s^{2916}H_{\rm cat}^{732}$, $R$, $A_{\rm ht}$, $T$, and $B_0$ and $\log41-\frac13\log392$
  (recomputed: $9.369$ and $1.723$). I also recomputed the three integer inequalities in Python.
- **Proof sketches, line by line**: abscissa parity; the pole obstruction; contact valuations;
  the common-group bound (the bound $-(3r-1)/4$, $(k+1)/4$ and $(97k+1)/4$); tests to congruence
  (both cases $p\nmid h$ and $p\mid h$, and the four-term identity for $n_1n_2-n_3$);
  contact support; the finite box (the chain $3A+\log3$, then $6A+2\log3$, then $12A+B_0$, then
  $N^2<24AN^{48/25}+10$); the box inequality; pattern slopes ($v_q(k)\le B_q$, the $8B_p$ bound,
  exact contact valuation $1$, at most six primes); shift choice; integrality at $S_b$
  (including $p=2$); selected-prime precision; pole-input valuations (including the
  $v_2$-scale at $(s)$, where it still works); positivity; weak approximation; slope
  completeness; the semantics articles against the template definitions.
- **Notes**: I ran one `lake env lean` with `#check` on 21 Mathlib names the notes cite (load
  6, 116 GB free). All exist except `Nat.squarefree_primorial`, which the note already
  describes as absent. I grepped the upstream names in `lean/ZInQ` (all found, signatures
  match), and checked that `padicValNat` has no `norm_num` extension.

## What I fixed

1. **Error in `pole-obstruction`**: the proof said "multiplying $r_2^2=T_2$ by $z^6$". The
   correct factor is $z^2$, since $(zr_2)^2=z^2T_2=Az^2(Az^2-eH)(Az^2+3eH)$. I fixed it, added
   the nonvanishing of both abscissas and both parameters, which the parity lemma needs, and
   said that the link to the PC article is only for the definition of $\Phi$: the lemma assumes
   no hypothesis.
2. **Granularity of the formal group** (it was one article with a 1500-3000-line estimate). I
   split it into three articles:
   - `local/formal-group.md` (same id, retitled "The formal neighbourhood of $y^2=x^3+Ax$ and
     its filtration"). It now has a complete elementary proof of the valuation shape, the
     subgroups $W_k$, the injectivity of $z$ and $v(z([n]P))\ge v(z(P))$. The proof is the
     chord computation in the coordinates $(z,\omega)=(-x/y,-1/y)$: the slope $\lambda$ with
     $v(\lambda)\ge2k$, the intercept $\nu$ with $v(\nu)\ge3k$, and by Vieta
     $z_3=-z_1-z_2-2A\lambda\nu/(1+A\lambda^2)$. It holds over any discretely valued field, with
     no completion and no formal group law, and is estimated at 300-500 lines.
   - New `local/formal-group-law.md` (background): the power series $\omega(T)$ and the formal
     group law $F$ with $z(P+Q)=F(z(P),z(Q))$.
   - `local/formal-logarithm.md` (same id) now covers convergence and the homomorphism. The
     isometry range moved to a new `local/logarithm-isometry.md` (background, about 150-200
     lines). `logarithm-ratio` now cites the isometry article for injectivity.
3. **Finite checks isolated as closed leaves**:
   - New `soundness/height-constant-integers.md` holds the integer core of the height
     constants. `height-constants` is now only the real-number step and is no longer marked
     finite.
   - New `local/generator-dyadic-numerals.md` holds the 2-adic valuations of the $P_0$
     numerators. `dyadic-generator` is no longer marked finite.
4. **Notes**: rewrote the notes of formal-group, formal-logarithm, dyadic-generator and
   height-constants. Wrote notes for the four new articles. Removed a garbled
   `Real.add_pow_le_pow_mul_pow_of_sq_le_sq ... not needed` pointer, and corrected the route for
   the dyadic numerals (no `norm_num` extension for `padicValNat`; use the closed form with
   `padicValNat.eq_zero_of_not_dvd`).
5. **Locators**: twelve tests 1162-1176, slope predicate 1177-1192 (it starts at line 1177),
   logarithm series 1150-1161.
6. Updated the local and soundness READMEs for the new leaves.

## Articles of the chapter (49 leaves, 5 containers)

The writer's 45 leaves (listed in `.fleet/bp-multiplication.md`) plus my four new leaves:
`local/formal-group-law`, `local/logarithm-isometry`, `local/generator-dyadic-numerals` and
`soundness/height-constant-integers`. Each has an implementation note. The interface articles
`pole-obstruction.md` and `multiplication-template.md` keep their ids.

## Finite computations (after the review)

| Article | Decidable statement | Size | Method |
| --- | --- | --- | --- |
| `local/logarithm-coefficients` | $16575(-1)^j\binom{2j}{j}/(4j+1)=c_j$, $j\le6$; $16575=3\cdot5^2\cdot13\cdot17$; $L$ is $16575$ times the degree-25 truncation | 7 rational identities $<10^6$ | `norm_num`/`decide` |
| `local/generator-dyadic-numerals` | $v_2(1641)=0$, $v_2(1160)=3$, $v_2(123720)=3$, $v_2(87483)=0$, $v_2(8)=3$, $v_2(32)=5$ | $<2\cdot10^5$ | `decide` on the closed parity/factorization form |
| `certificate/clearing-arithmetic` | for $B\in\{1,4\}$, $v\in\{0,1,2\}$: $2E-C-2D>v$, $2E-C-2v=103C+8\ge4$; $52\cdot56+4=2916$; $52\cdot14+4=732$; $v_2(12)=2$, $v_3(12)=1$ | 6 cases | `decide` |
| `soundness/height-constant-integers` | $3^{24}2^9\cdot39202\cdot676^2\cdot1000^{60}<2718^{60}$; $392\cdot27183^3<41^3\cdot10^{12}$; $2\cdot13860^2<19601^2$ | 207 digits | kernel `decide` (GMP `Nat`), `norm_num` fallback |

No fixed constant ($M_0$, $c_*$, $\ell_0$, $R$, $A_{\rm ht}$, $T$) is evaluated, the guard
product is never expanded, and no byte-level check of the JSON artifacts is used.

## Hypotheses by direction (confirmed)

- **Soundness** uses H (only through `contact-support`, then `finite-box` and `soundness`) and
  MW (membership typing, injectivity of codes, infinite order of $P_0$). It uses the
  unconditional Lemma 5.1, but not PC and not 22P.
- **Completeness** uses 22P (only through `pattern-slopes`), PC (only through
  `slope-completeness`) and MW. It does not use H.
- CAT is not used anywhere in the chapter.
- No extra hypothesis was introduced.

## What still needs work

1. **Size chapter**: $M_0\ge1$ (the search defining $M_0$ succeeds) is needed by both
   directions: soundness needs $p\nmid c_*$ and the fixed-scalar semantics needs $c_*\ge1$. The
   manuscript proves it inside Proposition 12.1 (lines 6310-6349), and
   `certificate/constants-properties` links `size/cutoff.md`, which is still a stub. The size
   chapter should expose this as a leaf, and the link should then point to it.
2. **Formal group law and formal logarithm** are the deepest gaps (Mathlib has only the bare
   `FormalGroup` structure). They are classical and formalizable, so I kept them as background
   theorems, not `def` propositions. If the lead wants explicit inputs until they are proved,
   `formal-group-law` and `formal-logarithm` are now small, well-delimited articles that can
   become `def` propositions without touching anything else.
3. **Model chapter**: the selected-prime precision needs $\#\widetilde E(\mathbb F_p)$ to equal
   `pointCount` of Hypotheses/PrimePattern.lean, about 100 lines that Mathlib lacks. The model's
   reduction-torsion article could use the new `formal-group` article for its kernel of
   reduction.
4. **Shared heights**: `field-height-bounds` needs a `NumberField` instance on
   `QuadraticAlgebra ℚ 2 0` (it does not synthesize with `import Mathlib`), and Mathlib's
   `logHeight₁` must be aligned with the model's normalized height ($h=\text{logHeight}_1/2$).
5. The degree-75 claim for $Q_{\rm pole}$ (line 987) has no leaf here. I checked it by hand:
   $\deg T_2=37$, so $\deg B(r_2^2-T_2)^2=75$. It belongs to the size or syntax degree bounds.

## Manuscript issues

The writer's list of 13 issues in `.fleet/bp-multiplication.md` is accurate. I re-verified each
one; all are handled in the articles. Additions from this review:

- The "three differences of the corresponding $L$-ratios" (line 1172) must be differences with
  the *conjugate* of the primed ratios, $A_i-\sigma B_i$, as the generator implements.
  Without the conjugation the transfer of integrality between places fails. The articles use
  $A_i-\sigma B_i$.
- The argument at line 1145 (identification with the reduction kernel of a minimal model) is
  not needed. Together with the new elementary proof of the filtration, the integrality and
  dyadic arguments need neither completions nor formal group laws.

## Faithfulness verdict

The chapter is faithful to the manuscript. Every definition, displayed formula, claim and
finite check in lines 973-1000 and 1123-1759 (with the proof of Proposition 6.2 replaced by
hypothesis 22P) has a leaf or an explicit place in a proof sketch. Constants are copied
exactly and agree with the construction generator. Quantifiers, domains and strict versus weak
inequalities match the manuscript, and where they differ the article says so and gives the
corrected version: the conjugate place in the local congruence, $2\widehat h(P_0)>1$, $N\ge1$
for $|f|\le2N^2$, $q$ small at $S_b$ meaning $v_p(q)\ge C_p$, the unspecified groups set to
$h=2c_*$, and the inverse guards proved automatic. I found one real error, the wrong factor
$z^6$ in the pole-obstruction proof (the statement was unaffected), and fixed it. Otherwise
every sketch I checked step by step is correct and detailed enough to formalize. After the
splits the remaining risk is concentrated in two clearly marked background articles, the
formal group law and the formal logarithm.
