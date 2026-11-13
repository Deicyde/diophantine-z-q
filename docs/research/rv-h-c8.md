# rv-h-c8: adversarial review of the twist-and-weight step C8 of h-trust

Status: focused adversarial review (task rv-h-c8, 2026-11-11) of step **C8** of
`docs/research/h-trust.md` (§1, Part C), that is, of the frozen 11/5 manuscript
`diophantine_zq.tex` at N5 L757-768, together with the supplier added there after rv-h-trust §1.2
item 1: the 5-adic representation of a weight-`k` eigenform is de Rham at 5 with Hodge–Tate weights
`{0, 1−k}` (Faltings 1987; Scholl 1990 with Faltings 1989 or Tsuji 1999; Saito 1997). "N5 Lxxx"
means the frozen 11/5 text (repository root, sha256 `cb1148cd…`, matching h-trust). The work log,
scripts and outputs are in `scratch/rv-h-c8/`.

Marks:

- **VERIFIED**: checked in this task, by reading N5, the 11/4 text, a repository note, or by an
  exact computation in `scratch/rv-h-c8/` (inputs and outputs saved).
- **STANDARD**: a published theorem, with a reference. There is no network here, so no locator in
  this note was read in this task. Locators are marked UNVERIFIED where it matters.
- **SPECULATIVE**: an assessment.

## Verdict

**C8 holds after the repairs of §8.** No mathematical gap was found: the conclusion that C9 and C10
use (`r₅` is the Tate-module representation of a weight-2 newform `f`, up to nothing) follows. But
the step as written in N5, and its supplier as listed in h-trust, are imprecise in three ways:

1. **Normalization (the most serious point).** N5 never fixes the normalization of the eigenform's
   representation `ρ_g`. The phrase "the modular weights `{0, 1−k}`" is right only for the
   arithmetic-Frobenius (Tate-module) normalization, `det ρ_g = ε_g·χ^{k−1}`. Pan's paper, whose
   output N5 is processing, uses **geometric** Frobenius (rv-h-a011 §2, VERIFIED there on the
   arXiv v2 source). In that normalization the weights are `{0, k−1}`, and the comparison gives
   `k = 2` but twist **`χ¹`, not "power zero"** (VERIFIED, `weights.py`). The conclusion survives,
   because for `k = 2` the extra `χ` turns the cohomological representation into the Tate-module
   one up to a finite character, which N5 absorbs into the eigenform anyway. But "power zero" is a
   normalization-dependent statement, and the step needs one sentence fixing the normalization.
2. **Weight one.** The value `{0, 1−k} = {0, 0}` at `k = 1` is correct, but none of the listed
   suppliers covers it (they are all for `k ≥ 2`). It needs Deligne–Serre 1974 (finite image).
3. **Level divisible by 5.** The eigenform from Pan's theorem can have level divisible by 5 (the
   set `T` of bad primes depends on `u`, and N5's conductor bound treats `p = 5` like any `p ∈ T`). "Scholl 1990 with Faltings 1989" is, as far as
   it can be judged without the sources, the crystalline comparison and covers only `5 ∤ N`; Tsuji
   1999 needs de Jong's alterations for Kuga–Sato varieties at `p | N`. Saito 1997, or Scholl's
   motive plus Scholze 2013 Cor. 1.8 (already a leaf of C3), cover every level.

**Consequence for H's trust statement.** C8 keeps status **[M]**; its new supplier is **[R]**
with the corrections of §8 (add Deligne–Serre; prefer Saito 1997, or Scholl + Scholze, for
`5 | N`). This review is the first model review that names the eigenform input and checks it
against the N5 text; with Astra "descent" (11/4 text, identical here up to one citation), C8 now
has two model reviews. Nothing in Lean changes; no constant changes.

| Question | Answer |
| --- | --- |
| Which eigenform, weight, character, twist? | Any cuspidal eigenform `g` of weight `k ≥ 1`, any nebentypus, with `r₅ ≅ ρ_g ⊗ ψ` for a continuous character `ψ` (Pan's "up to twist"). The nebentypus is invisible to the weights (§2) |
| Do the cited theorems give exactly the needed weights? | Yes for `k ≥ 2` and in the arithmetic-Frobenius normalization; `k = 1` needs Deligne–Serre; `5 \| N` needs a supplier that covers bad reduction (§3) |
| Sign of the weights, effect of twist and character | Tate convention (`χ` has weight −1) is used consistently by N5, C3 and Pan. Finite characters do not move weights; `χ^m` moves both by `−m`; dualizing negates. Only the difference `k − 1` is normalization-free, and only that is needed for `k = 2` (§3.2) |
| Is the conclusion what the next steps use? | Yes: `r₅ ≅ ρ_f` (Tate-module normalization) for a weight-2 newform `f`, in either normalization of Pan's output (§5) |
| Other uncited inputs in N5 L740-790 | Finiteness of `ψ` on inertia at `ℓ ≠ 5`; Kronecker–Weber; closure of Hodge–Tate representations under Hom and subobjects; "duality preserves the conductor" (L774). All standard (§6) |

## 1. The step

N5 L757-768, paraphrased (not quoted). Fix the Tate convention, in which the cyclotomic character
`χ` has Hodge–Tate weight `−1`. Pan's Theorem 1.0.4 at `ℓ = 5` gives a cuspidal eigenform up to
twist. The twisting character is a subrepresentation of a Hom representation, hence de Rham, and it
is unramified almost everywhere. Local algebraicity (Conrad, App. B) and class field theory make it
a finite character times an integral power of `χ`. Comparing `{0, −1}` with the modular weights
`{0, 1−k}` after that power forces `k = 2` and power zero. The finite character is absorbed into the
eigenform, and C9 takes the primitive newform `f`.

- **Consumes.** C3: `r₅|G_{ℚ₅}` is de Rham with Hodge–Tate weights `{0, −1}` (Tate convention).
  C7: Pan's conclusion. Nothing else from earlier steps.
- **Delivers** (to C9, C10, Part D): `r₅ ≅ ρ_{g'}` for a cuspidal eigenform `g'` of weight 2, with
  `ρ` in the normalization in which it is a constituent of a Tate module.
- **Review history.** The C8 text of N5 equals the 11/4 text accepted by Astra ("descent" AUDIT
  item 6, ADDENDUM item 5), except that the Conrad citation was added (VERIFIED: diff of 11/4
  L731-745, commit 09c0c3f3, sha256 `bfc4192d…`, against N5 L757-771). Astra's AUDIT item 6 already
  warns that the cohomological pair `{0, k−1}` must not be mixed with the arithmetic-Frobenius pair
  `{0, 1−k}`; N5 did not act on the warning by fixing the normalization (finding 1).

## 2. Which eigenform, which weight and character, which twist

- **Pan's conclusion** (h-a011 §1.1, quoted from arXiv v2 and VERIFIED there): `ρ` "comes from a
  cuspidal eigenform up to twist". No weight, level, character or Frobenius convention is stated.
  Pan's notation section: `ε` has Hodge–Tate weight `−1`, `Frob_v` is geometric (rv-h-a011 log,
  VERIFIED there; the TeX source is no longer on disk here, so not re-read).
- **Reading.** `r₅ ≅ ρ_g ⊗ ψ` with `g` a cuspidal eigenform of some weight `k`, some level `N`, some
  nebentypus `ε_g`, and `ψ : G_ℚ → Ē₅^×` continuous. Whichever Frobenius convention Pan's `ρ_g`
  has, the other one differs by duality, and for a 2-dimensional `U`, `U^∨ ≅ U ⊗ det(U)^{−1}`, so
  the reading only changes `ψ` (h-a011 §4; VERIFIED as an argument). The reading "regular algebraic
  cuspidal automorphic representation up to twist" of Pan's body is a special case (`k ≥ 2`).
- **Weight range.** `k ≥ 1`, since `S_k = 0` for `k ≤ 0`. Pan's introduction does not exclude
  `k = 1`, so N5 must (finding 2).
- **Character.** The nebentypus `ε_g` and the finite part of `ψ` have finite image, hence
  Hodge–Tate weight 0, and do not affect any weight (STANDARD: a potentially unramified character is
  `ℂ_p`-admissible).
- **Twist.** `ψ` is a priori arbitrary. Its form is the content of §4.

## 3. The p-adic Hodge theory: what is needed, and what the sources give

### 3.1 What is needed

Exactly the following, for every cuspidal eigenform `g` (every `k ≥ 1`, every level `N`,
including `5 | N`, every nebentypus):

> (HT) `ρ_g|G_{ℚ₅}` is Hodge–Tate, and its two Hodge–Tate weights differ by `k − 1`.

N5 uses (HT) twice: to make `ψ` Hodge–Tate (as a subobject of `ρ_g^∨ ⊗ r₅`, both Hodge–Tate), and to
compare weights. **De Rham is not needed anywhere in C8**: Tate's local algebraicity needs only
Hodge–Tate, Hodge–Tate representations are closed under tensor products, duals and subobjects
(STANDARD: Fontaine, Astérisque 223, Exp. III), and only Hodge–Tate weights are compared. N5's word
"de Rham" for `ψ` is true but stronger than necessary (VERIFIED as an argument).

### 3.2 Normalization and sign (VERIFIED, `weights.py`)

In the Tate convention (`χ` has weight `−1`, so `V_p(E) ⊗ ℂ_p ≅ ℂ_p ⊕ ℂ_p(1)` has weights `{0, −1}`;
this is the convention of N5 L757, of C3 and of Pan):

| Normalization of `ρ_g` | `det` | weights |
| --- | --- | --- |
| HOM: trace of arithmetic Frobenius `= a_ℓ(g)`, as on `V_p(J₁(N))` for `k = 2` | `ε_g χ^{k−1}` | `{0, 1−k}` |
| COH: trace of geometric Frobenius `= a_ℓ(g)` (Pan's notation; `H^{k−1}` of Kuga–Sato) | `ε_g^{−1} χ^{1−k}` | `{0, k−1}` |
| `k = 1` (either) | finite | `{0, 0}` |

Write `ψ = η·χ^{−n}` with `η` finite, so `n` is the weight of `ψ`. Exhaustive search over
`1 ≤ k ≤ 200`, `|n| ≤ 300` for `wt(ρ_g) + n = {0, −1}` as multisets:

- HOM: the only solution is `(k, n) = (2, 0)` — N5's "`k = 2` and power zero";
- COH: the only solution is `(k, n) = (2, −1)`, i.e. `ψ = η·χ`;
- `k = 1` never matches (equal weights), and in both cases the determinant check
  `Σ wt = −1 = wt(det r₅)` holds.

So `k = 2` is normalization-free (it uses only the difference `k − 1`), while "power zero" is true
only in HOM. N5's text is internally consistent if read in HOM, which is also the normalization the
next sentence (Tate module of `A_f`) needs. That HOM is the Tate-module normalization was checked on
a sample: for `11a1`, `37a1`, `389a1` and the first 25 good primes each, the weight-2 newform's
`a_ℓ` equals `ℓ + 1 − #E(𝔽_ℓ)`, the trace of the Frobenius endomorphism on `V_p(E)` (0 mismatches;
`normalization.py`; VERIFIED on the sample, STANDARD in general: Eichler–Shimura).

### 3.3 What the cited sources give (STANDARD, locators UNVERIFIED)

- **Faltings, Math. Ann. 278 (1987)**: Hodge–Tate decomposition for the étale cohomology of modular
  curves with coefficients `Sym^{k−2}`; gives (HT) for `k ≥ 2`. Whether it covers `p | N`:
  UNVERIFIED (SPECULATIVE: I believe it does, since Faltings' Hodge–Tate theory needs no reduction
  hypothesis, but this was not read).
- **Scholl, Invent. Math. 100 (1990)**: the Chow motive `M(g)` as a direct summand of `h^{k−1}` of the
  Kuga–Sato variety `W_{k−2}` (level `Γ(N')`, `N' ≥ 3`), with Hodge filtration jumps `0, k−1` on the
  `g`-part of `H^{k−1}_dR` (Deligne 1969). Then de Rham comparison gives (HT) with weights `{0, k−1}`
  (COH). The comparison must hold for `W_{k−2}/ℚ₅` with **bad** reduction when `5 | N'`:
  - Faltings 1989 (crystalline comparison) covers good reduction, i.e. `5 ∤ N'` (SPECULATIVE whether
    that paper also claims the general de Rham comparison);
  - Tsuji, Invent. Math. 137 (1999), is `C_st` for semistable models; Kuga–Sato fibre products are
    not semistable at `p | N'` in general, so de Jong's alterations (Publ. IHÉS 83, 1996) are also
    needed;
  - **Scholze, Forum Math. Pi 1 (2013), Cor. 1.8** gives de Rham comparison for every proper smooth
    rigid space over a `p`-adic field. It is already a leaf of C3, and so is Fontaine's closure
    under subquotients. With Scholl this route adds only Scholl's (refereed) motive and the Hodge
    numbers to the trust base.
- **Saito, Invent. Math. 129 (1997)**: `ρ_g|G_{ℚ_p}` is potentially semistable for every level, with
  `D_pst` matching the local component; Hodge–Tate weights `0, k−1` (COH). Covers `5 | N` directly.
- **None of the three covers `k = 1`.** For `k = 1`: Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1
  (finite image), plus: a character or representation with finite image on inertia has all
  Hodge–Tate weights 0 (STANDARD). With that, `ρ_g ⊗ ψ` has equal weights, contradicting C3.
- **Can level `5 | N` actually occur?** Yes as far as the proof knows. `T = S ∪ supp M_S(u)`
  (N5 L528) depends on `u`, and N5's local conductor bound (L814-830) treats every `p ∈ T` alike,
  `p = 5` included; nothing excludes ramification of `L` or bad reduction of `A` above 5. (That N5
  computes the conductor at 5 through `r₃`, L793-794, is not evidence either way: a conductor at `p`
  is read off an `ℓ`-adic representation with `ℓ ≠ p`.) So the supplier must cover `5 | N`
  (VERIFIED as a reading of N5).

### 3.4 Effect of the twist and the character on de Rham-ness

Twisting by a finite character or by `χ^m` preserves de Rham-ness and Hodge–Tate-ness (tensor
products of de Rham representations are de Rham). Finite characters have weight 0; `χ^m` has weight
`−m`. This is all N5 needs; it is STANDARD (Fontaine, Exp. III).

## 4. Local algebraicity and class field theory

N5's chain, made explicit (VERIFIED as an argument; the cited theorems STANDARD):

1. `ψ` is the character of the `G_ℚ`-stable line spanned by the identity in
   `Hom(ρ_g, r₅) = ρ_g^∨ ⊗ r₅` when `r₅ ≅ ρ_g ⊗ ψ`; so it is continuous, with values in a finite
   extension of `ℚ₅`, Hodge–Tate at 5 by (HT) and C3, and unramified wherever `ρ_g` and `r₅` are.
2. Its weight `n` is an integer; `ψχ^n` has weight 0, so it has finite image on `I₅`: this is Tate's
   theorem (Tate, *p-divisible groups*, 1967, §3.3, Thm 2) or, for `E`-valued characters, Sen 1973 /
   Serre 1968, Ch. III, Appendix. N5 cites Conrad's preprint, App. B; h-trust already lists Serre
   1968 Ch. III as the refereed replacement.
3. At `ℓ ≠ 5`, `ψ(I_ℓ)` is the image of `ℤ_ℓ^×` (local class field theory); `ℤ_ℓ^×` is (finite) ×
   pro-`ℓ` and `O_E^×` is virtually pro-5, so the image is finite. **N5 asserts this without
   argument** ("finite inertia … at every other prime"); it is elementary.
4. `ψχ^n` is a character of `G_ℚ^{ab} ≅ ℤ̂^×` (Kronecker–Weber), trivial on an open subgroup of each
   `ℤ_ℓ^×` and on `ℤ_ℓ^×` for almost all `ℓ`, hence of finite order. N5's "finite ray-class
   character" is this.

No step uses more than Hodge–Tate.

## 5. What the next steps use

- **C9** absorbs the finite character into the eigenform (twist of an eigenform is an eigenform,
  Shimura 1971 §3.6) and passes to the primitive newform `f` (Li 1975), then places `r₅` in the
  Tate module of `A_f` (Shimura 1973 Thm 1). This needs `r₅ ≅ ρ_{g'}^{HOM}` for a weight-2 eigenform
  `g'`.
- **In HOM**, power zero gives `r₅ ≅ ρ_g^{HOM} ⊗ η = ρ_{g⊗η}^{HOM}`: exactly that.
- **In COH** (Pan's notation), `ψ = η·χ` and, since `k = 2`,
  `ρ_g^{COH} ⊗ χ = (ρ_g^{HOM})^∨ ⊗ χ = ρ_g^{HOM} ⊗ ε_g^{−1}`, so `r₅ ≅ ρ_{g⊗ε_g^{−1}η}^{HOM}`: the
  same conclusion with a different finite character (VERIFIED as an argument).
- The identity behind the COH case, `f̄ = f ⊗ ε_f^{−1}` is a Galois conjugate of `f` (so both
  normalizations land in `V(A_f)`), was checked exactly on the weight-2 newform of level 13 with a
  character of order 6, coefficients in `ℚ(ζ₆)`: `conj(a_ℓ) = conj(ε(ℓ))·a_ℓ` for the 24 primes
  `ℓ < 100`, `ℓ ≠ 13` (`normalization.py`; VERIFIED on the sample, STANDARD in general).
- **C10** uses the "modular trace at five" of `f` and the 3-adic representation of `f`; **Part D**
  uses the level of `f` (Carayol). All three need only that `r₅` is `ρ_f` for a weight-2 newform,
  which §5 delivers.

## 6. Other uncited inputs in N5 L740-790

Inside C8 (all STANDARD, none affects correctness):

- the finiteness at `ℓ ≠ 5` (§4 item 3) and Kronecker–Weber (§4 item 4);
- Hodge–Tate (or de Rham) closure under Hom and subobjects (Fontaine, Astérisque 223, Exp. III);
- `k = 1` (Deligne–Serre), §3.3;
- the normalization of `ρ_g` (§3.2).

Elsewhere in L740-790 (already in h-trust's lists, recorded for completeness):

- C5 (oddness): Betti–étale comparison with the action of complex conjugation (h-trust: Milne 1986
  or SGA 4 XI);
- C6: Néron–Ogg–Shafarevich (listed);
- C9: Eichler–Shimura (`a_p = ` Frobenius trace), Shimura §3.6 or Atkin–Li (listed);
- L774 "this duality preserves the conductor": the Artin/Weil–Deligne conductor of `V^∨` equals that
  of `V` (STANDARD; e.g. Serre, *Local fields*, VI, and Deligne 1973, *Les constantes …*, §8; not in
  h-trust's lists; harmless);
- C10: Néron mapping property, independence of `ℓ`, Serre–Tate, Chebotarev, Brauer–Nesbitt
  (listed).

## 7. Refutation attempts (all failed)

1. *Wrong sign of the weights.* Checked against the Tate convention of N5, C3 and Pan: consistent.
   A sign error would only flip `n`, never `k` (§3.2).
2. *Pan's eigenform in the other normalization breaks "power zero".* True (§3.2), but the conclusion
   C9 needs survives (§5). Finding 1, repair R1.
3. *`k = 1` slips through.* Excluded by N5's formula, but with no supplier. Finding 2, repair R2.
4. *The supplier does not apply when `5 | N`.* Partly true for one of the three listed routes.
   Finding 3, repair R3.
5. *`ψ` need not be locally algebraic away from 5, or need not be of finite order after removing
   `χ^n`.* False: §4 items 3-4.
6. *The Hom representation needs `ρ_g` de Rham, which is stronger than Faltings 1987.* No: Hodge–Tate
   is closed under Hom and subobjects, and Tate's theorem needs only Hodge–Tate (§3.1).
7. *Determinant cross-check.* `det r₅ = (finite)·χ` (since `det V₅(A) = χ²` on `G_{L'}`), and
   `det(ρ_g ⊗ ψ) = (finite)·χ^{k−1−2n}` in HOM: consistent exactly at `(2, 0)`; it does not by itself
   determine `k`, which is why the eigenform's individual weights are needed (`weights.py`).
8. *Could the eigenform input be avoided?* No: the determinant and Weil weights (purity) are
   consistent with every `k` once `ψ` absorbs a half-integral power, so some form of (HT) for `ρ_g`
   is unavoidable (SPECULATIVE as a claim about all possible routes; VERIFIED for these two).

## 8. Repairs

- **R1 (normalization).** In h-trust C8 (and in any future manuscript edit), fix `ρ_g` as the
  representation with `tr ρ_g(Frob_ℓ^{arith}) = a_ℓ(g)` and `det ρ_g = ε_g χ^{k−1}`, so that its
  weights are `{0, 1−k}` in the Tate convention, and note that Pan's conclusion, in his
  geometric-Frobenius notation, is brought to this form by `U^∨ ≅ U ⊗ det(U)^{−1}`, changing only
  `ψ` (h-a011 §4). State the supplier in the normalization-free form (HT) of §3.1.
- **R2 (weight one).** Add to C8's suppliers: Deligne–Serre 1974, Thm 4.1 (weight-1 forms have
  finite image), plus "finite image on inertia implies Hodge–Tate weights 0". Or record that Pan's
  body produces regular algebraic automorphic representations, hence `k ≥ 2` (UNVERIFIED reading).
- **R3 (level divisible by 5).** Say that the supplier is needed for all levels, including `5 | N`.
  Prefer Saito 1997, or Scholl 1990 + Scholze 2013 Cor. 1.8 + Fontaine (the last two already leaves
  of C3). Keep "Scholl + Faltings 1989" only for `5 ∤ N`, and "Scholl + Tsuji 1999" only with de
  Jong 1996. Faltings 1987 may cover all levels (UNVERIFIED; check its hypotheses on the level).
- **R4 (minor, uncited).** Add one sentence for the finiteness at `ℓ ≠ 5` and Kronecker–Weber
  (§4 items 3-4), and add "duality preserves the conductor" (L774) to C9's standard inputs.
- **R5 (bookkeeping).** h-trust C8 status: "[M]: Astra 'descent' on the identical 11/4 text, and
  rv-h-c8 (this review), which names the eigenform input"; "De Rham" in the supplier line can become
  "Hodge–Tate" (§3.1).

None of R1-R5 changes an argument, a constant, or the Lean statement.

## 9. Consequence for H's trust statement

H's trust statement stands. C8 remains a repository argument with model reviews only ([M]), now two
(Astra on 11/4, this review on N5), and its eigenform supplier is refereed ([R]) once R2 and R3 fix
its coverage. The weakest point of C8 is no longer the argument but the unread locators (Faltings
1987, Scholl 1990, Saito 1997, Deligne–Serre 1974, Tate 1967 / Serre 1968): a human check of whichever
one is kept, at `p | N`, is the single next step.
