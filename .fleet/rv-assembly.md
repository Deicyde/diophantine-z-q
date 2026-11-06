# rv-assembly: adversarial review of the assembly chapter

Scope: `blueprint/roadmap/assembly/` (the writer's 29 leaves and 4 containers), its notes and
`blueprint/sources/assembly-locators.md`, against Section 1 (lines 52-140) and Section 11
(lines 6094-6271) of `diophantine_zq.tex`. I re-read both ranges in full and compared the
templates and recipes with `construction/variable-shift-polynomial-library.js`,
`construction/ordinary-integer-polynomial.js`, `rational-elliptic-core.js` and
`rational-model-assembly.js`. I also checked the interface articles that the other chapters wrote
in their own worktrees (`bp-compiler-natural`, `bp-compiler-translation`, `bp-multiplication`,
`bp-size`), reading them only.

`autoform check blueprint`: OK (167 articles, 515 dependencies). `autoform audit blueprint`: no
finding in the owned paths. The remaining errors are `declared-coverage-gap` rows in
`coverage/README.md` and `missing-source-link` on other chapters' stubs.

## What I fixed

1. **Input C did not connect to the compiler interfaces (substantive).** `close-relation.md`
   assumed input C in the form "`Rel_precision(E) ⟺ ∃c∈ℕ⁵, Eᵢ=ι(cᵢ) ∧ Prec(dec c)`". Neither
   compiler interface states this. The rational translation gives "`∃c, Eᵢ=ι(cᵢ)` and
   `∃z∈ℕ^1305806, C(c,z)=0`". The natural semantics turns that into `accepts(c)`. The compiler's
   `accepts` differs from the assembly's `Prec` in two ways:
   (a) it has an explicit admissibility clause for `l,a,j` (`[k]P₀` affine with nonzero ordinate);
   (b) it uses the height constant with `Q₀ = D^{DE₀}`, where the assembly uses
   `R_ht = max(D,317,10¹²)`.
   I added the leaf `approximation/precision-acceptance.md` (lemma, bridged, unconditional), which
   proves `accepts(c) ⟺ Prec(dec c₀,…,dec c₄)`:
   - admissibility follows from the early tests (`n≠0` because `0∈𝒞`, so `j=na≠0`) and the
     nonzero-multiples lemma;
   - the two height constants are equal because `D ≥ 324! ≥ 15! > 10¹²`, proved without
     evaluating `D`.
   `close-relation.md` now spells out the three-step chain (translation, natural semantics,
   bridge). The approximation README and both affected notes are updated, and the new leaf has
   its own note (`af_be2811faba7749bf8b907409`).
2. **Off-by-one in `local-tests/good-reduction-multiples.md`.** The statement claimed
   `1 ≤ m ≤ q²`, but the pigeonhole on `[1]P,…,[q²+1]P` misses the case where `[q²+1]P` itself
   lies in `E₁(π)`. Corrected to `m ≤ q²+1`, in the statement, the proof, `deep-multiples.md` and
   the note. Only existence is used downstream.
3. **Notation clash.** `value-test-semantics.md` wrote the first code coordinate of `K` as
   "`K_0=0`", which collides with the field `K₀`. The same pattern appeared as `A_0=L_0=0` in
   `close-coordinates-semantics.md`. Both now use `K[0]`, `H[0]`, `V₀[0]`, `A[0]`, `L[0]`.

## What I verified and left unchanged

- **Lemma 11.1** (`test-divisibility.md`), step by step: `α=δ+2b` is odd; the trace bound
  `v_p(Θ) ≥ -λ`; positivity from the pole obstruction; `v_π(D_j) > δ/4-3b/2 > 0`; the reduction
  to `Q=[gcd(h,s₀)]P₀`; `s₀ ≡ th` and `s₀-κn ≡ t(h-κ)` mod p; `p | κ(n-c) | κF(n)`. The case
  `p | h`, which the manuscript glosses as `log U/log H = s₀/h`, is handled correctly.
- **Formal groups** (`formal-group.md`, `formal-multiplication.md`). I re-derived the `(z,ω)`
  curve `ω = z³+Azω²`, the chord-slope identity, the cubic and
  `z(P₁+P₂) = z₁+z₂+2Aμν/(1+Aμ²)`. The cases `ν=0` and `z₁=z₂` are implicitly fine. Item 3,
  `z([m]Q) = m·z(Q)·u` with `u ≡ 1` at odd `p`, composes correctly.
- **Lemma 11.2** (`pole-input-local`, `pole-input-real`, `test-completeness`, `deep-multiples`):
  - at the primes of `R₀`: `v_π(D_j) ≥ 2N` or `≥ 4N`, with conjugate primes handled;
  - `W ≡ 1`, `Θ ≡ 2`, and `v₂(Θ)=1` at the ramified prime;
  - `v₂(B)=4+v₂(F(n))` and `v_p(B)=6+v_p(F(n))` for `p=3,5,7,13`;
  - even valuations elsewhere;
  - the real bound `(1+Rc)⁶ ≤ e^{0.6} < 2`;
  - `a₀ ≠ 0` from `gcd(R₀, R₀j+1) = 1`. The manuscript's "adjust by one" is indeed never needed.
- **Close.**
  - Soundness: `|t-n| < 2ε_l < 4^{-B}/2 < e^{-B}`.
  - Real accumulation: the compactness and continuity cases of `real-subtraction.md`, including
    the translation by `(0,0)` for `Q=O`.
  - Derivative of `[n]`: leading coefficients `φₙ ~ x^{n²}`, `ψₙ² ~ n²x^{n²-1}`,
    `f₂ₙ ~ n·x^{2n²-2}`, `ψₙ⁴ ~ n⁴x^{2n²-2}`, giving the ratio `n³/n² = n`.
  - Completeness: the choice of `l` before `a`, and `ε_l ≤ |σ₊z|+|σ₋z|`.
- **Templates against the JS sources.**
  - `value.signed_encode`: the two branches and the generator `ι(1)`.
  - `value.close_coordinates`: `finite(A)` and `finite(L)`; `J` may be `O`.
  - `value.test`: the seven `member` calls, `multiply(K,N,C1)`, `raw_add(H,−K,V0)` and
    `raw_add(U,−C1,V1)`; `D₅`, `D₆` with the conjugation; `F·Cⱼ = Dⱼ`; `Θ = 2·re(W⁻¹)`;
    `B·Θ² = R`; the `pole` call. The `z` and `inverseX` gadgets are inline formulas with `O ↦ 0`.
  - `value.exceptions`: `fixedMultiple` chains of `raw_add` calls with counts `0,7,6,6,8,9`.
  - Recipes: `close`, with the order `(N,K,A,L,J)` and the precision input order
    `(n,κ,a,l,j)`; `main`, with one shared `K`; `value_union` as a product; `value`;
    `integers`.
- **Finite check `bad-place-check.md`.** I recomputed `[7]P₀` exactly in ℚ(√2) (Python,
  `fractions`): `v₇(γ)=2`, `(α+3β) mod 7 = 2`, numerators of 167 digits and denominator γ of
  165 digits. `x(P₀) = (1641-1160s)/8` gives `v_s = -6`, and the reduction of `P₀` at `d` is
  `(2,6)` on `y²=x³` over 𝔽₇.
- **Main-branch exactness.** The Lean hypothesis `SixContactEstimate` is applied with `S=S_ht`
  and `R=max(D,317,10¹²)`. `contactSupport S_ht t = M_{S_ht}(t)`. The final separation
  `|t-n| ≥ 1/b ≥ e^{-h(t)}` is correct.
- **Notes.** I re-checked these Mathlib pointers in `.lake/packages/mathlib`:
  `tendsto_subseq_of_bounded`, `Real.exp_one_lt_d9`,
  `Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq`, `natDegree_Φ`, `leadingCoeff_Φ`,
  `natDegree_ΨSq`, `leadingCoeff_ΨSq`, `natDegree_preΨ`, `leadingCoeff_preΨ`, `Point.map`
  (Affine/Point.lean:822), `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`,
  `Real.add_one_le_exp`, `Nat.sum_four_squares`, `QuadraticAlgebra.lift`, `star`, `norm`,
  `HeightOneSpectrum.valuation`, `padicValRat.min_le_padicValRat_add`,
  `Point.add_self_of_Y_eq`, `ZMod.exists_sq_eq_two_iff`, `Nat.factorial_le`. The upstream names
  also exist: `HeightConstantAlgorithm.heightConstant` (with `r = max (max d 317) (10^12)`),
  `h6_for_max_317_eq_height_constant`, `eq_int_of_real_abs_sub_lt_exp_neg_of_height_le`,
  `rationalLogHeight`, `rational_pos_iff_four_squares_inverse` and
  `poleSystem_no_negative_odd_valuation` (PoleValuation.lean:262).
- **Locators.** Spot-checked line numbers (93, 110, 114, 6112, 6114, 6125, 6151, 6186, 6202,
  6210, 6236, 6322, 11144 and others): all correct.

## Finite computations (after review)

| Leaf | Closed statement | Size | Method |
| --- | --- | --- | --- |
| local-tests/bad-place-check (1) | `v_s((1641-1160s)/8) = -6` | trivial | `norm_num` with the model's `v_s(a+bs)` formula |
| local-tests/bad-place-check (2) | `7•P₀ = some x y _ ∧ v_d(x) = -2` | 4 group-law steps, literals < 10¹⁷⁰ | certificate: literal points checked by `norm_num`, then `49∣γ`, `¬343∣γ`, `(α+3β)%7≠0` by `decide`/`norm_num`; no `native_decide` |
| approximation/precision-acceptance | `10¹² < 15!` | 13 digits | `decide`/`norm_num` |
| inline | `0<|c-c'|≤60` on 𝒞; `max S_ht = 317`; `v_p(2730⁶)=6`; chain counts | trivial | `decide` |

`D`, `A₀`, `B(n,κ)`, `4^B` and `324!` are never evaluated. `D ≥ 10¹²` goes through
`D ≥ 324! ≥ 15!`.

## Extra hypotheses

None. Every input is one of H, PC, MW, 22P or CAT, or an interface article of another chapter.
Lemmas 11.1 and 11.2 need neither MW nor 22P: infinite order of `P₀` comes from the torsion
theorem.

## Still needs work (not fixable inside the owned paths)

1. **Duplicate definitions with the compiler-natural chapter.** It defines its own `enc`/`dec`,
   `z`/admissibility, `ε`, `r` and `A^{(0)}_ht` (`compiler/natural/precision/*.md`), and the
   assembly's `precision-predicate.md` repeats them. The new bridge makes them provably
   equivalent. When the chapters are merged, keep one copy (preferably the compiler's) and turn
   the bridge into a corollary. These articles are not interface articles and do not exist on
   this branch, so I could not link them.
2. **Duplicate natural-code lemma.** `compiler/translation/natural-code-semantics.md` states the
   same theorem as `assembly/value-templates/natural-codes.md`. Keep one and relink.
3. **Duplicate formal-group material.** `formal-group.md`, `formal-multiplication.md` and
   `k0-valuations.md` may duplicate formal-group or valuation infrastructure in the
   multiplication chapter (Section 6) and the model-field chapter (`v_s`, `v_d`). This needs a
   pass once the chapters are merged.
4. **Granularity at the upper end.** `formal-group.md` (~500 lines), `test-divisibility.md`
   (~500) and `real-subtraction.md` (~400) are large. Each is still one coherent theorem. If a
   formalizer finds them too big, split them as follows: formal-group into items 1-2 (subgroup)
   and item 3 (the 5k estimate); real-subtraction into compactness and continuity.
5. **Push.** This review's commits are on local `wip/bp-assembly`. `git push` failed with
   "Recv failure: Connection reset by peer", and `git fetch` failed the same way. The remote
   branch is at the writer's `ec80fe6`.

## Manuscript issues (confirmed from the writer's list, plus mine)

- Lemma 1.2 assumes G, M, C and B. Here it is restated over the five Lean hypotheses (G from MW;
  M from H, PC, MW and 22P; C unconditional given M; B's bounds from CAT). This is faithful and
  makes the main theorem a one-liner.
- Lemma 11.2's "adjusting by one if equality occurs" is never needed.
- Lemma 11.1's `log U/log H = s₀/h` needs care when `p | h`. It is expanded without the formal
  logarithm.
- Lemma 11.2 cites VII.6.3 for the bad places. It is replaced by the explicit facts
  `P₀ ∈ E₃(s)` and `[7]P₀ ∈ E₁(d)`.
- New: the manuscript defines the precision predicate on "nonzero multiples of `P₀`" and
  `A^{(0)}_ht = H₆(S_ht)` with `R = max(D, max S, 10¹²)`, while the compiler chapter formalizes it
  with admissibility and `R = D`. The two agree, but only because of the infinite order of `P₀`
  and `D ≥ 10¹²`. This step is now explicit.

## Faithfulness verdict

The chapter is faithful to Section 1 and Section 11. Every definition, claim, displayed formula
and step of the two lemmas has a leaf that states it exactly or with a documented correction:
Close, B(n,κ), the two Close properties, the six tests, Test, Lemmas 11.1 and 11.2, Val, the real
separation, and the S01/S16 composition. The constants match exactly (2730⁶, 𝒞, F,
`H₆(S_ht)`, the exponent 24, the strict inequalities, `0<B<1/2`, the valuations 4 and 6). The
quantifier order matches too: `l` is fixed before `a`, and `κ` is fixed before Close's witnesses.
The proof sketches go beyond the manuscript where it says "clearly". Its analytic and
formal-group citations become elementary lemmas with complete arguments, which I re-derived. The
only substantive defect was the unproved interface step from the compiler's acceptance relation
to the assembly's precision predicate. That step is now a separate, unconditional bridge lemma.
There was also an off-by-one in an auxiliary bound, now corrected. With these fixes the assembly
lemma follows from its dependencies, and `ZInQKernel/Main.lean` reduces to
`assembly hH hPC hMW h22 hCAT`, provided the compiler, multiplication and size chapters deliver
their interface statements as written in their worktrees.
