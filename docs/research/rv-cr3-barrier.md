# rv-barrier: adversarial review of the two CR₃ barrier statements

Branch `wip/rv-barrier` (from `main` d549dabb). Under review:
- **Theorem G**, with the column form, the Stein remark, the global-soundness paragraph and the column
  property: `docs/research/el-gadget.md` §1–§2, computations E1 and E2.
- **Lemma G**, with Corollaries 1–4 and the scope paragraph: `docs/research/el-special.md` §4,
  computations C3 and C5.

No Lean was run, and no file under `ZInQKernel/`, `blueprint/` or another note was changed. Scripts are in
`scratch/rv-barrier/` and the step log is `scratch/rv-barrier/log.md`.

Marks:
- **VERIFIED**: checked against the sources, or by exact computation (script named).
- **STANDARD**: a published theorem (reference given).
- **SPECULATIVE**: not proved.

## 0. Verdicts

| Statement | Verdict |
| --- | --- |
| Theorem G (local part: an RC gadget is not LUS) | **Holds after repairs R1–R3.** None of the repairs changes the conclusion. |
| Column form and column property | **Holds** (VERIFIED). Repair R4 removes an overreach in the Stein remark. |
| el-gadget's global-soundness paragraph | **Refuted as stated.** Its premise is false for the actual gadget (R5). The paragraph is not needed for Theorem G. |
| Lemma G | **Holds as stated**, with one clarification R6 (`γ₀` may lie on the closure of `Γ`). |
| Lemma G, Corollaries 1 and 3 | **Hold after repairs R1 and R7.** |
| Lemma G, Corollary 2 | **Holds** (VERIFIED, C5 rerun). It is also stronger than stated: `q` can stay fixed. |
| "Hence CR₃'s kind (rank or Ш) is needed" (both notes) | **Not proved.** It is a heuristic (SPECULATIVE), not a consequence of either statement. |

Both barriers are correct as theorems about *rationally connected gadgets* and *explicit witness families*
whose soundness is *local and uniform in all large primes*. They do not support the stronger sentence "CR₃
cannot be removed by redesigning the pole gadget". The report should state the precise scope of §3.

## 1. The soundness hypothesis is the one the project uses (VERIFIED, by reading the Lean)

- `PoleSoluble B` (`ZInQKernel/Hypotheses/Pole.lean:52`) asks for a rational zero of `polePoly`. Its fibre
  over `B` is:
  - a conic in `(e, r₁)`: `r₁² = A(A² − e²)`, with `A = mB`;
  - over each `e`, a genus-1 quartic in `(z, r₂)`: `r₂² = A(A²z⁴ − e²H²)`;
  - plus the bits `b`, which take finitely many values.

  So the fibre is not rationally connected, which is consistent with Theorem G.
- The soundness proof, `poleSystem_no_negative_odd_valuation`
  (`ZInQKernel/Multiplication/Certificate/Parity.lean:93`), uses only `padicValRat` identities: the min
  rule, and the evenness of `2v(y)`. The same argument works for `ℚ_p`-witnesses. So the current soundness
  is local and uniform (LUS), with exceptional set `{p | 2730}`.
- `pole_step` (`Assembly/Local/TestDivisibility.lean:225`) uses only `¬(v_p(B) < 0 ∧ odd)` at `p > 13`.

So the LUS hypothesis of Theorem G and the local-soundness hypothesis of Lemma G describe the actual
design.

## 2. Proof audit and repairs

### Theorem G

**(G-a), the dichotomy.**
- (ii)⇒(i) needs a smooth proper model over `ℤ[1/N]` with three properties:
  - `f` is a morphism to `ℙ¹`, not just a rational map (blow up first);
  - `div(1/f)` has no vertical component;
  - `f⁻¹(0)` and `f⁻¹(∞)` are disjoint.

  Then even multiplicities give `div(1/f) = 2D` near `f⁻¹(∞)`. Since the scheme is regular, hence locally
  factorial, `D` is locally principal, so `1/f = u·h²` locally. The note implies these conditions; R3 asks
  that they be stated.
- (i)⇒(ii) uses Lang–Weil, Hensel and Chebotarev. It is correct.
- Points of an *open* gadget variety stay in the open set because the reduction is a general point of the
  odd component. This holds provided the component is not contained in the boundary. Even when it is, the
  transversal curve below has only finitely many boundary points.

**R1 (definition).** "The generic fibre is rationally connected" must mean the following: the generic fibre
`X_η` is geometrically integral, and some smooth proper model of `X_η` is rationally connected.
- Rational connectedness is a birational invariant of smooth proper varieties, so this is well defined.
- The loose reading fails. Take the affine cone over a plane cubic. It is rationally chain connected
  through its vertex. With a guard `≠ 0` that removes the vertex, the fibre has no rationally connected
  model and may have no points.
- With R1, Graber–Harris–Starr gives a point of the *proper* model only. To land in the open, possibly
  singular, gadget fibre, use the density of sections: for a smooth proper rationally connected `X` over
  `K = k(curve)` with `k` algebraically closed of characteristic 0, `X(K)` is Zariski dense. (STANDARD:
  Graber–Harris–Starr, JAMS 16 (2003) 57–67, together with Kollár–Miyaoka–Mori's very free curves; see
  Kollár, *Rational curves on algebraic varieties*, IV.3, and Hassett, *Weak approximation and rationally
  connected varieties over function fields of curves*, 2010.)

**R2 (proof route).** (G-b) and (G-c) apply Graber–Harris–Starr over `F_m = Q̄((s))`. That theorem concerns
function fields of curves, not Laurent series fields. The notation is also garbled: `s^m = t` together with
`1/g = t^m` should read `v_s(1/g) = m`. Replace the formal germ as follows:
1. Take an algebraic curve `Γ ⊂ Y`: a general complete intersection through a general point `γ₀` of the
   odd component `C`, transversal to `C`.
2. Then `v_{γ₀}(1/g|_Γ) = mult(C)`, which is odd, and `Γ` meets the open set where the fibres are
   rationally connected.
3. Graber–Harris–Starr over `Q̄(Γ)`, with R1, gives a section over a number field `K`.
4. Evaluate the section at the points `γ ∈ Γ(ℚ_p)` with `t(γ) = p`, for `p` split in `K(γ₀)`.

This removes Artin approximation, Eisenstein's theorem and Lang's C₁ theorem from the proof. It is exactly
Lemma G's argument. The conic, quadric, norm-form and Châtelet cases still need only Tsen's theorem over
`Q̄(Γ)`, together with a smooth point.

**With R1–R3, Theorem G is VERIFIED** as a proof from STANDARD inputs: Graber–Harris–Starr, density of
sections, Lang–Weil, Hensel, Chebotarev, resolution of singularities. The conclusion is unchanged: the
gadget has bad `ℚ_p`-points for a set of primes of positive density.

**Column form and the column property (VERIFIED).**
- Badness is independent of `q`:
  - if `v_p(R₀)` is odd and ≥ 1, a `p`-integral `q` gives `v(a) = 0`, the maximal value of `v(R)`;
  - if `v_p(R₀) < 0`, then `v(B) ≤ v(R) < 0` for every `q`.

  So data that is bad at `q = 0` is bad for every `q`.
- Theorem G then applies with base the data space `D` and `g = B(·, q = 0)`.

**R4.** The Stein remark says that soundness "lives on square-class conditions `f(y, q) ∈ ℚ²`". This is too
narrow. The finite part can be any finite cover with even ramification index along the bad divisor, for
example `z⁴ = f`, or a non-abelian cover. The conclusion that it has genus ≥ 1 over a bad column is
unaffected.

**R5 (the global paragraph is refuted as stated).** The paragraph assumes that the total space `X` is
smooth, proper and rationally connected. Then `Br X / Br ℚ` is finite, and Colliot-Thélène's conjecture
would give global bad points. But the real data space contains the test points on `E/K₀`, so `X` fibres
over a base with an abelian-variety factor and is not rationally connected. Even a *conditional* exclusion
of globally sound gadgets would need fibration-method conjectures over such bases (Harpaz–Wittenberg type,
plus finiteness of Ш). E1's global examples are evidence (VERIFIED for the sampled gadgets), not a proof.
Theorem G's local statement does not use this paragraph.

### Lemma G

- **Steps 1–4 are correct (VERIFIED):**
  - the section is defined over a number field;
  - Hensel at a smooth point with a `ℚ`-rational uniformizer;
  - `u(γ) ≡ u(γ₀)` mod `p`, so `v_p(B(γ)) = −r`;
  - the section is regular at `γ` and satisfies the guards at `γ` for large `p`, because the
    exceptional points are finitely many algebraic points and `γ ≠ γ₀`.
- **R6.** Hensel's lemma and the evaluation only need `γ₀` to be a smooth point of the *closure* `Γ̄`.
  Corollary 2 uses `q = q₀λ^{−M}`, whose pole point lies at `q = ∞`, outside the affine `P`. With R6 this
  is legitimate. The C5 rerun also shows that `M = 0` already works (pole order 11), with `q` fixed and
  `p`-integral.
- **R7 (Corollaries 1 and 3).**
  - Corollary 1 needs R1 together with the density of sections. Its Tsen sub-case needs a smooth point: a
    degenerate quadric may have the vertex as its only point.
  - "Uniform witness construction" must be defined: a ℚ-variety `W → P`, dominant, with rationally
    connected generic fibre in the sense of R1, together with a `P`-morphism `W → Y`. With this definition
    Corollary 3 is VERIFIED. A general curve of the covering family (Corollary 2) meets the open set of `P`
    over which `W` has rationally connected fibres.
- **Strengthening (Lemma G′, VERIFIED as a proof; it is the same argument).** Let `ρ : P′ → P` be any
  dominant morphism. Suppose `B∘ρ` has an odd-order pole at a smooth point of some curve in `P′`. Then no
  witness family over `P′` with rationally connected fibres exists. Examples covered:
  - étale covers, such as "∃ S with 2S = T";
  - bases enlarged by points `jP₀` on `E`, provided the honest tuples are Zariski dense there;
  - covers with odd ramification along the bad divisor.

  What Lemma G′ leaves open is exactly the covers `P′` over which `B` has *only even* poles. On those, the
  honest instances must lift to rational points of `P′`, which is again a per-instance existence problem.

## 3. Scope

**Excluded:**
- **X1 (Theorem G).** Every gadget `X → Y` that is LUS (sound at all `ℚ_p`-witnesses, for all `p > p₀`, with
  `p₀` fixed) and whose generic fibre is rationally connected in the sense of R1. Here `Y` is the full
  data space, including the witness `q` (column form). The coefficients may be arbitrary rational functions
  of the data and of extra parameters. This covers conics, quadrics, norm forms, Châtelet surfaces, conic
  bundles, towers of these, and conjunctions of finitely many of them. Conjunctions do not help: a finite
  set of fixed conics `(a_i, f)` fails at the primes that split completely in `ℚ(√a_i)`.
- **X2 (Lemma G and G′).** Every explicit witness family, that is, any family with rationally connected
  fibres over `P` or over any `P′ → P` on which `B` keeps an odd pole, whenever soundness is local. This
  includes witness formulas built from prime configurations (el-special C1, routes S and A) and route M
  (C3).
- **X3.** Events other than "odd negative valuation" fall to the same proof. For example, `v_p(g) < 0` with
  `v_p(g) ≢ 0 (mod k)` needs fibre multiplicities divisible by `k`, so again no rationally connected fibres.
  The event `v_p(g) < 0` itself is integrality, which is the target. Redesigns of the consumer that keep the
  shape "a valuation condition at every large prime" therefore stay excluded. (VERIFIED as a sketch: same
  proof as (G-a).)

**Not excluded:**
- **N1 (gadgets that are not rationally connected).** Finite covers with even ramification, genus-1
  fibrations and torsors, all with points supplied per instance. The current Lemma 5.1 gadget is of this
  kind. Both notes assert that completeness then needs a rank or Ш theorem "of CR₃'s kind". This is
  **SPECULATIVE**: the barriers prove only that completeness is a per-instance rational-point problem on
  varieties that are not rationally connected, over a cover where `B` has only even poles (Lemma G′).
  *Plausibility: low but nonzero.* The only concrete candidate is el-gadget's E4 redesign: `Θ` made
  independent of `q`, giving the genus-1 quartic `h² = m(mΘ₀² − R₀(1 − R₀q²)²)`. Its soundness is
  unchecked, and in 30 samples no point of height ≤ 2000 was found.
- **N2 (global, not local, soundness).** Soundness that uses reciprocity, Brauer–Manin, or the fact that the
  test points are global points of `E(K₀)`. By R5 this is not excluded, even conditionally, by the notes'
  argument. *Plausibility: very low* (SPECULATIVE). The adversary controls the Hilbert symbols at the other
  places unless supports are constrained, and constraining supports is an integrality condition.
- **N3 (soundness not uniform in the primes).** For example, `p₀` depending on the witness, or soundness
  only on a Chebotarev set of primes. Such a gadget cannot alone yield "tests small at every `p`". A second
  device would be needed to exclude the exceptional primes, and that device is again covered by X1–X3 or
  falls under N1. *Plausibility: very low.*
- **N4 (per-instance existence theorems and thin families).** CR₃ through Tian–Yuan–Zhang is one example.
  Infinitely many families, each covering a thin set of instances, would be another. Lemma G's own scope
  paragraph lists both. These are not elementary, but neither statement shows they are unavailable.
- **N5 (changing the architecture so that no pole gadget is needed).** This means putting the parity on
  the data space (rs-global C1–C2). It was not reviewed here. Theorem G applied to `Y` says that it needs a
  base that is not rationally connected, which is N1 again.
- **N6 (changes to Lemma 5.1's arithmetic beyond the bad event).** For example, rational multipliers
  (route M). C3 shows that they break soundness, and route M is a case of X2.

**Recommended wording for the project report:** "No pole gadget with rationally connected fibres, and no
explicit (rationally connected) witness family, can have the local soundness that the consumers use. Any
sound redesign needs, at each instance, rational points on varieties that are not rationally connected; no
known elementary theorem supplies them." Do not write "CR₃ cannot be removed by redesigning the pole
gadget".

## 4. Computations rerun

All four reruns use independent code, at most 30 inputs each, exact arithmetic, run one after another.

| Rerun | Script | Inputs | Outcome | Agrees with the note? |
| --- | --- | --- | --- | --- |
| E1 | `e1_rerun.py` | 30 primes (every other prime in `[331, 1000)`); `B = c/p` with `v_p(B) = −1`; multipliers among the divisors of 2730; PARI `qfsolve` | G1 (`x² + y² = m(m − B)`): witnesses at exactly the 10 sampled primes with `p ≡ 1 (mod 4)`, 0 mismatches with the Hilbert-symbol prediction. G2, G3 (Poonen type) and G5: witnesses at 30/30 primes. | yes (28/59, 59/59). VERIFIED |
| E2 | `e2_rerun.py` | 30 bad data with tests in `ℚ(√2)`: 10 each with `v_p(R₀) = 1, 3, −1`; 20 values of `q` each, with denominators up to `p⁴` | 600/600 pairs bad | yes; the note sampled only `v_p(R₀) = 1` with rational tests. VERIFIED |
| C3 | `c3_rerun.py` | (a) 30 random `(B, m₀, λ)`; (b) 30 random `(p, B = c/p, λ)` with `v_p(λ) ∈ [−3, 3]` | (a) explicit witnesses on both curves: 30/30. (b) the maximum of `v_p(k)` is −1, which the paper proof in the log confirms for all `λ`. | yes. VERIFIED |
| C5 | `c5_rerun.py` | `p ∈ {10007, 100003, 1000033}` × `c ∈ 𝒞` × `M ∈ {0, 1, 2, 3}`, random `q₀` and `D_j` | `v_p(B) = 15 − 52M` for `M ≥ 1`, and `−11` for `M = 0`: 30/30 | yes, and `M = 0` is new. VERIFIED |

Caveat on C5 (and the original): the test site is modelled with arbitrary fixed `D_j ∈ ℚ(√2)` and
`C_j = D_j / F(n)`, matching `hC` in `TestDivisibility.lean`. The model does not require the `D_j` to be
coordinates of points on `E`. Since the `D_j` are held fixed along `Γ`, this does not affect the
pole-order computation.
