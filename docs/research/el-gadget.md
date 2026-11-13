# el-gadget: replacing the pole gadget by one with elementary completeness

Checkout: `wip/el-gadget`, based on `wip/cr3-maps` (main `50d1b05` plus the two CR₃ maps). No Lean was run,
and no Lean file was edited. Scripts are in `scratch/el-gadget/`, and the step log is
`scratch/el-gadget/log.md`.

Marks:
- **VERIFIED**: proved here, checked against the sources, or computed exactly (script named).
- **STANDARD**: a published theorem (reference given).
- **SPECULATIVE**: not proved.

The notation follows `cr3-map-needs.md`: `B = R/Θ²`, `R = R₀a²`, `a = 1 − R₀q²`, tests `C_j`, and
`W = Π(1 + RC_j²)`. The witness (data) space `Y` is the variety of all construction witnesses that feed the
pole call. A **gadget** is a ℚ-variety `π : X → Y` with `Φ'(y) :⇔ X_y(ℚ) ≠ ∅`.

The soundness the consumers use (`pole_step`, `TestDivisibility.lean:225`; `CommonGroup.lean:114`) is local
and uniform in `p`. Call it **LUS**: for all `p > p₀` and all `x ∈ X(ℚ_p)`, `π(x)` is not in
`Bad_p = {v_p(R) odd, 2v_p(Θ) ≥ v_p(R)} = {v_p(B) < 0 odd}`. Lemma 5.1 is LUS with `p₀ = 13`.

## 0. Verdict

**The angle does not eliminate CR₃. Chance: very low.** This is not a failure to find the right conic. It
is a theorem (§1): every gadget whose fibres are rationally connected fails LUS at a set of primes of
positive density. This covers conics, quadrics, norm forms, conic bundles, Châtelet surfaces, and towers of
these, with coefficients depending on the input in any way. Combined with the column property of the
current pole input (§2), it shows that any LUS gadget needs rational points, over the honest data, on
varieties with no point over `Q̄(Y)((t))`. These are not rationally connected. The simplest such objects
are genus-one torsors with a double fibre, which is exactly what Lemma 5.1's gadget uses. No Hasse
principle and no algebraic witness family is available for them. So completeness needs an arithmetic
existence theorem of CR₃'s kind (positive rank, or finiteness of Ш).

Findings:
1. **Theorem G (the rationally-connected wall)**, §1. It generalizes rs-global C2. C2 covered only devices
   of the form "abscissa of a point on `y² = g(x, e)`"; Theorem G covers every gadget with rationally
   connected generic fibre. (VERIFIED as a proof from STANDARD inputs: Lang's C₁ theorem, Lang–Weil,
   Hensel, Chebotarev, Artin approximation; Graber–Harris–Starr for general rationally connected fibres.)
2. **Input-dependent coefficients do not escape.** Theorem G concerns the total space. Over
   `F = Q̄((t))`, every conic or quadric has a point whatever its coefficients. Exact counterexamples
   (E1) bear this out:
   - for `x² + y² = m(m − B)`, explicit rational witnesses with `v_p(B) = −1` exist at exactly the primes
     `p ≡ 1 (mod 4)` in `[331, 700)`, 28 of 59;
   - for a multiplier-twisted conic, a Poonen-type quaternion gadget built from the input, and a gadget
     using the instance class `R₀`, they exist at all 59 primes. (VERIFIED)
3. **Column property** (§2). Data that is bad because a test is large stays bad for every value of the
   free witness `q`, because `v_p(a) ≤ 0`. So the gadget must reject whole lines `{y} × ℙ¹_q`, and
   Theorem G applies to the completeness variety over the data. (VERIFIED: derivation, plus 6000 exact
   checks in E2)
4. **What remains after Theorem G is genus ≥ 1, and it is CR₃'s kind.**
   - The sound square-class gadget `m(m − B) ∈ ℚ²` needs a point on a curve of genus 25–37 per toy
     instance (E3).
   - A redesign with `Θ` independent of `q` lowers this to genus 1, the minimum Theorem G allows. That is a
     2-covering quartic. In 30 samples none had a point of height ≤ 2000, while the Jacobians have rank ≥ 1
     (E4). (VERIFIED computations; interpretation SPECULATIVE)
5. **No explicit witnesses** (§3, route F). The honest data are Zariski dense, so a witness family over
   them would be a rational section. That section would give `Φ'` on bad data. (VERIFIED; this is rs-global
   C4 in column form)

## 1. Theorem G

**Setting.**
- `Y` is a geometrically integral ℚ-variety.
- `g` is a rational function on `Y` whose odd negative valuations are the bad event. For example
  `g = B`, or `g = 1/π_D` for a local equation `π_D` of a bad divisor `D`.
- `π : X → Y` is dominant with geometrically integral generic fibre.
- `F_m = Q̄((s))` with `s^m = t`.

**(G-a) Dichotomy** (VERIFIED as a proof). Let `V` have a smooth proper model over `ℤ[1/N]` with
`f : V → ℙ¹`. The following are equivalent:
- (i) for all but finitely many `p`, no `x ∈ V(ℚ_p)` has `v_p(f(x))` negative and odd;
- (ii) every geometric component of `f⁻¹(∞)` has even multiplicity;
- (iii) `V` has no `F_m`-point with `1/f = t^m` for any odd `m`.

*Proof.*
- (ii)⇒(i). Near `f⁻¹(∞)`, `1/f = u·h²` with `u` a unit on the model. Also `f⁻¹(0)` and `f⁻¹(∞)` are
  disjoint. So a `ℤ_p`-point has even `v_p(1/f)` whenever that valuation is positive.
- (i)⇒(ii). Suppose a component `C` has odd multiplicity `m` and is defined over a number field `L`. Take
  `p ∤ N` split in `L`. Lang–Weil gives a smooth `𝔽_p`-point of `C` off the other components. Hensel lifts
  it with local parameter of valuation 1, giving `v_p(1/f) = m`. Such `p` have density at least
  `1/[L^gal : ℚ]` (Chebotarev).
- (ii)⇔(iii). Use a germ through a general point of `C`, transversal to `C`. ∎

**(G-b) Transfer** (VERIFIED as a proof). Suppose `Y` has an `F_m`-point `P` with `1/g = t^m`, `m` odd,
and `X_P` has an `F_m`-point. Then `X` has `ℚ_p`-points with `v_p(1/g) = m` for a set of `p` of positive
density.

*Proof.*
- By Artin approximation the point is defined over `L{s}` (algebraic power series over a number field `L`).
- By Eisenstein's theorem, algebraic series converge `p`-adically at `s = p` for almost all `p`.
- Take `p` split in `L`. ∎

**(G-c) Fibres with points over `F_m`.**
- `F_m` is C₁ (Lang 1952, a complete discretely valued field with algebraically closed residue field;
  STANDARD). So the following have `F_m`-points, at a general `P`:
  - conics and quadrics in at least 3 variables;
  - norm-form varieties `N_{K/ℚ}(x) = c`, since `K ⊗ F_m` splits;
  - Châtelet surfaces `y² − az² = P(t)`, since `a` is a square in `Q̄`;
  - towers of these.
- In general, every rationally connected variety over `F_m` has a point (Graber–Harris–Starr, JAMS 16
  (2003), Thm 1.1, plus spreading out; STANDARD).

**Theorem G.** Suppose the generic fibre of `π` is rationally connected (in particular, any of the classes
in (G-c), with coefficients any rational functions of `y` and of extra existential parameters). Suppose
also that `Y` is not already LUS, that is, `Y` has bad `ℚ_p`-points for infinitely many `p`. Then `X` is
not LUS: it has bad `ℚ_p`-points for a set of primes of positive density.

*Proof.* By (G-a) for `Y`, `Y` has a component of odd multiplicity, hence an `F_m`-point with `m` odd.
Choose the germ outside the degeneracy locus of `π`. Then (G-c) and (G-b) apply. ∎

**Column form.** Suppose some data `y` is bad for every value of the gadget's free witnesses. Then the
completeness variety over the data (all gadget witnesses, `q` included) cannot have rationally connected
generic fibre if the gadget is LUS. Moreover, if `X → Y' → Y` is the Stein factorization and `X → Y'` is
rationally connected, then `X` is LUS iff `Y'` is LUS. So soundness lives on the finite part, that is, on
square-class conditions `f(y, q) ∈ ℚ²`. Over a bad column the curve `h² = f(y, q)` then has no
`ℚ_p`-points, so it has genus ≥ 1.

**Hypothesis "Y is not LUS".** It holds for the construction. At every prime the adversary has data with
`v_p(F(t)) = 1` and a `p`-unit test numerator, which is the case `prime_dvd_of_test` excludes. And if `Y`
were LUS, no pole gadget would be needed.

**Global (non-local) soundness.** Theorem G is about local points. A reciprocity argument could in
principle exclude the global points.
- For smooth proper rationally connected `X`, `Br X / Br ℚ` is finite, and its classes evaluate
  constantly at primes of good reduction (Colliot-Thélène–Skorobogatov, *The Brauer–Grothendieck group*,
  2021; STANDARD). So adelic points that are bad only at a good prime survive the Brauer–Manin pairing.
  Under Colliot-Thélène's conjecture, rational bad points then exist.
- Unconditionally this holds when the total space is ℚ-rational with a point (weak approximation), and for
  quadric fibrations of rank ≥ 5 over a rational base (Hasse–Minkowski with weak approximation on the
  base).
- E1 found global bad points directly in every case it tested.

## 2. The column property (VERIFIED)

For odd `p` with `v_p(R₀)` odd:
- `v(1 + RC²) = min(0, v(R) + 2v(C))`, with no cancellation;
- `v(R) = v(R₀) + 2v(a)` with `v(a) ≤ 0`, because `1 − R₀q²` cannot cancel;
- `v(B) = v(R) + 2Σ_j min(0, v(R) + 2v(C_j))` is nondecreasing in `v(R)`.

So data that is bad at one `p`-integral `q` is bad for all `q`. The trace over `K₀` only raises `v(Θ)`
(`trace_val`). Script `column_check.py`: 30 random bad data at primes `p ∈ (349, 2741)` × 200 random `q`
(denominators up to `p³`). All 6000 pairs were bad.

The property is intrinsic to the job. The consumer must derive "tests are small", which is a property of
the data alone, from `∃ q, Φ'`. If some `q` rescued bad data, the derivation would fail.

## 3. Routes tried

For each route: the exact replacement, soundness, completeness, experiment, and verdict.

**A. Fixed conic or quadric gadget.** Example: `Φ'(B) :⇔ ∃ m ∈ M, x, y : x² + y² = m(m − B)`.
- *Soundness:* only at primes inert in the splitting field of the components over `B = ∞`.
- *Completeness:* Hasse–Minkowski, with explicit Hilbert symbols.
- *E1:* bad rational witnesses at exactly the 28 primes `p ≡ 1 (mod 4)` among 59 primes in `[331, 700)`.
  Example: `(−139/337)² + (−659/337)² = 2(2 − 1/337)`.
- *Verdict:* fails, as Theorem G predicts.

**B. Coefficients depending on the input or the instance (Poonen-type).** Three gadgets were tested
(VERIFIED; `g0_counterexamples.py`, exact):
- `x² − m y² = m − B`;
- `2/B ∈ S_{m, m−B}`, i.e. `(1/B)² − m x² − (m−B) y² + m(m−B) z² = 1` (Poonen's norm-one set for an
  algebra built from the input);
- `x² − R₀y² = m(m − B)` with `B = R₀σ²`.

All three admit bad rational witnesses at all 59 primes. The third has a section (`m = 1`, `x = 1`,
`y = σ`).
- *Soundness argument attempted:* make the algebra ramify at the bad primes.
- *Why it fails:* ramification at `p` is decided by Hilbert symbols, which an existential adversary
  controls. Over `F_m` every such variety has a point (G-c).
- *Verdict:* fails. Poonen and Koenigsmann need the universal quantifier for exactly this reason.

**C. Conic bundles, Châtelet surfaces, norm-form and other rational surfaces.**
- *Completeness:* Châtelet surfaces have known Hasse principle / Brauer–Manin theorems
  (Colliot-Thélène–Sansuc–Swinnerton-Dyer 1987, STANDARD).
- *Soundness:* excluded by Theorem G, since their generic fibre is rational and has `F_m`-points (G-c).
- *Verdict:* fails.

**D. Global (Brauer–Manin) soundness for rationally connected gadgets.** See §1, global soundness.
Unconditionally excluded for ℚ-rational total spaces and for quadric fibrations of rank ≥ 5; conditionally
excluded in general. Verdict: fails.

**E. Square-class (finite-cover) gadgets, with rationally connected layers on top.**
- *Replacement:* `Φ'(y) :⇔ ∃ q, h : h² = f(y, q)` (plus rationally connected conditions, which are
  irrelevant to soundness by the Stein reduction).
- *Soundness:* possible, for example `f = m(m − B)`, whose valuation is odd at bad `y`.
- *Completeness:* a rational point on the curve `h² = f(y_inst, q)` with `q ∈ U`. By Theorem G (column
  form) this curve has genus ≥ 1.
- *E3* (`genus_trivial.py`, toy test site with six tests in `ℚ(√2)`): degree 84–100, 52–76 branch points,
  genus 25–37.
- *E4* (`genus1_redesign.py`): if `Θ` did not depend on `q`, the curve would be the genus-1 quartic
  `h² = m(mΘ₀² − R₀(1 − R₀q²)²)`. Over 30 samples and 16 multipliers, no point of height ≤ 2000 was found,
  and the Jacobian rank lower bound was ≥ 1 in all 30 samples.
- *Verdict:* the minimum is a genus-1 Hasse problem, of CR₃'s kind. Not elimination. The redesign's
  soundness is unchecked (SPECULATIVE).

**F. Curves or varieties with a section over the needed locus (explicit witnesses).**
- The honest tests come from multiples of `P₀`. A proper subvariety of `E` contains only finitely many
  multiples, so the honest data are Zariski dense.
- A witness family over the honest data is therefore a rational section. It is defined on a dense open
  set, which meets the `p`-adically open bad set.
- *Verdict:* fails (VERIFIED). Per-instance choices (`q`, `κ`, shifts, `m`) cannot confine the data to a
  subvariety.

**G. Integral-point (Pell) gadgets via `m = m₀k²`.**
- `k` is bit-encoded, hence bounded by `2^{#bits}`. Pell solutions grow exponentially, so completeness
  cannot be uniform.
- Integrality from elsewhere in the construction would be circular.
- *Verdict:* fails.

## 4. The strongest obstruction, and what would be needed

The obstruction is (G-a) with Graber–Harris–Starr:
- LUS ⇔ a geometric double fibre over the bad locus;
- a geometric double fibre ⇒ no `F_m`-point ⇒ the fibre is not rationally connected.

The column property makes this apply to the completeness variety itself. Hence any gadget satisfying SC1
must ask, for completeness, for rational points on non-rationally-connected varieties over a Zariski-dense
set of data. Those points cannot be algebraic (route F) and cannot come from a Hasse principle for
rationally connected varieties (Theorem G).

An escape would need one of the following:
- (i) an arithmetic existence theorem for non-rationally-connected varieties in a thin family, which is
  CR₃'s kind (cr3-map-literature);
- (ii) an architecture whose data space `Y` already carries the parity, so that no pole gadget is needed.
  rs-global C1–C2 together with Theorem G applied to `Y` show that this needs genus ≥ 1 there instead.

Neither falls within this angle.

**Variable budget.** No sound gadget was found, so nothing is charged. The genus-1 redesign (E4) adds no
pole witnesses, but it changes `Θ` and therefore the soundness proof (unchecked).

## Scripts (`scratch/el-gadget/`)

- `g0_counterexamples.py`: E1, explicit bad witnesses for genus-0 gadgets (PARI `qfsolve`, exact check).
- `column_check.py`: E2, the column property (standard library only).
- `genus_trivial.py`: E3, the genus of `m(m − B(q)) = h²` on honest lines (sympy).
- `genus1_redesign.py`: E4, the genus-1 redesign (PARI `hyperellratpoints`, `ellrank`).
