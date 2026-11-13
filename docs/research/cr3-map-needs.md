# CR₃ attack, map-needs: what the Lean proof needs from CR₃

Checkout: `Deicyde/diophantine-z-q` at `50d1b052` (read only).
Marks as in `docs/research/rs-pole.md`: **VERIFIED** (checked against the Lean sources, the notes,
or by exact computation; scripts in `scratch/cr3-map/`), **STANDARD** (published theorem, with
reference), **SPECULATIVE** (idea, unproved). No Lean was run (host load 145-280).

This note builds on rs-pole §2.1-2.3 and §4.3, slot-k, descent-alt §1.3, §4.2 and §4.5,
rv-route-k §4.2 and rs-global §1.2-1.3. Facts proved there are cited, not re-derived.

## 0. Findings

1. **Two consumers, both instance-existential.** In the headline theorem
   `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank`
   (`MainGreenTao.lean`), CR₃ reaches the proof only through
   `poleCompleteness_of_certifiedRank`. PC is applied in two places: `test_complete`
   (`Assembly/Local/TestCompleteness.lean:104`) and `slope_complete_AP`
   (`Multiplication/Completeness/AP/SlopeCompleteness.lean:177`). (`slope_complete` is the non-AP
   twin on the 22P path.) Each place needs `Φ(B(q))` for one `q` per instance. (VERIFIED)
2. **Per instance, CR₃ is used on two curves.** For an admissible `B`, DL produces
   `d₁ = |β|·q₀·Π r_p·Π r_ℓ` and `d₂ = d₁θ`. CR₃ must put a point with `x ∈ βℚ*²` on each of
   `C_{d₁}` and `C_{d₂}`. (VERIFIED)
3. **Exact curve form of `Φ`.** `Φ(B)` holds iff there are `m ∣ 2730`, `m ≠ B`, and `N ∈ ℚ*` with
   `Loc N β ∧ Loc (Nθ) β`. Here `Loc d a` holds iff the quartic `w² = a(a²s⁴ − d²)` has a rational
   point with `s ≠ 0` (§1, L5). So CR₃ can be replaced by any statement that yields these two
   quartic points, for one `(q, m, N)` per instance. (VERIFIED)
4. **Soundness needs Lemma 5.1 only at primes `p > 324`.** The two consumers are `pole_step`
   (`TestDivisibility.lean:321`) and `CommonGroup.lean:114`. Hence `S₀ = {2,3,5,7,13}` can be
   enlarged to any set of primes `≤ 324`. (VERIFIED)
5. **Multipliers are much freer than divisors of 2730.** The proof of Lemma 5.1 goes through
   unchanged whenever `v_p(m)` is even and `≥ 0` at every `p > 324`. So `m = m₀k²`, with `m₀` a
   signed divisor of `Π_{p≤324} p` and `k` a bit-encoded integer, keeps soundness. A negative even
   `v_p(m)` breaks it. (VERIFIED by derivation, 20 exact cases plus a counterexample)
6. **rs-pole §4.3 excludes less than it states.** Its p-adic argument rules out `q` polynomial in
   the parameters. It does not rule out rational families whose poles avoid `ℚ_p` at the finitely
   many relevant primes. What blocks explicit-witness families is genus: `θ(q) = 1` lies on a curve
   of large genus. Soundness itself cannot use a free square factor, because no nonconstant function
   is integral at all large primes. (§1, L8; the genus claim is STANDARD by Faltings, its
   application here SPECULATIVE)
7. **The variable budget is a hard redesign constraint.** `FrozenTarget` fixes
   `Fin 292890231905` (`Target.lean:19`). rs-global counts 292,890,231,904 witnesses, about 8.3
   million copies of the multiplication template, and one pole call per copy. So every extra pole
   witness variable costs about 8.3 million variables, which must be saved elsewhere. Degree and
   coefficient bounds have huge slack. (VERIFIED)

## 1. Results log

### L1. Call graph (VERIFIED, by `grep` and reading)

- `CertifiedRank` is applied only in `poleCompleteness_of_certifiedRank`
  (`RouteK/Assembly/PoleCompleteness.lean`). It is applied twice, at
  `d = n.natAbs` and `d = (n·θ).natAbs`, both times with `a = betaOf B m`.
- `PoleCompleteness` is applied in these places:
  - `test_complete`, called by `value_relation_iff_of` (`Assembly/Top/ValueRelation.lean:60`). Any
    `κ ≠ 0` works there: `hcomp` (Close completeness) holds for every `κ ≠ 0`.
  - `slope_complete_AP` (via `slopes_of_int_AP`, `completeness_core_AP`, `multiply_complete_AP`,
    `multiplication_exact_AP`), or `slope_complete` on the 22P path.
- PC also feeds soundness of the value relation, indirectly. `close_sound` takes
  `SpecMultiplicationExact`, which is an iff whose completeness half is `slope_complete_AP`. So
  CR₃'s only effect is the existence of slope and test witnesses.

### L2. Test site (`test_complete`, Lemma 11.2, manuscript lines 6202-6234) (VERIFIED)

- **Instance:** an integer `n ∉ 𝒞 = {0, −15, −20, −24, −30, −60}`. Let `F = sixF n`,
  `Z = 2730⁶F`, `η = sign F`, and `R₀ = |Z| > 1` (`testR₀ η n`).
- **Integer choices.** `κ ≥ 1` comes from `exists_common_smul_mem_Ek`, with `[κ]P₀ ∈ E_N(π)` for
  every `π ∣ R₀` in `ℤ[√2]` and `N = 1 + Σ v_π(F)`. Then `h = 2κ` and `s₀ = 2κn`. `Test` itself
  accepts any `h ≠ 0, κ` and any `s₀`. Other choices `h = jκ`, `s₀ = jκn` are plausible
  (SPECULATIVE: `tests_deep` was checked only for `j = 2`).
- **Pole input:**
  ```
  B(q) = R₀·a₀(q)² / Θ(q)²,   a₀ = 1 − R₀q²,   R = R₀a₀²,
  Θ = Tr_{K₀/ℚ}(W⁻¹),   W = Π_{j<6} (1 + R·C_j²),   C_j = D_j / F,
  ```
  where `D_j` are the six tests (`testD n κ n 2κ 2κn`): `w` and `z` coordinates of
  `[h]P₀, [s₀]P₀, [h−κ]P₀, [s₀−κn]P₀` on `y² = x³ − (75 − 53√2)²x` over `K₀ = ℚ(√2)`.
- **Open set of `q`** (`poleInput_real`, `poleInput_local`):
  `U_test = {q : v_p(q) ≥ 0 for all p ∣ R₀} ∩ {q : R₀a₀² < r(C)}`. The real part is two intervals
  around `±R₀^{−1/2}`. Lean uses `q = k/(R₀j + 1)`. On `U_test`: `a₀, W, Θ ≠ 0`, `0 < B < 1/2`,
  `v₂(B) ≥ 4`, `v_p(B) ≥ 6` (`p = 3, 5, 7, 13`), and the reduced denominator is a square.
- **Square classes.** `β = sqf(m·ηF(n))` does not depend on `q`, `κ`, `h`, `s₀`. All of these move
  `θ = sqf(m(m − B))` (rs-pole §2.1(a), descent-alt §1.3).

### L3. Slope site (`slope_complete_AP`, manuscript lines 1704-1751) (VERIFIED)

- **Instance:** `n₁, n₂ ∈ ℤ` and a slope `t` with `GoodSlopeAP B₀ t`. `t` is fixed by the
  hypothesis. `P(t)` is the set of odd contact primes outside `S_b`, with `|P| ≤ 6`.
- **Pole input:**
  ```
  B(q) = ℓ₀²·a(q)²·R₀ / Θ(q)²,   R₀ = ηF(t)/(t − 1)⁸,   a = 1 − R₀q²,   R = ℓ₀²a²R₀,
  Θ = Tr Σ_{g<6} W_g⁻¹,   W_g = Π_{j<12} (1 + R·C_{gj}²),   C_{gj} = D_{gj} / (R₀^{k_j}(t−1)^{k_j+1}),
  ```
  Here `D_g = testValues(h_g, z_g, c)`, `c = certShifts(n₁, n₂, n₁n₂)`, `z_g = (n₁h_g, n₂h_g, n₁n₂h_g)`,
  and `k_j ∈ {1, 25}`. `ℓ₀ = Syntax.ell` is a fixed constant. `η` is fixed by `R₀ > 0`.
- **Shifts.** `h_g = hfun(sel g)`. At a selected prime `p` this is the shift from `exists_shift`
  (`shift_choice`); otherwise it is `2c_*`.
- **Open set of `q`** (`weak_approx_q` or `weak_approx_targets`):
  `U_slope = {q : |q − x₀| < δ, q ≠ ±x₀}`, with `x₀ = R₀^{−1/2}` and `δ` from `pole_input_small`,
  intersected with the local conditions:
  - `v_p(q) ≥ C_p` for `p ∈ S_b` (`C_p = 56` for `p ≤ 324`, `14` on the catalogue);
  - `v_p(q) ≥ 0` for `p ∈ P(t)`;
  - under field 2′, at an old prime that uses Lemma P, the Lemma P(2) ball replaces `v_p(q) ≥ C_p`:
    `v_p(1 − R₀q²) ≥ 23e + v_p(12) + 2`, so `q` is `p`-adically near `±R₀^{−1/2}`.
- **Valuations of `B`** (`pole_input_valuations`):
  - `v_p(B) ≥ 103C_p + 8` on `S_b`;
  - `v_p(B) = 1` at each `p ∈ P(t)`;
  - `v_p(B)` is even at all other primes.
- **Square classes.** `β = sqf(m·ηF(t))` depends only on `t` and `m`. The primes of `β` lie in
  `S_b ∪ P(t) ∪ {primes of m}` (descent-alt §1.3).

### L4. PC → DL → CR₃ (VERIFIED, `PoleCompleteness.lean`, `DL.lean`, `Slots/*`, `Points.lean`)

- **Admissible `B`.** `IsSquare B.den`, `0 < B < 1/2`, and `v_p(B) ≥ 4` on `S₀`. Each hypothesis
  is used:
  - the square denominator and the `S₀` valuations give (θ1)-(θ4):
    - (θ1) `θ > 0`, `θ ≡ 1 (mod 8)`, `gcd(θ, 2730) = 1`;
    - (θ2) `β` and `θ` are coprime;
    - (θ3) `(β/ℓ) = 1` for every `ℓ ∣ θ`;
    - (θ4) `(θ/p) = 1` for every `p ∣ β`;
  - `0 < B` gives `θ > 0`;
  - `B < 1/2` gives `m ≠ B`.
- **Multiplier** (`exists_multiplier_pos`). `m = 2^f·m₀` with `f ≤ 1` and `m₀ ∈ {1, 3, 5, 7}`
  chosen so that `β` is odd with `|β| ≡ 7 (mod 8)`. DL uses only positive divisors of 210, one per
  `B`. The factor 13 and the negative signs are never used.
- **Slots** (`Slots β θ p₀`, any `p₀ ∣ β`).
  - `q₀`: a prime `≡ 3 (mod 8)`, prime to `2βθ`, with prescribed symbols `[p/q₀]` for `p ∣ β`
    and `[ℓ/q₀] = 0` for `ℓ ∣ θ`.
  - `r_p` for `p ∈ P∖{p₀}`, and `r_ℓ` for `ℓ ∣ θ`: primes `≡ 1 (mod 8)` with a prescribed
    symbol pattern against all earlier primes.
  - All of them exist by Dirichlet, quadratic reciprocity and CRT. Each slot has infinitely many
    choices.
- **Curves and points needed:**
  - `C_{d₁}`, `d₁ = |β|q₀Π r_pΠ r_ℓ ≡ 5 (mod 8)`;
  - `C_{d₂}`, `d₂ = d₁θ ≡ 5 (mod 8)`;
  - on each, a point `(x, y)` with `x ≠ 0` and `x/β ∈ ℚ²`.

  DL certifies `#Σ(𝒞_d) = 8` and that the class of `β` lies in `Σ` for both curves. CR₃ converts
  each certificate into a point. L6 (`poleSoluble_of_points`) rescales the two points into the
  eleven witnesses: `e = d₁(t/s)²`, `z = s′h/s`, `w = (eHz)⁻¹`.

### L5. Exact curve form of `Φ` (VERIFIED)

- **Definition.** `Loc d a :⇔ ∃ x y, y² = x³ − d²x ∧ x ≠ 0 ∧ IsSquare (x/a)`. With `x = as²` and
  `y = sw`: `Loc d a ⇔ ∃ s w, s ≠ 0 ∧ w² = a(a²s⁴ − d²)`. Checked on 12 points
  (`check_needs.py`, check1).
- **Equivalence.** For `B ≠ 0`, `Φ(B)` holds iff `∃ m ∣ 2730, m ≠ B, ∃ N ∈ ℚ*, Loc N β ∧ Loc (Nθ) β`.
  - (⇐) is L6.
  - (⇒) is not in Lean; derivation: a zero of `polePoly` forces bits in `{0,1}`, so `m` is a
    signed divisor of 2730. `eHzw = 1` gives `A, H, e, z ≠ 0`. Then `(A, r₁) ∈ C_e` with
    `A ∈ βℚ*²`, and `(Az², zr₂) ∈ C_{eH}` with `eH ∈ eθℚ*²`. Take `N = e`.
  - In both `Loc` statements, `θ` can be replaced by `m(m − B)` and `β` by `A = mB`.
- **Parametrized form.** By rv-route-k §4.2 this is `θ(β² − τ₁⁴)(β² − τ₂⁴) ∈ ±ℚ*²`. The witnesses
  were rebuilt by the Points.lean recipe, and `polePoly = 0` was checked exactly for three toy
  `(B, m, τ₁, τ₂)` (check2). Of 8 toy inputs, 5 have no `τ` of height ≤ 6. These toys test only
  the algebra; they are not admissible.
- **Torsion shortcut.** `N = ±β` gives `Loc β β` from the 2-torsion point `(β, 0)`. Then one curve
  remains: `Loc (βθ) β`, equivalently `Loc (βθ) θ`, the quartic `w² = θ(θ²s⁴ − β²θ²)`. DL never
  uses it: `d₁` always contains `q₀`. descent-alt §4.2 gives the exact Selmer criterion for it and
  a structural obstruction (all primes of `θ` `≡ 1 (mod 4)`).
- **Torsion classes.** The torsion abscissa classes on `C_d` are `±1, ±d`. Since `|β| ≡ 7 (mod 8)`,
  `Loc d β` needs a non-torsion point unless `d ≡ ±β`.

### L6. Where soundness consumes Lemma 5.1 (VERIFIED)

- `pole_step` (`TestDivisibility.lean:225`, applied at line 321), used by `prime_dvd_of_test` for primes
  `p > 324` with `v_p(t − c) > 0` odd. Its form: `Φ(R/Θ²)` and `v_p(R)` odd imply
  `2v_p(Θ) < v_p(R)`.
- `CommonGroup.lean:114`, at odd contact primes `p > 324` with `v_p(ℓ₀) = 0`.
- Nothing else. So the obstruction is needed only at `p > 324`. Conditions at primes `≤ 324`
  (`S₀`, the multipliers) are design freedom.
- **Consequence for the hypothesis side.** The slope site already supplies `v_p(B) ≥ 103C_p + 8`
  on `S_b ⊇ {p ≤ 324}`. The test site supplies high valuations only at 2, 3, 5, 7, 13, through the
  factor `2730⁶` in `testR₀`. Enlarging `S₀` would require `2730⁶ → (Π_{p≤324} p)⁶` there.
  (SPECULATIVE: the effect on `test_dvd` and `tests_deep` was not checked)

### L7. Generalized multiplier (VERIFIED by derivation; check3)

**Lemma.** Let `p` be odd, `B ≠ 0` with `b = v_p(B) < 0` odd, and `v_p(m) = 2j` with `j ≥ 0`.
Then the pole system with multiplier `m` has no solution.

**Proof.**
- `a = v_p(A) = b + 2j` is odd. `(A, r₁) ∈ C_e` forces `v(e) = a`; otherwise `v(r₁²)` is `3a` or
  `a + 2v(e)`, both odd.
- `(Az², zr₂) ∈ C_{eH}` forces `v(eH) = a + 2v(z)`, so `v(H) = 2v(z)` is even.
- But `a − 2b = 2j − b > 0`, so `v(A − B²) = 2b` and `v(H) = 3b + 2j`, which is odd. ∎

**Boundary.** If `v_p(m) = −2`, `v_p(B) = −1`, then `v(A) = −3 < 2b`, so `v(H) = −6` is even and
the argument fails (check3).

**Consequence.** A multiplier set `M` keeps Lemma 5.1 at `p > 324` iff (for this proof) every
`m ∈ M` has `v_p(m) ∈ 2ℕ` at all `p > 324`. Example: `m = m₀k²`, with `m₀ ∣ Π_{p≤324} p` signed
and `k = Σ 2^i c_i`, `c_i² = c_i`.

**Use and limits.**
- `m₀k²` leaves `β` unchanged and moves `θ = sqf(m₀(m₀k² − B))`.
- For fixed `B`, only finitely many integers `k` give `θ = 1`: these are integral points on the
  hyperbola `(m₀k)² − v² = m₀B·c²`. (VERIFIED, divisor argument)
- Cost: each multiplier bit is one witness per pole call (finding 7).

### L8. rs-pole §4.3 refined (STANDARD facts; application SPECULATIVE)

- **What the p-adic obstruction excludes.** It forbids `q` near `∞` in `ℚ_p` for `p ∈ P(t)` (the
  bad region is `v_p(q) < −v_p(R₀)/2`). Per instance this is a finite set of primes. A family
  `q = φ(x)`, with `φ` rational and poles that are not `ℚ_p`-rational for `p ∈ P(t) ∪ S_b`, is
  bounded on `ℚ_p`. It is not excluded by that argument.
- **What blocks explicit families.**
  - `θ(φ(x)) = 1` means a map from `ℙ¹` to the curve `m(m − R₀σ(q)²) = v²`. Its genus is large
    (σ has degree in the hundreds), so no nonconstant map exists. Faltings even gives finiteness
    of such `q` (STANDARD).
  - More generally, `Φ` along a family needs a curve on the 3-fold
    `V: ±m(m − R₀σ(q)²)(β² − τ₁⁴)(β² − τ₂⁴) = w²`, which is fibred over the `q`-line in K3 surfaces.
- **What blocks free square factors in soundness.** Soundness would need a function integral at
  all `p > 324` at once. By Chebotarev, some prime splits each pole field, so no nonconstant
  function on a curve is integral on all `ℚ_p`-points for all large `p` (STANDARD). This, not
  "polynomial in parameters", is the obstruction to a free square factor.

### L9. The sandwich (VERIFIED as stated; consequence SPECULATIVE)

- Let `Ob = {B ≠ 0 : ∀ p > 324, ¬(v_p(B) < 0 ∧ Odd v_p(B))}`.
  - Soundness (L6) needs `Φ' ⊆ Ob ∪ {0}`.
  - Completeness needs `B_inst(q*) ∈ Φ'` for one `q*` per instance.
- PC-type statements want `Adm ⊆ Φ'`. Then `Φ' ∩ Adm-box` is an existential definition of the
  square-denominator rationals in a box, which is essentially the definability problem itself.
- The only slack is that completeness needs just the instance points. The predicate may also take
  more inputs than `B`, such as `R` and the tests separately. Soundness is consumed only through
  the implication `Φ'(R/Θ²) ∧ Odd v_p(R) → 2v_p(Θ) < v_p(R)`.

## 2. The weakest replacement statements (Lean-like)

Write `LocQ d a := ∃ s w : ℚ, s ≠ 0 ∧ w ^ 2 = a * (a ^ 2 * s ^ 4 - d ^ 2)`. By L5,
`LocQ d a ↔ ∃ x y, y² = x³ − d²x ∧ x ≠ 0 ∧ IsSquare (x/a)`, the conclusion of CR₃.

**(W0) What the consumers need, exactly.** The current proofs derive both conjuncts from PC.
```
def PCNeed : Prop :=
  (∀ n : ℤ, (n : ℚ) ∉ contactSet → ∃ κ : ℤ, κ ≠ 0 ∧ Assembly.Test n κ n) ∧
  (∀ (n₁ n₂ : ℤ) (t : ℚ) (B₀ : ℝ), Mult.GoodSlopeAP B₀ t →
      Mult.SlopePred t Syntax.ell (Mult.certShifts ![n₁, n₂, n₁ * n₂]))
```

**(W1) Instance-level, curve form.** This is the weakest statement in CR₃'s vocabulary that both
proofs accept unchanged up to the last line. Below, `inst` is either `n` (test site, with `κ` from
L2) or `t` (slope site, with `h` from L3); `U inst` is `U_test` or `U_slope` (L2, L3); and
`σ inst q` is `a₀/Θ` or `ℓ₀a/Θ`.
```
def CR3Inst : Prop := ∀ inst, ∃ q ∈ U inst, ∃ m : ℤ, m ∣ 2730 ∧ ∃ N : ℚ, N ≠ 0 ∧
  LocQ N (sqf (m * R₀ inst)) ∧
  LocQ (N * (m * (m - R₀ inst * σ inst q ^ 2))) (sqf (m * R₀ inst))
```
- It suffices because L6 applies at `B = R₀σ²`. It is equivalent to W0 for the current `polePoly`
  (L5).
- `PC⁻` of rs-pole §2.1(b) is this statement before the curve translation.

**(W2) PC in curve form.** Equivalent to `PoleCompleteness` (L5).
```
def CR3Adm : Prop := ∀ B : ℚ, RouteK.Admissible B → ∃ m : ℤ, m ∣ 2730 ∧ (m : ℚ) ≠ B ∧
  ∃ N : ℚ, N ≠ 0 ∧ LocQ N (betaOf B m) ∧ LocQ (N * thetaOf B m) (betaOf B m)
```

**(W3) Drop-in for CR₃ that keeps DL's construction.** This is strictly implied by CR₃:
- `selmerCertified_d₁` and `selmerCertified_d₂` hold for every `D`;
- `CertifiedRank` turns each certificate into `LocQ`.
```
def CR3DL : Prop := ∀ (β θ : ℤ) (p₀ : ℕ), RouteK.Inputs β θ p₀ →
  ∃ D : RouteK.Slots β θ p₀, LocQ (D.d₁ : ℚ) β ∧ LocQ (D.d₂ : ℚ) β
```
`poleCompleteness_of_certifiedRank` adapts by reading the source (no Lean run):
`exists_multiplier_and_slots`, `inputs_of_admissible`, `CR3DL`, `D.d₂_eq`, then
`poleSoluble_of_points` with `N = d₁`. This is the cleanest narrowing that keeps the Selmer
engineering optional. A proof of CR3DL may pick the slots (infinitely many choices each, L4), and it
does not need the 8-solution condition.

**(W3′) One-curve variant** (sufficient, not necessary):
`∀ β θ, Inputs-like β θ → LocQ (β * θ) β`. This is the torsion shortcut of L5. It is false in
general, by the obstruction in descent-alt §4.2(iii). Its instance form, with `θ = θ(q)` for some
`q ∈ U`, is open.

**Chain.** `CR₃ ⇒ W3 ⇒ W2 ⇔ PC ⇒ W1 ⇔ W0` for the current `polePoly`.
- W0 and W1 change if the pole predicate is redesigned.
- The other two hypotheses of the headline theorem are untouched: `SixContactMin` (H) is a
  separate input, and route AP is proved.

## 3. Freedom dimensions and their constraints

| # | Freedom | Range now | Constraint | Effect on the needed points |
| --- | --- | --- | --- | --- |
| F1 | witness `q` | open set of `ℝ × Π_{p∈S} ℚ_p` (L2, L3) | real part keeps `0 < B < 1/2`; `p`-integral at `P(t)` (soundness, L8); `v_p(q) ≥ C_p` or Lemma P ball on `S_b`; `p`-integral at `p ∣ R₀` (test) | only `θ` moves; `β` fixed |
| F2 | test integers `κ, h, s₀` | `κ` from deep multiples; `h = 2κ`, `s₀ = 2κn` | deep membership at `π ∣ R₀`; `h ≠ 0, κ`; Close needs only `κ ≠ 0` | `θ` moves, through `Θ`; `β` fixed |
| F3 | slope shifts `h_g` | `shift_choice` at `P(t)`, else `2c_*` | precision at one place over each `p ∈ P(t)`; integrality over `S_b` | `θ` moves; `β` fixed |
| F4 | multiplier `m` | signed divisors of 2730 (DL uses 8 positive ones) | soundness needs `v_p(m)` even `≥ 0` at all `p > 324` (L7); DL needs `|β| ≡ 7 (mod 8)` (TYZ shape) or `|d| ≡ 5, 6, 7 (mod 8)` (parity), and `m(m − B) > 0`; bits cost variables | moves both `β` (by the class of `m₀`) and `θ` |
| F5 | `S₀` | `{2,3,5,7,13}` | any subset of `{p ≤ 324}` (L6); the test site must then supply its valuations | more local control on `θ` |
| F6 | twist `N` | `d₁ = |β|q₀Π r_pΠ r_ℓ` | any `N ∈ ℚ*/±ℚ*²` with odd `supp β ⊆ supp N` (local necessity, rs-pole §2.3) | chooses the two curves |
| F7 | slot primes, `p₀` | Dirichlet residue and symbol conditions | infinitely many per slot | fine structure of `Sel₂` |
| F8 | certificate | `#Σ = 8` and `β ∈ π₁Σ` | `Φ` needs only the two `LocQ` | none (proof device) |
| F9 | pole predicate shape | Route K `polePoly`, 2 curves, `H = A(A − B²)` | soundness constraints SC1-SC4 (§4); variable budget | defines what "points" means |
| F10 | per-instance choice | one `(q, m, N)` per instance | none (W1 is existential) | no uniformity needed |

## 4. Soundness constraints any redesign must keep

**SC1. One-sided obstruction at `p > 324`.**
```
∀ B ≠ 0, Φ'(B) → ∀ p, p.Prime → 324 < p → ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B))
```
or at least its consumed form: `Φ'(R/Θ²) ∧ Odd v_p(R) → 2v_p(Θ) < v_p(R)` at `p > 324`. Today's
proof uses only:
- the multiplier is a `p`-unit (L7 relaxes this to even `v_p ≥ 0`);
- for a `p`-unit parameter, the cubic `x(x² − ℓ²)` has valuation `v(x)` when `v(x) > 0` and
  `3v(x)` when `v(x) < 0`;
- `v(H) = 3v(B)` for `v(B) < 0`.

**SC2. The free data enter `B` only through squares.** We need `v_p(R)` odd at every odd contact
prime, for every witness value:
- test: `v_p(R) = δ + 2v_p(a₀)` (`testR_val`);
- slope: `2v(ℓ₀) + 2v(a) + v(R₀)`.

Hence `β = sqf(mR₀)` contains every prime with `v_p(F)` odd, and `ω(β)` is unbounded (rs-pole
§2.3). Any input must handle twists with unboundedly many primes.

**SC3. The pole denominator `Θ` must be built from the tests.** Soundness extracts
"tests small" from `2v_p(Θ) < v_p(R)` through the trace bound (`trace_val`, `CommonGroup`). A
redesign may change `W` and `Θ`, but must keep this implication.

**SC4. Completeness forces `q` to be `p`-adically bounded.**
- At each `p ∈ P(t)` (and at each `p` with `v_p(R₀)` odd at the test site), `v_p(q) < −v_p(R₀)/2`
  makes `v_p(B) ≤ 3k − 12N + O(1)` negative and odd (rs-pole §4.3), so `Φ'` must fail.
- On `S_b` and `S₀` the PC hypothesis needs `v_p(q) ≥ C_p`, or a Lemma P ball.
- Real place: `|1 − R₀q²|` is small.
- These are finitely many local conditions per instance, with the set depending on the
  factorization of `F(t)`.

**SC5. Budget.** At most 292,890,231,905 variables in total (`Target.lean`). The pole call sits
inside the multiplication template, so every extra pole witness costs about 8.3 million variables
(rs-global §2.4). The `polePoly` degree (75) is far below the bound.

## 5. Where an elimination attempt must act (SPECULATIVE)

- **The depth lies in two quartic points.** By W1, CR₃ is used to produce two rational points on
  the quartics `w² = β(β²s⁴ − N²)` and `w² = β(β²s⁴ − N²θ²)`.
  - `β` is fixed by the instance.
  - `θ = sqf(m(m − R₀σ(q)²))`, with `q` in a box.
  - `N` is free.
- **Local freedom alone cannot do it.** descent-alt §4.2(i) shows the quartics are everywhere
  locally soluble. The obstruction is global, and F1-F7 are local or finite freedoms.
- An elimination therefore needs one of the following.
  - (a) A redesigned `Φ'` (F9) that satisfies SC1-SC5 and whose completeness at the honest inputs
    follows from a theorem already in Lean. The candidates are Mordell-Weil for one fixed curve
    (`mordellWeilE`), Dirichlet, and density statements. L9 says `Φ'` cannot be complete on all
    admissible `B` unless it encodes the problem itself. So it must exploit the instance structure
    `B = R₀σ²` with `σ` built from labels.
  - (b) An instance-level argument that some `q ∈ U` makes `θ(q)` land on a pair for which points
    are explicit. L8 says rational families cannot do this (genus), so it would need a
    Hilbert-irreducibility or sieve input on values `θ(q)`. descent-alt §4.5 rates that open.
- **Narrowing if elimination fails.**
  - W3 (CR3DL) is strictly weaker than CR₃ and is a drop-in.
  - Its one-curve instance form, `∃ q ∈ U, LocQ (βθ(q)) β`, removes the slots and halves the
    curves. It is not known to hold for every instance.
- **Next step.** Write W3 as a Lean `def` with the adapted
  `poleCompleteness_of_certifiedRank` when a Lean slot is free. Success means the proof compiles
  with CR3DL in place of CR₃. Separately, test L7 (multipliers `m₀k²`) and the one-curve instance
  form on devserver samples. Spec: 30 admissible test-site `B(q)`, `k ≤ 2⁸`; record how often
  `θ = 1` or the torsion shortcut certifies.

## Scripts

- `scratch/cr3-map/check_needs.py`, standard library only, under 1 s:
  - check1: quartic form of `Loc`, 12 points;
  - check2: `polePoly = 0` from `(m, τ₁, τ₂)` by the Points.lean recipe, 3 of 8 toy inputs;
  - check3: generalized multiplier valuations, 20 cases and one counterexample.
