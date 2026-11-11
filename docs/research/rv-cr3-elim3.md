# rv-cr3-elim3: adversarial review of el-cert, el-k3 and el-qfree

Branch `wip/rv-elim3` (from `d549dabb`). No Lean was run. No file under `ZInQKernel/`,
`blueprint/` or another note was edited. Scripts are in `scratch/rv-elim3/`. The step log
`scratch/rv-elim3/log.md` gives the inputs and outcome of each computation (Steps 0-10).
PARI 2.17 via cypari2. Every computation ran sequentially in the foreground, each in under 6 minutes.

Marks:
- **VERIFIED**: by exact computation (script named) or by a derivation checked here against the
  Lean sources.
- **STANDARD**: a published theorem.
- **SPECULATIVE**: a heuristic or an unproved step.

## Summary

| note | main claims | repairs | verdict "very low" |
| --- | --- | --- | --- |
| el-cert | verified after repairs | 2 minor (the Lean form of M1; scope of L-B) | **stands** |
| el-k3 | verified after repairs | 3 minor (θ = −β case added; "2-covering" wording; θ-uniformity argument is heuristic) | **stands** |
| el-qfree | verified after repairs | 3 (finiteness of `M` is open, not proved; the Hom claim holds only for constant `N`; the window is now proved necessary) | **stands** |

None of the three main obstructions was refuted. Each repair narrows a claim's scope or its
mark. None of them opens a route to eliminating CR₃.

## 1. el-cert

### 1.1 M1 soundness: VERIFIED (by reading the Lean proofs)

**Test site** (`Assembly/Local/TestDivisibility.lean`, `prime_dvd_of_test`). The proof chains:
- `pole_step` on `(R, Θ)`;
- `trace_val`: `−v_π(W) ≤ v_p(Θ)`;
- `tests_small`, with the **same** `R` inside `W`;
- the closing inequality `4v(F) − 3v(R) < 4v_π(D)`, with `v(R) = v(F) + 2b`, `b = v(a₀) ≤ 0`.

Under M1 the numerator is `R₀a₀²` and `W₀ = poleW(R₀, C)`.
- `pole_step` on `(R₀a₀², Θ₀)` gives `2v(Θ₀) < v(F) + 2b ≤ v(F)`.
- With `trace_val` this is `−v(R₀) < 2v_π(W₀)`, which is the hypothesis `hlam` of `tests_small`
  with `R := R₀`.
- The conclusion `v(F) < 4v_π(D)` then gives `v_π(D) ≥ 1`. This is exactly the original proof at
  `q = 0`.

**Slope site** (`Multiplication/Soundness/CommonGroup.lean`, `common_group_of`). The step `hex`
derives a contradiction from "`2v_π(W_g⁻¹) ≥ r` for every `g` and `π`" through
`pole_obstruction`. Under M1:
- `r_W = v(ℓ²R₀) = k`, since `v(ℓ) = 0`;
- the hypothesis gives `v(Θ₀) ≥ (k + 1)/2`;
- so `v(ℓ²a²R₀/Θ₀²) ≤ 2v(a) − 1`, which is negative and odd.

The closing step needs `r ≤ k`, and it holds with equality.

**Where `v(a) ≤ 0` comes from.** Every use of the pole step has `v_p(R₀)` odd, and then
`v(a) ≤ 0` holds because `x² − R₀y²` is anisotropic.

**Guards.** `R₀ ∈ ℚ` is positive, so every factor of `W₀` is at least 1 in both real embeddings,
and `W₀, Θ₀ > 0`: VERIFIED.

**Repair (minor).** M1 is not a literal substitution in Lean. `pole_step`, and `hex` in
`common_group_of`, must be restated for a numerator `R_W·a²` that differs from the argument of
`W`. The restatement adds one use of `2v(a) ≤ 0`. el-cert's own enumeration X1 checks exactly
this inequality (`x1_genus.py`, rerun in Step 9: 0 counterexamples).

### 1.2 Local obstruction lemma: VERIFIED

**Statement.** Let `p` be odd with `p ∤ 2mR₀`, `v_p(Θ₀) ≥ 1` and `(R₀/p) = −1`. Then the curve
`C_m : Y² = m²Θ₀² − mR₀(1 − R₀q²)²` has a `ℚ_p`-point iff `(−m/p) = −1`.

**Independent proof.**
- `v(a(q)) = min(0, 2v(q))`, since `x² − R₀y²` is anisotropic mod `p`.
- So `f(q) = −mR₀a²(1 + O(p^{2v(Θ₀) − 2v(a)}))` has even valuation and unit class `−mR₀`.
- The points at infinity have the class of `−mR₀³`, which is the same.
- So `C_m(ℚ_p) ≠ ∅` iff `(−mR₀/p) = 1`, i.e. iff `(−m/p) = −1`.

**Rerun** (`c1_local.py`). 26 new random cases: `p` ∈ {7, 29, 31, 37, 41, 43}, seed 7,
`v_p(Θ₀)` ∈ {1, 2}. el-cert's brute force mod `p³` agrees with the criterion in 26/26
(10 soluble, 16 insoluble).

**New adversarial check on real data** (`c2_theta0_primes.py`). The lemma matters only if primes
with `(R₀/p) = −1` actually divide `Θ₀`. I computed `Θ₀` from the Lean formulas (el-qfree's
`k0.py`) on 12 genuine test-site instances: `n ≤ 3`, `κ = 1`, four shift pairs. `num Θ₀` has
248-1315 digits; I trial-divided it up to 2·10⁶.
- `(R₀/p) = −1` at 32 of the 70 primes found, so there is no bias toward residues.
- Each instance has 1-5 obstruction primes among those found.
- Signed divisors `m` of 2730 that pass every obstruction found: 8, 4, 16, 8, 16, **0**, 8, 32, 32,
  16, 32, 2 of 64. These are upper bounds, because the factorization is partial.

So the obstruction is real even at `κ = 1`, and X3b's independence model fits the data.

### 1.3 Other claims

- **θ = 1 locus has genus 1 under M1** (VERIFIED). The curve is a quartic in `q` with 4 distinct
  roots `a = ±Θ₀√(m/R₀)`.
- **L-A** (VERIFIED, elementary).
- **L-B** (VERIFIED, with a repair of scope).
  - The honest locus `{(n, [κ]P₀, [κn]P₀)}` is Zariski dense in `𝔸¹ × E × E`: the curves
    `Γ_[n]` have unbounded degree.
  - The bad locus is also dense: the closure of `ℤP₀ × ℤP₀` is `E × E`, since `P₀` has infinite
    order. A dense set meets the domain of definition of any rational map.
  - Repair: the lemma covers witnesses that are rational functions of `(t, V₀, V₁)` and of the
    free witnesses. It does not cover witnesses that use `n` or `κ` as integers, for example
    through `[n]`. That is the "arithmetic, non-uniform" case the note already concedes.
- **L-C, the Kodaira-dimension consequence, and "Conic Φ′ cannot replace Φ"** are marked
  SPECULATIVE in the note. I agree with those marks and did not check them further.

**Verdict.** The main claims are verified after the repairs. "Very low" **stands**. M1 is a sound,
budget-neutral cleanup. The θ = 1 route it opens is locally blocked on genuine data with the present
multipliers. Beyond that block it is a rank/Ш question for one 2-covering per instance.

## 2. el-k3

### 2.1 Néron–Severi computation: VERIFIED

**Reruns.** `k1_rerun.sh` makes copies of el-k3's `ns_lattice.py`, `ns_invariants.py` and
`ns_h1.py` with β substituted. I ran it for β ∈ {7, 15, 23, −7, 39}. In all 5 runs:
- the Gram matrix of the 40 curves has rank 20, the lattice has discriminant −16, and Galois acts
  isometrically;
- `NS(X̄)^G` for generic θ has rank 8, discriminant −1024, `D² ≡ 0 (mod 4)` and `D·D′` even;
- θ = ±1 gives rank 9, discriminant 1024, with odd pairings;
- θ = β gives rank 8 and an even lattice;
- `H¹` is 0 for generic θ, and `ℤ/2` for θ = 1, −1 and β.

**Independent recomputation** (`k2_invariants.py`). I recomputed the invariants with PARI
(`matkerint` on the stacked `g − 1`, then `qfsign`) for the same 5 values of β. The results agree,
with signature (1, 7). I also covered **θ = −β, which el-k3 omits**: it also gives rank 8,
discriminant −1024 and an even lattice with `D² ≡ 0 (mod 4)`.

**Checked by hand.**
- `σ_β` and `σ_i` act on the roots as the script says.
- For the family-1 graphs, `f(λ/(βs)) = −f(s)/(βs²)²`, so `w = ±i√θ f(s)/(βs²)`. Hence `σ_i` and
  `σ_θ` both flip ε, as coded.
- Each graph curve `G^±` has self-intersection −2: `π*Γ = G⁺ + G⁻` with `Γ² = 2 − 4`.
- `H¹(Gal(K/ℚ), NS) = H¹(ℚ, NS)` by inflation-restriction, because `NS` is torsion-free with
  trivial `G_K`-action.
- Disc −16 equals `−disc T(Km(E × E))` for CM by `ℤ[i]` (STANDARD). With rank 20, this is strong
  evidence that the numerically computed intersection numbers are right.

### 2.2 Consequences

- **No `(−2)`-class over ℚ, so no smooth rational curve and no section over ℚ.** VERIFIED from
  `Pic X ⊆ NS(X̄)^G`.
- **The generic fibre of every genus-one fibration over ℚ has even index.** VERIFIED: the closure
  of a degree-`d` divisor on the generic fibre has `D·F = d`.
  - Repair (wording): this makes every fibre a torsor of even index. It need not have period 2:
    `D·F = 2` is not shown to occur, and fibres over special `t` may still have points. "Is a
    2-covering, exactly CR₃" should read "is a torsor of even index, a Hasse-principle question
    of CR₃'s kind".
- **Br₁ = Br₀** (VERIFIED). Only a transcendental obstruction could remain, and points exist
  anyway by CR₃.
- **Case B never occurs over ℚ.** VERIFIED (`caseB_parity.py` rerun gives `[]`).
  - The node orbits are correct.
  - The parity of `Γ·L_c` equals the parity of the number of odd branches on `L_c`.
  - Two odd branches cannot lie on the same line: `σ_β` would move a Galois-stable pair on `L₁`
    to `L₂`.
  - No ℚ-point lies on the branch locus `B`.
- **"The lattice does not depend on θ, so no construction read off it can select θ."** This is a
  heuristic, and should be marked SPECULATIVE.
- **The height estimate (§4)** is marked SPECULATIVE in the note. I did not rerun it.

**Verdict.** The main claims are verified after the three repairs. "Very low" **stands**. Note
also that all the computed obstructions hold for every admissible θ ≠ 1, **including those
where CR₃ supplies points**. So they rule out *uniform geometric* constructions only, which is
exactly the scope of the note's claim.

## 3. el-qfree

### 3.1 Multiplier window: VERIFIED, and strengthened

**Sufficiency.** This is L7 generalized. The pole system (`Hypotheses/Pole.lean:39`) has no
`ℚ_p`-solution whenever `a = v_p(mB)` is odd and `a − 2v_p(B) > 0`.
- The proof never uses `v_p(B) < 0`.
- So the same argument proves el-qfree's **completeness constraint** directly: if `v_p(B) = b ≥ 1`
  is odd and `v_p(m) > b` is even, then Φ fails at `p`.
- Hence `v_p(m) = 0` wherever `v_p(B) = 1`. This derivation does not need Loc or β.

**Necessity, which el-qfree and L7 claimed only "for this proof"** (`q1_window.py`). Take
`B = m(1 − c²)`. Then `m(m − B) = (mc)²`, and the trivial witness (`e = A`, `r₁ = r₂ = 0`,
`z = √H`) solves the system exactly. I checked:
- `p` ∈ {331, 337, 1009};
- `v_p(m)` ∈ {1, −2, 3}, giving `v_p(B) = −1`.

All 9 cases are solved. So **any** multiplier with `v_p(m)` odd or negative at some `p > 324`
breaks SC1 globally. The window "`v_p(m)` even and ≥ 0" is necessary and sufficient.

### 3.2 Finiteness of M: repaired to SPECULATIVE (open)

The note says "`M` is finite". The argument shows something weaker:
- bit-encoded `k` gives a finite `M`;
- an infinite sound `M` would give an infinite diophantine subset of `{k² : k ∈ ℤ[1/S]}·m₀`.

Whether such a subset exists is open: it is not known to be impossible, and it would follow from
the target theorem itself. The comparison "`ℤ[1/S]` is as hard as the target" covers only the
full `ℤ[1/S]`. Repair: "`M` is finite for every construction available today; an infinite `M`
needs an infinite diophantine set of `S`-integers, which is open". This does not affect the
verdict, because el-qfree §3 (finitely many `q` per bounded `k`; E2 has 0 hits) already handles
bounded `M`.

### 3.3 θ = ±1 criterion: VERIFIED

`m(m − B) = m₀k²(m₀k²D − N)/D`, so `θ ≡ ε` iff `εm₀D(m₀k²D − N) ∈ ℚ*²` (algebra). I did not rerun
E2: it takes 50 min, and Step 4 covers the same real data from a different side.

### 3.4 Hom(Jac Y_θ, C₁): VERIFIED for constant N; repaired in general

**The test is valid.** Suppose `Jac Y_θ` has a `ℚ̄`-factor isogenous to `C₁`. At a prime `p ≡ 3
(mod 4)` where the Jacobian has good reduction, that factor has CM by `ℤ[i]` with `p` inert, so it
is supersingular over `𝔽_{p^f}`. Then `(α²/p)^f` is a root of unity, and so is `α²/p`.

**Rerun** (`q2_e3.py`).
- Positive controls: `y² = x³ − x` (p = 19) and `y² = x⁴ − 1` (p = 23) both give the cyclotomic
  factor `y + 1`.
- Genus-33 instances: the outcomes are in §3.5.

**Repair (scope).**
- The reduction to `Hom(Jac Y_θ, C₁)` holds for a constant twist `N`; el-qfree §0 and §4 state it
  that way.
- For a `q`-dependent `N(q)`, one needs `Hom(Jac Y_N, C₁) ⊕ Hom(Jac Y_{Nθ}, C₁) ≠ 0`. This does not
  reduce to `Y_θ`, and E3 does not test it. Rational base changes `q = φ(x)` are not covered either.
- Both cases fall under the dimension count of §4, which is SPECULATIVE.
- So "every `q`-uniform witness needs `Hom(Jac Y_θ, C₁) ≠ 0`" is VERIFIED only for witnesses
  rational in `q` with constant `N`.

### 3.5 E3 sample outcome (VERIFIED, `q2_e3.py`, log Step 10)

All four instances have genus 33, and every good prime tested gives `[]`.

| instance `(n,h,s₀,η,m)` | primes with `[]` | singular primes | new here |
| --- | --- | --- | --- |
| (1,2,2,1,1) | 19, 43 | none | prime 43 |
| (1,2,2,1,−1) | 19 | 47 | none |
| (1,2,2,−1,3) | 67, 71 | none | prime 71 |
| (1,2,2,1,2) | 19, 43 | 23, 47 | the whole instance (new multiplier) |

So there is no supersingular factor at any good prime `p ≡ 3 (mod 4)`, and
`Hom(Jac Y_θ, C₁) = 0` on all four instances. el-qfree's E3 is reproduced and extended.

**Verdict.** The main claims are verified after the repairs. "Very low" **stands**. The strongest
point, that a per-instance choice of `q` leaves a rank statement for `C_{Nθ(q)}`, is untouched by
the repairs.

## 4. Scripts (`scratch/rv-elim3/`)

| script | checks | inputs |
| --- | --- | --- |
| `q1_window.py` | necessity of the multiplier window | 9 (p, m) pairs |
| `c1_local.py` | el-cert local lemma (reuses el-cert's `locsol`) | 26 random cases |
| `c2_theta0_primes.py` | obstruction primes of real `Θ₀` | 12 Lean-formula instances |
| `k1_rerun.sh` | el-k3 `ns_*` with β substituted | β ∈ {7, 15, 23, −7, 39} |
| `k2_invariants.py` | independent `NS^G`, plus θ = −β | the same 5 β |
| `q2_e3.py` | el-qfree E3 with controls | 4 controls, 4 instances |
