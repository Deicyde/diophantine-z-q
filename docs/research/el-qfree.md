# el-qfree: using the freedom in the witness `q` and in the multipliers to remove CR₃

Branch `wip/el-qfree` (from `wip/cr3-maps`). This note builds on cr3-map-needs (L1-L9, W0-W3) and
cr3-map-literature (R1-R7), and does not repeat them.

Claims are marked:
- **VERIFIED**: checked against the Lean sources or by exact computation. Scripts are in
  `scratch/el-qfree/`; inputs and outcomes are in `scratch/el-qfree/log.md` (S1-S4, E2, E3).
- **STANDARD**: a published theorem, with reference.
- **SPECULATIVE**: an idea or estimate, not proved.

No Lean was run. No file under `ZInQKernel/`, `blueprint/` or other notes was edited.

## 0. Verdict

- **The angle does not eliminate CR₃. Chance: very low.**
- **New fact: the freedom is larger than the maps assumed** (§1, VERIFIED). The consumers of PC
  need, per instance, one witness tuple in which:
  - `q ∈ ℚ` is arbitrary;
  - `η = ±1` is free;
  - the test shifts `(h, s₀)` (test site) or `(h_g, z_g)` (slope site) are arbitrary integers.

  The open sets `U_test` and `U_slope` exist only to meet PC's hypotheses.
- **But it is the wrong kind of freedom.** All of it reaches `θ` through the single number
  `σ = a₀/Θ` (or `ℓ₀a/Θ`), which is a value of a rational function of degree 25 in
  `R = R₀a₀²`. `β` is fixed by the instance and `m₀`.
- **Multipliers are pinned** (§2, VERIFIED derivation).
  - Soundness forces `v_p(m) ∈ 2ℕ` at every `p > 324`.
  - Completeness at slope-site primes with `v_p(B) = 1` forces `v_p(m) = 0` there.
  - Input-dependent multipliers are excluded. For example, `m = μR₀B` makes `θ` independent of
    `q`, but then `Φ` fails at every genuine instance.
  - Unbounded `k` needs an existential definition of `ℤ[1/S]` in `ℚ`, which is the target problem.
  - So `M` is finite.
- **(1) `θ = 1`.**
  - The exact criterion is in §3. With S-integral `k` it reduces to Legendre conditions modulo
    the prime-to-S denominator, but only with `k` doubly exponential in the size of `B`.
  - With encodable `k` (bounded bits) it is a union of hyperelliptic curves of genus 33-49 in `q`:
    finitely many `q` (Faltings), and none expected.
  - E2: 0 hits on 30 real test-site inputs, over all `m₀ | ±Π_{p≤324}p` allowed by the data, all
    `k ≤ 256` and both signs.
- **(2), (3) Other `θ` classes, rational curves of `q`** (§4).
  - A witness uniform in `q` with a constant twist needs `Hom(Jac Y_θ, C₁) ≠ 0`. E3 shows it is
    `0` on three real instances: no supersingular Frobenius at `p ≡ 3 (mod 4)`.
  - General rational curves of `q`-values are rational curves on a Kodaira-dimension-1 variety
    fibred over the `q`-line. The expected dimension is `−48e − 1 < 0`.
- **Strongest obstruction.** The only remaining freedom is to choose one `q` per instance. For a
  single `q`, `Φ(B(q))` is a positive-rank or Sha statement for `C_{N}` and `C_{Nθ(q)}`, which is
  CR₃'s shape, now with `θ(q)` uncontrolled. Picking `q` cannot replace a Hasse principle for
  2-coverings. At best it trades one instance for another.

## 1. What the consumers actually quantify (VERIFIED, log S1)

| Predicate | File | Witnesses | Constraints on the witnesses |
| --- | --- | --- | --- |
| `Test n κ t` | `Assembly/Local/SixLocalTests.lean:66` | `h s₀ : ℤ`, `η q : ℚ` | `h ≠ 0, κ`; `η² = 1`; `a₀, W, Θ ≠ 0`; `Φ(R/Θ²)` |
| `SlopePred t ℓ c` | `Multiplication/Certificate/SlopePredicate.lean:52` | `η q : ℚ`, `h : Fin 6 → ℤ`, `z : Fin 6 → Fin 3 → ℤ` | `h g ≠ 0, c 0`; nonvanishing; `Φ(R/Θ²)` |

- `test_complete` picks `q` from `poleInput_real` only to verify PC's hypotheses. These are
  `IsSquare B.den`, `0 < B < 1/2` and `v_p(B) ≥ 4` on `S₀`.
- `Test(n, κ, n)` accepts any `κ ≠ 0`. A deep `κ` is used only for those `S₀`-valuations.

So the weakest completeness input is W0/W1 of cr3-map-needs with `U` replaced by all of `ℚ`, and
with `η`, the shifts and `κ` existential:

```
CR3Free : ∀ inst, ∃ η q shifts, ∃ m ∈ M, ∃ N ≠ 0,
  LocQ N (sqf (m R₀)) ∧ LocQ (N · m(m − R₀ σ(η, q, shifts)²)) (sqf (m R₀))
```

**Soundness** is untouched. Lemma 5.1 holds for every witness tuple. `η = −sign F` gives `B < 0`,
which is allowed: the pole system needs only `B ≠ 0` and `m ≠ B`.

**Consequence.** For free `q`, `B.den` is generally not a square (E2: 30 of 30 non-square). PC's
admissibility is a design artefact of routing completeness through DL, not a need of the
consumers.

## 2. Route M: enlarged multipliers (statement, soundness, completeness)

**Replacement statement.** Use `Φ_M(B) :⇔ ∃ m ∈ M, (pole system with multiplier m)`, with
`M = {m₀k² : m₀ | ±Π_{p≤324} p, 0 ≤ k < 2^K}`, `k` bit-encoded.

**Soundness** (VERIFIED, log S2). L7's proof needs only that `a = b + v_p(m)` is odd and that
`v_p(m) − b > 0`, where `b = v_p(B) < 0` is odd. So the exact window is: `v_p(m)` even and
`v_p(m) > v_p(B)`. To be sound against `b = −1`, every element of `M` needs `v_p(m) ≥ 0` even at
all `p > 324`.

**Completeness constraint** (VERIFIED, log S2). Let `p` be a consumed prime of a genuine instance,
so `b ≥ 1` is odd (`b = 1` on `P(t)`). If `v_p(m) > b`, then `v_p(θ)` is odd and `p | β`, and
`Loc N β ∧ Loc Nθ β` fails locally at `p`: a point at good reduction has abscissa of even
valuation. Hence:
- the prover must use `v_p(m) < b`;
- every multiplier tied to the input fails.

  Example: `m = μR₀B` has `v_p(m) > v_p(B)` at every consumed prime, and gives the attractive
  `θ = sqf(μR₀(μR₀ − 1))`, independent of `q`. It kills completeness at every instance.

**Unbounded `k`** (STANDARD + derivation).
- Certifying `k ∈ ℤ[1/S]` with boundedly many variables would give `ℤ` in `ℚ` existentially,
  because each `ℤ_(p)` with `p ∈ S` is diophantine.
- Poonen's quaternion sets (Poonen, *Characterizing integers among rational numbers with a
  universal-existential formula*, Amer. J. Math. 131 (2009), Lemma 2.5) give integrality only at
  the primes `Δ_{a,b}` where `H_{a,b}` ramifies.
- Soundness would need `Δ_{a,b}` to contain the consumed primes for every witness `(a, b)`. No
  fixed `b` forces this: by Chebotarev, primes split in `ℚ(√b)` escape.

**Cost.** `K` bits cost `K` witnesses per pole call, about `8.3·10⁶·K` variables against a
budget with no slack (cr3-map-needs finding 7).

**Verdict.** `M` is finite. It enlarges DL's existing choice of `m`; it is not a new mechanism.

## 3. Route T1: the trivial torsion witness `θ = ±1`

**Replacement statement.** `∀ inst, ∃ η q shifts, ∃ m ∈ M, ∃ c ≠ 0, m(m − B) = ±c²`. Then `N = β`
and two 2-torsion points give `Φ` (rs-pole §2.2(2); `Loc` depends only on `d²`).

**Soundness.** Unchanged (Lemma 5.1).

**Exact criterion** (VERIFIED derivation, log S3). Let `B = N/D` be reduced. Then
`θ ≡ ±1 ⇔ ε m₀ D (m₀k²D − N) ∈ ℚ*²`.
- **Bounded `k`.** `m₀` must lie in `S ∩ (supp N ∪ odd-supp D)`, so the check is finite.
- **`k ∈ ℤ[1/S]`.** The prime-to-S part `D'` of `D` must be a square, `D' = E²`. With `k`
  integral at `ℓ | D'`, `v_ℓ(X) = v_ℓ(D)`. Then
  `k = (g + m₀N/g)/(2m₀E)` with `g ∈ (divisors of N)·(S-units)`, so `θ = 1` holds iff some such
  `g` satisfies `g² ≡ −m₀N (mod 2m₀E)`. The S-unit part makes this a Legendre condition when
  `⟨S⟩ mod E` is large, but `g`, and hence `k`, then has exponents of size about `ord(⟨S⟩ mod E)`.
- **Fixed `k`.** The condition is the curve `w² = ε m₀(m₀k²T(R)² − R N_W(R)²)` with
  `R = R₀(1 − R₀q²)²`, of degree 100 in `q` (genus 49). When tests vanish (`n = 1`,
  `h = 2κ`, `s₀ = 2κn`: `D₄ = D₅ = 0`) the degree is 68 (genus 33). By Faltings (STANDARD) there
  are finitely many `q`.

**Heuristic** (SPECULATIVE).
- Σ_good = {σ : `m₀(m₀k² − R₀σ²)` is ± a square for some `k ≤ K`} has density about
  `K/ht` among rationals of height `ht`.
- `σ(q)` has height about `ht(q)^{25}` or more.
- So the expected number of `q` is `≪ Σ_q ht(q)^{−23}`, which is finite and tiny. Shifts and `η`
  give countably many such curves and do not change this.

**Experiment E2** (VERIFIED, `e2_theta1.py`, `e2_out.txt`).
- Inputs: 30 real test-site inputs from the Lean formulas (`k0.py`, exact arithmetic in `ℚ(√2)`,
  `P₀`, `genD`), with `n ≤ 3`, `κ = 1`, three shift pairs, `η = ±1`, `q ∈ {0, 1/2}`.
- Sizes: `N` has 356 to more than 4000 digits; `D` has 210 to more than 2000.
- Search: all admissible `m₀`, `k ≤ 256`, `ε = ±1`.
- Outcome: **0 hits.** `D` is never a square, and has prime factors above 324 (found: 491, 577,
  593, 8273, 81611).

**Verdict.** Fails. Obstruction: the denominator of `B(q)` must cancel against an S-integral
`k`, which forces either astronomically large `k` (not encodable) or rational points on
genus-33/49 curves.

## 4. Routes C and R: other `θ` classes, and rational curves of `q`-values

**Replacement statement.** `∀ inst, ∃ η q shifts m, θ(q) ∈ ±G_β`, where `G_β` is the group of
classes `(β² − τ₁⁴)(β² − τ₂⁴)` (rs-pole Prop. 1 in congruent form; cr3-map-needs L5).

**Explicit points for a given `q`.**
- Every prime of `θ(q)` must divide `g(τ₁)g(τ₂)`.
- `θ(q)` has prime factors of hundreds of digits (E2 sizes), so small-height `τ` cannot work.
- rs-pole §2.2 found none at height ≤ 12 even for admissible `B`. This is not repeated.

**`q`-uniform witnesses** (VERIFIED structure, log S4; E3).
- Over `ℚ̄(q)`, `C_N(ℚ̄(q)) ⊗ ℚ ≅ Hom(Jac Y_N, C₁) ⊗ ℚ` with `Y_N : y² = N(q)` (STANDARD).
- Both points torsion would need `θ(q) ∈ ±ℚ(q)*²`, which is false.
- With a constant twist `N` (for example `N = β`, where the first point is torsion), one needs
  `Hom(Jac Y_θ, C₁) ≠ 0`.

**E3** (VERIFIED, `e3_cmfactor.py`, `e3b.py`).
- Instances: `(n, h, s₀, η, m) = (1,2,2,1,1)`, `(1,2,2,1,−1)`, `(1,2,2,−1,3)`, all genus 33.
- Test: the characteristic polynomial of Frobenius at `p = 19, 19, 67` (each `≡ 3 mod 4`, inert
  in `ℚ(i)`).
- Outcome: no Frobenius root has `α²/p` a root of unity. A factor ℚ̄-isogenous to `C₁` would be
  supersingular there, so `Hom = 0`.
- The `n = 2` curve (`f` not squarefree, `deg gcd(f, f′) = 8`) was not tested.

**General rational curves** `q = φ(x)`, `N = G(ψ(x))`.
- These are rational curves on `V' : w² = m(m − R₀σ(q)²)(β² − τ₁⁴)(β² − τ₂⁴)`.
- `K_{V'} = π*O(48, 0, 0)`: Kodaira dimension 1, and the canonical fibration is the `q`-line.
- On the surfaces `w² = θ(q)Q(ρ)`, a rational curve of `q`-degree `e` has expected dimension
  `−K·Z − 1 = −48e − 1`.
- Parameter count: `50e + 2d` conditions against `2e + 2d − 1` parameters.
- (Derivation; the conclusion that none exist is SPECULATIVE. cr3-map-literature R6 gives the same
  picture qualitatively.)

**Anisotropic denominators.**
- rs-pole §4.3 forbids only `q` that are `p`-adically large at `P(t)`.
- A curve `q = φ(x)` with `φ` bounded on `ℚ_p` passes that test, but it still has to be a curve
  as above. The `p`-adic freedom (and, by §1, the real freedom) is irrelevant to the genus
  obstruction.

**Verdict.** Fails as an elimination. Obstruction: no rational curve of `q`-values; for a single
`q`, the problem is the rank of `C_{Nθ(q)}`.

## 5. What survives, and the single next step

- **Usable narrowing (VERIFIED).** By §1, the completeness proofs need W1 with `U = ℚ` and free
  `η`, shifts and `κ`. A hypothesis "for each instance, some `(η, q, shifts, m)` gives
  `Loc N β ∧ Loc Nθ β`" is strictly weaker than PC. Admissibility (`IsSquare B.den`,
  `0 < B < 1/2`, `S₀`-valuations) is needed only by the DL route.
- **The freedom cannot remove the rank input.** For every `q`, the needed statement is a Hasse
  principle for two 2-coverings with `θ(q)` uncontrolled. A proof that some `q` works would need
  a "rank goes up in a family of twists `C_{Nθ(q)}` over `ℚ(q)`" theorem whose generic rank is 0
  (E3). Results of that kind (root-number variation, Rohrlich, Helfgott; Desjardins on density of
  points on elliptic surfaces) are conditional on squarefree-value or parity conjectures
  (STANDARD that they are conditional; SPECULATIVE that this is the relevant obstruction).
- **Next step.** Drop this angle. If anything is pursued here, formalize the §1 narrowing: state
  `CR3Free` as a Lean `Prop` and re-route `test_complete` and `slope_complete_AP` through it. That
  makes visible that no admissibility is needed. It is a cosmetic weakening, not an elimination.

## Scripts (`scratch/el-qfree/`)

| Script | Role | Runtime |
| --- | --- | --- |
| `k0.py` | `ℚ(√2)` arithmetic; `P₀`, `genD`, `testD`, `testC`, `testR₀`, `poleTheta`, `testB` exactly as in Lean | — |
| `e2_theta1.py` | E2, output `e2_out.txt` | about 50 min |
| `e3_cmfactor.py`, `e3b.py` | E3, outputs `e3_out.txt`, `e3b_out.txt` | minutes |
