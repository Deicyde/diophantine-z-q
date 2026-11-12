# pn-design: the Lean formalization of Proposition N

Task: replace the hypothesis `ZInQ.Literature.TYZRow5b` (`ZInQKernel/Hypotheses/CR3Literature.lean`)
with faithful statements of the Tian–Yuan–Zhang (TYZ) results that Proposition N
(`docs/research/nt-tyz.md` §4) uses, and prove Lemma N1, Lemma N2 and the final argument in Lean.
Draft: `scratch/pn-design/PropN.lean`; log: `scratch/pn-design/log.md`; scripts
`scratch/pn-design/n2_check.py`, `enc_check.py`.

Line numbers `Lnnnn` refer to the TYZ arXiv source `Period7.tex` (arXiv:1411.4728v1). Marks:
**VERIFIED** (checked against the source, proved here or in Lean, or exact computation with a
script), **STANDARD** (published theorem, with reference), **SPECULATIVE** (not proved).

> **Locator correction (2026-11-12, loc-adopt).** The convolution lemma (L1062–1066) that
> `LemmaTwoEight` encodes was called "Lemma 2.8" here; it is printed as **Lemma 2.9**, and Lemma
> 2.8 is the symmetry lemma (`lem2.6`, L1009, formerly called "Lemma 2.7"). The earlier count of
> TYZ's shared §2 counter skipped Definition 2.7 (L842). VERIFIED for arXiv v1 by recounting
> `Period7.tex`; the journal has the same numbers per the locator audit `docs/research/locators.md`
> (AI agents, 2026-11-12). The Lean name `LemmaTwoEight` is kept (historical); its docstring now
> says that it encodes Lemma 2.9. The same audit reports that arXiv Theorem 1.2 is journal
> Theorem 1.4, with "all `d_i > 1`" kept. Line numbers and the encoding are unchanged.

## Summary

1. **Encoding** (§2). `TYZInputs` is one Prop: there is `L : ℕ → ℤ` (TYZ's `𝓛`) with `L 1 = 1`,
   Lemma 2.9 with Proposition 2.3 modulo 2 (`LemmaTwoEight L`), the link I7 to the L-series
   (`L n ≠ 0 → ∃ F, IsLContinuation (shortCurve (−n²)) F ∧ analyticOrderAt F 1 ≤ 1` for squarefree
   `n ≡ 5 (mod 8)`), and, for each such `n`, a structure `GenusData L n`. That structure holds an
   abstract `ℤ[i]`-module `M` (the role of `A(ℍ'_n)`), the points `Z, P`, the units `ε` with
   Theorem 3.3's classes, the recursion I1, the torsion statements I3 and I4 through
   `τ(y/2)`, an additive `β : M →+ M` fixing torsion, and I5. Each field is a consequence of a
   printed TYZ statement, except that `β` being an endomorphism of `M` uses F5 (`ℍ'_n/ℚ` Galois).
   F5 is derived from TYZ's Proposition 3.2(1) and a standard fact, and is not printed by TYZ
   (§2, §5).
2. **Lean** (§3). `PropN.lean` compiles with `lake env lean` after `lake build ZInQKernel`. It has
   exactly four `sorry`s: `lemmaN1_core`, `lemmaN2`, `finalStep` and `matching` (VERIFIED). The
   following are proved: `lemmaN1` (from its core), `genusSums_eq_zero`,
   `tyzRow5b_of_tyzInputs : TYZInputs → TYZRow5b`, and also
   `tyzThm35ReadingA_of_tyzInputs : TYZInputs → TYZThm35ReadingA` (reading A, both rows).
   `Witness.genusData_nonempty : L n ≠ 0 → Nonempty (GenusData L n)` is proved without `sorry`.
   It shows that the fields of `GenusData` are not jointly contradictory (VERIFIED).
3. **New observation** (§4). Lemma N2 in the form `c_n(e) ≡ 𝓛(n/e) (mod 2ℤ[i])` holds for an
   *arbitrary* integer function `𝓛`. Its proof is a pairing `q ↔ (d/e)/q` of divisors, with no
   use of Lemma 2.9 or N1 (VERIFIED by hand; `n2_check.py`: 190 trials, 0 mismatches). N1 is
   needed only to pass from `𝓛` to `Λ` at the matching step. The induction does need the
   `ε`-classes of Theorem 3.3 *including the uniformity at `(5, 3)`*. With mixed classes there,
   154 coefficients mismatch. rv-prop-n §4.3's "the value at `(5, 3)` is irrelevant" is
   therefore too strong: the class must be the same for all `(5, 3)` pairs (VERIFIED).
4. **Plan** (§6). Four proofs, against fixed statements. `finalStep` is about 150–250 lines;
   `lemmaN2` 300–450 (inductive identity, not the chain expansion); `matching` 350–600;
   `lemmaN1_core` 400–700. `matching` and `lemmaN1_core` share a small partition-sum
   infrastructure (transport of `Lam`, `T5aCl`, `T5bCl` to `Finpartition`s of
   `n.primeFactors : Finset ℕ`).
5. **Most serious risk to faithfulness** (§5): the field `β : M →+ M`. TYZ never state that
   `ℍ'_n/ℚ` is Galois (F5). They use it implicitly at L2593–2595. It follows from Proposition 3.2(1)
   and the generalized-dihedral structure of ring class fields (STANDARD; Cox, Lemma 9.3). A
   fallback that uses F4 instead of F5 is described in §5.

## 1. What Proposition N uses, input by input (VERIFIED against `Period7.tex`)

- **I1** (recursion, §3.1). The definition of `P(n)` (L1325–1330). The sum is over `n = d₀d₁` with
  `d₀ ≡ 5, 6, 7`, `d₁ ≡ 1, 2, 3 (mod 8)` and `d₁ > 1`. The coefficient is `ε(d₀, d₁)𝓛(d₁)`, with
  `ε ∈ μ₄` "as in Theorem 3.3" (L1329) and `𝓛(d₁) ∈ ℤ` by Theorem 1.1 (L1330). `P(n)` lies in the
  `ℤ[i]`-module `A(ℍ'_n)` (L1324), where `ℍ'_n = L_n(i)·Π_{d₀≡5,6} H'_{d₀}` (L1321). Theorem 3.3
  (L1309–1310) gives `ε(d₀, d₁) = ±i` for `(d₀, d₁) ≡ (5, 3)` and `±1` otherwise. *Used:* the
  recursion for every `d ∣ n` with `d ≡ 5, 7`, inside `A(ℍ'_n)`; `ε ≡ 1 (mod 2)` on the classes
  `(5,1)`, `(7,1)`, `(7,3)`; and one common class of `ε` modulo 2 on `(5,3)` (§4).
  `Z(d) ∈ A(ℍ'_n)` for `d ∣ n`: for `d ≡ 5` because `H'_d` is a factor of `ℍ'_n`, and for `d ≡ 7`
  because `Z(d)` is defined over `L_d` (L2558).
- **I2** (Lemma 2.9, L1062–1066; Proposition 2.3, L580–586; §2 assumes `n ≡ 1, 2, 3` positive and
  squarefree, L499; `𝓛(1) = 1`, L1082). The lemma reads `Σ ε(d₁, d₂)𝓛(d₁)𝓛(d₂) = Q(n)` over the
  non-ordered `n = d₁d₂` with `d₂ ≡ 1 (mod 8)`, `ε = ±1`. Proposition 2.3 gives
  `Q(n) ≡ g(n) (mod 2)`. *Used:* the identity modulo 2, for odd `m ≡ 1, 3`. For `m ≡ 1` the pairs
  are unordered: the proof halves the ordered sum by the symmetry `P(d₁, d₂) = P(d₂, d₁)`
  (L1068–1077).
- **I3** (Theorem 3.5, first assertion, L1353–1356; `𝒫(n) = 0` if `𝓛(n) = 0`, L1295). `P(n)` and
  `𝒫(n) = 2^{−1−ρ(n)}𝓛(n)α_n` are equal in `A(ℍ'_n) ⊗ ℚ`. *Used:* `𝓛(n) = 0 ⟹ P(n)` is torsion.
- **I4** (Lemma 3.16, L2182–2185: `A(ℚ(i)) = A[(1+i)³]`; Lemma 3.18, L2230–2232:
  `A(ℍ'_n)_tors = A[(1+i)³]` for odd `n`; the uniformization `τ : ℂ/(1+i)ℤ[i] → A(ℂ)`, L1385–1399,
  with `τ : ½ℤ[i]/(1+i)ℤ[i] → A[(1+i)³]` bijective). *Used:* every torsion point of `A(ℍ'_n)` is
  some `τ(y/2)`, and `τ(y/2) = 0` iff `y ∈ 2(1+i)ℤ[i]`.
- **I5** (Lemma 3.21(1), (4), L2504–2516; `β₁ = r_∞(−1)r₂(−2)` and its liftings
  `β'₁ ∈ Gal(ℚ̄/ℚ)`, "any liftings", L2496–2500). For `e ≡ 5`:
  `Z(e)^{β'+1} ∈ g(e)τ((1−i)/2) + ℤτ(1)`. For `e ≡ 7`: `Z(e)^{β'+1} = g(e)τ(1/2)`. The statement
  holds for any lifting, so one `β' ∈ Gal(ℚ̄/ℚ)` serves every `e ∣ n`. Also used: "β acts on ℚ(i)
  trivially" (L2581), so `β'` fixes `A(ℚ(i)) = A[(1+i)³]`.
- **I6** (Proposition 3.2(1), L1253–1260). Gives F5: `ℍ'_n/ℚ` is Galois. `H'_d` is the fixed field
  in the ring class field `H_{d,4}` of an order-2 element of `Gal(H_{d,4}/K_d)`. That group is
  generalized dihedral over `ℚ` (STANDARD; Cox, *Primes of the form x² + ny²*, Lemma 9.3), so
  `H'_d/ℚ` is Galois, and so is the compositum (VERIFIED in nt-tyz §2.2 and rv-prop-n §2). *Used:*
  `β'` maps `A(ℍ'_n)` into itself.
- **I7** (definition of `𝓛`, L337–345; root number, L318–327). `𝓛(n) = 0` if
  `ord_{s=1}L(E_n, s) > 1`, so `𝓛(n) ≠ 0 ⟹ ord ≤ 1`. `E_n : ny² = x³ − x` is `ℚ`-isomorphic to
  `C_n` by `(x, y) ↦ (nx, n²y)` (VERIFIED, rv-prop-n §1). *Used:* `𝓛(n) ≠ 0 ⟹` the continuation of
  `L(C_n, s)` has order `≤ 1` at `s = 1`. The root number is not used here: it is the separate
  hypothesis `FunctionalEquation5` of `CR3Literature`.
- **Not used:** Proposition 3.4, Theorem 1.2 (journal Theorem 1.4), the "i.e." of Theorem 3.5(2), `ρ(n)`, the action of
  `β` on `K_n`, and F4 (rv-prop-n §4.2).

## 2. The encoding, field by field

`TYZInputs := ∃ L : ℕ → ℤ, L 1 = 1 ∧ LemmaTwoEight L ∧ (I7) ∧ ∀ n ≡ 5 squarefree, Nonempty
(GenusData L n)`. Every field below is satisfied by TYZ's objects, read as indicated, and asks
for no more than the cited statement.

| Lean | TYZ | Why it is a consequence | Mark |
|---|---|---|---|
| `L : ℕ → ℤ` | `𝓛`, L337–345, L361; integral by Thm 1.1 (L371–380), Thm 3.5(1) (L1357) | `L(n)` is `𝓛(n)` with one choice of its sign (TYZ: "defined up to a sign", L361) for squarefree `n`, and `0` otherwise. Each field is invariant under changing the sign of any `L(m)`: `LemmaTwoEight` is mod 2; in the recursion the sign is absorbed into `ε` (`±1 ↦ ∓1`, `±i ↦ ∓i`), and each pair `(d₀, d₁)` occurs in one recursion only; I3 and I7 see only `L n = 0`. | VERIFIED |
| `L 1 = 1` | L1082 | stated ("Since 𝓛(1) = 1"); sign chosen `+` | VERIFIED |
| `LemmaTwoEight L`, `m ≡ 1` | Lemma 2.9 + Prop 2.3, §2 (L499) | for squarefree `1 < m ≡ 1`: `Σ_{d∣m, d≡1, d²<m} L(d)L(m/d) ≡ gNat m`. The non-ordered pairs `{d, m/d}` (`d ≠ m/d`) are each counted once, through the member with `d² < m`. `d ≡ 1` is TYZ's `d₂ ≡ 1`, and then `m/d ≡ 1`. Signs vanish mod 2. Restricted to `m > 1`. | VERIFIED |
| `LemmaTwoEight L`, `m ≡ 3` | same | `Σ_{d∣m, d≡1} L(m/d)L(d) ≡ gNat m`: `d₂ = d ≡ 1` and `d₁ = m/d ≡ 3` are told apart by their classes | VERIFIED |
| I7: `L n ≠ 0 → ∃ F, IsLContinuation (shortCurve (−n²)) F ∧ analyticOrderAt F 1 ≤ 1` | L337–345 | contrapositive of "`𝓛(n) = 0` if `ord > 1`", with `L(E_n,s) = L(C_n,s)` and the existence of the entire continuation (Hecke/Deuring: CM; STANDARD; TYZ presuppose it when writing `ord_{s=1}`). Mathlib's `LSeries` is taken as `L(C_n, s)`, the convention of `CR3Literature`. | VERIFIED (reading) + STANDARD (continuation) |
| `GenusData.M : Type`, `[AddCommGroup M] [Module ℤ[i] M]` | L1324 | `A(ℍ'_n)` with `[i]` | VERIFIED |
| `Z P : ℕ → M` | L1318, L1325 | `Z(e)`, `P(e)` for `e ∣ n`, `e ≡ 5, 7`, in `A(ℍ'_e) ⊂ A(ℍ'_n)` (L1321, L2558); other values arbitrary | VERIFIED |
| `ε`, `eps_53`, `eps_pm1` | Thm 3.3, L1309–1310; L1329 | `ε(d₀,d₁) = ±i` on `(5,3)`, `±1` on `(5,1)`, `(7,1)`, `(7,3)`, for `d₀d₁ ∣ n`. A per-`n` `ε` is weaker than TYZ's single function. | VERIFIED |
| `recursion` | L1325–1330 | for `d ∣ n`, `d ≡ 5, 7`: `P d = Z d − Σ_{d₁ ∣ d, 1 < d₁, d₁ ≡ 1,3} (ε(d/d₁, d₁) L(d₁)) • P(d/d₁)`. For odd `d ≡ 5, 7`, TYZ's conditions `d₀ ≡ 5,6,7`, `d₁ ≡ 1,2,3` are exactly `d₁ ≡ 1, 3` (`d₀` is then `≡ 5, 7`). The identity holds in `A(ℍ'_d)`, hence in `A(ℍ'_n)`. | VERIFIED |
| `torsion_of_zero : L n = 0 → IsOfFinAddOrder (P n)` | Thm 3.5 L1356, L1295 | `P(n) ⊗ 1 = 𝒫(n) = 0` in `A(ℍ'_n) ⊗ ℚ` | VERIFIED |
| `τ : ℤ[i] →+ M` | L1385–1399 | `y ↦ τ(y/2)`. Additive, since `τ` is a group isomorphism. It lands in `A[(1+i)³] = A(ℚ(i)) ⊂ A(ℍ'_n)`, as `i ∈ L_n(i) ⊂ ℍ'_n`. | VERIFIED |
| `τ_eq_zero : τ y = 0 ↔ (2+2i) ∣ y` | L1386 | `τ(y/2) = 0 ⟺ y/2 ∈ (1+i)ℤ[i] ⟺ y ∈ 2(1+i)ℤ[i] = (2+2i)ℤ[i]` | VERIFIED |
| `tors_mem_range` | Lemma 3.18, L2230–2232; L1399 | `A(ℍ'_n)_tors = A[(1+i)³] = τ(½ℤ[i])` | VERIFIED |
| `β : M →+ M` | L2500; F5 from Prop 3.2(1) | the action of one lifting `β'` of `β₁` on `A(ℚ̄)` is additive and preserves `A(ℍ'_n)` because `ℍ'_n/ℚ` is Galois (I6/F5) | VERIFIED given STANDARD (Cox 9.3); **not printed** |
| `β_τ : β (τ y) = τ y` | Lemma 3.16 (L2183), L2581 | `τ(y/2) ∈ A(ℚ(i))`, and `β'` fixes `ℚ(i)` | VERIFIED |
| `beta_five` | Lemma 3.21(1), L2506–2508 | for `e ∣ n`, `e ≡ 5`: `∃ k, β(Z e) + Z e = g(e)•τ(1−i) + k•τ(2)`, with `τ(1−i) = τ((1−i)/2)` and `τ(2) = τ(1)`. `g(e) = gNat e = #2Cl(ℚ(√−e))` (fork's `gCl`). | VERIFIED |
| `beta_seven` | Lemma 3.21(4), L2514–2516 | for `e ∣ n`, `e ≡ 7`: `β(Z e) + Z e = g(e)•τ(1)`, where `τ(1) = τ(1/2)` | VERIFIED |

Notes.

- **Elementary.** `GenusData` mentions no elliptic curve, field or Galois group. `M` is an abstract
  `ℤ[i]`-module, and torsion is Mathlib's `IsOfFinAddOrder`. The only non-elementary objects in
  `TYZInputs` are `gCl` (class groups, already used by `T5bCl`) and the L-series in I7, which is
  the same object `TYZRow5b` already uses.
- **What was dropped as unneeded** (making the Prop weaker, hence safer): the `ℤ[i]`-linearity of
  `τ` and `β` (F4), the action of `β` on `K_n`, `Q(m)` itself, the exact signs in Lemma 2.9, the
  value `ε ∈ μ₄` beyond its class, `𝓛(n) ∈ ℤ` for `n ≢ 1, 3, 5`, and everything about `n ≡ 6, 7`.
- **Universe.** `M : Type`, and `GenusData L n : Type 1`. `Nonempty (GenusData L n)` is a `Prop`.

## 3. Checks on the encoding

1. **TYZ's objects satisfy it** (VERIFIED by reading, table above). The one field whose
   justification is not a printed TYZ sentence is the typing of `β` (F5).
2. **No field is contradictory** (VERIFIED, Lean). `Witness.genusData_nonempty` builds, for *any*
   `L` with `L n ≠ 0` and any values of `g`, the model `M = ℤ[i]/(2+2i) × (ℕ →₀ ℤ[i])`: `τ` is the
   first factor, `Z e` the basis vectors, `β(t, v) = (t + Σ_e v_e c_e, −v)` with `c_e` the values
   prescribed by I5, and `P` defined by the recursion. So `τ_eq_zero`, `tors_mem_range`, `β_τ`,
   `beta_five`, `beta_seven`, the `ε`-fields and the recursion are jointly consistent. When
   `L n = 0`, `GenusData` has real content: it yields `T5a ≡ T5b ≡ 0` (that is Proposition N).
   This is consistent exactly when TYZ's Theorem 3.5 is.
3. **Not trivially true.** `TYZInputs → TYZRow5b`, and `TYZRow5b` is a deep statement. `L` cannot
   be chosen cheaply. `LemmaTwoEight` and `L 1 = 1` fix `L mod 2` on classes 1 and 3 as `Λ`
   (Lemma N1). I7 forces `L n = 0` whenever the analytic rank is `≥ 2` (e.g. `n = 26565`, rank 3;
   nt-tyz §1.4). Then `GenusData L n` must hold with a torsion `P(n)`.
4. **Sensitivity** (VERIFIED, scripts). The `ε`-uniformity at `(5,3)` is needed (`n2_check.py`,
   second line). The unordered reading for `m ≡ 1` in `LemmaTwoEight` is needed: an ordered
   reading counts `𝓛(m)𝓛(1)` twice and gives no information on `𝓛(m)` (rv-prop-n §2). The
   encodings of `LemmaTwoEight` and `matching` were tested on abstract data (`enc_check.py`: 180
   trials, 0 mismatches for N1-core; 40 trials with `n ≡ 5`, 0 mismatches for matching).

## 4. Lemma N2 without Lemma N1 (VERIFIED)

For `d ∣ n` with `d ≡ 5, 7`, write `P(d) = Σ_e c_d(e) Z(e)` over `e ∣ d`, `e ≡ 5, 7`. Set
`φ(d, e) = i` if `(d, e) ≡ (7, 5)` and `φ = 1` otherwise, and use `𝓛(1) = 1`.

**Claim.** `c_d(e) ≡ φ(d, e) 𝓛(d/e) (mod 2ℤ[i])`, for any integers `𝓛(q)`.

*Proof.* By the recursion, `c_d(e) = [e = d] − Σ ε(d/q, q)𝓛(q) c_{d/q}(e)`, summed over
`q ∣ m := d/e` with `q > 1` and `q ≡ 1, 3`. For `e = d` the sum is empty and `c = 1`. Let
`e ≠ d`. Then `m ≡ d·e ≡ 1` or `3`, and every divisor `q ≡ 1, 3` of `m` has `m/q ≡ 1, 3`. By
induction `c_d(e) ≡ Σ_q κ(q) 𝓛(q)𝓛(m/q)`, where `κ(q) = ε(d/q, q) φ(d/q, e)` modulo 2. Modulo 2,
`κ(q)` depends only on the class of `q`:

| `(d, e)` | `m` | `κ(q)`, `q ≡ 1` | `κ(q)`, `q ≡ 3` | `q = m` term `ε(e, m)` |
|---|---|---|---|---|
| (5, 5) | 1 | 1 | `i` (from `φ(7,5)`) | `ε(5,1) ≡ 1 = φ` |
| (5, 7) | 3 | 1 | 1 | `ε(7,3) ≡ 1 = φ` |
| (7, 7) | 1 | 1 | `i` (from `ε(5,3)`) | `ε(7,1) ≡ 1 = φ` |
| (7, 5) | 3 | `i` (from `φ(7,5)`) | `i` (from `ε(5,3)`) | `ε(5,3) ≡ i = φ` |

On `{q ∣ m : 1 < q < m, q ≡ 1, 3}` the map `q ↦ m/q` is an involution without fixed points
(`m > 1` squarefree). It preserves `κ`: for `m ≡ 1`, `q` and `m/q` have the same class; for
`m ≡ 3`, `κ` is constant. It also preserves `𝓛(q)𝓛(m/q)`. So these terms cancel in pairs modulo 2,
and only `q = m` remains, with `κ(m)𝓛(m)𝓛(1) = ε(e, m)𝓛(m) ≡ φ(d, e)𝓛(m)`. ∎

For `d = n ≡ 5`, `φ = 1`, so `c_n(e) ≡ 𝓛(n/e)`. Lemma N1 then gives nt-tyz's form
`c_n(e) ≡ Λ(n/e)`. The table uses `ε ≡ i` for *every* `(5, 3)` pair. If all `(5,3)` classes were
`1`, the same proof would run with `φ ≡ 1` (rv-prop-n's "∅" variant). Mixed classes break the
pairing in the rows `(7,7)` and `(7,5)`, and through them the row `(5,5)` at the next level.
`n2_check.py` confirms this: 0 mismatches with uniform `±i`, 154 mismatches with random units at
`(5,3)`. A minimal example: `n/e = q₁q₂` with `q₁, q₂ ≡ 3`. Then
`c_n(e) = −ε(e, q₁q₂)𝓛(q₁q₂) + (ε(e,q₂)ε(n/q₁,q₁) + ε(e,q₁)ε(n/q₂,q₂))𝓛(q₁)𝓛(q₂)`, which is real
modulo 2 only if `ε(e, q₁) ≡ ε(e, q₂)`.

This simplifies the formal proof: N2 is a divisor-pairing induction, independent of N1 and of all
partition combinatorics.

## 5. Risks to faithfulness, ranked

1. **`β : M →+ M` (F5).** TYZ never state that `ℍ'_n/ℚ` is Galois. They use that
   `X^{β'} + X ∈ A(ℍ'_n)` (L2593–2595: the image of `2A(ℍ'_n)` under `β'+1` is torsion "contained in"
   `2A(ℍ'_n)_tor`). F5 follows from Proposition 3.2(1) and Cox, Lemma 9.3 (STANDARD; VERIFIED in
   nt-tyz §2.2 and rv-prop-n §2). *Fallback (SPECULATIVE design):* drop F5 and use F4 (`β'`
   commutes with `[i]`, since `β'` fixes `ℚ(i)`, L2581). Then `X^{β'} + X = Σ γ_e (Z(e)^{β'} + Z(e))`
   lies in `A(ℚ(i))` by I5. In Lean, `β` would be a semilinear map on a module containing `M`, or
   one would quantify only over the `ℤ[i]`-span of the `Z(e)`. That costs one more structure field
   and about 30 lines in `finalStep`.
2. **`ε`-uniformity.** N2 depends on Theorem 3.3's "`ε = ±i` if `(d₀,d₁) ≡ (5,3)`, `±1`
   otherwise", including the `(5,3)` half (§4). This is printed and unambiguous (L1309–1310), but
   it is the one place where a misprint in TYZ would break the argument.
3. **I3 and I5 rest on TYZ's proofs**: Theorem 3.5 (first assertion, via the Gross–Zagier formula
   of Yuan–Zhang–Zhang, Theorem 3.3) and Lemma 3.21 (via Theorem 3.6). These are TYZ theorems with
   proofs, read in arXiv v1 only. The journal version (Asian J. Math. 21 (2017)) was not compared
   (nt-tyz §1.1). (2026-11-12: the AI locator audit `locators.md` read the journal text and gives
   journal locators for Theorem 3.5(2), p. 740, and the proof of Proposition 3.4, pp. 751–753; it
   did not compare Theorem 3.5's first assertion or Lemma 3.21 with arXiv v1.)
4. **I7 bundles the continuation** (Hecke). The order is that of Mathlib's
   `WeierstrassCurve.LSeries (shortCurve (−n²))`, the convention already used by `TYZRow5b`,
   `GrossZagier` and `FunctionalEquation5`. If preferred, I7 can be split into
   `∀ F, IsLContinuation … F → L n ≠ 0 → analyticOrderAt F 1 ≤ 1` plus `HeckeContinuation`. The
   glue is unchanged up to one line.

## 6. The plan for the four proofs

All four statements are fixed in `PropN.lean`. Each agent proves one lemma in a copy of the file
and must not change any statement. Line counts are estimates (SPECULATIVE).

### A. `finalStep` (≈150–250 lines; independent)

Route (nt-tyz §4.4, in the abstract module):
1. `P n` is torsion (`torsion_of_zero hL`), so `P n = τ y` (`tors_mem_range`).
2. Apply `x ↦ β x + x` to `hX`, using `map_sum`, `map_zsmul` and `map_add`:
   `τ(2y) = Σ_e L(n/e)•(β(Z e) + Z e) + 2•W`, where `W = β X + X`. The left side comes from `β_τ`.
3. Split the filter `e ≡ 5 ∨ e ≡ 7` into two disjoint filters (`Finset.filter_or`, `sum_union`).
   Insert `beta_five` (choose the `k_e` with `choose`) and `beta_seven`. This gives
   `τ(2y) = a•τ(1−i) + K•τ 2 + N•τ 1 + 2•W` with `a, N, K ∈ ℤ`.
4. `2•W ∈ range τ`, so `W` is torsion (`IsOfFinAddOrder` of `2•W` gives that of `W`), so `W = τ w`.
5. `τ(2y − 2w − 2K − a(1−i) − N) = 0`, so `(2+2i)` divides it (`τ_eq_zero`). Components:
   `(2+2i)(p+qi) = (2p−2q) + (2p+2q)i`, so both components are even. The imaginary part gives `a`
   even; the real part gives `a + N`, hence `N`, even (`Zsqrtd.ext_iff`, `omega` on components).
6. Cast to `ZMod 2` (`ZMod.intCast_zmod_eq_zero_iff_dvd`, `push_cast`).

Reuse: Mathlib only (`isOfFinAddOrder_iff_nsmul_eq_zero`, `Zsqrtd`). Helper: `τ(2⟨a,b⟩) = (a+b)•τ 2`,
from `τ_eq_zero` on `2i − 2 = (2+2i)·i`.

### B. `lemmaN2` (≈300–450 lines; independent)

Route: the inductive identity of §4. **Not** nt-tyz's chain expansion, which needs ordered
factorizations, ordered set partitions and Fubini numbers; that would be well over 1000 lines.
1. Auxiliary statement, by strong induction on `d`: for `d ∈ n.divisors` with `d ≡ 5, 7`,
   `∃ c : ℕ → ℤ[i], G.P d = Σ_{e ∈ d.divisors, e ≡ 5,7} c e • G.Z e ∧
   ∀ e ∈ …, (2 : ℤ[i]) ∣ c e − φ d e * L(d/e)`, with `φ d e = if d%8=7 ∧ e%8=5 then gi else 1`.
2. Step: insert the IH into `recursion`, and swap `Σ_{q} Σ_{e ∣ d/q}` to `Σ_{e ∣ d} Σ_{q ∣ d/e}`
   (`Finset.sum_comm'`; for squarefree `d`, `q ∣ d ∧ e ∣ d/q ↔ e ∣ d ∧ q ∣ d/e`).
3. Coefficient congruence. Work in `R := ℤ[i] ⧸ Ideal.span {2}`, where `−1 = 1`, `ε ↦ 1` or
   `ε ↦ i` by `eps_pm1`/`eps_53`, and `x + x = 0`. Split off `q = m`, and cancel the rest with
   `Finset.sum_involution` (`q ↦ m/q`; no fixed points because `m` is squarefree and `> 1`). Class
   bookkeeping mod 8 uses `div_mod8_of` (in `PropN.lean`) and `decide` over residues.
4. Specialize to `d = n` (`φ = 1`). From `2 ∣ c e − L(n/e)` choose `w_e` and set
   `X := Σ w_e • Z e`. Convert `ℤ[i]`-smul to `ℤ`-smul (`Int.cast_smul_eq_zsmul`).

Reuse: `div_mod8_of`; Mathlib `Nat.divisors`, `Nat.div_div_eq_div_mul`, `Squarefree.squarefree_of_dvd`,
`Nat.Coprime` for complementary divisors of squarefree numbers.

### Shared infrastructure for C and D (≈150–250 lines, written by C, statement agreed first)

Transport the subtype-indexed sums to `Finpartition`s of `Finset ℕ`. All the sets are then in the
one type `Finset ℕ`, and `(n/e).primeFactors = n.primeFactors \ e.primeFactors`
(`Nat.primeFactors_div_gcd`):

```
def LamS (s : Finset ℕ) : ZMod 2 := ∑ P : Finpartition s,
  if (∀ B ∈ P.parts, B.prod id % 8 = 1 ∨ B.prod id % 8 = 3) ∧
     (P.parts.filter (fun B => B.prod id % 8 = 3)).card ≤ 1
  then ∏ B ∈ P.parts, (gNat (B.prod id) : ZMod 2) else 0
theorem Lam_eq_LamS (m : ℕ) : Lam m = LamS m.primeFactors
-- and the same for T5aCl, T5bCl (Finpartition.map along Function.Embedding.subtype)
```

Mathlib API: `Finpartition.map`, `extend`, `avoid`, `restrict` and `sum_restrict`, `combine` and
`sum_combine`, `parts_eq_empty_iff`, and the `Unique` instance on `Finpartition ⊥`; also
`Nat.prod_primeFactors_of_squarefree`, `Nat.primeFactors_prod`,
`Nat.prod_primeFactors_sdiff_of_squarefree` and `Nat.divisors_filter_squarefree_of_squarefree`. Fork
API: `RouteK/Rank5b/Sec3/Glue.lean` (`Finpartition.ofPartFun`, `parts_eq_image_part`,
`finpartition_ext_part`, `part_mem_univ`), `neZero_dProd`, and the definitions `Admissible5aNat` and
`Admissible5bNat`.

### C. `matching` (≈350–600 lines including the infrastructure)

1. Reindex `e ∈ n.divisors` by `B = e.primeFactors ⊆ n.primeFactors` (squarefree `n`).
2. **Split lemma.** For a block predicate `C`, sum over partitions of `s` with exactly one block in
   `C` = `Σ_{B ⊆ s, B ≠ ∅, C B} w(B) · Σ_{Q : Finpartition (s \ B)} …`. The bijection is
   `P ↦ (B, P.avoid B)`, with inverse `(B, Q) ↦ Q.extend …`.
3. Admissibility. For `T5a` (one class-5 block, the rest class 1), the rest is `Λ`-admissible for
   `n/e ≡ 1`. For `T5b` (one class-7 block, one class-3 block, the rest class 1), the rest is
   `Λ`-admissible for `n/e ≡ 3`. Conversely, a `Λ`-admissible partition of `m ≡ 3` has exactly one
   class-3 block, because the product of the block classes is `m`
   (`Finset.prod_biUnion`/`Finpartition` sup, then mod-8 arithmetic).

### D. `lemmaN1_core` (≈400–700 lines; needs `Lam_eq_LamS`)

1. `Lam 1 = 1`: `primeFactors 1 = ∅`, the unique partition of `⊥` has no parts, and the empty
   product is 1.
2. **Product lemma.** For disjoint `A, B`, the product of the partition sums over `A` and over `B`
   is the sum over the partitions of `A ∪ B` whose blocks each lie in `A` or in `B`. Use
   `restrict` and `combine` (or the fork's `prod_sum_allF` pattern).
3. `m ≡ 3`: `Σ_{A ⊆ s, class A = 1} Λ(A)Λ(s∖A) = Σ_π 2^{|C(π)|} w(π)`, summed over the partitions
   with one class-3 block, where `C(π)` is the set of class-1 blocks: `A` runs over the unions of
   class-1 blocks. Modulo 2 only `C = ∅`, i.e. `π = {s}` with weight `g(m)`, survives.
4. `m ≡ 1`: first replace the representatives "`d² < m`" by "`p₀ ∈ A`" for the least prime `p₀`.
   The summand is symmetric under `d ↔ m/d`; use the bijection `d ↦ if p₀ ∣ d then d else m/d`.
   Then `Σ_{A ∋ p₀, class A = 1} Λ(A)Λ(s∖A) = Σ_π 2^{b(π)−1} w(π)`: `A` is the block of `p₀`
   together with any subset of the other blocks. Modulo 2 only `b = 1` survives, with weight
   `g(m)`.

### Order and assignment

A and B can start at once. C writes `Lam_eq_LamS` first (about half a day) and publishes its
statement. D can work against that statement (stated with `sorry` in its own copy) in parallel,
then merge. The proved glue (`lemmaN1`, `genusSums_eq_zero`, `tyzRow5b_of_tyzInputs`) is unchanged
by any of these proofs. Total ≈1200–2000 lines.

### Adoption (after the four proofs)

Move `PropN.lean` to `ZInQKernel/Hypotheses/TYZInputs.lean` (statements) and
`ZInQKernel/RouteK/PropN/*.lean` (proofs), and add a headline variant of
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier`
taking `TYZInputs` in place of `TYZRow5b`. `TYZRow5b` stays as a corollary.

## 7. Next step

Run the four proofs (A–D) against the fixed statements. Then have a reviewer, with
`Period7.tex`, check the table of §2 field by field. That reviewer should be someone other than
this note's author, with priority on `β : M →+ M` (F5) and on `eps_53`.
