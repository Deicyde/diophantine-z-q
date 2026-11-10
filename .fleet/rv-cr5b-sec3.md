# rv-cr5b-sec3 report: adversarial review of `CertifiedRankTYZ` (cr5b-sec3)

**Verdict: faithful after the listed repairs.** The Lean statement of `CertifiedRankTYZ` and the
definitions behind it are faithful. `T5b d = 1` is exactly the parity condition of TYZ's `(7, 3)`
genus sum, given Rédei's formula. The premises are TYZ's premises plus `#Sel₂ = 8`, which the last
step needs. The hypothesis follows from the cited published results. The repairs are to the trust
statement (docstrings) and to `KERNEL_PLAN.md`. No Lean statement or proof needs to change.

Full review: `docs/research/rv-cr5b-sec3.md`. Scripts and outputs: `scratch/rv-cr5b-sec3/`
(`mirror.py`, `out_mirror.txt`, `out_axioms.txt`, `log.md`).

## Findings

| # | Severity | Where | Finding |
|---|----------|-------|---------|
| F1 | moderate | `CertifiedRankTYZ` docstring (3rd bullet), root-module docstring | Cites "Gross–Zagier and Kolyvagin (manuscript Lemma 5.5)" for `rank = 1`. Only `rank ≥ 1` is used (VERIFIED: with `#Sel₂ = 8`, Mordell–Weil and Silverman X.1.4 give that the Kummer map is onto). Lemma 5.5 brings in BCDT (not needed: `C_d` has CM) and Kolyvagin through the unrefereed MPIM preprint. "Gross–Zagier" alone is also incomplete: it needs an auxiliary Heegner field `K` with `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein, Murty–Murty), as pc-audit RK7 says. Kolyvagin does enter upstream, inside TYZ's definition of `𝓛(n)` (TYZ L334–352). |
| F2 | minor | docstring (1st bullet) | Cites TYZ "in the form proved in the proof of Theorem 3.5(2)" with conclusion "`2^{−ρ}𝓛(n)` odd". nt-tyz and rv-nt-tyz found that this proof depends on Proposition 3.4 (a sketch), and recommend Proposition N (nt-tyz §4), which gives `𝓛(n) ≠ 0`, all that is needed. The docstring does not point to §4 or to Proposition N. `CertifiedRank5b` and `CertifiedRankSel` (earlier tasks) have the same wording. |
| F3 | minor | docstring (1st bullet), `T5b` docstring | `𝓛` has two meanings in one sentence: the partition sum `𝓛₁` inside `T_5b`, and TYZ's L-value invariant in the conclusion. They agree mod 2 for `m ≡ 1 (mod 8)` (TYZ Theorem 1.1), so this is not wrong, but it is ambiguous. Write `𝓛₁`. |
| F4 | minor | docstring (2nd bullet) | Rédei is cited without the paper. The exact reference is J. Reine Angew. Math. 171 (1934), 55–60 (from TYZ's bibliography; the paper itself is UNCHECKED). Say also that the formula is used only for blocks of class 1, 3, 7. |
| F5 | minor | `KERNEL_PLAN.md` | Not updated: no mention of `CertifiedRankTYZ`, `det_M5b_eq_T5b` or the new main-theorem variant. |
| F6 | remark | report, docstrings | `CertifiedRankTYZ ↔ CertifiedRank5b` by `det_M5b_eq_T5b` (both directions are immediate). This is not stated. Both are logically stronger than CR₃^Sel. |
| F7 | cosmetic | `scratch/cr5b-sec3/build0.txt`, `buildfull.txt` | About 5,800 lines of lake build logs are committed. |
| F8 | remark | report §Cross-check | `T5b_21` and `T5b_5` are not independent of Theorem 3.6 (the report says so). The red team below supplies the independent check. |

### Checks that passed

- **Definitions** (VERIFIED). The bits `aBit/yBit/zBit` match tyz-5b Notation. The only junk value
  `aBit d i i = 0` is never read. `lapl` has the orientation that genus theory needs: the diagonal
  `Σ_{k≠i} a_ik` is the symbol `(p_i, −d_B)_{p_i}`. `kappa` and `redeiG` are tyz-5b Proposition 2.3
  (1)–(2), with `redeiG_eq_kappa` covering the `y(B) = 1` form. `Admissible5bNat` and `Finpartition`
  give exactly TYZ's bracket `Σ_{d₀≡7, d₁≡3, d_i≡1} Π_{i≥0} g(d_i)` (L2582–2593): each set partition
  is counted once, there are no class-5 blocks, and the `g(d₀)` factor comes from Lemma 3.21(4).
- **Edge cases**: for `d` prime, `T5b = 0`. For `d = pq`, `T5b = 1` iff `{p, q} ≡ {3, 7} (mod 8)`.
  The empty partition is excluded by `d % 8 = 5`. Blocks of class 5 are excluded.
- **Premises**: `d % 8 = 5` and `Squarefree d` are exactly TYZ's premises (positive squarefree
  `n ≡ 5 (mod 8)`). `#Sel₂ = 8` is needed for the last step: `d = 205, 221` have rank 1 but
  `#Sel₂ = 32`, and only 8 classes are realized.
- **Statements** of `det_M5b_eq_T5b`, `certifiedRank5b_of_certifiedRankTYZ` and the variant
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ` say what
  the report says.
- **Axioms**: `lake build ZInQKernel.RouteK.Rank5bSec3` succeeded. The modules had not been built in
  this worktree, so one build was run. `#print axioms` on the three declarations gives
  `[propext, Classical.choice, Quot.sound]` for each.

## Recommended docstring (trust statement of `CertifiedRankTYZ`)

```
*Trust statement.* This is not proved in Lean. It follows from the following published results,
none of them formalized here, together with Theorem 3.6 (`det_M5b_eq_T5b`, proved):

* **Tian–Yuan–Zhang** (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), no. 4, 721–774; read in arXiv:1411.4728v1, the journal
  text was not available): Theorem 3.5 (first assertion) and the argument of the proof of
  Theorem 3.5(2) in §3.3, for `n ≡ 5 (mod 8)`, as completed in `docs/research/nt-tyz.md` §4
  (Proposition N; reviewed in `docs/research/rv-nt-tyz.md`). For squarefree `n ≡ 5 (mod 8)`: if
  the `(7, 3)` genus sum `Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)` is odd, where `𝓛₁(m)` is
  the sum of `Π g(B)` over the set partitions of the primes of `m` into blocks `≡ 1 (mod 8)`, then
  TYZ's invariant `𝓛(n)` is nonzero, so `ord_{s=1} L(C_n, s) ≤ 1`, and since the root number is `−1`
  (Birch–Stephens), `ord_{s=1} L(C_n, s) = 1`. TYZ's Theorem 1.2 must not be cited literally (with
  "all `d_i > 1`" it is false; nt-tyz §1.4). TYZ's own definition of `𝓛(n)` uses Coates–Wiles,
  Rubin, Gross–Zagier and Kolyvagin (TYZ §1).
* **Rédei's formula** (genus theory; L. Rédei, J. Reine Angew. Math. 171 (1934), 55–60; the `κ`
  forms are derived in `docs/research/tyz-5b.md` Proposition 2.3): for every set `B` of primes of
  `d` with `d_B ≢ 5 (mod 8)`, `gBit d B = #2Cl(ℚ(√−d_B)) mod 2`. So `T5b d` is the `(7, 3)` genus
  sum above for `n = d`.
* **Gross–Zagier** (Invent. Math. 84 (1986), 225–320), over an imaginary quadratic field `K` that
  satisfies the Heegner hypothesis and has `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein;
  Murty–Murty); `C_d` is modular because it has CM by `ℤ[i]` (Deuring, Shimura). This gives
  `ord_{s=1} L(C_d, s) = 1 ⟹ rank C_d(ℚ) ≥ 1` (`docs/research/pc-audit.md` RK7). Neither
  Kolyvagin nor BCDT is needed for this step.

Then (elementary, `docs/research/pc-audit.md` RK9): `C_d(ℚ)[2]` has order 4, so
`dim C_d(ℚ)/2C_d(ℚ) = 2 + rank ≥ 3 = dim Sel₂(C_d)`. The Kummer map is injective on
`C_d(ℚ)/2C_d(ℚ)` (Silverman X.1.4), hence onto `Sel₂(C_d)`, and every Selmer class has
`D_{a,b}(ℚ) ≠ ∅` (`Selmer.loc_iff_kummer`). Neither finiteness of `Ш` nor the Cassels–Tate
pairing is used.

Under `d % 8 = 5` and `Squarefree d`, `CertifiedRankTYZ` is equivalent to `CertifiedRank5b` by
Theorem 3.6.
```

Root-module docstring of the variant: replace "Tian–Yuan–Zhang, Rédei's formula and
Gross–Zagier–Kolyvagin" with "Tian–Yuan–Zhang (Proposition N of `docs/research/nt-tyz.md`),
Rédei's formula and Gross–Zagier".

## Red-team table (30 values of `d`; VERIFIED, exact computation)

`mirror.py` is a Python mirror of the Lean definitions: `legBit`, the bits, `lapl`, `kappa`,
`redeiG`, `Admissible5bNat`, `T5b`, `genusSum5b` and `M5b`. `Sel2` is computed from Lean's local
conditions `Loc ℝ`, `Loc ℚ_p` through the local Kummer images. The independent checks use PARI 2.17
(cypari2): `quadclassunit` for `g`, `ellrank` and `ellanalyticrank`. For each Selmer class there is
an explicit point `x` with `x/a`, `(x−d)/b`, `(x+d)/(ab)` all squares, which is Lean's `Loc ℚ`
checked directly.

| d | primes | #Sel₂ | T5b | genusSum5b | det M_5b | Rédei = PARI (blocks) | ellrank | an. rank | classes realized |
|---|--------|-------|-----|-----------|----------|-----------------------|---------|----------|------------------|
| 5 | 5 | 8 | 0 | 0 | 0 | ok (0) | [1,1] | 1 | 8/8 |
| 13 | 13 | 8 | 0 | 0 | 0 | ok (0) | [1,1] | 1 | 8/8 |
| 29 | 29 | 8 | 0 | 0 | 0 | ok (0) | [1,1] | 1 | 8/8 |
| 85 | 5·17 | 8 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/8 |
| 205 | 5·41 | 32 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/32 |
| 221 | 13·17 | 32 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/32 |
| 365 | 5·73 | 8 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/8 |
| 21 | 3·7 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 69 | 3·23 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 77 | 7·11 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 93 | 3·31 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 133 | 7·19 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 141 | 3·47 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 165 | 3·5·11 | 8 | 1 | 1 | 1 | ok (5) | [1,1] | 1 | 8/8 |
| 237 | 3·79 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 253 | 11·23 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 285 | 3·5·19 | 8 | 1 | 1 | 1 | ok (5) | [1,1] | 1 | 8/8 |
| 301 | 7·43 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 309 | 3·103 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 357 | 3·7·17 | 8 | 0 | 0 | 0 | ok (5) | [1,1] | 1 | 8/8 |
| 413 | 7·59 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 429 | 3·11·13 | 8 | 1 | 1 | 1 | ok (5) | [1,1] | 1 | 8/8 |
| 469 | 7·67 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 517 | 11·47 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 589 | 19·31 | 8 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 645 | 3·5·43 | 8 | 0 | 0 | 0 | ok (5) | [1,1] | 1 | 8/8 |
| 741 | 3·13·19 | 8 | 1 | 1 | 1 | ok (5) | [1,1] | 1 | 8/8 |
| 1365 | 3·5·7·13 | 8 | 1 | 1 | 1 | ok (11) | [1,1] | 1 | 8/8 |
| 2109 | 3·19·37 | 8 | 1 | 1 | 1 | ok (5) | [1,1] | 1 | 8/8 |
| 4389 | 3·7·11·19 | 8 | 1 | 1 | 1 | ok (11) | [1,1] | 1 | 8/8 |

- **No mismatch.** `T5b = genusSum5b = det M_5b` on all 30 (Theorem 3.6). This includes `d = 357, 645`,
  where admissible partitions exist and the sum is `0` because of the `g` values.
- **Rédei:** `redeiG` agrees with PARI on all 89 blocks of class ≠ 5.
- **TYZ + Gross–Zagier prediction holds:** for the 21 values with `#Sel₂ = 8` and `T5b = 1`, the rank
  is 1 and all 8 classes are realized. The 7 values with `T5b = 0` and `#Sel₂ = 8` are also rank one
  with all classes realized; they are just not certified by TYZ's bracket.
- **No `d` without a point:** `ellrank` found a generator for all 30 values.

## Limits

- The Lean proofs of §§2–3 were not reread. Lean checks them; their statements and axioms were
  checked.
- The journal text of TYZ, Rédei 1934, Gross–Zagier, Bump–Friedberg–Hoffstein and Murty–Murty
  could not be read here (UNCHECKED). TYZ was read in its arXiv TeX source; the Gross–Zagier and
  Rédei bibliographic data come from TYZ's bibliography.
- Resource use: one `lake build` (the modules were missing), then one `lake env lean` run, one at a
  time. Load stayed below 15.
