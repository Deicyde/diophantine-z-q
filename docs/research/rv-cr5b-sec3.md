# Referee report on cr5b-sec3: the hypothesis `CertifiedRankTYZ` and its justification

This report reviews the hypothesis `ZInQ.RouteK.Rank5b.CertifiedRankTYZ`
(`ZInQKernel/RouteK/Rank5b/Sec3/TYZ.lean`), the definitions it depends on, its trust statement,
the proof chain `CertifiedRankTYZ → CertifiedRank5b → CertifiedRankSel → FrozenTarget`, and a
numeric red team. The task report is `.fleet/cr5b-sec3.md`. The Lean proofs of §§2–3 (forest
lemma, Propositions 3.3–3.5, Theorem 3.6) were not re-read line by line: Lean checks them. Only
their statements and axioms were checked.

Marks: **VERIFIED** (checked here: by reading the source, by logic, or by exact computation),
**STANDARD** (a published theorem whose exact statement was checked), **SPECULATIVE**,
**UNCHECKED** (a source that could not be read here).

Sources read here: the arXiv TeX source of Tian–Yuan–Zhang, arXiv:1411.4728v1 (`Period7.tex`,
downloaded again for this review; line numbers `Lnnnn` refer to it), `docs/research/tyz-5b.md`
§§0–3, `docs/research/nt-tyz.md` (Verdict, §4), `docs/research/rv-nt-tyz.md`,
`docs/research/pc-audit.md` (RK4, RK7, RK9), the manuscript `diophantine_zq.tex` (Lemma 5.5),
`KERNEL_PLAN.md`. The journal text of TYZ (Asian J. Math. 21 (2017)) and Rédei's paper
(J. Reine Angew. Math. 171 (1934)) could not be read (UNCHECKED). The papers of Gross–Zagier,
Bump–Friedberg–Hoffstein and Murty–Murty were not readable here either. For those, this report
relies on the statements recorded in pc-audit RK7 and on standard knowledge, and marks them
accordingly.

## Verdict

**Faithful after the listed repairs.** The Lean statement needs no change. The repairs concern the
trust statement (the docstring of `CertifiedRankTYZ`, and the one-line summary in the docstring of
the main-theorem variant) and the project documentation.

- `T5b d = 1` is exactly the parity condition of TYZ's `(7, 3)` genus sum (the coefficient of
  `τ(1/2)` in the proof of their Theorem 3.5(2), L2582–2593), once Rédei's formula (tyz-5b
  Proposition 2.3) identifies `gBit d B` with `#2Cl(ℚ(√−d_B)) mod 2` on the blocks that occur
  (VERIFIED, §1).
- The premises `d % 8 = 5` and `Squarefree d` are exactly those of TYZ (positive squarefree
  `n ≡ 5 (mod 8)`). `(Sel2 d).ncard = 8` is not needed by TYZ or Gross–Zagier, but it is needed for
  the last step (rank ≥ 1 ⟹ every Selmer class is realized), and the red team shows that this step
  fails without it (§4: `d = 205, 221`, rank 1, 8 of 32 classes realized).
- `CertifiedRankTYZ` follows from the published results as cited, provided TYZ is taken in the
  form of Proposition N (nt-tyz §4, reviewed in rv-nt-tyz), and Gross–Zagier is supplemented by
  the auxiliary nonvanishing theorem it needs. The docstring cites TYZ in a form ("proved in the
  proof of Theorem 3.5(2)", with conclusion "`2^{−ρ(n)}𝓛(n)` is odd") that the project's own
  reviewed analysis says is not proved as written, and it cites "Gross–Zagier and Kolyvagin
  (manuscript Lemma 5.5)", which imports BCDT and an unrefereed preprint for a step that needs
  neither (§2).
- `#print axioms` on `det_M5b_eq_T5b`, `certifiedRank5b_of_certifiedRankTYZ` and the main-theorem
  variant lists only `propext`, `Classical.choice`, `Quot.sound` (VERIFIED, §3).
- Red team (30 values of `d`): no mismatch. `T5b = genusSum5b = det M_5b` on all 30. Rédei's
  formula agrees with PARI's class groups on all 89 blocks of class ≠ 5 that occur. On all 21
  values with `#Sel₂ = 8` and `T5b = 1`, every Selmer class is realized by an explicit rational
  point, checked against Lean's `Loc ℚ` (§4).

## Findings

| # | Severity | Where | Finding |
|---|----------|-------|---------|
| F1 | moderate | `CertifiedRankTYZ` docstring, 3rd bullet; root-module docstring | The trust statement cites "Gross–Zagier and Kolyvagin (manuscript Lemma 5.5)" for `rank C_d(ℚ) = 1`. Only `rank ≥ 1` is used (§2.3, VERIFIED). Lemma 5.5 proves more than needed and brings in BCDT (modularity, unnecessary for the CM curve `C_d`) and Kolyvagin through the MPIM preprint MPI/90-69 (unrefereed; nt-tyz Verdict 7). Moreover "Gross–Zagier" alone is not a complete citation for "analytic rank one ⟹ rank ≥ 1": it also needs an auxiliary imaginary quadratic field `K` satisfying the Heegner hypothesis with `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein, Murty–Murty), as pc-audit RK7 says. Repair: the wording of §5. |
| F2 | minor | `CertifiedRankTYZ` docstring, 1st bullet | TYZ is cited "in the form proved in the proof of their Theorem 3.5(2)", with the conclusion "`2^{−ρ(n)}𝓛(n)` is odd". nt-tyz (Verdict 3, 5) and rv-nt-tyz found that this proof takes the coefficients of the genus point from Proposition 3.4, whose proof is a sketch with the `d₁ = 1` ambiguity, and recommended citing **Proposition N**, "Theorem 3.5 (first assertion) and the argument of the proof of Theorem 3.5(2), §3.3, as completed in nt-tyz §4" (nt-tyz §4.5). The docstring points to nt-tyz.md but neither to §4 nor to Proposition N, and asserts the stronger conclusion `2^{−ρ}𝓛` odd, where only `𝓛(n) ≠ 0` is needed. (The stronger conclusion is also true: rv-nt-tyz finding A2.) Repair: §5. The same wording (from the earlier task) is in the docstrings of `CertifiedRank5b` and `CertifiedRankSel`; they are not part of this task, but should be aligned when this is merged. |
| F3 | minor | `CertifiedRankTYZ` docstring, 1st bullet; `T5b` docstring | One sentence uses `𝓛` with two meanings: "if `Σ g(d₀) g(d₁) 𝓛(n/d₀d₁)` is odd, then `2^{−ρ(n)}𝓛(n)` is odd". In the sum `𝓛` must be the partition sum `𝓛₁` (class-1 blocks), as in Lean's `T5b`; in the conclusion it is TYZ's invariant built from `L(E_n, s)`. Mod 2 they agree for `m ≡ 1 (mod 8)` by TYZ Theorem 1.1 (nt-tyz Lemma N1), so the statement is not wrong, but the reader cannot tell which is meant. Repair: write `𝓛₁` and define it, as nt-tyz does. |
| F4 | minor | `CertifiedRankTYZ` docstring, 2nd bullet | Rédei's formula is cited as "Gauss, Rédei 1934" without the paper. TYZ's bibliography (L3316–3317) has the exact reference: L. Rédei, *Arithmetischer Beweis des Satzes über die Anzahl der durch vier teilbaren Invarianten der absoluten Klassengruppe im quadratischen Zahlkörper*, J. Reine Angew. Math. 171 (1934), 55–60 (UNCHECKED: not readable here). The docstring should also say that the formula is used only for blocks of class 1, 3, 7, and that tyz-5b Proposition 2.3 derives the `κ` forms from genus theory (G1–G3 there; exact theorem numbers UNCHECKED). |
| F5 | minor | `KERNEL_PLAN.md` | Not updated: it still describes `CertifiedRank5b` as "the step toward Tian–Yuan–Zhang's own statement (`tyz-5b.md` §3)", with no mention of `CertifiedRankTYZ`, `det_M5b_eq_T5b` or the new main-theorem variant. It should say that §3 is now in Lean and that `CertifiedRankTYZ` is the hypothesis in TYZ's terms, logically equivalent to `CertifiedRank5b` (§3.2). |
| F6 | remark | `.fleet/cr5b-sec3.md`, docstrings | `CertifiedRankTYZ` and `CertifiedRank5b` are logically equivalent in Lean: `det_M5b_eq_T5b` gives both directions under the common premises `d % 8 = 5`, `Squarefree d`. The report proves only one direction (all that the chain needs), and does not state the equivalence. Stating it would make clear that the new hypothesis is neither weaker nor stronger than CR₃^5b. Both are logically stronger than CR₃^Sel (they assert the conclusion for more `d`). |
| F7 | cosmetic | `scratch/cr5b-sec3/build0.txt`, `buildfull.txt` | Two lake build logs (2,712 and 3,124 lines) are committed despite the commit "untrack build log". They contain only build output, but they inflate the diff. Suggest removing them from the index before the merge. |
| F8 | remark | `.fleet/cr5b-sec3.md` §"Cross-check" | `T5b_21` and `T5b_5` go through Theorem 3.6 and are not independent checks; the report says so. The red team here provides the independent check that was missing: the Python mirror of `T5b` computed from the definition agrees with `det M_5b` on 30 values (§4). |

No finding affects the Lean statement or the proofs.

## 1. The Lean statement and its definitions against tyz-5b and TYZ

### 1.1 The statement (VERIFIED by reading)

```
def CertifiedRankTYZ : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5b d = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2
```

It is `CertifiedRank5b` (`Rank5b/Row5b.lean:208`) with `(M5b d).det = 1` replaced by `T5b d = 1`.
`Sel2` and `Loc` are those of `Selmer/Covering.lean`, already used by `CertifiedRankSel`:
`Sel2 d` is the set of pairs of squarefree integers `(a, b)` such that `Loc ℝ d a b` and
`Loc ℚ_[p] d a b` for every prime `p`. `Loc K d a b` says that `a, b` are squares in `K`, or some
`x ∈ K` has `x/a`, `(x − d)/b`, `(x + d)/(ab)` squares, i.e. `D_{a,b}(K) ≠ ∅`. By the Lean lemma
`loc_iff_kummer` this is "`(a, b)` is the Kummer class of a point of `C_d(K)`", with Lean's
`kummer` sending `P = (x, y)` to `(x, x − d)` off the 2-torsion, as in Silverman X.1.4 with
`e₁ = 0`, `e₂ = d`. So `(Sel2 d).ncard = 8` says `#Sel₂(C_d/ℚ) = 8` (an infinite set would have
`ncard = 0`), and the conclusion says that every Selmer class comes from a rational point. These
definitions were reviewed with CR₃^Sel. They were rechecked here only for the facts this review
needs, and the mirror of §4 computes `Sel2` from the same local conditions.

### 1.2 The bits (VERIFIED)

- `legBit p a = 0` iff `(a : ZMod p)` is a square (`Slots/Symbols.lean:17`). `0` counts as a
  square, so `legBit p a = 0` when `p ∣ a`.
- `aBit d i j = legBit p_i p_j = (p_j/p_i)₊`, `yBit d i = legBit p_i (−1)`,
  `zBit d i = legBit p_i 2` (`Rank5b/Matrices.lean:54–60`), on the subtype `d.primeFactors`.
  These match tyz-5b Notation: `a_ij = (p_j/p_i)₊`, `y_i = (−1/p_i)₊`, `z_i = (2/p_i)₊`.
- **Primes dividing the argument.** The only such value is the diagonal `aBit d i i =
  legBit p_i p_i = 0`. It is never read: `Sec3.lapl a U` uses `a i j` only for `i ≠ j`, and its
  diagonal is `Σ_{k ∈ U.erase i} a i k`. Since `d` is odd, `p = 2` never occurs.

### 1.3 `lapl`, `kappa`, `redeiG`, `gBit` (VERIFIED)

- `Sec3.lapl a U i j = a i j` (`i ≠ j`), `Σ_{k ∈ U, k ≠ i} a i k` (`i = j`). On `U × U` this is
  tyz-5b's `L_U` (Smith's `A_Rows[U, U]`). The orientation matters for the diagonal, so it was
  checked against the genus-theory derivation of tyz-5b §2.2: at `p_j ∣ d_B` the Hilbert symbols are
  `(p_i, −d_B)_{p_j} = a_{ji}` (`i ≠ j`) and `(p_j, −d_B)_{p_j} = ((d_B/p_j)/p_j) = Σ_{k≠j} a_{jk}`,
  so the local conditions on an exponent vector `e` read `(L_B e)_j = 0` with row `j` of `L_B`
  as in Lean. (The `κ` forms would change if `a` were transposed, because the diagonal would
  change.)
- `Sec3.kappa a B ρ` is the determinant of `lapl a B` on the subtype `B.erase ρ`. For `B = {ρ}`
  this is the empty determinant, `1`. For `ρ ∉ B` it is a junk value, never used: `redeiG` sums
  only over `ρ ∈ B`.
- `Sec3.redeiG a y z B = Σ_{ρ∈B} y_ρ κ_ρ(B)` if `y(B) = 1`, else `Σ_{ρ∈B} z_ρ κ_ρ(B)`. For
  `y(B) = 1` it equals `κ(B)` by `Sec3.redeiG_eq_kappa` (all `κ_ρ(B)` are equal by
  `kappa_eq_kappa`, Lemma 2.2(1), and `Σ_ρ y_ρ = 1`). This is tyz-5b Proposition 2.3 (1)–(2) on the
  nose. For `B = ∅` it is `0`, but empty blocks never occur.
- Singletons: `g({p}) = 1` if `p ≡ 3 (mod 4)` and `z_p` if `p ≡ 1 (mod 4)`. This agrees with
  genus theory: `h(−p)` is odd for `p ≡ 3 (mod 4)`; for `p ≡ 1 (mod 4)` the 2-part of
  `Cl(ℚ(√−p))` is cyclic of order 2 exactly when `p ≡ 5 (mod 8)` (STANDARD; also checked by PARI on
  the singleton blocks of §4).
- `gBit d B = redeiG (aBit d) (yBit d) (zBit d) B`.

### 1.4 `dProd`, `Admissible5bNat`, `T5b` (VERIFIED)

- `dProd B = Π_{p∈B} p`.
- `Admissible5bNat d P`: exactly one part with `dProd ≡ 7`, exactly one with `dProd ≡ 3`, and every
  part `≡ 7, 3` or `1 (mod 8)`. Together these say: one block of class 7, one of class 3, all others
  of class 1. No block of class 5 (and none even, since `d` is odd).
- `T5b d = Σ_{P : Finpartition univ} [Admissible5bNat d P] Π_{B ∈ P.parts} gBit d B`. Mathlib's
  `Finpartition s` is a structure whose `parts` are nonempty, pairwise disjoint and cover `s`, and
  `Finpartition.ext` makes a partition determined by its parts. So the sum runs over the set
  partitions of the primes of `d`, each counted once.
- TYZ's bracket (L2589–2593): `Σ_{n = d₀d₁⋯d_ℓ, d₀ ≡ 7, d₁ ≡ 1,3, d_i ≡ 1 (i>1)} Π_i g(d_i)`. The
  product runs over all `i ≥ 0`: the coefficient of `Z(d₀)` carries `Π_{i≥1} g(d_i)`
  (Proposition 3.4, L1332–1346), and `Z(d₀)^{β'+1} = g(d₀)τ(1/2)` for `d₀ ≡ 7` (Lemma 3.21(4),
  L2515). For `n ≡ 5` the class of `d₁` is forced: `d₁ ≡ 5·7 ≡ 3`. With `n` squarefree, a
  factorization with distinguished `d₀`, `d₁` and an unordered multiset of factors `d_i > 1`
  (`i > 1`) is the same as a set partition with one block of class 7 and one of class 3 (these
  being unique, they are distinguished by their classes). Under nt-tyz's Lemma N2, which
  replaces Proposition 3.4, the coefficient is `Σ_{e≡7} g(e) Λ(n/e)` with
  `Λ(n/e) = Σ_{d≡3} g(d) 𝓛₁(n/ed)`, which is the same sum. Hence `T5b d` is TYZ's `(7, 3)`
  bracket, modulo the identification `gBit d B = g(d_B)` (Rédei).
- `T5b_eq_genusSum5b` (proved) identifies `T5b` with the bit form `genusSum5b`, using
  `(y(B), z(B)) = (λ, μ)(d_B)`.

### 1.5 Edge cases (VERIFIED)

| case | Lean | TYZ / genus theory |
|------|------|--------------------|
| `d` prime (`d ≡ 5 (8)`) | one partition `{{d}}`, class 5, not admissible: `T5b = 0` (`T5b_5_direct` for `d = 5`) | no factor `d₀ ≡ 7`: bracket `0` |
| `d = pq` | admissible iff `{p, q} mod 8 = {3, 7}`, then `T5b = g(p)g(q) = 1` | same: `g(p) = 1` for `p ≡ 3 (mod 4)` |
| empty partition | only for `d.primeFactors = ∅`, i.e. `d ∈ {0, 1}`, excluded by `d % 8 = 5` | — |
| blocks of class 5 | excluded by `Admissible5bNat` | do not occur in the `(7, 3)` bracket |
| `d ≡ 5`, not squarefree | outside the premises; `T5b` would see only the radical | TYZ needs squarefree |
| `d` even | impossible (`d % 8 = 5`) | — |

`Squarefree d` is used by Lean only to get `y(V) = 0` (`sum_yBit_univ`). TYZ need it too
(`n` squarefree), and it makes "set partition of the primes" equal to "unordered factorization of
`n`".

### 1.6 Are the premises the right ones? (VERIFIED, with STANDARD inputs)

- TYZ (Proposition N): `n` positive, squarefree, `n ≡ 5 (mod 8)`. Lean's `d : ℕ` with
  `d % 8 = 5` is positive. Exactly the same premises.
- Gross–Zagier: no premise beyond `ord_{s=1} L(C_d, s) = 1` (modularity being classical for `C_d`).
- The final step needs `#Sel₂ = 8`. Without it the conclusion can fail even at rank one: for
  `d = 205` and `d = 221`, `#Sel₂ = 32`, PARI's `ellrank` gives rank exactly 1, and exactly 8 classes
  are realized (§4). Those two have `T5b = 0`, so they do not touch `CertifiedRankTYZ`. Whether
  some `d` has `T5b = 1` and `#Sel₂ > 8` was not examined: Proposition N gives `𝓛(n) ≠ 0` only,
  and `Ш[2]` could be nonzero (SPECULATIVE). The premise is harmless in any case: an extra premise
  makes the hypothesis weaker, and the chain to CR₃^Sel has it anyway.

### 1.7 Is the hypothesis implied by the published results as cited?

Yes, with the citations of §5 (VERIFIED as logic, from STANDARD and cited inputs):

1. Rédei (tyz-5b Proposition 2.3) for the blocks of classes 1, 3, 7: `T5b d ≡` TYZ's `(7, 3)`
   bracket for `n = d` (§1.4).
2. Proposition N (TYZ Theorem 3.5 first assertion and the argument of §3.3, completed in nt-tyz §4;
   reviewed in rv-nt-tyz, "proved after one minor repair"): bracket odd ⟹ `𝓛(n) ≠ 0` ⟹
   `ord_{s=1} L(E_n, s) ≤ 1` (definition of `𝓛`, L338–345); root number `−1` for `n ≡ 5`
   (Birch–Stephens, quoted at L318–327) ⟹ `= 1`. `E_n : ny² = x³ − x` is isomorphic to `C_n` over `ℚ`,
   so the L-functions agree.
3. Gross–Zagier with an auxiliary field (§2.2): `rank C_d(ℚ) ≥ 1`.
4. Counting (§2.3): every Selmer class comes from a rational point: `Loc ℚ d a b` by
   `loc_iff_kummer`.

What is missing from the docstring as written: the auxiliary nonvanishing input of step 3 (F1),
the pointer to Proposition N for step 2 (F2). What remains UNCHECKED in any case: the journal text of
TYZ (the project has only arXiv v1; Crossref records no erratum, per nt-tyz), and the proofs of TYZ's
deep inputs (rv-nt-tyz B4).

## 2. The trust statement

### 2.1 Tian–Yuan–Zhang (VERIFIED against `Period7.tex`)

- Bibliographic data: Asian J. Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728. As in nt-tyz and
  pc-audit RK4 (journal text UNCHECKED).
- Locator "proof of their Theorem 3.5(2) (§3.3, 'Proof of Theorem 3.5: part (2)')": the
  subsubsection "Proof of Theorem \ref{m3}: part (2)" is at L2489, and the argument for `n ≡ 5, 7` is
  L2568–2600. The theorem `m3` (L1353) is Theorem 3.5 under the section counter. Correct.
- The quoted genus sum `Σ_{d₀ ≡ 7, d₁ ≡ 3} g(d₀)g(d₁)𝓛(n/d₀d₁)` is TYZ's bracket only if `𝓛` means
  `𝓛₁` (F3).
- "if [the sum] is odd, then `2^{−ρ(n)}𝓛(n)` is odd": the proof of part (2) assumes
  `P(n) ∈ A(K_n)^− + A[4]` and identifies it with "`2^{−ρ(n)}𝓛(n)` is even" (L1358). nt-tyz F6
  calls this "i.e." unproved. rv-nt-tyz A2 shows that the direction needed is immediate from
  Theorem 3.5 and Lemma 3.18. So the claim is true, but more than needed. The proof as written
  takes the coefficients from Proposition 3.4, a sketch (nt-tyz Verdict 3). The project's reviewed
  statement is Proposition N, which gives only `𝓛(n) ≠ 0` (F2).

### 2.2 Gross–Zagier, Kolyvagin, and what is needed

The docstring: "Gross–Zagier and Kolyvagin (manuscript Lemma 5.5, `lem:forward-rank`): analytic
rank one gives `rank C_d(ℚ) = 1`".

- Manuscript Lemma 5.5 (line 1086, read here): "If `ord_{s=1} L(A, s) = r ≤ 1` then
  `rank A(ℚ) = r` and `Ш(A/ℚ)` is finite", with modularity from BCDT Theorem A and the rest from
  Kolyvagin, *Theorem 1, pp. 4–5* (the MPIM preprint MPI/90-69 per audit record A020; nt-tyz
  Verdict 7). As a theorem this is correct (STANDARD), but it is stronger than needed and its
  citation is unrefereed.
- What is needed: `ord_{s=1} L(C_d, s) = 1 ⟹ rank C_d(ℚ) ≥ 1`. This is the Gross–Zagier theorem
  (B. Gross, D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
  225–320; data as in TYZ's bibliography, L3276–3277), applied over an imaginary quadratic field `K` satisfying the Heegner hypothesis for the
  conductor `32d²` with `L(C_d^K, 1) ≠ 0`. Such a `K` exists by the nonvanishing theorems of
  Bump–Friedberg–Hoffstein and Murty–Murty (both 1990–91; exact statements UNCHECKED here; pc-audit
  RK7 records the same input). Then `L'(C_d/K, 1) = L'(C_d, 1)L(C_d^K, 1) ≠ 0`, so the Heegner point
  `y_K` has infinite order, and since the root number of `C_d` is `−1`, `y_K + ȳ_K ∈ C_d(ℚ)` has
  infinite order. Modularity of `C_d` is classical (CM by `ℤ[i]`; Deuring, Shimura), so BCDT is not
  needed. Kolyvagin is not needed (STANDARD; this is pc-audit RK7, rechecked).
- Kolyvagin does enter upstream, inside TYZ: TYZ define `𝓛(n)` in the case `ord_{s=1} = 1` through
  the regulator `R_n` of "a generator of `E_n(ℚ)/E_n(ℚ)_tor` (in the case of rank one)" (L352), and
  `α_n` as a generator of `A(K_n)^−/tors` (L1295), after citing Coates–Wiles, Rubin, Gross–Zagier
  and Kolyvagin for the rank part of BSD (L334–335). This is part of the TYZ citation, not of the
  extra step. The recommended wording says so, so that "Kolyvagin is not needed" is not read as a
  claim about the whole chain.

### 2.3 "Under `#Sel₂ = 8`, rank ≥ 1 realizes every Selmer class" (VERIFIED)

Let `δ : C_d(ℚ) → (ℚ*/ℚ*²)²` be the Kummer map (Lean's `kummer`). It is a homomorphism with
kernel `2C_d(ℚ)` and image in `Sel₂(C_d)` (Silverman X.1.4, STANDARD). `C_d(ℚ)[2] = C_d[2]` has
order 4 (the roots `0, ±d` are rational). By Mordell–Weil, `C_d(ℚ) ≅ ℤ^r ⊕ T` with `T` finite,
so `C_d(ℚ)/2C_d(ℚ) ≅ (ℤ/2)^r ⊕ T/2T` and `#T/2T = #T[2] = 4`. If `r ≥ 1` this has at least 8
elements, and it injects into `Sel₂(C_d)`, which has 8. So `δ` is onto `Sel₂(C_d)`, and by
`loc_iff_kummer` every `(a, b) ∈ Sel2 d` satisfies `Loc ℚ d a b`. (Also `r = 1`.) Neither
finiteness of `Ш` nor the Cassels–Tate pairing is used, and only `r ≥ 1` is. This is pc-audit RK9.
The docstring's "`rank = 1` ... `dim C_d(ℚ)/2C_d(ℚ) = 2 + 1 = 3 = dim Sel₂`" is correct but needs
only `rank ≥ 1`.

### 2.4 Rédei's formula (STANDARD, checked numerically)

tyz-5b Proposition 2.3 derives the `κ` forms from genus theory (G1)–(G3) (classical; Rédei 1934,
exact theorem numbers UNCHECKED). The derivation was reread here, including the orientation of
`L_B` (§1.3) and the exceptional case `d = 3`. pc-audit checked Smith's Table 1 against PARI for all
squarefree `n < 20000`. Here `redeiG` agreed with PARI's `quadclassunit` (4-rank of
`Cl(ℚ(√−d_B))`) on all 89 blocks of class ≠ 5 occurring in the 30 values of §4. PARI's
`quadclassunit` is GRH-conditional in general. For discriminants this small (`|D| ≤ 4·4389`) that
does not matter here.

## 3. The proof chain and the axioms

### 3.1 Statements (VERIFIED by reading)

- `det_M5b_eq_T5b (hd5 : d % 8 = 5) (hsq : Squarefree d) : (M5b d).det = T5b d`. As in the report.
  The generic `Sec3.det_M5bG_eq_genusSum5b` needs only reciprocity and `Σ_i y_i = 0`.
- `certifiedRank5b_of_certifiedRankTYZ (h : CertifiedRankTYZ) : CertifiedRank5b`. As in the report.
- `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ
  (hH : SixContactMin) (hCR : RouteK.Rank5b.CertifiedRankTYZ) : FrozenTarget`, proved by composing
  `certifiedRank5b_of_certifiedRankTYZ`, `certifiedRankSel_of_certifiedRank5b` and
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel`. As in the
  report.

### 3.2 Equivalence with CR₃^5b (VERIFIED)

Under `d % 8 = 5` and `Squarefree d`, `det_M5b_eq_T5b` rewrites `(M5b d).det = 1` into
`T5b d = 1` and back, so `CertifiedRankTYZ ↔ CertifiedRank5b` (finding F6).

### 3.3 Axioms (VERIFIED)

The modules were not built in this worktree, so `lake build ZInQKernel.RouteK.Rank5bSec3` was run
once (it succeeded). Then a scratch file with `#print axioms` for the three declarations was run
with `lake env lean` and deleted. Output (in `scratch/rv-cr5b-sec3/out_axioms.txt`):

```
'ZInQ.RouteK.Rank5b.det_M5b_eq_T5b' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Only the three allowed axioms. No `sorryAx`, no `Lean.ofReduceBool`.

## 4. Numeric red team (VERIFIED, exact computation)

`scratch/rv-cr5b-sec3/mirror.py`, output `out_mirror.txt`, run with `python3 -I` in a venv that has
cypari2 (PARI/GP 2.17). The mirror follows the Lean definitions: `legBit` (with `0` a square), the
bits, `lapl` (diagonal `Σ_{k∈U, k≠i} a_ik`), `kappa` as the `𝔽₂` determinant on `B∖ρ`, `redeiG`,
`Admissible5bNat` by `dProd mod 8`, `T5b` over all set partitions, `genusSum5b` by bits, and
`M5b = border (fromBlocks (L+Lᵀ) Lᵀ L (diag z)) (Sum.elim 0 y)`. `Sel2` is computed from Lean's local
conditions: `Loc ℝ` (sign pattern), and `Loc ℚ_p` for `p ∣ 2d` via the local Kummer image of
`C_d(ℚ_p)` (Lean's `loc_iff_kummer` over `ℚ_p`). The image is found by sampling local points
until it reaches its known size: 4 for odd `p`, 8 for `p = 2`. For `p ∤ 2d` the condition is
automatic on the support `{−1, 2, p ∣ d}`, which contains every Selmer pair (Lean's Proposition 0,
`Sel2 d ⊆ range selPair`).

Independent sources (PARI): `quadclassunit` for `g(d_B)`; `ellrank` (rank bounds and points),
`ellanalyticrank`. For each Selmer class `(a, b)` the script builds a point `R = P + 2G` with
`δ(P) = (a, b)` and `G` the non-torsion point found by `ellrank`, and checks Lean's `Loc ℚ d a b`
directly: `x(R)/a`, `(x(R) − d)/b` and `(x(R) + d)/(ab)` are rational squares.

Selection: 30 hand-picked squarefree `d ≡ 5 (mod 8)` below 4400 with 1–4 prime factors: primes and
products of primes `≡ 1 (mod 4)` (where `T5b = 0` is forced, since there is no class-7 block), and
products with primes `≡ 3 (mod 4)`. No larger scan was run, so the sample stays within 30 inputs.
28 of the 30 have `#Sel₂ = 8`. `d = 205, 221` have `#Sel₂ = 32` and are kept as a control for the
premise `#Sel₂ = 8`.

| d | primes | #Sel₂ | T5b | genusSum5b | det M_5b | #adm. partitions | Rédei = PARI (blocks) | ellrank | an. rank | classes realized |
|---|--------|-------|-----|-----------|----------|------------------|-----------------------|---------|----------|------------------|
| 5 | 5 | 8 | 0 | 0 | 0 | 0 | ok (0) | [1,1] | 1 | 8/8 |
| 13 | 13 | 8 | 0 | 0 | 0 | 0 | ok (0) | [1,1] | 1 | 8/8 |
| 29 | 29 | 8 | 0 | 0 | 0 | 0 | ok (0) | [1,1] | 1 | 8/8 |
| 85 | 5·17 | 8 | 0 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/8 |
| 205 | 5·41 | **32** | 0 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/32 |
| 221 | 13·17 | **32** | 0 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/32 |
| 365 | 5·73 | 8 | 0 | 0 | 0 | 0 | ok (1) | [1,1] | 1 | 8/8 |
| 21 | 3·7 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 69 | 3·23 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 77 | 7·11 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 93 | 3·31 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 133 | 7·19 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 141 | 3·47 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 165 | 3·5·11 | 8 | 1 | 1 | 1 | 2 | ok (5) | [1,1] | 1 | 8/8 |
| 237 | 3·79 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 253 | 11·23 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 285 | 3·5·19 | 8 | 1 | 1 | 1 | 2 | ok (5) | [1,1] | 1 | 8/8 |
| 301 | 7·43 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 309 | 3·103 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 357 | 3·7·17 | 8 | 0 | 0 | 0 | 3 | ok (5) | [1,1] | 1 | 8/8 |
| 413 | 7·59 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 429 | 3·11·13 | 8 | 1 | 1 | 1 | 2 | ok (5) | [1,1] | 1 | 8/8 |
| 469 | 7·67 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 517 | 11·47 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 589 | 19·31 | 8 | 1 | 1 | 1 | 1 | ok (2) | [1,1] | 1 | 8/8 |
| 645 | 3·5·43 | 8 | 0 | 0 | 0 | 2 | ok (5) | [1,1] | 1 | 8/8 |
| 741 | 3·13·19 | 8 | 1 | 1 | 1 | 2 | ok (5) | [1,1] | 1 | 8/8 |
| 1365 | 3·5·7·13 | 8 | 1 | 1 | 1 | 5 | ok (11) | [1,1] | 1 | 8/8 |
| 2109 | 3·19·37 | 8 | 1 | 1 | 1 | 2 | ok (5) | [1,1] | 1 | 8/8 |
| 4389 | 3·7·11·19 | 8 | 1 | 1 | 1 | 7 | ok (11) | [1,1] | 1 | 8/8 |

Summary:

- **Theorem 3.6:** `T5b = det M_5b` on all 30, and `T5b = genusSum5b` (`T5b_eq_genusSum5b`) on all
  30. This includes `d = 357` and `645`, where admissible partitions exist (3 and 2) and the sum
  vanishes because of the `g` values, not vacuously.
- **Rédei:** `redeiG = g` from PARI on all 89 blocks of class ≠ 5 (including class-1 blocks with two
  primes, e.g. `{3, 11}`, `{3, 43}`, where the `κ` orientation matters).
- **TYZ + Gross–Zagier prediction** (`T5b = 1` ⟹ rank 1 and every class realized): 21 values with
  `#Sel₂ = 8` and `T5b = 1`. All have analytic rank 1, `ellrank` bounds `[1, 1]`, and all 8 classes
  are realized by explicit points satisfying Lean's `Loc ℚ`. **No mismatch.**
- `T5b = 0` with `#Sel₂ = 8` (7 values): also rank 1 with all classes realized. This is expected:
  these curves are rank one, they are just not certified by TYZ's `(7, 3)` bracket.
- `#Sel₂ = 32` (205, 221): rank exactly 1, exactly 8 classes realized. This shows that the premise
  `#Sel₂ = 8` cannot be dropped from the last step.
- No `d` was left without a point within the search limits: `ellrank` found a generator in all 30
  cases.

## 5. Recommended docstring

For `CertifiedRankTYZ` (replacing the "*Trust statement.*" paragraph and its three bullets):

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

For the root-module docstring of the main-theorem variant, replace "a consequence of
Tian–Yuan–Zhang, Rédei's formula and Gross–Zagier–Kolyvagin" with "a consequence of
Tian–Yuan–Zhang (Proposition N of `docs/research/nt-tyz.md`), Rédei's formula and Gross–Zagier".

## 6. What was not done

- The Lean proofs of §§2–3 were not reread. Lean checks them, and the statements and axioms were
  checked (§3).
- The journal text of TYZ, Rédei's paper, Gross–Zagier, Bump–Friedberg–Hoffstein and Murty–Murty
  are UNCHECKED here: no literature host other than arXiv was reachable.
- Whether `T5b(d) = 1` can occur with `#Sel₂(C_d) > 8` was not examined (SPECULATIVE; irrelevant
  for the hypothesis, which has the premise).
