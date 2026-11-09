# tyz-5b: Route K on published theorems (Tian–Yuan–Zhang, row 5b)

Deliverable: `docs/research/tyz-5b.md`. Scripts and outputs: `scratch/tyz-5b/` (they import
`scratch/rv-route-k/sel2cong.py` and `scratch/slot-k/slotk.py`). Running log: `scratch/tyz-5b/log.md`.

## Verdict

**Yes.** For the curves produced by the slot construction, Route K can rest on published theorems only:
Tian–Yuan–Zhang (Asian J. Math. 2017) and Gross–Zagier–Kolyvagin (manuscript Lemma 5.5, A020), plus
elementary lemmas that the note proves. For every admissible input, `C_n` and `C_{nθ}` have a point of
infinite order with abscissa in `βℚ*²`. Kriz is not needed, and neither is Smith's preprint: the one row of
Smith's Theorem 2.2 that is used (row 5b) is reproved by a new and shorter argument.

One citation issue remains. The form of TYZ that is used is: for `n ≡ 5 (mod 8)`, if the `(7,3)` genus sum
`T_5b(n)` is odd, then `2^{−ρ}𝓛(n)` is odd, so the analytic rank is one. The proof of TYZ Theorem 3.5(2)
(arXiv v1, §3.3) proves exactly this, as a separate bracket. The *statement* of Theorems 1.2 and 3.5(2)
groups this sum with the `(5,1)` sum. It gives the form used only if `d₁ = 1` is admitted in the second sum,
which is the reading the proof needs. The journal text could not be retrieved (UNCHECKED).

## What is proved (all VERIFIED)

- **TYZ (§1).** The theorem used, with section and theorem numbers (Theorems 1.2 and 3.5(2), Proposition
  3.4, Lemmas 3.18 and 3.21). The note checks two facts that the proof leaves implicit: the `τ(1/2)`
  bracket is exactly `T_5b`, and the two torsion coefficients are independent modulo `ℤτ(1)`.
- **What TYZ gives.** Rank one (with Gross–Zagier and Kolyvagin) and an explicit genus/Heegner point, but
  no Kummer class. The class `β` comes from Selmer-minimality: rank one and `dim Sel₂ = 3` give
  `C(ℚ)/2C(ℚ) = Sel₂` (pc-audit RK9).
- **Rédei's formulas (§2).** Derived from genus theory: `g(d) = κ(B)` for `d ≡ 3 (mod 4)`, and
  `g(d) = Σ z_ρκ_ρ(B)` for `d ≡ 1 (mod 4)`, where `κ_ρ` counts arborescences mod 2. A self-contained
  `𝔽₂` all-minors forest lemma does the counting.
- **Smith's row 5b (§3), by forest expansion.**
  - `det M₁` is the sum of `Π g` over partitions into class-3 blocks.
  - `det M_5b` is the sum over partitions with one block of class 7 and all other blocks of class 3.
  - A new identity (Proposition 3.5): partitions into class-1 blocks and partitions into class-3 blocks
    give the same sum. Its proof uses a `κ_i + κ_j` lemma, and the identity is Smith's row 1.
  - Together these give `T_5b(n) = det M_5b`.
- **pc-audit's rule RK6 for row 5b (§4).**
  - Lemma 4.1: for `n ≡ 5 (mod 8)`, `Sel₂(C_n) = 𝒯 ⊕ H` with `H ≅ ker M₁` via `(a, b) ↦ (S(ab), S(a))`,
    on the representative with `b` odd and `a ≡ 1 (mod 4)`.
  - With the bordered-determinant lemma: on a Selmer-minimal curve, `det M_5b = [|a|_odd ≡ 3 (mod 4)]`.
- **Slot curves (§5).** `|n| ≡ |nθ| ≡ 5 (mod 8)` and `|β| ≡ 7 (mod 8)`, so the rule holds on both curves.
  Nothing beyond slot-k's theorem is needed. In particular no condition on `n/β` mod 8 has to be added,
  and the sign of `β` plays no role.

## Validation

- **Abstract data, 0 mismatches.** About 850–3,000 random configurations per statement test the forest
  lemma, the `κ`-difference lemma, `det M₁`, `det M_5b`, Proposition 3.5, and Smith's rows 1 and 5b.
- **Actual curves `n ≡ 5 (mod 8)`.** 1,200 curves, Selmer groups from the exact descent. Lemma 4.1 holds
  on all 1,200. The rule holds on all 931 Selmer-minimal curves. On the 682 of them with at most 8 primes,
  `T_5b` computed from PARI class groups equals `det M_5b`; both values occur (387 ones, 295 zeros).
- **Slot curves.** The 30 admissible inputs of slot-k's `random30` give 60 curves; all are Selmer-minimal
  with `β ∈ π₁` and `det M_5b = 1`. 30 small realizations give 60 curves; on the 55 with at most 8 primes,
  the PARI genus sum `T_5b` equals 1. On 12 tiny slot curves, PARI finds analytic rank 1 and a point with
  abscissa in `βℚ*²`.
- **Automated referee.** It redid §§2–4 by hand and with its own code, including Rédei against class
  numbers for all odd squarefree `d < 6000`. It found no error. Its presentational remarks are
  incorporated.

## What remains

1. Settle the TYZ citation: cite the proof of Theorem 3.5(2), or confirm the `d₁ = 1` reading in the
   journal version (or with the authors).
2. Slot-k's descent lemma (under review) and Proposition 0 for `c = 5`. Lemma 4.1 also rests on
   Proposition 0, but it was also checked against the independent exact descent.
3. A human review of the note.

## Suggestions

- Adopt K-TYZ as the deep input for Route K, citing TYZ Theorem 3.5(2) with its proof (§3.3) and
  Lemma 5.5 (A020). Keep Kriz only as a remark.
- Slot-k's narrowed hypothesis CR₃ can be restricted to `d ≡ 5 (mod 8)` and `|a|_odd ≡ 3 (mod 4)`; it then
  follows from published theorems (§5).
- §3's forest method should also give Smith's other rows quickly (SPECULATIVE). That is worth doing only
  if a later variant of the descent needs them.
