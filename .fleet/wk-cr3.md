# wk-cr3: reduction plan for CR₃ (fleet report)

**Recommended reduction.** Replace `CertifiedRankTYZClRk` by three Props stated with Mathlib
v4.35.0's `WeierstrassCurve.LSeries` (minimal-model Euler product) and `analyticOrderAt`:

- `GrossZagierKolyvagin`: for every elliptic `E/ℚ`, if the entire continuation of `L(E, s)` has
  order 1 at `s = 1`, then `E(ℚ)` has a point of infinite order (Gross–Zagier 1986 with BFH 1990 or
  Murty–Murty 1991, plus BCDT).
- `FunctionalEquation5`: for squarefree `d ≡ 5 (mod 8)`, `Λ(2 − s) = −Λ(s)` with conductor `32d²`
  (Deuring/Hecke; root number from Birch–Stephens).
- `TYZRow5b`: for squarefree `d ≡ 5 (mod 8)` with `T5bCl d = 1`, `L(C_d, s)` has an entire
  continuation of order at most 1 at `s = 1`. This is TYZ's "`𝓛(n) ≠ 0`" for row `(7, 3)`.

The draft `scratch/wk-cr3/Literature.lean` proves `CertifiedRankTYZClRk`, and `FrozenTarget` from
`SixContactMin`, using these three Props. It compiles with no `sorry` and only the standard axioms
(checked with `lake env lean` against prebuilt oleans at `520e27e5`, which has the same Lean
sources as the base). PARI checks on 20 curves confirm the conventions: conductor, root number,
minimal model, additive bad reduction, and `a_p`.

The first two Props are textbook theorems. `TYZRow5b` is the only remaining input written for this
project. Its source is reading A of TYZ Theorem 3.5(2), and the gap is Proposition N
(Lemmas N1, N2, F5). Note `docs/research/wk-cr3.md`.

**Most serious obstacle.** No refereed text states `TYZRow5b`. TYZ's printed Theorem 1.2 is false,
and Theorem 3.5(2) is ambiguous. Proposition N has only model reviews. No published theorem with
prime restrictions (Heegner, Monsky, Tian 2014, TYZ Cor. 1.4) can replace TYZ under any slot
choice: every `d` used has at least two primes `≢ 1 (mod 8)` and unbounded `ω` (proved in the note,
§1.3). A row-5a redesign does not help either (30-curve experiment).

**Single next step.** Adopt the draft as `ZInQKernel/Hypotheses/CR3Literature.lean` with a
main-theorem variant (cheap: no new mathematics). In parallel, read Tian's ICM 2022 article or the
journal text of TYZ for a printed statement of reading A, which would make `TYZRow5b` a citation.
