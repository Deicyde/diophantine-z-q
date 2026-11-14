# tyz-split (fleet report)

**Main result.** Row **T-11** (`TYZ35.TYZThm33Pinned`, for every `ℓ` with `IsTYZLcal ℓ`) is now a Lean
theorem, `ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33`. It follows from one leaf,
`TYZSplit.TYZThm33`, which is TYZ Theorem 3.3 (Period7.tex L1299–1311) in its printed form for
`n ≡ 5, 7`. In that leaf, `Cl_n = Gal(H_n/K_n)`, `Φ` is encoded by lifts, and `χ_{d₀,d₁}` is the
character of `K_n(√d₁)` resp. `K_n(√d₁*)`. `h₂` is `log₂ [Cl_n : 2Cl_n]`. `𝒫` is existential, because
its coefficient needs Néron–Tate regulators. The headline form is
`tyzThm35ReadingA_of_printedThm33 (h11 h29 hS h33)`.
- What is now proved Lean glue:
  - the genus character used by the row is TYZ's Galois character;
  - the excluded characters are not contributing;
  - `h₂ = #ramSet − 1`;
  - reindexing from `Φ` to lift families.
- Lemma 3.14 is not needed as a leaf. Its conclusion is the first sentence of the printed Theorem
  3.3, and its hypotheses (root numbers) have no Lean definition.
- Reading the source settled tyz-35's three HUMAN CHECK items: `Φ` is arbitrary (L1279), the
  `K_n(√d₁)` convention is printed (L1304), and so is `h₂` (L992).
- One check remains open: the `[i]`-sign of `z_n` for `n ≡ 5` is a numerical choice, not printed, and
  the wrong sign would make the leaf false.
- A read-only AI review against the TeX found the leaf faithful with caveats and never stronger than
  the print.

Row **T-5** (`Shimura.ShimuraReciprocityModFn`) is **not done**. No printed form of Shimura
reciprocity can be stated over Lean definitions today:
- Thm 5.4 needs the idelic `[s,K]` and ideles acting on lattices;
- Thm 6.31 also needs Shimura's `τ`;
- Gross's form needs `X₀(N)/ℚ`.

`TYZSplitT5.shimuraReciprocityModFn_of_split` splits T-5 into two GLUE Props:
- `CMModuli`: the CM part, for `j` and Weber-function moduli coordinates over Mathlib's
  `PeriodPair`. It is a consequence of Shimura Thm 5.4.
- `X0RatStructure`: no CM. It says the q-expansion ℚ-structure of `X₀(N)` is the moduli ℚ-structure
  (the canonical model).

Unlike the `(j, j_N)` model, the Weber coordinates separate every point of `Y₀(N)`.

**What compiles.** `lake env lean` on `scratch/tyz-split/T11.lean` and `scratch/tyz-split/T5.lean`
gives 0 errors and no `sorry`. The axioms are `[propext, Classical.choice, Quot.sound]` (outputs in
`T11.out` and `T5.out`). Both files import only built kernel modules (`TYZChain.Main`,
`ShimuraModFn`).

**What remains.**
- T-11: the leaf `TYZThm33` itself, which needs the explicit Gross–Zagier formula, Néron–Tate heights
  and Kolyvagin; and the `[i]`-sign HUMAN CHECK.
- T-5: `CMModuli` and `X0RatStructure`.

Report: `docs/research/tyz-split.md`. Log: `scratch/tyz-split/log.md`.
