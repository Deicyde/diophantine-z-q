# rv-h-c8: report

**Verdict: C8 (twist and weight, N5 L757-768) holds after the listed repairs.** No mathematical gap:
the step delivers what C9, C10 and Part D use (`r₅` is the Tate-module representation of a weight-2
newform). The repairs are a normalization sentence and citations; no argument, constant or Lean
statement changes. Full review: `docs/research/rv-h-c8.md`; log and scripts: `scratch/rv-h-c8/`.

Findings:

1. **Most serious: normalization unstated.** N5's "modular weights `{0, 1−k}`" holds only for the
   arithmetic-Frobenius (Tate-module) normalization of `ρ_g`. Pan's notation uses geometric
   Frobenius, where the weights are `{0, k−1}`; an exhaustive search (`weights.py`, VERIFIED) gives
   `k = 2` in both normalizations, but the twist is `χ¹`, not "power zero", in Pan's. The conclusion
   survives (for `k = 2` the extra `χ` is a dual up to a finite character, which N5 absorbs anyway;
   VERIFIED as an argument and on a PARI sample, `normalization.py`). Astra's descent AUDIT item 6
   had warned about mixing the two; N5 never fixed the normalization.
2. **Weight one not covered by the supplier.** Faltings 1987, Scholl 1990 and Saito 1997 are all for
   `k ≥ 2`. `k = 1` needs Deligne–Serre 1974 (finite image, so weights `{0, 0}`). STANDARD.
3. **Level divisible by 5.** Pan's eigenform can have `5 | N`. "Scholl + Faltings 1989" covers only
   good reduction, and "Scholl + Tsuji 1999" needs de Jong's alterations. Saito 1997, or Scholl +
   Scholze 2013 Cor. 1.8 (already a C3 leaf), cover all levels. SPECULATIVE where it concerns the
   content of Faltings 1987/1989, which could not be read.
4. Only Hodge–Tate is needed in C8, not de Rham. Uncited but elementary: finiteness of `ψ` on inertia
   at `ℓ ≠ 5`, Kronecker–Weber, and "duality preserves the conductor" (L774).

**Consequence for H's trust statement.** H stands. C8 stays [M], now with two model reviews (Astra
on the identical 11/4 text, VERIFIED by a diff, and this one); its eigenform supplier is [R] once
repairs R2-R3 fix its coverage.

**Single next step.** In h-trust C8, adopt repairs R1-R3 of rv-h-c8 §8: fix the normalization, add
Deligne–Serre for `k = 1`, and name Saito 1997 (or Scholl + Scholze) as the supplier covering
`5 | N`. Then have a human check that supplier's locator.
