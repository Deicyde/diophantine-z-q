# h21-lcal (fleet summary)

**Result.** Step (a) of the queue10 verdict on `h21C` is proved in Lean with no new leaf. The step was
`lcalSq = 𝓛²`, which needs root number `+1` and the functional equation for `m ≡ 1, 3 (mod 8)`.
* `functionalEquationPlus_proof`: `Λ(2−s) = +Λ(s)` for `L(C_d,s)`, squarefree `d ≡ 1, 3 (mod 8)`, `N = 32d²`, on
  `0 < Re s < 2` (`FunctionalEquation5` with sign `+`). Proved from the in-tree Hecke theory over `ℤ[i]`; new parts:
  `L(C_d,s) = T_{¼c_d}` for every odd squarefree `d` (Deuring at 1 + twist + reciprocity), and the Fourier relation
  for `d ≡ 3 (mod 4)`.
* `analyticOrderAt_ne_one`: `ord_{s=1} L(C_d,s) ≠ 1` for the same `d`.
* `lcalSqPrinted R n`: TYZ's printed `𝓛²` (L338–353 as transcribed: split on the order, with an
  `L′/(Ω R)` branch and the regulator as a parameter). `lcalSqPrinted_eq`: it equals `lcalSq m` on squarefree
  `m ≡ 1, 3 (mod 8)` for every `R`. `lcalSqPrinted_one = 1`.
* `TYZThm21PairsPrinted ↔ TYZThm21PairsC` and `TYZThm21SpanPrinted ↔ TYZThm21Span` (h21c-steps).

**Compiles** (standard axioms only): `scratch/h21-lcal/H21Lcal.lean` (8 audited declarations) and
`scratch/h21-lcal/FoldCheck.lean`. The fold check imports `OneProof.Main` and has two variants: A, on the current
Main (`h21C → h21P`), and B, after h21c-steps (`h21S → h21SP`). Fold spec: `scratch/h21-lcal/autofold.json`. Kinds
rows: `scratch/h21-lcal/kinds-rows.tsv` (kind consequence, flag pending review). Count unchanged. The new files are
separate from h21-gchar's, so the two can be combined.

**Remains:**
* review of `h21P`/`h21SP`;
* re-reading TYZ L338–353 against the source, which is not on the host (the definition is from the project's
  transcriptions);
* step (b) (h21-gchar);
* integration (move `H21Lcal.lean` into `Contrib/OneProof/`). h21c-steps' FoldCheck names an older `frozenTarget`
  signature and must be re-applied on the current top.

Report: `docs/research/h21-lcal.md`.
