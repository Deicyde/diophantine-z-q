# h21-gchar (fleet summary)

**Result: step (b) of the queue10 verdict on `h21C` is closed in Lean.** TYZ's genus character `χ_{d₁,d₂}` is defined
over genuine objects:
* the character of `Cl_n = Gal(H_n/K_n)` attached to `K_n(√d₂*)`, `d* = (−1)^{(d−1)/2} d`, over the tree's
  `TYZSplit.IsExtChar`. `H_n` is Tau Ceti's Hilbert class field;
* read on ideal classes through Tau Ceti's Artin map: `tyzChiCl`.

`tyzChiCl_eq_gchar` proves that it equals the Legendre-symbol character `gchar n (divSet n d₂)` of `quadPeriod`, for
every odd squarefree `n`, every `d₂ ∣ n` and every class. The norm form is also proved:
* `χ([𝔞]) = (d₂*/N𝔞)` (Jacobi) for `N𝔞` prime to `2d₂`;
* the `d₁`-side form `(D₁/N𝔞)`;
* uniqueness from these values.

**Restated hypotheses** (each proved equivalent to the statement it restates):
* `h21G = H21GChar.TYZThm21SpanG`: h21c-steps' `h21S` with `quadPeriodTYZ`, i.e. TYZ's character;
* `h21PG = TYZThm21PairsG`: `h21C` with TYZ's character.

The restatement is independent of whether the character is attached to `d₂` or to `d₁` (`tyzThm21SpanG_iff_swap`).
This matters because TYZ's own definition (near L510) could not be re-read: `~/tyz-src` is absent on this host, so TYZ
line numbers are UNVERIFIED.

**Compiles** (standard axioms only; `lake env lean`):
* `scratch/h21-gchar/GChar.lean`;
* `scratch/h21-gchar/FoldCheck.lean`: hand fold of `Main.lean`, with `frozenTarget_h21G(')` and `frozenTarget_h21PG(')`;
* `scratch/h21-gchar/Discharges.lean`: `DISCHARGES [h21C] by H21GChar.tyzThm21PairsC_of_G`.

Fold spec: `scratch/h21-gchar/autofold.json` (manual: `h21C` is top level; new module `Contrib/OneProof/TYZThm21GChar.lean`
suggested). Kinds rows: `scratch/h21-gchar/kinds-rows.tsv`, with `h21G` (and alternative `h21PG`) of kind consequence,
flag pending review, GLUE/GLUE.

**Remains:**
* step (a) `lcalSq = 𝓛²` (task h21-lcal; separate files, the dictionaries compose);
* review of `h21G`;
* a check of TYZ's printed `χ_{d₁,d₂}` definition against `IsTYZChi` (both conventions are already covered);
* locator row (report §5).

Report: `docs/research/h21-gchar.md`.
