# derham-scholze (2026-11-17)

**Result.** I re-routed both research fields `deRhamVpAbVarDirect` and `hodgeTateDecompOr` to the manuscript's own
proof (`lem:de-rham-descent`, L10939-11004, step C3). Both are proved in Lean from two leaves:

* `DeRhamScholze.ScholzeDeRhamAlg` (new): for a finite `F/ℚ_p`, a proper smooth `X/F` and every `i`,
  `Hⁱ(X_{F̄}, ℚ_p)` is de Rham with Hodge jumps in `[0, i]`. The statement uses **Mathlib's `Scheme.EllAdicCohomology`**
  (pro-étale), with the Galois action by transport. Rated a *consequence* of Scholze 2013 Cor. 1.8 + Thms 9.1/9.3,
  not printed form, because Mathlib has no rigid-analytic spaces (known issue).
* `T10Etale.T10_TateDuality` (t10-etale's Milne leaf, reused; Milne AV Part I Thm 12.1(a)): unread.

Everything else is proved in Lean with the standard axioms only:

* duality and transport along Milne's identification;
* the manuscript's "consequently" (Fontaine: de Rham with jumps in `[0, 1]` ⇒ Hodge–Tate), via the gr maps and a
  twisted Tate–Sen lemma;
* Fontaine's `t`: `t = log[ε₀]` is a uniformizer of `B_dR^+` with `σ(t) = χ(σ)t`.

**What compiles.** Three files, all built:

* `ZInQKernel/Contrib/OneProof/DeRhamScholze.lean`
* `ZInQKernel/Contrib/OneProof/DeRhamScholzeHT.lean`
* `ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean`

`#discharges`: `deRhamVpAbVarDirect` by `DeRhamScholze.deRhamVpAbVarDirect_of_leaves`, and `hodgeTateDecompOr` by
`DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne`. Each still assumes exactly
`[ScholzeDeRhamAlg, T10_TateDuality]`, with standard axioms.

Autofold spec: `scratch/derham-scholze/autofold.json`. The dry run gives `strict 4/27 on 31 -> 4/27 on 31`, and the
fold module (`sixContactMin_of_open68`) compiles with standard axioms.

**What remains.**

* A reading of Milne's theorem, and the integrator's ruling on whether the manuscript's algebraic application of
  Cor. 1.8 counts as LEAF. Each would lower the GLUE count by 1.
* The fold itself.
* Not needed by these fields and not done: the descent to `K` and the coefficient-field step for `r`, and the Hodge
  numbers 2,2 (no `H_dR` in Mathlib).

Report: `docs/research/derham-scholze.md`.
