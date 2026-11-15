# r16-split (2026-11-15)

**Verdict.** `r16` (`LeafModCurves.R16_EichlerShimuraJ1'`) cannot be split today into Shimura 1971 Thm 7.9 and
Shimura 1973 Thm 1 as printed. Both theorems are about Hecke correspondences on `X₁(N)` and Shimura's `A_f`, and
those have no Lean definition. The definitions still missing:
- the quotient isogeny `E → E/C` (Vélu), needed for the second degeneracy map;
- above all, the Hecke-equivariant comparison `S₂(Γ₁(N)) ≅ H⁰(X₁(N)_ℂ, Ω¹)`, without which `I_f` cannot be
  defined.

The other pieces are now available or definable: models of `X₁(N)` (cloud-w07 `Xn`), morphisms from maps of
function fields (`exists_hom_of_valuationRing_stalk`), `Pic.map`, and `A_f` as an image instead of a quotient.
`docs/research/r16-split.md` §4 has the full table.

**Main result (compiled, standard axioms).** This is the smallest faithful split, in
`ZInQKernel/Contrib/OneProof/R16Split.lean`:
`R16Split.r16_of_printed : R16CoreY → mumfordTorsionAlgClosed → charPolyIndepOfEllAlgClosed → r16`.
- `R16CoreY` is r16 with the rank-two clause deleted, so it is a consequence of r16 (`coreY_of_r16`). It is not
  in printed form: it is a composite (GLUE) of Shimura 1973 Thm 1 and the Frobenius characteristic polynomial
  (Diamond–Shurman Thm 9.5.4).
- The rank-two clause, which the audit flagged as unsourced, is now proved. The argument uses `dim A = [K_f:ℚ]`,
  the rational traces from Mumford §19 Thm 4, nondegeneracy of the trace form and Dedekind independence.
- Alternative: `r16_of_coreX` (the dimension clause from the rank-two clause, using `TateModuleFree`).

**Checks.**
- `#discharges` shows `OpenResearchLeaves20.r16` discharged by `r16_of_printed`, `r16_of_coreY` and
  `r16_of_coreX`, all with standard axioms. The output is recorded in the report §6 and in
  `scratch/r16-split/Discharges-output.txt`.
- The autofold spec is `scratch/r16-split/autofold.json` (new leaf `r16CoreY`, kind composite). Its dry run
  leaves the counts at 47/11 and compiles: `sixContactMin_of_open28` has standard axioms.

**What remains.**
- Fold the spec. This is the integrator's step.
- To reach printed leaves: define Vélu isogenies, `T_p` and `⟨d⟩` on `J₁(N)`, and the `S₂ ↔ H⁰(Ω¹)` comparison.
