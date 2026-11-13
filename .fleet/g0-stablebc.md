# g0-stablebc (fleet summary)

**Result.** g0-split's missing piece 6, `StableHeightBaseChange`, is reduced in Lean to one smaller
glue statement, `HodgeLineBaseChange`, and the reduction compiles with no `sorry`.
`StableHeightBaseChange` (`h_F^st(A_L) = h_F^st(A)`, copied verbatim) follows from it by the
proved theorem `stableHeightBaseChange_of_hodgeLine`. `HodgeLineBaseChange` is about group models
alone: for a base change `𝒢'` of `𝒢`, the natural map `ψ` on `⋀^g ω` is semilinear and injective,
carries `⋀^g ω_𝒢` onto a spanning set of `⋀^g ω_{𝒢'}`, and is compatible with analytic
uniformizations. It is glue, not a leaf, STANDARD. No leaf is used. The piece is neither false
nor vacuous.

**Proved along the way (all axioms `[propext, Classical.choice, Quot.sound]`):**
- `groupModelBaseChangeExists`: h5-neron's glue H4b, which hit a kernel deterministic timeout
  there. The workaround: pasting lemmas proved over arbitrary schemes with `subst` on the square,
  instantiated afterwards, and one explicit `instIsMonHomComp` term.
- `baseChangeCompIso`: `(A_L)_M ≅ A_M` as group schemes.
- `modelHeight_eq_of_isHodgeBaseChange` and `secIndex_baseChange`: the Arakelov half of H4a.
  Base change of Hodge data preserves the model height, and `#(Λ'/𝓞'ψw) = #(Λ/𝓞w)^{[L':L]}`.
- `metrizationBaseChange_of_hodgeLine`: the Hodge data of `𝒢'`.
- Transport of group models along `(A_L)_M ≅ A_M`, and the infimum arguments.

**Reviews.** Two read-only model reviews, no human review. All the new glue statements are TRUE
and none is vacuous (docs §5).

**What compiles.**
- `scratch/g0-stablebc/StableBC.lean`: verbatim def-faltings block, then the new part; about 35 s.
- `scratch/g0-stablebc/SplitPlus.lean`: g0-split's `Split.lean` plus the new part, 2m42s. It
  proves `glueOutputs_of_leaves_hodgeLine`, g0-split's main theorem with `hBC` replaced by
  `HodgeLineBaseChange`.

**What remains.** `HodgeLineBaseChange` (size L): the stalk and cotangent map along
`𝒢' → 𝒢`, base change of `omegaAt` and `⋀^g`, and the pullback bijection of complex points,
compatible with `evalAt`/`jacDet`. Integration: replace h5-neron's commented-out H4b attempt by
`groupModelBaseChangeExists`, which removes `hbcE` from its H5. Replace `hBC` in `Split.lean` by
`HodgeLineBaseChange`.

Report: `docs/research/g0-stablebc.md`. Log: `scratch/g0-stablebc/log.md`.
