# g0-mod-field (G2, G4, G7: fibre field, Hom field, scalar descent to L')

**Main result.** `scratch/g0-mod-field/ModField.lean` (1047 lines; it imports `ZInQKernel/HDecomp/`)
compiles with no `sorry`. All eleven `#print axioms` lines give `[propext, Classical.choice,
Quot.sound]` (VERIFIED). For every fibre context, `fieldDescentUnr` proves G7's output
`G7OutUnr u P` from three named glue Props and the B2 leaves (T14a, T14b, T15, T30, T31). The
glue Props are:
- `FibreCoverExists` (G2: Prop. TS + Lemma NV);
- `KernelFieldExists` (G4: Weil restriction, the Galois image in `GL_r(ℤ)`, and the conjugacy
  isogenies `ConjugacyData`);
- `UnramifiedSup` (a compositum of unramified fields is unramified; STANDARD).

`modularConstituent_of_ranges_T14` then proves g0-split's `ModularConstituent` (over
`PkgI3.AbVar`) from these and `AfterG7`, which bundles G8-G16.

**The interface `G7Data`.** It contains: the Hom field `L` (`[L:ℚ] ≤ D`); a QM model `A/L`
(the base change of a `QML3` object, so it has good reduction away from 3); its descent datum
(maps `m_σ = μ_σ∘σ` on `A(ℚ̄)`, algebraic through scheme maps `F_σ`, with `a_σ` and the sign
cocycle `ε`); `χ` of level `∏_{p∈T₋} lev p`; `β` with `β² = χ`, `∂β = ε`; and
`L' ⊇ L` with `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`, `L'` unramified outside `T`,
and `A_{L'}` a model.

**Proved Lean.** G2's degree bookkeeping. B1's normalization (`descentDatum_of_conjugacy`). G4's
Minkowski bound and model by base change. B2-B3 with B3(v)'s twist (`b2_of_leaves_level`,
`b3_of_cochain`, `unramified_outside_noLeaf`). Transitivity of base change. The bridge to
g0-mod-galois' `G2Out` (`galoisG2Out_of_g7Data`), with `ResQRange` proved: the image of
`Field.absoluteGaloisGroup.map` for a finite Galois `L'` is `Fix(L')`. A sanity check that
`DescentDatum` is satisfiable (`descentDatum_bot`).

**Found and repaired (model checks).** Four problems in the interface:
1. `KernelFieldExists` quantified over all `K`-models, which is false: a twist ramified outside
   `T` can have bad reduction. It now quantifies over rational fibres only (`RationalFibre`).
2. The same problem for `AfterG7`. `G7Data`'s model must now be a QM model (`IsQMModel`).
3. The level of `χ` was unconstrained, which would break G15. It is now exposed and bounded.
4. `a_σ` was unconstrained on `G_L`. It now has `a = 1` there, inflated.

**Remains.** `FibreCoverExists`, `KernelFieldExists`, `UnramifiedSup`, and `TateBridge`: from
`G7Data` to g0-mod-galois' per-`ℓ` `G7Out` (Tate functor on `m_σ`, coefficients in `ℚ̄_ℓ`, matrix
units). `TateBridge` is stated in Lean, not proved. Every truth claim about the Props is a model
check, with no human review.

Report: docs/research/g0-mod-field.md. Log: scratch/g0-mod-field/log.md.
