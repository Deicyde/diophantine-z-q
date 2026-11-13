# unram-tate (2026-11-13): UnramifiedSup and TateBridge from g0-mod-field

**Result.** Both glue Props are closed. Statements are copied verbatim from
`scratch/g0-mod-field/ModField.lean`; none was changed.

* **`UnramifiedSup` is proved, with no leaf** (`scratch/unram-tate/UnramSup.lean`,
  `UnramTate.unramifiedSup`). Proof: an inertia element of Gal((E⊔K)/ℚ) lifts to G_ℚ. Its
  restriction to E (resp. K) lies in that field's inertia group, which is trivial because
  #I = e = 1 (Mathlib's `card_inertia_eq_ramificationIdxIn`). So it fixes E ⊔ K, and therefore
  e = #I = 1. `TateBridge.lean` also gives g0-mod-field's composites without `hSup`
  (`fieldDescentUnr'`, `modularConstituent_of_ranges_T14'`).
* **`TateBridge` is proved from the existing leaf I3.M0 `PkgI3.TateModuleFree` alone**
  (`scratch/unram-tate/TateBridge.lean`, `UnramTate.tateBridge_of_tateModuleFree`). The leaf is
  used only for continuity. The assembly `tateBridge_of_pieces` builds:
  * Tm g = ℚ̄_ℓ⊗ℚ_ℓ⊗T_ℓ(Θ∘m_{hgh⁻¹}∘Θ⁻¹), with c = ε' = n/d, a = 1, β' = γ(h·h⁻¹);
  * matrix units from i² = 2, j² = −3 in 𝒪;
  * continuity via `rho_map_mul` and an open embedding.

  Each of its five pieces is proved:
  * `TatePoints`: points of a base change as a group isomorphism, Galois-natural (new; h5-glue
    had only a bijection);
  * `EndBaseChange` (bp-qmmoduli's `endBC`);
  * `ScalarTransfer`: β/a has algebraic values and is embedded into ℚ̄_ℓ;
  * `TateCont`: from the leaf and glue-rho-cont;
  * `ResQEmbedding`.

**What compiles (VERIFIED).** `lake env lean` on `UnramSup.lean`, `QuatUnits.lean`,
`BCPoints.lean` and `TateBridge.lean` gives exit 0, 0 errors and no sorry. All `#print axioms` give
[propext, Classical.choice, Quot.sound].

**What remains.** Nothing open in this task's scope. For integration:
* append the section `UnramTate` to `ModField.lean`, with the extra import
  `ZInQKernel.HDecomp.I3Linalg.RhoCont`;
* `UnramSup.lean` and `BCPoints.lean` can become HDecomp modules as they stand;
* deduplicate `endBC` with bp-qmmoduli's copy.

g0-mod-field's other open Props (`FibreCoverExists`, `KernelFieldExists`, the latter blocked by
qm-pin) were not touched. Report: `docs/research/unram-tate.md`; log: `scratch/unram-tate/log.md`.
