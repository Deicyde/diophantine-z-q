# piclft results log

Task: remove `picLocFinType` (PicDict.PicLocFinType, ZInQKernel/Contrib/OneProof/PicDictionary.lean:2201).
Base wip/leaf-fold33b c7fbc273; `git merge origin/main`: already up to date (2026-11-16 21:15).

## Findings (reading)
- `picardFunctor f` = fppf sheafification of `picardPresheaf f` (T ↦ Pic(X ×_S T)), over all of `Over S`
  (CloudW07 Picard/Sheaf.lean). VERIFIED (read).
- `PicDict.pushforwardUnitUniversal` is proved (PicDictionary.lean:2334), so `PicDict.Θ` (vendored Kleiman 9.2.5,
  `picardFunctorNormalizedIso`) is an iso: `toPicardFunctor A.X.hom` is surjective at every `T`. VERIFIED (read).
- CloudW07 `Scheme.Modules.exists_isFinitePresentation_pullback_iso_of_isLimit` (Modules/Limits/Objects.lean:335):
  fp module sheaves descend along directed inverse limits of qc separated schemes with affine transitions
  (EGA IV 8.5.2(ii) for modules). `exists_hom_of_affine_limit` / `exists_hom_eq_of_affine_limit` (Hom.lean):
  morphisms / equalities descend on affine limits. VERIFIED (read).
- Invertible ⇒ IsFiniteLocallyFree ⇒ IsFinitePresentation are instances in CloudW07. VERIFIED (read).

## Plan
(I) LFT criterion: if every `Spec B → X` over `K` factors through `Spec S`, `S ≤ B` a f.g. `K`-subalgebra, then
`X → Spec K` is LFT. (II) transfer through `rep` + surjectivity of `toPicardFunctor`. (III) Pic spreading out
(EGA IV 8.5.2 + 8.5.5 for invertible sheaves) on `A ×_K Spec B = lim A ×_K Spec S`.

## Results (2026-11-16, all VERIFIED = compiled with `lake env lean`)
- Step 1 `scratch/piclft/Criterion.lean`: `PicLFT.locallyOfFiniteType_of_fgFactor` — if every `Spec B → X` over `K`
  factors through `Spec S`, `S ≤ B` a f.g. `K`-subalgebra, then `X → Spec K` is LFT (retraction argument on each
  affine open: enlarge `S` by finitely many elements so `Spec S' → X` lands in `V`; then `Γ(V) → S' ⊆ Γ(V)` is a
  section, so `S' = Γ(V)`). Compiled, Mathlib only, 20 s.
- Step 2 `scratch/piclft/Reduce.lean`: `PicLFT.picLocFinType_of_spreadOut : PicSpreadOut → PicDict.PicLocFinType`
  (via `rep.homEquiv` naturality and surjectivity of `toPicardFunctor` from `PicDict.Θ` + `pushforwardUnitUniversal`).
- Step 3/4 `scratch/piclft/Spread.lean`: `PicLFT.invAtStage`: on a directed inverse limit of compact schemes with
  affine transitions, an fp module at a stage whose pullback to the limit is invertible is invertible at a later
  stage. Core `exists_iso_stage` (generic, over an affine limit: two applications of CloudW07
  `exists_hom_of_affine_limit` and two of `exists_hom_eq_of_affine_limit`), `triv_stage` (one affine open, via
  CloudW07 `preimageDiagram`/`isLimit_preimageCone`), assembly with Mathlib `isBasis_preimage_isAffineOpen`,
  `exists_map_eq_top`, `Scheme.compactSpace_of_isLimit`.
  Pitfall: a monolithic `triv_stage` had kernel type checking 207 s; splitting out the generic `exists_iso_stage`
  (over variables) brought the whole file to 30 s.
- Step 5 `scratch/piclft/Main.lean` (all parts in one file): `PicLFT.picSpreadOut : PicSpreadOut` from CloudW07
  `exists_isFinitePresentation_pullback_iso_of_isLimit` (EGA IV 8.5.2 for fp modules) + `invAtStage`, limit setup
  from CloudW06 `AdjoinFinset.specOverCone` (index `Finset B`, stages `K[s]`) and `isLimitBcF`.
  **`PicLFT.picLocFinType_proof : PicDict.PicLocFinType`**; `#print axioms`: [propext, Classical.choice, Quot.sound].
  No new leaf. 31 s.
- Universe pitfall: `SheafOfModules.IsInvertible` / `IsFinitePresentation` carry a universe parameter; instance
  search across `let`-bound modules or different universes fails — pass instances with `@` or re-derive via
  `isInvertible_iff_forall_exists_pullback_unit` (.1 then .2).
