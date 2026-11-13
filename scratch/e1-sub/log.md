# e1-sub results log

- 22:57 built ZInQKernel.HDecomp.ModCurves.Glue, I3Linalg.C2, I3Linalg.TateBC (lake build, exit 0).
- 23:00 VERIFIED (compiled, `lake env lean scratch/e1-sub/VSurj.lean`, no errors):
  `E1Sub.homVK_surjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
   [NumberField K] (J A : AbVar K) (π : Hom J A) (hπ : Surjective π.hom.left) :
   Function.Surjective (homVK ℓ π)`; route: semisimple complement of the image, lattice
  clearing, Faltings Tate, injectivity of precomposition (`precomp_injective`, from Mathlib
  `ext_of_isDominant_of_isSeparated`, `A` reduced via `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`),
  flatness of ℤ_ℓ over ℤ. No Poincaré reducibility used.
