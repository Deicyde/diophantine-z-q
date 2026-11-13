# image-plane results log

Task: (G1') `ImagePlaneCurveClosed` (scratch/curve-glue/C3K.lean). Base f90cf864 + merges of
origin/wip/curve-glue and origin/wip/infra-smooth-dim.

Known (curve-glue, VERIFIED there): G1' <- (CI) + (G1''); (G1'') <- C2K + (CI) + (AD) + (IC);
C2K <- (L) <- (L0) leaf; (CI) proved from infra-smooth-dim.

## 1. (IC) `ImageClosed` PROVED (VERIFIED, compiled)
- File: scratch/image-plane/ImageClosed.lean (assembled by mk_ic.sh from IC_head, ICbase
  (verbatim copies from curve-glue C2K/C3K/AlgDep.part), IC.lean.part (new)).
- `theorem LeafQM.AV.Pin.imageClosed : ImageClosed` — 0 errors, axioms
  [propext, Classical.choice, Quot.sound] (run_ImageClosed.txt).
- General form `ImagePlane.image_closed`: X proper over K = K̄, any closed T ⊆ X, σ ρ : ToP1 X:
  the set {(σ p, ρ p) ∈ K²} over K-points p in T is V(S). Smoothness not used.
- Method: graph cut out in X ×_K Spec K[x][y] by f_σ = x on U_σ, x g_σ = 1 on V_σ (same for ρ, y);
  complement of a union of basic opens, so closed; image under pullback.snd closed
  (Mathlib `universallyClosed_snd`, `Scheme.Hom.isClosedMap`); S = vanishingIdeal of the image;
  closed points of the fibre are K-points (curve-glue's `exists_point_of_isLocallyClosed`).
