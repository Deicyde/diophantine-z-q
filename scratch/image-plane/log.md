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

## 2. (AD) `AlgDep` PROVED from C1b + C2K + (CI) (VERIFIED, compiled)
- File: scratch/image-plane/AlgDepProof.lean (mk_ad.sh: IC parts + ADbase (verbatim defs of
  ConstOrOntoAlgClosed, ComponentIrreducible, SmoothStalkDimOne, AlgDep) + AD.lean.part).
- `theorem algDep_of (h1 : SmoothStalkDimOne) (h2 : ConstOrOntoAlgClosed)
   (hI : ComponentIrreducible) : AlgDep` — 0 errors, 0 warnings, axioms standard
  (run_AlgDepProof.txt). C1b and (CI) are proved (infra-smooth-dim, curve-glue).
- Lemma `ImagePlane.finite_of_closed_ssubset`: Noetherian scheme, closed points have stalk dim 1,
  W irreducible closed, Y ⊊ W closed ⇒ Y finite (chain x < η(Y') < η(W) gives coheight ≥ 2,
  Mathlib `ringKrullDim_stalk_eq_coheight`).
- Proof: σ constant ⇒ P = x − c or 1; else W \ V_σ = {σ = 0} finite, so finitely many u with
  (0,u) hit; pick u outside (K infinite); some Q ∈ S (IC equations) has Q(0,u) ≠ 0; P = Q.

## 3. C2K `ConstOrOntoAlgClosed` PROVED from (CI) alone (VERIFIED, compiled)
- Same file AlgDepProof.lean (+ C2Kproof.lean.part). `constOrOntoAlgClosed_of_CI
  (hI : ComponentIrreducible) : ConstOrOntoAlgClosed`, `algDep_of_CI h1 hI : AlgDep`; 0 errors,
  axioms standard; warnings only `if_neg`/`if_pos` deprecation.
- So the leaf (L0) FiniteGlobalSections is NOT needed for C2K (curve-glue derived C2K from L0).
- Proof: image_closed with ρ = σ: diagonal equations Q(x,x) show the finite values of σ on W form
  a finite set or all of K; finite ⇒ {σ = t} (closed: complement of two basic opens) and X∖U cover
  the irreducible W (Jacobson) ⇒ σ constant; same for 1/σ (charts swapped, `ImagePlane.inv`) gives ∞.
