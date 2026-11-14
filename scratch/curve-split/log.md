# curve-split results log

Rows: H-79 GenusX1Field, H-81 NormalCurveSmoothQ, H-82 GeomConnectedOfConstantFieldQ (Contrib/CurvesG),
H-85 CurveBijIso (scratch/model-glue/ModelGlue6.lean), H-83 ShimuraGoodReduction
(scratch/vert-witness/VertWitness.lean), H-41 x0Transitive (Contrib/RLeaf/IgusaX0.lean).

## H-41 X0Transitive
- `scratch/curve-split/X0Split.lean`: `CurveSplit.x0Transitive_of_igusaSL2X : IgusaSL2X → X0Transitive`,
  `x0Transitive_of_igusaGL2 : IgusaGL2 → X0Transitive`. COMPILED (lake env lean, 5 s), axioms standard. VERIFIED.
- Leaves already in kernel (ZInQKernel/Contrib/RLeaf/IgusaSL2.lean): IgusaSL2X (geometric part of Igusa 1959),
  IgusaGL2 (Igusa 1959). The modular-equation form (Lang Ch.5 §2 Thm 3) cannot be stated over Mathlib 4.35:
  no j-function / modular polynomial in Mathlib (grep of NumberTheory/ModularForms: VERIFIED absent).

## H-82 GeomConnectedOfConstantFieldQ
- `scratch/curve-split/CurvesGSplit.lean`: `CurveSplit.geomConnectedOfConstantFieldQ_of_zariski :
  ZariskiConn.ZariskiConnectedness.{0} → GeomConnectedOfConstantFieldQ`. COMPILED, standard axioms. VERIFIED.
- Leaf: kernel's `ZariskiConn.ZariskiConnectedness` (EGA III₁ 4.3.1 + 4.3.4, locators UNVERIFIED).
- Glue proved: `appTop_bijective_of_constantField` (Γ(X,𝒪) integral over ℚ by Mathlib
  `isIntegral_appTop_of_universallyClosed`, embeds in function field, ℚ alg. closed in F ⇒ Γ = ℚ);
  then `ZariskiConn.app_bijective_of_appTop_bijective`. Normality hypothesis unused. No finiteness leaf needed.

## H-81 NormalCurveSmoothQ
- `CurveSplit.normalCurveSmoothQ_of_regularSmooth : RegularSmoothPerfect → NormalCurveSmoothQ`. COMPILED,
  standard axioms. VERIFIED.
- New leaf `RegularSmoothPerfect` (Stacks 00TV, ⇐ direction, tag UNVERIFIED): k perfect, S finite type k-algebra,
  q prime, S_q regular (Mathlib IsRegularLocalRing) ⇒ ∃ g ∉ q, Algebra.Smooth k S_g.
- Glue proved: `isRegularLocalRing_stalk_of_normal` (stalk = Dedekind domain ⇒ regular, Mathlib instance),
  `mem_smoothLocus_of_regular` (leaf applied on affine charts with k = Γ(Spec ℚ, ⊤)), Mathlib
  `smoothLocus_eq_top_iff`, `smoothOfRelativeDimension_one` (Contrib.Dim stalk dimension at a closed point).
