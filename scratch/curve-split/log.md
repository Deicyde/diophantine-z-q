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
