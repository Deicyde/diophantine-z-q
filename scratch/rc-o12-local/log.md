# rc-o12-local results

Base: `71d379283cea3d3650e7bd8c2b23ecb58163a7e7`.

| Statement / finding | Outcome |
| --- | --- |
| Tex 9816–9840: evaluate the `Fin p` translates at 1 in actual `GL₂(ℚ_p)`. | `Newvector.lean`: three theorems pass. Complex proof uses `Padic.norm_p`; algebraic proof uses the same transported half-modulus as Carayol. |
| Tex 9799–9811: central congruence units fix any (K_1)-fixed vector. | `Conductor.lean`: six theorems pass, including conductor (1), ordered characters and dimension (1) at the allowed level. |
| Tex 9784–9797: arbitrary arithmetic Frobenius lift. | Reciprocity image is inverse uniformizer **modulo units**. The first inducing character and the half-modulus are trivial on those units. |
| Tex 9848–9854: compares a change at (p) to the full finite argument at (p n). | Away from (p), the diagonal factor is a level matrix with lower-right entry (1); the Whittaker model needs this right invariance. |
| Exact base imports. | Rebuilt changed transitive dependencies in order; prior O12 artifacts predated the Round 4 `GaloisConstituentModel` interface. |
| Tex 9819–9824: conjugation by the level matrix and the two fixed-space tests. | Convention.lean: three theorems pass. |
| Tex 9836: BK0(p) support, the lower-right character, and normalization at 1. | Support.lean: nine theorems pass. |
| Tex 9828–9835: affine residue permutation and level-one right factors. | Cosets.lean: three theorems pass. |
| Tex 9778–9797, 9810–9811: both duals, inertia signs, Frobenius value. | Galois.lean: five theorems pass. |
| Tex 9840, 9855–9861: the stable newvector line and its copies. | Ramified.lean: four theorems pass. |
| Tex 9841–9856: away-component level test and Whittaker shift. | Whittaker.lean: two theorems pass. |
| Tex 9754–9771, 9866–9873: disjoint sectors, normalized eigenform scalar at p, and LocalInput. | Blocks.lean: twelve theorems pass. |
| Final sequential check using lake env lean -j1. | All nine modules exit successfully; all 47 axioms reports contain only propext, Classical.choice, and Quot.sound. |
