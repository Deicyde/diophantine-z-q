# Results

- Base: `4ba51ebc2ab8f5de3f7a4492efab4421efb7428c` merged with `2293288bdd68df76586788b6c80e3927e7220d9b`.
- `Scalars.lean`: \(p\ne\ell_0\) admits integral A, B with \((2A-1)^2+(2B)^2=-\ell_0\). Odd case: residue sum of squares and unit derivative. Dyadic case: Hensel at one, with second coordinate zero or two. Compile and axiom audit passed.
- `Ramification.lean`: `AppF.RamifiedExactlyAtEll0Infty ell (-1) (-(ell : ℚ))`. Isotropic vector away from the detecting prime: \((2A-1,2B,1,0)\). Anisotropy: existing real positivity and local reduced norm theorems. Compile and axiom audit passed.
- Lattice.lean: completion membership iff all four coordinates on the explicit order basis lift from the local integers. Compile passed.
- MatrixModel.lean: explicit split profile for every prime away from the detecting prime, including two; level-one IsEichler from the detecting-prime maximality clause. Matrix inverse uses the inverse of the unit \(-\ell_0\). Compile passed.
- All four files checked sequentially with lake env lean. All 15 theorem axiom audits passed: propext, Classical.choice, Quot.sound only.
