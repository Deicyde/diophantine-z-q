# pkg-I3 log (Faltings 1983, Mumford; steps A9, C2, E1, C10)

## Step 1 (2026-11-11): inventory and Tate module
- Mathlib v4.35.0 (VERIFIED by grep): `AlgebraicGeometry/Group/Abelian.lean` has
  `isCommMonObj_of_isProper_of_geometricallyIntegral` (proper geometrically integral group schemes
  over a field are commutative; Stacks 0BFD); `CategoryTheory/Monoidal/Cartesian/Grp.lean` has
  `Hom.commGroup` (morphisms into a commutative group object form a group);
  `RepresentationTheory/Semisimple.lean` has `IsSemisimpleRepresentation`;
  `FieldTheory/AbsoluteGaloisGroup.lean` has `Field.absoluteGaloisGroup`;
  `PadicInt.toZModPow`, `Algebra ℤ_[p] ℚ_[p]`. No Tate module, no abelian-variety Hom group,
  no Galois action on points (grep `TateModule`: no hit).
- `scratch/pkg-I3/I3.lean` §1: `PkgI3.Tate.T ℓ M` (sequences with x₀ = 0, ℓ•xₙ₊₁ = xₙ) with a
  `Module ℤ_[ℓ]` instance ((a•x)ₙ = (a mod ℓⁿ)•xₙ) and functoriality `Tate.map`.
  Compile: `lake env lean scratch/pkg-I3/I3.lean`, no errors, no sorry (VERIFIED).
