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

## Step 2: abelian-variety layer (compiles, no sorry)
- `PkgI3.AbVar K` (structure: `X : Over (Spec K)`, `GrpObj X`, `IsProper`, `Smooth`,
  `GeometricallyIntegral`); commutativity derived from Mathlib's
  `isCommMonObj_of_isProper_of_geometricallyIntegral` (an instance, not a field).
- `AbVar.homGroup A B : Subgroup (A.X ⟶ B.X)` = morphisms with `IsMonHom`; `Hom A B` its
  `Additive`; `End A` with a `Ring` instance (product = composition); `End0 A = ℚ ⊗[ℤ] End A`.
- `AbVar.Pt L A = (Spec L as K-scheme ⟶ A.X)`, `galHom σ = Spec.map σ`, `galAct` (a monoid
  hom; `galHom_one`, `galHom_mul` proved: left action), `ptMap f`.
- `AbVar.T ℓ A = Tate.T ℓ A(K̄)`, `AbVar.V ℓ A = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ A`,
  `galRep ℓ A : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (V ℓ A)` (monoid-hom laws
  proved), `tateHom`, `tateHomZl : ℤ_ℓ ⊗[ℤ] Hom A B →ₗ[ℤ] (T_ℓ A →ₗ[ℤ_ℓ] T_ℓ B)`,
  `IsGalEquivariant`, `IsIsogenyMor` (finite and surjective), `dim` (topological Krull dim).
- Compile: `lake env lean scratch/pkg-I3/I3.lean` → no output (VERIFIED).
