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

## Step 3: leaves (compile)
Seven leaf Props in `I3.lean` §3, bundled in `structure I3Leaves`:
- `FaltingsSemisimple` (Faltings 1983 Satz 3): `(A.galRep ℓ).IsSemisimpleRepresentation` for
  every abelian variety over every number field, every prime ℓ.
- `FaltingsTate` (Satz 4 for A = B, Korollar 1): `tateHomZl ℓ A B` injective and its range is
  `{φ | IsGalEquivariant φ}`.
- `TateModuleFree` (Mumford §4 / §§18-19): T_ℓ(A) free, finite, rank 2·dim A, for ℓ ≠ char k.
- `HomFreeFinite` (Mumford §19 Thm 3): Hom(A,B) free f.g. over ℤ, rank ≤ 4 dim A dim B, and
  ℤ_ℓ ⊗ Hom → Hom(T_ℓ, T_ℓ) injective for ℓ ≠ char k.
- `CharPolyIndepOfEll` (Mumford §19 Thm 4): ∃ monic P ∈ ℤ[X] equal to the charpoly of V_ℓ(φ) in
  any finite basis, for every ℓ ≠ char k.
- `PoincareReducibility` (Mumford §19 Thm 1, E1 form, char 0): End⁰(A) division (every nonzero
  endomorphism finite surjective), f : A → J nonzero ⇒ ∃ Z, g with (f, g) : A × Z → J finite
  surjective.
- `QMDichotomy` (A9): k alg. closed char 0, dim A = 2, (a,b)_ℚ division embedding in End⁰(A) ⇒
  End⁰(A) ≅ (a,b)_ℚ or M₂(ℚ(√d)), d < 0. (Consequence of several Mumford results; single
  refereed locator UNVERIFIED.)
Compile: no errors (VERIFIED).

## Step 4: glue checks (compile, no sorry; axioms propext, Classical.choice, Quot.sound)
- `range_tateHomZl_subset`: range ⊆ equivariant maps holds outright (non-vacuity check: the
  leaf's content is exactly injectivity + the reverse inclusion).
- `exists_hom_ne_zero_of_equivariant` (E1 glue): `FaltingsTate → TateModuleFree →` a nonzero
  G_K-equivariant ℚ_ℓ-linear map V_ℓA → V_ℓB gives a nonzero f : Hom A B. Proof uses Mathlib's
  `Module.FinitePresentation.exists_lift_of_isLocalizedModule` (clearing denominators).
- `#print axioms` on both and on `AbVar.galRep`: [propext, Classical.choice, Quot.sound]
  (VERIFIED). `grep -c sorry I3.lean` = 0.

## Step 5: base change, inhabitant, C2 glue statement
- `AbVar.baseChange A L : AbVar L` via `Over.pullback` + `Functor.grpObjObj` (proper, smooth,
  geometrically integral by Mathlib base-change instances). Compiles (VERIFIED).
- `AbVar.zero K` (`Spec K`), with a new instance `GeometricallyIntegral (𝟙 (Spec K))` (proved).
  Mathlib v4.35.0 has no projective group scheme besides this one: `EllipticCurve/` has no
  `Scheme`, and `GrpObj` occurs in `AlgebraicGeometry/` only in `Group/{Abelian,Affine,Smooth}`
  and `Pullbacks` (VERIFIED by grep). So no nonzero `AbVar` can be built today.
- `equivEnd A ℓ` (G-equivariant ℚ_ℓ-endomorphisms of V_ℓA, a submodule) and
  `finrank_equivEnd` (GLUE for C2: dim End_G(V_ℓA) = rank End A from FaltingsTate,
  TateModuleFree, HomFreeFinite): statement compiles, body `sorry` with outline.
- Repository evidence for Faltings locators: `docs/theorem-application-audit/INVENTORY.md`
  A008 (page images checked 2026-11-05: §5, Satz 3 and Satz 4, printed p. 360; erratum p. 381
  does not withdraw them); `docs/reviews/height-replacement/descent/AUDIT.md` item (Kor. 1,
  pp. 360-361). AUDIT-READ, not read here.

## Step 6: report
- `docs/research/pkg-I3.md` written: uses (N5 L564-575, L731-734, L768-795, L861-867, L545-548;
  VERIFIED by reading), published statements with marks, the seven leaves with faithfulness
  notes, Mathlib inventory, glue by step, the Jacobian question, obstacles.

## Step 7: C2 glue proved
- `finrank_equivEnd` proved (no sorry): `finrank ℚ_ℓ (equivEnd A ℓ) = finrank ℤ (End A)` from
  `FaltingsTate`, `TateModuleFree`, `HomFreeFinite`. Route: `ET` (equivariant ℤ_ℓ-endos of T_ℓ)
  ≅ ℤ_ℓ ⊗ End A via `tateHomZl` (shown ℤ_ℓ-linear); `Φ : ET → equivEnd`, ψ ↦ ψ ⊗ ℚ_ℓ, is
  `IsLocalizedModule ℤ_ℓ⁰`; then `IsLocalization.finrank_eq`, `IsLocalizedModule.finrank_eq`,
  `Module.finrank_baseChange`.
- `#print axioms` for `finrank_equivEnd`, `exists_hom_ne_zero_of_equivariant`, `AbVar.zero`,
  `AbVar.baseChange`: [propext, Classical.choice, Quot.sound]. `grep -c sorry I3.lean` = 0.
  Whole file compiles with no errors (VERIFIED).
