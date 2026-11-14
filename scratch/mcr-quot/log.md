# mcr-quot results log

Targets: the glue Props A `FibreAutTame`, B `GenericQuotientP1`, C1 `CMSectionsDisjoint`,
C2 `CoordinateFromSections` of `scratch/mcr-glue/MCRGlue.lean` (copied verbatim as the prefix of
`scratch/mcr-quot/MCRQuot.lean`).

## Step 0 (06:50, 2026-11-14) — VERIFIED
- `scratch/mcr-quot/MCRQuot.lean` = `scratch/mcr-glue/MCRGlue.lean` verbatim. Needs
  `lake build ZInQKernel.Contrib.Mobius.Main ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue`.
- `lake env lean scratch/mcr-quot/MCRQuot.lean`: exit 0, 23 s (compile0_out.txt).
- Tau Ceti / Contrib check: no quotient-by-group, P¹-scheme or fixed-locus piece in
  ZInQKernel/Contrib (directory listing + grep for ToP1/Möbius: only `ImagePlane.inv` (swap charts)
  and the Möbius rigidity of `Contrib/Mobius`). Mathlib 4.35 has the commutative-algebra core of
  quotients: `Algebra.IsInvariant`, `Algebra.IsInvariant.exists_smul_of_under_eq` (transitivity on
  primes), `Ideal.Quotient.stabilizerHom_surjective` (decomposition group onto residue
  automorphisms) in `Mathlib/RingTheory/Invariant/Basic.lean`.
- Computation (py/units.py, VERIFIED): all 72 classes of `(𝒪/3𝒪)^×` (coordinates in the basis
  `1, i, (1+j)/2, (i+k)/2`) contain a unit of `𝒪` (reduced norm ±1) with coordinates in [-3,3].

## Step 1 (07:45) — VERIFIED (MCRQuot.lean = MCRGlue.lean + parts 1-2; exit 0)
- `MCRQuot.exists_unit_congr`: `u₀ ∈ 𝒪` invertible mod `3𝒪` ⇒ some `u ∈ 𝒪^×` with `u ≡ u₀ mod 3𝒪`
  (`𝒪^× ↠ (𝒪/3𝒪)^×`), from `unit_table` (81 cases by `fin_cases`, witnesses from py/units.py,
  checked by `decide`) and the norm form `nrdZ` (`nrdZ_mul`, by `ring`).
- `MCRQuot.TwistEq` (twist-equivalence of objects) with `trans'`, `symm'`, `twistEq_of_iso`.
- `MCRQuot.twistEq_of_mem_fibreAut`: given uniqueness of fibres at `ℚ̄`-points, elements of
  `fibreAut` preserve twist classes (closure induction).
- `MCRQuot.mem_orbit_of_twistEq` (T5 `TorsionStructure` as hypothesis): two `ℚ̄`-points with
  twist-equivalent fibres differ by an element of `fibreAut` (Hecke clauses + `Level3.torsor`
  + `exists_unit_congr` + moduli injectivity).

## Step 2 (08:30) — VERIFIED (parts 1-3; exit 0)
- `MCRQuot.exists_root_smul`, `MCRQuot.exists_comp_smul_eq` (pure algebra): for `A → B` with
  `Algebra.IsInvariant A B G`, `G` finite, two ring maps `φ φ' : B → K` (K a field) agreeing on `A`
  satisfy `φ' = φ ∘ (g • ·)` for some `g ∈ G`. (transitivity on primes + stabilizer onto residue
  automorphisms, both from Mathlib.)
- `MCRQuot.secMap`, `secAction` (the `MulSemiringAction` of `G` on `Γ(X, q⁻¹W)` for an
  `IsGQuotient`), `eq_of_appLE_eq` (a `K`-point is determined by its map on sections of an affine
  open containing it).
- **`MCRQuot.exists_eq_comp_of_isGQuotient`**: for `q : X → Z` with `IsGQuotient G q`, `G` finite,
  two `K`-points of `X` (any field `K`) with `y ≫ q = y' ≫ q` satisfy `y' = y ≫ g` for some `g ∈ G`.

## Step 3 (09:40) — VERIFIED (parts 1-4 + axioms part 9; exit 0; compile4_out.txt; all new
`#print axioms` = [propext, Classical.choice, Quot.sound]; no sorry)
- `MCRQuot.ev_eq_appLE`, `eq_of_ev_eq_chart`, **`val_injective_of_isP1Coordinate`**: an
  isomorphism onto `P¹_{ℤ_(p)}` by charts is injective on field points.
- `MCRQuot.exists_rat_of_fixed`: a Galois-fixed point of `P¹(ℚ̄)` is rational
  (`InfiniteGalois.mem_range_algebraMap_iff_fixed`).
- New glue Prop `MCRQuot.P1ThreePoints` (P¹ geometry over ℤ_(p), no literature): an isomorphism
  `ρ₀ : 𝒵 ≅ P¹_{ℤ_(p)}` and three `ℚ̄`-points with rational `ρ₀`-values and pairwise disjoint
  closures ⇒ some `ρ : 𝒵 ≅ P¹_{ℤ_(p)}` with values `0, ∞, −16/27` there.
- **`MCRQuot.coordinateFromSections_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
  (hN : P1ThreePoints) : CoordinateFromSections`** (glue C2 reduced; A is used only for
  `Finite (fibreAut 𝒴 𝒜)`). Finding: C2 as stated needs the finiteness of `fibreAut` (for an
  infinite group `IsGQuotient` does not force orbits = fibres: `ℤ` acting on `𝔸¹_ℚ` by translation
  has `IsGQuotient` onto `Spec ℚ`); A supplies it.
