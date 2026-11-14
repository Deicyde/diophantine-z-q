# mcr-quot: the glue Props A, B, C1, C2 under `ModelCoordinateResidue`

Task mcr-quot, 2026-11-14 (two runs; the second resumed from `scratch/mcr-quot/log.md`). Base
`origin/main` (f70ec251). Targets: the four glue Props that mcr-glue left under
`ModelGlue.ModelCoordinateResidue` (`scratch/mcr-glue/MCRGlue.lean`, docs/research/mcr-glue.md §4):

- A `FibreAutTame`;
- B `GenericQuotientP1`;
- C1 `CMSectionsDisjoint`;
- C2 `CoordinateFromSections`.

Lean file: `scratch/mcr-quot/MCRQuot.lean`. It is `MCRGlue.lean` verbatim (the whole file),
followed by the parts `MCRQuot1.lean.part` … `MCRQuot16.lean.part` in the order of `build.sh`.

## 1. Main result

**C2 is proved from A and T5. A and C1 are proved from two textbook-level inputs and one glue Prop
on CM stabilizers. B is reduced to two glue Props.** All of this is by compiled Lean proofs. No
target statement was changed.

| Target | Compiled theorem | Remaining inputs |
|---|---|---|
| C2 `CoordinateFromSections` | `coordinateFromSections_of''` | A (used only for `Finite (fibreAut 𝒴 𝒜)`), T5 |
| A `FibreAutTame` | `fibreAutTame_of''` + `fibreAutFixFinite_of'` | T5, `CurveBijIso`, `ModelYIrreducible` |
| C1 `CMSectionsDisjoint` | `cMSectionsDisjoint_of''` + `fibreAutFixFinite_of'` | A, `CurveBijIso`, `ModelYIrreducible`, (C1b) `CMStabInvolution` |
| B `GenericQuotientP1` | `genericQuotientP1_of` | A, T5, L3, (B-desc) `QuotientDescendsQ`, (B-iso) `ToP1BijIsCoordinateQ` |

Notes on the inputs:

- L5 and L6 are hypotheses of C1's own statement. L3 is mcr-glue's leaf.
- T5 is the kernel's textbook leaf `ObjBridge.TorsionStructure`.
- `CurveBijIso` is model-glue's textbook leaf (it is in the prefix).
- `ModelYIrreducible` says that `Y` is irreducible over `ℚ`. It is proved from the decomposition's
  existing glue `CoverModelOfHeckeN` together with T5 (`modelYIrreducible_of_coverModelN`).

The final composite (namespace `MCRQuot`):

```lean
theorem modelCoordinateResidue_final5
    (hAF : ProperCurveAF) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth)
    (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic)
    (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso) (hCov : CoverModelOfHeckeN)
    (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ) (hI : CMStabInvolution) :
    ModelCoordinateResidue
```

Its hypotheses fall into four groups:

- mcr-glue's leaves L1–L6;
- the textbook leaves T5 and `CurveBijIso`;
- the decomposition's existing glue `CoverModelOfHeckeN`;
- **three new glue Props of this task**: (B-desc), (B-iso), (C1b).

`modelCoordinateResidue_final4` is the same theorem with `ModelYIrreducible` in place of
`CoverModelOfHeckeN`.

VERIFIED: `lake env lean scratch/mcr-quot/MCRQuot.lean` exits 0 in about 27 s (output in
`compile16_out.txt`).

- The parts contain no `sorry` and no `axiom`.
- All 39 `#print axioms` of `MCRQuot` declarations (part 9) read
  `[propext, Classical.choice, Quot.sound]`.

## 2. What was proved (all compiled, namespace `MCRQuot`)

### 2.1 Glue Props of this task, proved outright

| Name | Statement | Proof |
|---|---|---|
| (C2-T) `P1Translate` | for `ρ : 𝒵 ≅ P¹_{ℤ_(p)}` by charts and `e ∈ ℤ_(p)`, `ρ + e` is again an isomorphism by charts, with values shifted by `e` | `p1Translate` (part 14), described in §2.2 |
| (C1c) `StabFixesClosure` | an automorphism over `ℤ_(p)` fixing a `ℚ̄`-point `y` fixes every field point over the closure of the point of `y` | `stabFixesClosure` (part 13). The equalizer of `h` and `id` in `Over S` is a closed subscheme (Mathlib's `isClosedImmersion_equalizer_ι_left`, Stacks 01KM; only `IsSeparated` is needed). A field point over the range of a closed immersion factors through it (`exists_factor_of_mem_range_closedImm`). Smoothness and EGA IV 8.13.1 are not needed |
| (C1a) `GQuotientPointOrbits` | the points over a point of an SGA 1 quotient form one orbit | `gQuotientPointOrbits` (part 10, first run) |
| (C1d) `QbarPointsConjugate` | two `ℚ̄`-points with the same underlying point are Galois conjugate | `qbarPointsConjugate` (part 10, first run) |
| (A-count) `TwistClassCard` | a twist class has at most 324 isomorphism classes | `twistClassCard` from T5 (part 11, first run) |
| (A-dim) `CurveClosedQbarFinite` | for `𝒴` integral, proper, smooth of relative dimension 1 over `ℤ_(p)`: a closed `Z ∌ η` carries finitely many `ℚ̄`-points | `curveClosedQbarFinite` (part 16), described below |

How `curveClosedQbarFinite` is proved:

1. Every point of `Z` in the generic fibre is closed there. Otherwise a chain `η ⤳ x ⤳ z` of
   length 2 would lie above a closed point `z`. This contradicts the kernel's
   `smoothStalkDimOne`, via `ringKrullDim_stalk_eq_coheight`.
2. A closed set of closed points in a Noetherian quasi-sober space is finite
   (`finite_of_isClosed_of_closedPoints`).
3. A closed point of a `ℚ`-scheme of finite type has a residue field finite over `ℚ`. This is
   Zariski's lemma (Mathlib's `finite_of_finite_type_of_isJacobsonRing`), applied through the
   closed immersion `Spec κ(x) → X`. Hence only finitely many `ℚ̄`-points lie over each closed
   point (`finite_qbarPts_over_closed`).

### 2.2 `P¹` over `ℤ_(p)` by charts (PGL₂ generators)

| Declaration | Content |
|---|---|
| `isP1Coordinate_inv`, `val_inv` | `t ↦ 1/t` (the kernel's `ImagePlane.inv`) |
| `scale`, `isP1Coordinate_scale`, `val_scale` | `t ↦ u t`, `u ∈ ℤ_(p)^×` |
| `translate`, `isP1Coordinate_translate`, `val_translate` | `t ↦ t + e`, `e ∈ ℤ_(p)` |
| `val_injective_of_isP1Coordinate` | an isomorphism by charts is injective on field points |
| `isUnit_sub_of_disjoint` | two `ℚ̄`-sections with values `a, a' ∈ ℤ_(p)` and disjoint closures have `a − a'` a unit |
| `p1ThreePoints_of` | three rational sections with pairwise disjoint closures can be moved to `0, ∞, −16/27` |

How `translate` is built:

- The new charts are `U' = U`, `f' = f + e`, and `V' = D_V(1 + e g) ∪ D_U(f + e)`. The function
  `g'` is glued (`objSupIsoProdEqLocus`) from `g/(1 + eg)` and `1/(f + e)`.
- `V'` is affine by Mathlib's `isAffineOpen_of_isAffineOpen_basicOpen` (Stacks 01QF). The spanning
  pair is `g'` and `1 − e g'`, whose basic opens are `D_U(f + e)` and `D_V(1 + e g)`
  (`basicOpen_tg`, `basicOpen_tH`).
- The map `ℤ_(p)[Y] → Γ(V')`, `Y ↦ g'`, is surjective (`surjective_g'`). On each basic open, a
  section is a polynomial in `g'` up to a power (`exists_poly_DU`, `exists_poly_DV`, using
  `eval₂_reflect_mul_pow`). The powers are cleared in the localizations
  (`exists_pow_mul_eq_of_res`), and `Y^a` and `(1 − eY)^b` are coprime.
- The same map is injective (`injective_g'`): `Γ(U)` is a domain, the localization map is
  injective, and `reflect` is injective.

### 2.3 Quotients by finite groups, QM algebra (first run)

- `exists_eq_comp_of_isGQuotient`: the `K`-points of an SGA 1 quotient by a finite group are the
  orbits.
- `exists_unit_congr`: `𝒪^× ↠ (𝒪/3𝒪)^×`. Explicit units for the 72 classes were found by
  `py/units.py` and are checked by `decide`.
- `TwistEq`, `twistEq_of_mem_fibreAut`, `mem_orbit_of_twistEq` (T5): the orbits of `fibreAut` are
  the twist classes.

### 2.4 The reductions of A, C1, B (glue A-fix is proved from inputs)

- **(A-fix) `FibreAutFixFinite`**, by `fibreAutFixFinite_of` (part 15):
  - `𝒴` is integral (`isIntegral_model`). This is model-glue's `modelIntegral_of` argument, with
    `ModelYIrreducible` in place of the chart.
  - The fixed locus of `h` is a closed subscheme. If it held infinitely many `ℚ̄`-points it would
    contain `η` (`CurveClosedQbarFinite`).
  - Then it is everything, so `h = 1` (`eq_one_of_genericPoint_fixed`, using Mathlib's
    `isIso_of_isClosedImmersion_of_surjective`).
- **A**, by `fibreAutTame_of`: pick a `ℚ̄`-point off the finitely many fixed points of the
  elements `s⁻¹t`. Then `s ↦ y ≫ s` injects `fibreAut` into a twist class of size ≤ 324 < p.
- **C1**, by `cMSectionsDisjoint_of`: the inertia group at a common point of the two closures is
  cyclic (L6). So the involutions fixing the two CM points agree, and L5 gives disjointness.
- **C2**, by `coordinateFromSections_of`: the fibres of `ρ₀ ∘ q` are the twist classes, and the CM
  values are rational. Then `p1ThreePoints_of` normalizes the coordinate.
- **B**, by `genericQuotientP1_of`: `π ∘ g` descends to `𝒵_ℚ` (B-desc) and is bijective on
  `ℚ̄`-points, hence a coordinate (B-iso).

## 3. What remains: three new glue Props and one input

| Name | Statement (informal) | Kind | Why not proved here |
|---|---|---|---|
| (B-desc) `QuotientDescendsQ` | an orbit-invariant `σ : 𝒴_ℚ → P¹` descends through the SGA 1 quotient to `𝒵_ℚ`, and `ℚ̄`-points of `𝒵_ℚ` lift | glue (quotients; SGA 1 Exp. V §1, locator UNVERIFIED) | needs that the quotient commutes with `ℤ_(p) → ℚ`, plus saturated opens |
| (B-iso) `ToP1BijIsCoordinateQ` | a map to `P¹` of a proper smooth `ℚ`-curve that is bijective on `ℚ̄`-points is an isomorphism by charts | glue (the `P¹` case of `CurveBijIso`) | Mathlib 4.35 has no `P¹` as a scheme (no `ProjectiveSpace` under `AlgebraicGeometry/`), so `CurveBijIso` cannot be applied |
| (C1b) `CMStabInvolution` | the stabilizer in `fibreAut` of a CM point contains an involution `≠ 1` | glue (QM with CM) | see below |
| `ModelYIrreducible` | `Y` (with R1fp, R1hecke, R2fp) is irreducible over `ℚ` | input; proved from `CoverModelOfHeckeN` + T5 | — |

Why (C1b) is not proved here (SPECULATIVE analysis, not compiled):

- **CM by `ℤ[i]`.** The case can be done from what exists. The CM unit `φ` acts on `A[3]` as
  `·u` with `u ∈ 𝒪^×` (`Level3.torsor`, `exists_unit_congr`). Then `rightMul u` fixes the point,
  and `u² ≡ −1` acts trivially. This route also needs that automorphisms are determined by
  `ℚ̄`-points (available from `CurveClosedQbarFinite`) and the rigidity of level-3 structures.
- **CM by `ℤ[ζ₃]`.** The unit `ζ₆` only gives an element of order 3 on points. The involution in
  the order-6 stabilizer is an Atkin–Lehner-type twist.
- **CM by `ℤ[√−6]`.** `φ² = −6` gives no unit. The involution would be `ι(ij)⁻¹ φ`, which needs
  integrality in `End A`.
- Both of the last two cases need the normalizer of `ι(𝒪)` in `End(A)` at CM points. That is not
  among the leaves.
- An alternative route is through `CoverBranchData`: the ramification indices 4, 6, 2 are even,
  and in characteristic 0 the stabilizers are the inertia groups. That route needs the
  identification of `fibreAut` with `Gal(E/ℚ(X))`.

## 4. Findings

- **C2 needs the finiteness of `fibreAut`, which is glue A.** For an infinite group,
  `IsGQuotient` does not make the fibres of `q` the orbits. Example: `ℤ` acting on `𝔸¹_ℚ` by
  translation has `IsGQuotient` onto `Spec ℚ`.
- **B needs `𝒵` proper and smooth**, which B's statement does not assume. Leaf L3 supplies it.
- **A and C1 need `Y` (equivalently `𝒴`) to be irreducible over `ℚ`.** Their hypotheses (R1fp,
  R1hecke, R2fp as clause lists, `IsShimuraModel`) carry no normalization chart. model-glue
  derives the irreducibility from such a chart (`irreducible_of_chart`). Here it enters as
  `ModelYIrreducible`, discharged by the decomposition's `CoverModelOfHeckeN`.
  - It is true for `Y₃`: `π₀ ≅ (ℤ/3)^×` and the two geometric components are Galois conjugate.
    This is a SPECULATIVE reading; the locator is UNVERIFIED.
  - A, C1 and `ModelCoordinateResidue` themselves were not changed.
- **The glue (C1c) needs neither smoothness nor spreading out.** Separatedness alone gives a
  closed fixed locus.
- **Own glue amended (not targets):**
  - `TwistClassCard`: bound 288 → 324.
  - `QuotientDescendsQ`: added that `𝒴` is proper and smooth.
  - `CurveClosedQbarFinite`: added `IsProper`. Without quasi-compactness it is false: the affine
    line with infinitely many doubled points is integral and smooth, and its doubled points form an
    infinite closed set missing `η`.
- No target statement was found false, vacuous or inert.

## 5. Checks

- Statement review (first run, by a separate model, read-only): every new glue Prop was found true
  as stated, except `QuotientDescendsQ`, which was then amended (§4).
- Tau Ceti and `Contrib` were checked first. They have no quotient-by-group, no `P¹`-scheme and no
  fixed-locus piece. The only related piece is `ImagePlane.inv`, which is used.

## 6. Reproduce

```
lake build ZInQKernel.Contrib.Mobius.Main ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue
scratch/mcr-quot/build.sh                      # regenerates MCRQuot.lean from the parts
lake env lean scratch/mcr-quot/MCRQuot.lean    # exit 0, ~27 s; compile16_out.txt
```
