# mcr-quot: the glue Props A, B, C1, C2 under `ModelCoordinateResidue`

Task mcr-quot, 2026-11-14 (two runs; the second resumed from `scratch/mcr-quot/log.md`). Base
`origin/main` (f70ec251). Targets: the four glue Props that mcr-glue left under
`ModelGlue.ModelCoordinateResidue` (`scratch/mcr-glue/MCRGlue.lean`, docs/research/mcr-glue.md §4):

- A `FibreAutTame`;
- B `GenericQuotientP1`;
- C1 `CMSectionsDisjoint`;
- C2 `CoordinateFromSections`.

Lean file: `scratch/mcr-quot/MCRQuot.lean`. It is `MCRGlue.lean` verbatim (the whole file),
followed by the parts `MCRQuot1.lean.part` … `MCRQuot22.lean.part` in the order of `build.sh`.

## 1. Main result

**All four targets are proved by compiled Lean from leaves plus two remaining glue Props.**

- **C2** is proved from A and T5.
- **A** is proved from T5 and the textbook-level inputs `CurveBijIso` and `ModelYIrreducible`.
- **C1** is proved from A, those same inputs, and one object-level glue Prop on CM points
  (`CMStabObj`).
- **B** is proved from A, T5, L3 and one glue Prop, the `P¹` case of `CurveBijIso` stated by charts
  (`ToP1BijIsCoordinateQ`).

No target statement was changed.

| Target | Compiled theorem | Remaining inputs |
|---|---|---|
| C2 `CoordinateFromSections` | `coordinateFromSections_of''` | A (used only for `Finite (fibreAut 𝒴 𝒜)`), T5 |
| A `FibreAutTame` | `fibreAutTame_of''` + `fibreAutFixFinite_of'` | T5, `CurveBijIso`, `ModelYIrreducible` |
| C1 `CMSectionsDisjoint` | `cMSectionsDisjoint_of''` + `cMStabInvolution_of` | A, `CurveBijIso`, `ModelYIrreducible`, (C1b-obj) `CMStabObj` |
| B `GenericQuotientP1` | `genericQuotientP1_of'` | A, T5, L3, (B-iso) `ToP1BijIsCoordinateQ` |

Notes on the inputs:

- L5 and L6 are hypotheses of C1's own statement. L3 is mcr-glue's leaf.
- T5 is the kernel's textbook leaf `ObjBridge.TorsionStructure`.
- `CurveBijIso` is model-glue's textbook leaf (it is in the prefix).
- `ModelYIrreducible` says that `Y` is irreducible over `ℚ`. It is proved from the decomposition's
  existing glue `CoverModelOfHeckeN` together with T5 (`modelYIrreducible_of_coverModelN`).

The final composite (namespace `MCRQuot`):

```lean
theorem modelCoordinateResidue_final8
    (hAF : ProperCurveAF) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth)
    (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic)
    (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso) (hCov : CoverModelOfHeckeN)
    (hB : ToP1BijIsCoordinateQ) (hO : CMStabObj) : ModelCoordinateResidue
```

Its hypotheses fall into four groups:

- mcr-glue's leaves L1–L6;
- the textbook leaves T5 and `CurveBijIso`;
- the decomposition's existing glue `CoverModelOfHeckeN`;
- **two new glue Props of this task**:
  - (B-iso) `ToP1BijIsCoordinateQ`: the `P¹` case of `CurveBijIso`, stated by charts;
  - (C1b-obj) `CMStabObj`: each CM class is fixed by a Hecke operation of order exactly 2 on
    classes, a statement about QM objects over `ℚ̄` with no schemes in it.

The earlier composites `modelCoordinateResidue_final4` … `final7` are the intermediate forms.

VERIFIED: `lake env lean scratch/mcr-quot/MCRQuot.lean` exits 0 in about 30 s (output in
`compile22_out.txt`).

- The parts contain no `sorry` and no `axiom`.
- All 54 `#print axioms` of `MCRQuot` declarations (part 9) read
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
| (B-desc) `QuotientDescendsQ` | an orbit-invariant `σ : 𝒴_ℚ → P¹` descends through the SGA 1 quotient to `𝒵_ℚ`, and `ℚ̄`-points of `𝒵_ℚ` lift | `quotientDescendsQ` (parts 18–22), described in §2.5 |
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
- **(C1b) `CMStabInvolution`**, by `cMStabInvolution_of` (part 17):
  - `CMStabObj` supplies `T = twist α ∘ rightMul u`. The candidate is `ι = g_α * g_u`, built from
    the Hecke automorphisms in `fibreAut` (`hecke_mem_fibreAut`); it acts on classes as `T`.
  - `ι` fixes `y`, by moduli injectivity.
  - `ι²` fixes every `ℚ̄`-point, so `ι² = 1` (`eq_one_of_fixes_all`, from (A-fix) and the
    infinitely many `ℚ̄`-points).
  - `ι ≠ 1`, since `T` moves the class of some object, and every class is the fibre at some
    `ℚ̄`-point.
- **(B-desc) `QuotientDescendsQ`**, by `quotientDescendsQ_of` (part 18):
  - The lifting half is proved. `isGQuotient_surjective` is lying over for
    `Γ(W) = Γ(q⁻¹W)^G ⊆ Γ(q⁻¹W)`. `exists_lift_qbar` uses that the fibre `X ×_Z Spec ℚ̄` is finite
    and nonempty, so it has a closed point, which is a `ℚ̄`-point (Mathlib's
    `pointOfClosedPoint`).
  - The descent half `QuotientDescendsMapQ` is proved too (§2.5).
- **B**, by `genericQuotientP1_of`: `π ∘ g` descends to `𝒵_ℚ` (B-desc) and is bijective on
  `ℚ̄`-points, hence a coordinate (B-iso).

### 2.5 Quotients of maps to `P¹` (parts 19–22)

| Declaration | Content |
|---|---|
| `app_injective_of_isGQuotient` | `q^*` is injective over every open (germs, from the affine case) |
| `exists_descend_section` | invariant sections over any open descend (affine cover, `existsUnique_gluing'`) |
| `ToP1In`, `imgOpen`, `preimage_imgOpen` | maps to `P¹` on an open; images of `G`-stable opens are open and saturated (`q` closed, orbits) |
| **`exists_descend_toP1In`** | a `G`-invariant map to `P¹` on `q⁻¹O` descends to `O` |
| `pushToP1In`, `pullToP1`, `app_injective_of_le_range` | transport of maps to `P¹` along the open immersions `𝒴_ℚ → 𝒴`, `𝒵_ℚ → 𝒵` |
| `pushU_stable_iff`, `pushF_invariant` | invariance of the charts and functions as scheme data, from invariance of values at `ℚ̄`-points: a failure would show at a closed point of the Jacobson generic fibre, hence at a `ℚ̄`-point (`exists_qbarPt`); `𝒴` is reduced (`isReduced_of_smooth_zloc`) |
| **`quotientDescendsMapQ`**, **`quotientDescendsQ`** | (B-desc) proved |

## 3. What remains: two new glue Props

| Name | Statement (informal) | Kind | Why not proved here |
|---|---|---|---|
| (B-iso) `ToP1BijIsCoordinateQ` | a map to `P¹` of a proper smooth `ℚ`-curve that is bijective on `ℚ̄`-points is an isomorphism by charts | the `P¹` case of the textbook leaf `CurveBijIso`, stated by charts | Mathlib 4.35 has `Proj` with `IsProper (Proj.toSpecZero 𝒜)`, but no `P¹` with smoothness of relative dimension 1 and no gluing of a morphism to `Proj` from the two charts; with those, B-iso would follow from `CurveBijIso` |
| (C1b-obj) `CMStabObj` | a CM object's class is fixed by some `T = twist α ∘ rightMul u` with `T ∘ T = id` on `M3 ℚ̄` and `T ≠ id` | glue (QM with CM; elliptic points of orders 4, 6, 2, Baba–Granath §3.1, locator UNVERIFIED) | see below |

Why (C1b-obj) is not proved here (SPECULATIVE analysis, not compiled):

- **CM by `ℤ[i]`.** Take `α = id` and `u ≡ φ` on `A[3]` (`Level3.torsor`, `exists_unit_congr`).
  Then `T` fixes the class, and `u² ≡ −1`, so `T² = id`. But `T ≠ id` needs an object whose
  automorphisms do not realize `u`. That needs the rigidity of level-3 structures and the
  structure of `com q` at a CM point; neither is among the leaves.
- **CM by `ℤ[ζ₃]`.** The unit `ζ₆` gives an operation of order 3 only. The involution is an
  Atkin–Lehner-type twist.
- **CM by `ℤ[√−6]`.** No unit is available. The involution is induced by `ι(ij)⁻¹ φ`, which
  needs integrality in `End A`.
- Both of the last two cases need the normalizer of `ι(𝒪)` in `End(A)` at CM points.
- The independent review (§5) judged `CMStabObj` true. The stabilizers of the elliptic points are
  cyclic of orders 4, 6, 2, each with a unique involution.

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

- Statement review, first run (by a separate model, read-only): every new glue Prop was found true
  as stated, except `QuotientDescendsQ`, which was then amended (§4).
- Statement review, second run (by a separate model, read-only, SPECULATIVE judgements):
  `ModelYIrreducible`, `CurveClosedQbarFinite`, `CMStabObj`, `QuotientDescendsQ` and
  `ToP1BijIsCoordinateQ` were all judged true, none false or vacuous.
  - `ModelYIrreducible` rests on `Y ≅ Y₃` (via R1univ, with Lemma P for the polarization) and on
    Galois swapping the two geometric components.
  - In `CMStabObj`, every word in twists and rightMuls reduces to `twist α ∘ rightMul u`
    (`rightMul u ∘ twist β = twist β ∘ rightMul β(u)`).
  - `QuotientDescendsQ` needs neither `IsFinite q` nor properness.
- Tau Ceti and `Contrib` were checked first. They have no quotient-by-group, no `P¹`-scheme and no
  fixed-locus piece. The only related piece is `ImagePlane.inv`, which is used.

## 6. Reproduce

```
lake build ZInQKernel.Contrib.Mobius.Main ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue
scratch/mcr-quot/build.sh                      # regenerates MCRQuot.lean from the parts
lake env lean scratch/mcr-quot/MCRQuot.lean    # exit 0, ~30 s; compile22_out.txt
```
