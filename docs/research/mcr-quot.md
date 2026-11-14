# mcr-quot: the glue Props A, B, C1, C2 under `ModelCoordinateResidue`

Task mcr-quot, 2026-11-14. Base `origin/main` (f70ec251). Targets: the four glue Props that
mcr-glue left under `ModelGlue.ModelCoordinateResidue` (`scratch/mcr-glue/MCRGlue.lean`,
docs/research/mcr-glue.md §4): A `FibreAutTame`, B `GenericQuotientP1`, C1 `CMSectionsDisjoint`,
C2 `CoordinateFromSections`. Lean file: `scratch/mcr-quot/MCRQuot.lean`. It is `MCRGlue.lean`
verbatim (whole file), followed by the parts `MCRQuot1.lean.part` … `MCRQuot9.lean.part` in the
order of `build.sh`.

## 1. Main result

**All four glue Props are reduced to strictly smaller named Props, by compiled Lean proofs.**
No statement was changed. The composite (namespace `MCRQuot`) is:

```lean
theorem modelCoordinateResidue_of_mcrQuot''
    (hAF : ProperCurveAF) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth)
    (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic)
    (hT : ObjBridge.TorsionStructure)
    (hfix : FibreAutFixFinite) (hcnt : TwistClassCard) (hD : QuotientDescendsQ)
    (hB : ToP1BijIsCoordinateQ) (hO : GQuotientPointOrbits) (hI : CMStabInvolution)
    (hS : StabFixesClosure) (hC : QbarPointsConjugate) (hTr : P1Translate) :
    ModelCoordinateResidue
```

The first six hypotheses are mcr-glue's leaves L1–L6, used as stated. `TorsionStructure` is the
kernel's textbook leaf T5. The last nine are the new glue of this task (§3), each a `def … : Prop`
with a docstring naming its step and its proof outline.

The four reductions, one per target:

| Target | Reduction (compiled) | Inputs |
|---|---|---|
| C2 `CoordinateFromSections` | `coordinateFromSections_of'` | A (only for `Finite (fibreAut 𝒴 𝒜)`), T5, `P1Translate` |
| C1 `CMSectionsDisjoint` | `cMSectionsDisjoint_of` | A, `FibreAutFixFinite`, `GQuotientPointOrbits`, `CMStabInvolution`, `StabFixesClosure`, `QbarPointsConjugate` (L5 and L6 are hypotheses of the Prop itself) |
| A `FibreAutTame` | `fibreAutTame_of` | T5, `FibreAutFixFinite`, `TwistClassCard` |
| B `GenericQuotientP1` | `genericQuotientP1_of` | A, T5, L3, `QuotientDescendsQ`, `ToP1BijIsCoordinateQ` |

VERIFIED: `lake env lean scratch/mcr-quot/MCRQuot.lean` exits 0 in about 26 s (output in
`compile9_out.txt`).

- The parts contain no `sorry` and no `axiom`.
- All 18 `#print axioms` of `MCRQuot` declarations read `[propext, Classical.choice, Quot.sound]`.
- The file is `MCRGlue.lean` followed by the parts (`build.sh` regenerates it).

## 2. What was built (all compiled, namespace `MCRQuot`)

### 2.1 Quotients by finite groups (the SGA 1 quotient `IsGQuotient` of mcr-glue)

| Declaration | Content |
|---|---|
| `exists_root_smul`, `exists_comp_smul_eq` | pure algebra: for `Algebra.IsInvariant A B G`, `G` finite, two ring maps `φ, φ' : B → K` to a field that agree on `A` satisfy `φ' = φ ∘ (g • ·)` for some `g ∈ G` |
| `secMap`, `secAction` | the action of `G` on `Γ(X, q⁻¹W)` for an `IsGQuotient`, as a `MulSemiringAction` with invariants `Γ(Z, W)` |
| `eq_of_appLE_eq` | a `K`-point is determined by its map on the sections of an affine open containing it |
| **`exists_eq_comp_of_isGQuotient`** | the `K`-points of an SGA 1 quotient by a finite group are the orbits: `y ≫ q = y' ≫ q ⟹ y' = y ≫ g`, `g ∈ G` |

The algebra uses Mathlib's `Algebra.IsInvariant.exists_smul_of_under_eq` (transitivity on primes)
and `Ideal.Quotient.stabilizerHom_surjective` (decomposition group onto residue automorphisms).

### 2.2 `P¹` over `ℤ_(p)` by charts (`IsP1Coordinate` of mcr-glue)

| Declaration | Content |
|---|---|
| `ev_eq_appLE`, `eq_of_ev_eq_chart` | values through charts; a field point in a polynomial chart is determined by the chart value |
| **`val_injective_of_isP1Coordinate`** | an isomorphism onto `P¹_{ℤ_(p)}` is injective on field points |
| `scale`, `isP1Coordinate_scale`, `val_scale` | `t ↦ u t`, `u ∈ ℤ_(p)^×` |
| `isP1Coordinate_inv`, `val_inv` | `t ↦ 1/t` (the kernel's `ImagePlane.inv`, charts swapped) |
| `fromSpec_ker_mem_closure`, **`isUnit_sub_of_disjoint`** | in a chart, two `ℚ̄`-points with values `a, a' ∈ ℤ_(p)` and disjoint closures have `a − a'` a unit: otherwise the point over `(p, h − a)` lies in both closures |
| `zloc_or_inv`, `exists_infty`, `integral_of_disjoint_infty`, `exists_unit_neg_16_27` | normalization steps |
| **`p1ThreePoints_of : P1Translate → P1ThreePoints`** | three rational sections with pairwise disjoint closures can be moved to `0, ∞, −16/27` |

### 2.3 QM algebra

| Declaration | Content |
|---|---|
| `unit_table`, **`exists_unit_congr`** | `𝒪^× ↠ (𝒪/3𝒪)^×`: an element of `𝒪` invertible mod `3𝒪` is congruent mod `3𝒪` to a unit of `𝒪`. The 72 unit classes have explicit units of reduced norm ±1, with coordinates in [−3, 3]; they were found by `py/units.py` and are checked by `decide` |
| `TwistEq` and its `trans'`, `symm'`, `twistEq_of_iso` | twist-equivalence of objects, the relation of `CoordFibres` |
| `twistEq_of_mem_fibreAut` | orbits of `fibreAut` lie in twist classes, given uniqueness of fibres at `ℚ̄`-points (which R1fp's comparison `exists_genFib_to_Y` supplies) |
| **`mem_orbit_of_twistEq`** (T5) | twist classes lie in `fibreAut`-orbits. The proof uses the Hecke clauses of `IsShimuraModel`, `Level3.torsor`, `exists_unit_congr` and moduli injectivity |

### 2.4 The reductions

- **C2.** By `val_injective_of_isP1Coordinate`, `exists_eq_comp_of_isGQuotient` and the two
  orbit lemmas, the fibres of `ρ₀ ∘ q` on `ℚ̄`-points are the twist classes.
  - The values of `ρ₀ ∘ q` at the CM points are Galois-fixed, hence rational
    (`exists_rat_of_fixed`). The reason: their `π`-values `0, ∞, −16/27` are rational, and R2fp
    holds through the comparison `𝒴_ℚ → Y`.
  - `P1ThreePoints` then normalizes `ρ₀`, using the disjointness hypothesis of C2.
- **A.** Let `S ⊆ fibreAut` be finite. Pick a `ℚ̄`-point `y` outside the finitely many fixed
  points of the elements `s⁻¹t` (`FibreAutFixFinite`); one exists because 𝒴 has infinitely many
  `ℚ̄`-points (`infinite_qbarPoints`, from `curveFacts.2`).
  - Then `s ↦ y ≫ s` injects `S` into the twist class of `y`, which has at most 288 elements
    (`TwistClassCard`).
  - So `|fibreAut| ≤ 288 < 324 < p`. Finding: the bound `p > 324` is exactly what makes this
    argument work.
- **C1.** Suppose a point `z` lies in both closures.
  1. `z` lifts to `w ∈ closure{x}`, since a finite morphism is closed.
  2. Moving by some `h ∈ fibreAut` (`GQuotientPointOrbits`), also `w ∈ closure{h x'}`.
  3. The inertia group `H = fibreAut ⊓ fixOn {w}` contains an involution fixing `y`, and one
     fixing `y' ≫ h` (`CMStabInvolution`, `StabFixesClosure`).
  4. `H` is finite and tame, and it satisfies L6's hypothesis at `w`
     (`residue_trivial_of_fixesOn`), so it is cyclic (L6). Hence the two involutions agree
     (`eq_of_involutions_cyclic`).
  5. `x ≠ h x'`: Galois-conjugate points (`QbarPointsConjugate`) have equal rational `π`-values,
     and CM points of different types do not.
  6. L5 then makes the closures of `x` and `h x'` disjoint, a contradiction.
- **B.** `π ∘ g : 𝒴_ℚ → P¹` is constant on orbits, so it descends to `σ̄ : 𝒵_ℚ → P¹`
  (`QuotientDescendsQ`).
  - `σ̄` is injective on `ℚ̄`-points: equal values give twist-equivalent fibres, hence one orbit
    (T5), hence one point.
  - `σ̄` is onto (`curveFacts.2`, with finite twist classes).
  - So `σ̄` is a coordinate (`ToP1BijIsCoordinateQ`). L3 supplies that `𝒵` is proper and smooth.

## 3. The new glue Props (statements in the parts; none is literature beyond what is cited)

| Name | Statement (informal) | Kind | Outline in docstring |
|---|---|---|---|
| (A-fix) `FibreAutFixFinite` | for the smooth model and a triple with R1fp, R1hecke, R2fp, each `h ≠ 1` in `fibreAut` fixes finitely many `ℚ̄`-points | glue (curves) | `𝒴` integral (model-glue `ModelIntegral`); the fixed locus is a closed equalizer; infinitely many fixed points force it to contain the generic point |
| (A-count) `TwistClassCard` | a twist class of objects over `ℚ̄` has at most 288 = 4·72 isomorphism classes | glue (QM algebra; T5) | `Aut 𝒪` modulo conjugation by units is induced by `1, i, j, ij` (`NormO.T`); `Level3.torsor` gives ≤ 72 level structures |
| (B-desc) `QuotientDescendsQ` | an orbit-invariant `σ : 𝒴_ℚ → P¹` descends through the SGA 1 quotient to `𝒵_ℚ`, and `ℚ̄`-points of `𝒵_ℚ` lift | glue (quotients) | invariants commute with `ℤ_(p) → ℚ`; Jacobson density; `q` integral surjective |
| (B-iso) `ToP1BijIsCoordinateQ` | a map to `P¹` of a proper smooth ℚ-curve that is bijective on `ℚ̄`-points is an isomorphism by charts | glue (curves; the `P¹` case of `CurveBijIso`) | finite, degree 1, normal target |
| (C1a) `GQuotientPointOrbits` | the points of `X` over a point of `X/G` form one `G`-orbit | glue (SGA 1 V 1.1, UNVERIFIED locator) | Mathlib's `exists_smul_of_under_eq` on an affine chart |
| (C1b) `CMStabInvolution` | the stabilizer in `fibreAut` of a CM point contains an involution `ι ≠ 1` | glue (QM with CM) | stabilizers are the inertia groups, of orders `4, 6, 2` (`nY3`, `CoverBranchData`), all even |
| (C1c) `StabFixesClosure` | an automorphism over `ℤ_(p)` fixing a `ℚ̄`-point fixes every field point over the closure of its point | glue (schemes) | agreement at the generic point of the closure spreads out (EGA IV 8.13.1, UNVERIFIED); `Z` reduced, `𝒴` separated |
| (C1d) `QbarPointsConjugate` | two `ℚ̄`-points with the same underlying point differ by `σ ∈ Aut(ℚ̄/ℚ)` | glue (field theory) | extend an embedding (`IsAlgClosed.lift`) |
| (C2-T) `P1Translate` | for `ρ : 𝒵 ≅ P¹_{ℤ_(p)}` and `e ∈ ℤ_(p)`, the coordinate `ρ + e` is again an isomorphism by charts | glue (chart algebra) | `V' = D_V(1+eg) ∪ D_U(f+e)` is affine; `ℤ_(p)[Y,1/Y] ∩ ℤ_(p)[Y,1/(1−eY)] = ℤ_(p)[Y]` |

Intermediate glue Prop (proved from (C2-T)): `P1ThreePoints`.

**Truth review** (SPECULATIVE where not marked; arguments in the docstrings). Each new Prop was
checked against its intended meaning:

- (A-count) is consistent with the kernel's `NormO.T = {1, i, j, ij}` and with
  `Level3.torsor` (VERIFIED by reading the kernel).
- (C1b) uses that the ramification indices of `Y₃ → P¹` over `0, ∞, −16/27` are `4, 6, 2`
  (`nY3`, `CoverBranchData` in the prefix: VERIFIED by reading), all even.
- (A-fix) needs `𝒴` integral. That holds for the Shimura model (model-glue's `ModelIntegral`); it
  would fail for a disconnected `𝒴` whose automorphism is trivial on one component, but every
  element of `fibreAut` is defined over `ℚ` and so commutes with Galois.

**Findings.**

- **C2 needs the finiteness of `fibreAut`, which is glue A.** For an infinite group, `IsGQuotient`
  does not make the fibres of `q` the orbits. Example: `ℤ` acting on `𝔸¹_ℚ` by translation has
  `IsGQuotient` onto `Spec ℚ`.
- **B needs `𝒵` proper and smooth**, which B's statement does not assume. Leaf L3 supplies it.
- No statement was found false, vacuous or inert.

## 4. What remains

- **The nine new glue Props are not proved.** Their sizes vary:
  - (C1a), (C1d) and (A-count) are small and look provable from what exists: Mathlib's invariant
    theory, `IsAlgClosed.lift`, and the kernel's `NormO`/`Level3.torsor`.
  - (C2-T) is a chart computation.
  - (A-fix), (B-desc), (B-iso) and (C1c) are scheme theory of curves and quotients.
  - (C1b) is QM theory with CM.
- **The leaves L1–L6 and T5 need formalization.** Their locators are UNVERIFIED (no network).

## 5. Reproduce

```
lake build ZInQKernel.Contrib.Mobius.Main ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue
scratch/mcr-quot/build.sh                      # regenerates MCRQuot.lean from the parts
lake env lean scratch/mcr-quot/MCRQuot.lean    # exit 0, ~26 s
```
