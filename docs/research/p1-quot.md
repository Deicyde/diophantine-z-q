# p1-quot: the glue field `quotientP1Coordinate`

Task p1-quot, 2026-11-15. Base `wip/w72` (24f97774). Target: the bundle field
`HDec.HSyn.OpenGlue7.quotientP1Coordinate`, whose type is `HDec.MCRGlue.QuotientP1Coordinate`
(`ZInQKernel/OneProof/H/TailW.lean` L202, unchanged). Sources: docs/research/mcr-glue.md, mcr-quot.md,
gap-triage.md (A3, A12), leaf-fold9.md §5.

## 1. Main result

**`QuotientP1Coordinate` is reduced, by compiled Lean with standard axioms, to mcr-glue's six leaves L1-L6,
two inputs the chain already supplies (T5, `HeckeIrreducible`), and one glue Prop on CM objects (`CMStabObj`).**
mcr-quot's foundational glue `P1SchemeQ` is proved here, and Lemma NV (`CoverModelOfHeckeN`) is not used
(gap-triage finding 3).

```lean
-- ZInQKernel/Contrib/OneProof/QuotientP1Coordinate.lean
theorem HDec.MCRQuot.quotientP1Coordinate_of_printed
    (hAF : ProperCurveAF) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic)   -- L1-L6 (HDec.MCRGlue, TailW)
    (hT : PkgI2.TorsionStructure.{0})                             -- T5
    (hYI : PropTSGlue.HeckeIrreducible)                           -- Y irreducible over ℚ
    (hO : CMStabObj) :                                            -- glue (mcr-quot (C1b-obj))
    MCRGlue.QuotientP1Coordinate

-- ZInQKernel/Contrib/OneProof/QuotientP1/FromFields.lean: T5 and HeckeIrreducible from the chain's fields
theorem HDec.MCRQuot.quotientP1Coordinate_of_fields (L1 … L6)
    (hMT : AvSplit.MumfordTorsionAlgClosed)                 -- textbook field mumfordTorsionAlgClosed
    (hRC : LeafQM.AV.R1UnivRigid.MumfordRigidityCore)        -- research field mumfordRigidityCore
    (hD : ShimuraGlue.DeligneComponentsY3PrintedAb)          -- added field deligneComponentsY3PrintedAb
    (hO : CMStabObj) : MCRGlue.QuotientP1Coordinate
```

VERIFIED (compiled; outputs in `scratch/p1-quot/`):

- every contribution module compiles with `lake env lean -o` (no errors; no `sorry`, no `axiom`);
- `#discharges` (Main + Discharges + the contribution, `scratch/p1-quot/Discharges.lean`, output
  `discharges_out.txt`, §6) prints `DISCHARGES [OpenGlue7.quotientP1Coordinate] by
  HDec.MCRQuot.quotientP1Coordinate_of_printed`, still assuming exactly L1-L6, `PkgI2.TorsionStructure`,
  `HDec.PropTSGlue.HeckeIrreducible`, `HDec.MCRQuot.CMStabObj`, axioms `[propext, Classical.choice, Quot.sound]`;
- `HDec.MCRQuot.p1SchemeQ : HDec.MCRQuot.P1SchemeQ` and `quotientP1Coordinate_of_fields` have standard axioms.

No statement was changed. No statement was found false, vacuous or inert.

## 2. What was done

### 2.1 mcr-quot over the chain's constants (helpers `QuotientP1/MCRQuotA.lean`, `MCRQuotB.lean`)

mcr-quot's file is `MCRGlue.lean` (whose content the chain holds as `TailL`..`TailW` in `namespace HDec`)
followed by mcr-glue parts 5-6 and mcr-quot parts 1-24. Those parts (MCRQuot.lean L4406-end) were placed verbatim
inside `namespace HDec` over `import ZInQKernel.OneProof.H.TailW`. VERIFIED: 34 errors, all name resolution, fixed by
writing `ImagePlane.*`, `curveFacts`, `smoothStalkDimOne` and one `transportLevel` with the prefix
`_root_.LeafQM.AV.Pin.` (inside `namespace HDec` they resolve to the chain's aliases or are ambiguous between
`Pin.transportLevel` and `HDec.G0ModField.transportLevel`). After that the whole of mcr-quot compiles with every
target and glue name resolving to the chain's `HDec.MCRGlue.*`, `HDec.ModelGlue.*`, `HDec.PropTSGlue.*` constants
(`scratch/p1-quot/Port1.lean`, `port1_out.txt`). Split in two files at mcr-quot's part 12 (130 KB, 114 KB).

### 2.2 `P1SchemeQ` proved (helper `QuotientP1/P1Scheme.lean`, theorem `QuotientP1Proof.p1SchemeQ_body`)

mcr-quot's (B-P¹) (MCRQuot.lean L8549): a proper `ℚ`-scheme `P`, smooth of relative dimension 1, with charts `τ`
(`IsP1CoordinateQ`), such that every `σ : ToP1 Z` is `τ ∘ m`. Proof, all VERIFIED by compilation:

| piece | how |
|---|---|
| `P` | the vendored CloudW07 relative line `ProjectiveSpace (ULift (Fin 2)) (Spec ℚ)` (`ℙ(n; S)` is the pullback of `Proj ℤ[T₀,T₁]`) |
| proper | CloudW07 `ProjectiveSpace.instIsProper` |
| smooth of rel. dim. 1 | Zariski-local on the two standard opens; each is `≅ 𝔸¹_{Spec ℚ}` (`standardOpenIso`), Mathlib `AffineSpace.smoothOfRelativeDimension_of_card_eq` |
| `τ` | `U, V` = standard opens, `f = T₁/T₀`, `g = T₀/T₁` (CloudW07 `coordRatio`); `fg = 1` from `relativeChartCoordinate_mul`; `D(f) = U ∩ V` from the normalized-point description of the chart inclusion (`relativeChart_ι_eq_normalized`, `homOfSections_preimage_standardOpen`) |
| `ℚ[X] → Γ(U)` bijective | it equals `ℚ[X] ≃ MvPolynomial {i1} ℚ ≃ Γ(Spec) ≃ Γ(𝔸¹) ≃ Γ(U.toScheme) ≃ Γ(P, U)` (`Polynomial.ringHom_ext` on `C` and `X`; `AffineSpace.SpecIso_inv_appTop_coord`, `SpecIso_inv_over`, `standardOpenIso_hom_over`) |
| the factorization `m` | the CloudW07 coordinate cover `Scheme.CoordinateCover` on `{σ.U, σ.V}` with ratios `1, σ.f, σ.g, 1` (cocycle from `σ.inv`), and its morphism `CoordinateCover.hom` to `ℙ(ULift (Fin 2); Spec ℚ)` |
| `m⁻¹U = σ.U`, `m⁻¹V = σ.V` | `CoordinateCover.preimage_hom_standardOpen` (`⨆ᵢ D(ratio i 0) = σ.U ∪ (σ.U ∩ σ.V)`) |
| `m^* τ.f = σ.f`, `m^* τ.g = σ.g` | on `σ.U` the map is `homOfSections` with sections `(1, f)` (`CoordinateCover.ι_hom`); CloudW07 `homOfSections_appLE_coordRatio`; `appLE` to `app ∘ eqToHom` by thinness of the opens category |

This proves gap-triage's A3 (high probability, T1) completely.

### 2.3 The composite (`QuotientP1Coordinate.lean`)

`MCRGlue.quotientP1Coordinate_of_leaves` (TailW) with glue A = `fibreAutTame_of' hT (fibreAutFixFinite_of' hC hYI)`,
glue B = `genericQuotientP1_of'' gA hT hTS hC p1SchemeQ`, glue C = `coordinateNormalization_of` of
`cMSectionsDisjoint_of'' gA hfix (cMStabInvolution_of hC hYI hO)` and `coordinateFromSections_of'' gA hT`
(all mcr-quot). `CurveBijIso` is curve-split's `_root_.CurveSplit.curveBijIso` (`TailR`); `ModelYIrreducible` is
`PropTSGlue.HeckeIrreducible` by `rfl` (gap-triage's GlueProbe).

## 3. What remains, with ratings

| input | kind | printed form? | reason |
|---|---|---|---|
| L1 `ProperCurveAF` | composite (leaf-fold9 §5, frontier H-89) | no | Lichtenbaum 1968 Thm 2.8 / Liu 8.3.16 (projectivity of a regular proper flat relative curve) composed with EGA II 4.5.4 / Liu 3.3.36 (finite sets in an affine open); no single print states it |
| L2 `FiniteQuotientExists` | published, special case (H-90, LEAF) | yes (special case) | SGA 1 Exp. V Prop. 1.8 (existence when orbits lie in affine opens) with 1.1 (integrality); finiteness from finite type over Noetherian `ℤ_(p)`, as mcr-glue's docstring says; rated LEAF already |
| L3 `TameQuotientSmooth` | composite (H-91) | no | SGA 1 V 1.9 / Mumford AV §7 Thm 3 (tame quotients commute with base change), normal curves over perfect fields are smooth, EGA IV 17.5.1 (flat + smooth fibres) |
| L4 `SmoothModelOfP1` | consequence (H-92) | no | Liu AGAC §8.3, §10.1: a smooth proper model of `P¹_ℚ` over a DVR is `P¹` (via genus 0 special fibre with a rational point); the print states it for curves over the residue field, the model statement is a short argument |
| L5 `TameFixedPointsDisjoint` | consequence (H-93) | no | Edixhoven 1992 Prop. 3.4 (the fixed scheme of a tame group action on a smooth scheme is smooth), plus "finite étale over a DVR has one generic point per connected component"; the print does not state disjoint closures |
| L6 `TameInertiaCyclic` | composite (H-94) | no | Serre, Local Fields IV §2 Cor. 1 of Prop. 7 (for a complete DVR) transported to a 2-dimensional regular local ring by the cotangent-space argument in the docstring |
| T5 `PkgI2.TorsionStructure` | supplied by the chain | — | `AvSplit.torsionStructure_of_mumford` of the textbook field `mumfordTorsionAlgClosed` |
| `HeckeIrreducible` | supplied by the chain | — | from `deligneComponentsY3PrintedAb` and `mumfordRigidityCore` (`FromFields.lean`) |
| `CMStabObj` | project glue | — | §4 |

All locators are mcr-glue's (UNVERIFIED: no network). The six L statements were re-read against their docstring
arguments (SPECULATIVE judgement): each is true as stated, none is vacuous (each has a nonempty instance: the
chain's smooth model).

**Fold arithmetic (strict count).** Replacing the field (1 strict GLUE) by these inputs adds L1, L3, L4, L5, L6 and
`CMStabObj` (6 strict GLUE) and L2 (1 LEAF): net +5 strict GLUE (leaf-fold9 §5 counted +6 with `P1SchemeQ` and
`CoverModelOfHeckeN`, which are now gone). So by leaf-fold7's decision rule the fold still does not pay; what it
gives is that the field is now **a composite of published results plus one QM-object glue Prop**, with every
scheme-theoretic glue step (A, B, C1, C2, P¹, quotient descent) compiled.

## 4. `CMStabObj` (gap-triage A12)

Statement (mcr-quot, verbatim in `QuotientP1/MCRQuotB.lean`): for a level-3 object `P` over `ℚ̄` with CM by
`ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` (an element `φ` of the commutant with `φ² = −1`, `φ² − φ + 1 = 0`, `φ² = −6`), some
`T = twist α ∘ rightMul u` fixes `[P]`, satisfies `T ∘ T = id` on `M3 ℚ̄`, and is not the identity.

Analysis (SPECULATIVE, not compiled):

- **`ℤ[i]`.** With `α = id`, `T = rightMul u` fixes `[P]` when `u ≡ (action of φ on A[3])⁻¹ mod 3𝒪`: T5 makes
  `φ ∘ η` a level structure, `Level3.torsor` gives `φ(η(a)) = η(a u₀)`, `exists_unit_congr` lifts `u₀⁻¹` to a
  unit; `φ² = −1` gives `u² ≡ −1`, and `rightMul (−1)` and `rightMul (1 + 3𝒪)` act trivially on classes, so
  `T² = id`. The clause `T ≠ id` needs a class moved by `rightMul u`; with `QMCentralizerCM` (the commutant at
  the `ℤ[i]` point is `ℤ[φ]`, units `±1, ±φ`) one can take `rightMul v [P]` for a unit `v` with
  `v⁻¹ u v ≢ ±u, ±1 mod 3` (a finite check in `𝒪/3𝒪`, 72 units).
- **`ℤ[ζ₃]`, `ℤ[√−6]`.** The commutant gives only an operation of order 3 (`ζ₆`), resp. none. The stabilizers of
  orders 6 and 2 in `Γ'` modulo `±1` contain an Atkin–Lehner twist `α = conj(v)` with `nrd v ∈ {2, 3, 6}`; `T`
  fixes `[P]` iff some `ψ ∈ Aut(A)` has `ψ ι(a) ψ⁻¹ = ι(v a v⁻¹)`, i.e. `ψ = c ι(v)⁻¹` with `c` in the commutant and
  `c ι(v̄) ∈ nrd(v) End(A)`. This is a statement about `End(A)` beyond the commutant, which no leaf of the chain
  gives. In print it is the moduli form of "the Atkin–Lehner involution `w_m` fixes the CM points by orders
  containing `√−m`" (Ogg 1983, *Real points on Shimura curves*; Rotger 2004; locators UNVERIFIED), stated there on
  `X₀^D(ℂ)`, not on the objects `(A, ι, η)`.
- The involution is needed: in mcr-quot's proof of C1 the cyclic inertia group must contain *one* involution
  fixing both CM points, and for the pair `(ℤ[i], ℤ[ζ₃])` the operations coming from the commutants alone have
  orders 2 and 3.

So `CMStabObj` is not proved here; it remains the one project glue under the field.

## 5. Abelian-scheme form (R1fpPropsAb)

Question from the brief: can the field's consumer be stated with `R1fpPropsAb`, dropping Mumford's rigidity leaf
from this proof? Findings (VERIFIED by reading the compiled proof):

- In this proof `R1fpProps Y Φ` is used (a) through `HeckeIrreducible`, whose chain proof converts the abelian-scheme
  Deligne leaf with `mumfordRigidityCore` (`deligneComponentsY3Printed_iff_ab`), and (b) in model-glue's
  `exists_genFib_to_Y` (TailL L1645), which applies `R1univProps` to the base change `famBC 𝒜 j` of the family
  `𝒜 : QMFamily 𝒴.left` of `IsShimuraModel`. Otherwise only clauses 1-3 (proper, smooth, a `ℚ̄`-point) were found (grep of `h1` uses in TailL, TailW and the
  port; SPECULATIVE beyond that).
- (b) does not go through with `R1univAbProps`, which only classifies families that are abelian schemes
  (`QMAbScheme`). So an abelian-scheme form of the field must also take `IsShimuraModel` with a `QMAbScheme`
  family (and needs base change of a `QMAbScheme` along `𝒴_ℚ → 𝒴`). The good-reduction field
  `shimuraGoodReductionNoGuard` would then have to provide an abelian scheme over `𝒴` (the published form of the
  smooth model is a moduli scheme of abelian schemes, so this is the more faithful reading).
- With those two changes (field and consumer in abelian-scheme form, `IsShimuraModel` with `QMAbScheme`), the uses
  (a) and (b) need no rigidity: (a) comes from `DeligneComponentsY3PrintedAb` directly, (b) from `R1univAbProps`.
  This is SPECULATIVE (not compiled): the model-glue lemmas of TailL that take `R1fpProps` would have to be
  restated. Rigidity is used elsewhere in the chain as well (`r1R2fpRep_iff_ab`, `shimuraFamily_iff_ab`), so this
  field alone would not remove the rigidity field.

## 6. `#discharges` output (`scratch/p1-quot/discharges_out.txt`)

Run against the copied build tree of fork commit c2ad4181 (leaf-fold19, research bundle generation 19; this base's
Main is generation 20 with the same `OpenGlue7`), since a full `lake build` of this base was not run:

```
DISCHARGES [OpenGlue7.quotientP1Coordinate] by HDec.MCRQuot.quotientP1Coordinate_of_leaves'
  still assumes: [HDec.MCRGlue.ProperCurveAF, HDec.MCRGlue.FiniteQuotientExists, HDec.MCRGlue.TameQuotientSmooth,
 HDec.MCRGlue.SmoothModelOfP1, HDec.MCRGlue.TameFixedPointsDisjoint, HDec.MCRGlue.TameInertiaCyclic,
 ObjBridge.TorsionStructure, HDec.ModelGlue.CurveBijIso, HDec.PropTSGlue.HeckeIrreducible, HDec.MCRQuot.CMStabObj]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenGlue7.quotientP1Coordinate] by HDec.MCRQuot.quotientP1Coordinate_of_printed
  still assumes: [HDec.MCRGlue.ProperCurveAF, HDec.MCRGlue.FiniteQuotientExists, HDec.MCRGlue.TameQuotientSmooth,
 HDec.MCRGlue.SmoothModelOfP1, HDec.MCRGlue.TameFixedPointsDisjoint, HDec.MCRGlue.TameInertiaCyclic,
 PkgI2.TorsionStructure, HDec.PropTSGlue.HeckeIrreducible, HDec.MCRQuot.CMStabObj]
  axioms: [propext, Classical.choice, Quot.sound]
```

**Fold note.** `quotientP1Coordinate` is a bundle field (`OpenGlue7`), so no Main.lean edit is needed beyond
autofold. autofold's `{n}` reaches only the new glue bundle: T5 and `HeckeIrreducible` come from other bundles
(`mumfordTorsionAlgClosed`, `deligneComponentsY3PrintedAb` with `mumfordRigidityCore`), so the fold needs a hand
edit using `quotientP1Coordinate_of_fields`, or the two inputs as new fields. The contribution imports `TailW`,
`TailR` and (FromFields) `TailZ17`, never `Main`.

## 7. Reproduce

```
python3 -I scratch/p1-quot/py/gen_contrib.py        # writes the four contribution files from the scratch files
lake env lean scratch/p1-quot/Port3.lean            # single-file composite, ~20 s with the chain built
# contribution modules, in order:
for m in QuotientP1/MCRQuotA QuotientP1/MCRQuotB QuotientP1/P1Scheme QuotientP1Coordinate QuotientP1/FromFields; do
  lake env lean -o .lake/build/lib/lean/ZInQKernel/Contrib/OneProof/$m.olean ZInQKernel/Contrib/OneProof/$m.lean; done
lake env lean scratch/p1-quot/Discharges.lean
```
