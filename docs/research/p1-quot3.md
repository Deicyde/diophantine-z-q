# p1-quot3: L3 is proved; `quotientP1Coordinate` rests on L4 alone among the non-printed inputs

Task p1-quot3, 2026-11-15. Base `wip/p1-quot2` (19793c5d), with `origin/wip/dcy3-used` (36240662, which contains
leaf-fold23) merged cleanly (6abfc715). Target: the bundle field `HDec.HSyn.OpenGlue7.quotientP1Coordinate`, of type
`HDec.MCRGlue.QuotientP1Coordinate` (`ZInQKernel/OneProof/H/TailW.lean`, unchanged). Scratch: `scratch/p1-quot3/`,
results log `scratch/p1-quot3/log.md`. No statement was changed. Nothing under `ZInQKernel/` was edited; three
files were added under `ZInQKernel/Contrib/OneProof/`.

Marks: **VERIFIED** = compiled, or read in a source file. **STANDARD** = a published theorem with its reference.
**UNVERIFIED** = a locator recalled from memory (there is no network here).

## 1. Main result

**(1) Done.** p1-quot2's residual glue `HDec.MCRGlue.TameQuotientSmoothRelDim` is now a theorem. It is the
smoothness half of mcr-glue's L3; p1-quot2 had already proved the properness half. The proof uses only the chain's
existing textbook field `regularSmoothPerfect` (Stacks 00TV) and adds no new leaf. So all of L3
(`TameQuotientSmooth`) is proved.

**(2) Not done.** L4 `SmoothModelOfP1` is still a consequence (GLUE). I found no printed theorem with its
statement. A Lean proof is now possible with the vendored libraries, since Zariski connectedness, coherent
cohomology of families, local constancy of χ and cohomology and base change for positive line bundles are there.
But two steps have no library support, and I estimate the proof at several thousand lines (§5).

```lean
-- ZInQKernel/Contrib/OneProof/QuotientP1/TameQuotSmooth.lean
theorem HDec.MCRGlue.tameQuotientSmoothRelDim_of_regularSmoothPerfect
    (hRS : CurveSplit.RegularSmoothPerfect) : TameQuotientSmoothRelDim
theorem HDec.MCRGlue.tameQuotientSmooth_of_regularSmoothPerfect
    (hRS : CurveSplit.RegularSmoothPerfect) : TameQuotientSmooth

-- ZInQKernel/Contrib/OneProof/QuotientP1Smooth.lean
theorem HDec.MCRQuot.quotientP1Coordinate_of_fields4
    (hL : QuotientP1Proof.LichtenbaumProjective)      -- p1-quot2's printed leaf (Lichtenbaum 1968 Thm 2.8)
    (hQE : FiniteQuotientExists)                      -- mcr-glue L2 (published, special case)
    (hP1 : SmoothModelOfP1)                           -- mcr-glue L4 (consequence): the only GLUE input left
    (hE : EdixhovenFixedSmooth2)                      -- p1-quot's printed leaf (Edixhoven 1992 Prop. 3.4)
    (hRS : CurveSplit.RegularSmoothPerfect)           -- textbook field {t}
    (hMT : AvSplit.MumfordTorsionAlgClosed)           -- textbook field {t}
    (hM : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)        -- research field {r} (leaf-fold23)
    (hU3 : RayClassCFT.ShimuraMainThmIDeligneY3AbU)            -- research field {r} (dcy3-used's route)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll)     -- textbook field {t}
    (hG : ZInQ.HomLattice.GAGAMorphism) :                      -- textbook field {t}
    MCRGlue.QuotientP1Coordinate
```

Following the task's note, `HeckeIrreducible` now comes from dcy3-used's `DCY3Used.y3Connected_of_leaves hM hU3`.
p1-quot2 got it from `mumfordRigidityCore` and `deligneComponentsY3PrintedAb`. The first of those fields is now
`mumfordGroupLaw` (leaf-fold23), and the second is removed by dcy3-used's bypass.

Strict count of the fold, from `autofold.py --dry-run` (no `--allow-rise` needed):

| | strict GLUE (fold) | autofold strict count | strictest |
|---|---|---|---|
| p1-quot2 (`fields3`) | +1 (L3-smooth composite, L4 consequence) | 46/10 on 56 → 49/11 on 60 | 45/11 → 48/12 |
| **p1-quot3 (`fields4`)** | **0** (L4 consequence only) | **46/10 on 56 → 49/10 on 59** | **45/11 → 48/11** |

The fold removes one GLUE field (`quotientP1Coordinate`) and adds one GLUE leaf (L4) plus three published leaves.
It would pay −1 if L4 were replaced by a printed leaf or proved. That did not happen (§5).

VERIFIED (compiled; outputs in `scratch/p1-quot3/`):

- `lake build ZInQKernel.Contrib.OneProof.QuotientP1Smooth` succeeds on the merged tree, together with the two
  helpers `QuotientP1/TameInvariants.lean` and `QuotientP1/TameQuotSmooth.lean`. There is no `sorry` and no `axiom`.
- `#discharges` (`Discharges.lean`, output `discharges_out.txt`) prints
  `DISCHARGES [OpenGlue7.quotientP1Coordinate] by HDec.MCRQuot.quotientP1Coordinate_of_fields4`. It still assumes
  exactly the ten inputs above. Its axioms are `[propext, Classical.choice, Quot.sound]` (63 open hypotheses, 2489
  theorems checked).
- In the scratch copy (`Scheme.lean`), `tameQuotientSmoothRelDim_of_regularSmoothPerfect` depends on the standard
  axioms only.
- `scratch/p1-quot3/autofold.json` passes `--dry-run` without `--allow-rise` (output `autofold_dryrun.txt`). With
  line 1 stripped, the generated module (`FoldDry.lean`: `OpenGlue8`, `sixContactMin_of_open30`) compiles against
  TailZ35, and `sixContactMin_of_open30` depends on the standard axioms only.

## 2. The proof of `TameQuotientSmoothRelDim`

The statement is p1-quot2's, unchanged (`QuotientP1/QuotProper.lean`): `q : 𝒴 → 𝒵` over `S = Spec ℤ_(p)`, where
- `𝒴` is proper and smooth of relative dimension 1;
- `G ≤ Aut 𝒴` is finite with `p ∤ |G|` and acts over `S`;
- `IsGQuotient G q` holds and `q` is finite.

The conclusion is `SmoothOfRelativeDimension 1 𝒵.hom`.

### 2.1 Algebra (`QuotientP1/TameInvariants.lean`, namespace `QuotientP1Proof.TameQuot`; Mathlib + Contrib/Dim + one vendored FLT theorem)

| Lean | statement | how |
|---|---|---|
| `exists_algebraMap_mem_notMem` | `G` finite acting on `C` with invariants `D` (`Algebra.IsInvariant`); a `G`-stable ideal `I ⊄ 𝔫` (`𝔫` prime) contains an invariant element outside `𝔫` | prime avoidance over the `g • 𝔫` (`Ideal.subset_union_prime`), then the norm `∏ g • w` |
| `localRingHom_injective`, `dvd_of_dvd_atPrime` | `D_𝔮 → C_𝔫` is injective; divisibility in `C_𝔫` descends to `D_𝔮` | the norm trick applied to annihilator and colon ideals |
| `isDomain_isIntegrallyClosed_atPrime` | if every `C_𝔫` is an integrally closed domain, so is every `D_𝔮` | elementwise. It needs no decomposition of `C` into domains and no condition on `|G|` |
| `smooth_of_invariants_field` | over a perfect field `k`: `C` smooth with `dim C ≤ 1`, `D = C^G` of finite type ⇒ `D` smooth | `C_𝔫` is normal (vendored FLT `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`). So each `D_𝔮` is a noetherian normal local domain of dimension `≤ 1`, i.e. Dedekind, hence regular. Then `RegularSmoothPerfect` (Stacks 00TV; a verbatim copy of the chain field's `def`) gives smoothness at every prime, and Mathlib's `Algebra.smoothLocus_eq_univ_iff` concludes |
| `reynolds`, `exists_retraction`, `fibre_invariants` | with `|G|` invertible, invariants commute with every base change `k ⊗_R –` | the Reynolds operator `|G|⁻¹ Σ g` gives an `R`-linear retraction `B → A`, which is stable under `LinearMap.baseChange` |
| `smooth_of_invariants` | `R` noetherian with perfect residue fields; `B` smooth over `R` with fibres of dimension `≤ 1`; `|G|` invertible; `A = B^G` of finite type ⇒ `A` smooth over `R` | `A` is flat as a retract of `B` (`Module.Flat.of_retract`). The fibres `κ ⊗ A = (κ ⊗ B)^G` are smooth by the field case. Then Mathlib's `Algebra.Smooth.of_formallySmooth_fiber` (flat + finitely presented + smooth fibres) |
| `perfectField_residueField` | residue fields of a quotient of a localization of `ℤ` are perfect | char 0, or Frobenius fixes every element (`map_intCast`) |
| `ringKrullDim_of_isStandardSmoothOfRelativeDimension`, `ringKrullDim_tensor_eq_one`, `ringKrullDim_fibre_eq` | dimension of a standard smooth algebra over a field; of `κ ⊗_R B` when `Spec B → Spec R` is smooth of relative dimension 1; fibres of `A` and `B` have equal dimension | Contrib/Dim's `topologicalKrullDim_eq_of_smoothOfRelativeDimension`, `pullbackSpecIso`, `ringKrullDim_eq_of_isIntegral_of_injective` |

### 2.2 Schemes (`QuotientP1/TameQuotSmooth.lean`, namespace `HDec.MCRGlue.TameQuotScheme`)

- `sect`, `action`: `G` acts on `Γ(𝒴, q⁻¹V)` with `g` acting as `(g⁻¹)^*`, through `Scheme.Hom.appLE_comp_appLE`.
- `invariant_setup`: `Γ(𝒵, V) → Γ(𝒴, q⁻¹V)` is a `Γ(S, U)`-algebra map. It is injective, `G`-equivariant, and its
  image is the invariants (read off `IsGQuotient`).
- `smooth_appLE`: `Γ(S, ⊤) → Γ(𝒵, V)` is smooth for every affine `V`. This gives `Smooth 𝒵.hom` by
  `HasRingHomProperty.of_iSup_eq_top`. The inputs are:
  - `𝒵 → S` locally of finite type: p1-quot2's `locallyOfFiniteType_of_isGQuotient`;
  - `Γ(S, ⊤) ≅ ℤ_(p)` noetherian with perfect residue fields;
  - `|G|` a unit in `ℤ_(p)`;
  - fibre dimension `≤ 1`: `Spec Γ(𝒴, q⁻¹V) → Spec Γ(S, ⊤)` is smooth of relative dimension 1 by
    `HasRingHomProperty.Spec_iff`.
- `relDim_eq_one`: every standard smooth chart of `𝒵` (Mathlib `Smooth.exists_isStandardSmooth`) has relative
  dimension 1. The fibre `κ(𝔭) ⊗ Γ(𝒵, V)` through the point is nonzero (`PrimeSpectrum.preimageEquivFiber`) and has
  dimension `n`. It also has the dimension of `κ(𝔭) ⊗ Γ(𝒴, q⁻¹V)`, which is 1.

### 2.3 Rating

No new leaf. The one non-Mathlib input that is a statement rather than a proof is `CurveSplit.RegularSmoothPerfect`,
already a textbook field of `OpenTextbookLeaves11` (Stacks 00TV; locator as in TailR, UNVERIFIED). The other inputs
are Mathlib, `ZInQ.Contrib.Dim` (proved), the vendored FLT theorem above (proved in the vendored tree) and p1-quot2's
`QuotProper` (proved).

## 3. Leaves of the fold, rated

| leaf | kind | printed form? | reason |
|---|---|---|---|
| `lichtenbaumProjective` | published | yes, special case; flag **unread** | p1-quot2 §3.1: Lichtenbaum, Amer. J. Math. 90 (1968) Thm 2.8; Liu, AGAC Thm 8.3.16 (UNVERIFIED) |
| `finiteQuotientExists` (L2) | published | yes, special case | SGA 1 Exp. V Prop. 1.8 with 1.1 (UNVERIFIED); mcr-glue's rating |
| `edixhovenFixedSmooth2` | published | yes, special case; flag **unread** | Edixhoven, Compositio 81 (1992) Prop. 3.4 (UNVERIFIED); p1-quot's rating |
| `smoothModelOfP1` (L4) | **consequence** | **no** | §5: no printed statement located. It follows from textbook theorems (genus 0 with a rational point gives P¹ over a field; constancy of χ; cohomology and base change), but by a nontrivial argument |
| `TameQuotientSmoothRelDim` | — | — | **proved** (§2); removed from the spec |

No new printed leaf, so no new row is needed in `docs/research/locators.md`. p1-quot2's proposed row for
`LichtenbaumProjective` still stands.

## 4. What L4 is used for

`SmoothModelOfP1` (TailW L379) says: a proper `ℤ_(p)`-scheme `𝒵`, smooth of relative dimension 1, whose generic
fibre is `P¹_ℚ` by charts (`IsP1CoordinateQ`), is `P¹_{ℤ_(p)}` by charts (`IsP1Coordinate`).

In `quotientP1Coordinate_of_printed2` (p1-quot2):
1. `𝒵 = 𝒴/G` is the quotient by the Hecke group.
2. Its generic fibre is `P¹_ℚ` (`genericQuotientP1_of''`).
3. L4 turns that into an isomorphism `ρ'₀ : 𝒵 ≅ P¹_{ℤ_(p)}`.
4. `coordinateFromSections_of''` uses the three pairwise disjoint CM sections (Edixhoven) to adjust `ρ'₀` by a
   Möbius map in `PGL₂(ℤ_(p))`, so that `ρ' ∘ q` has the fibre relation.

So L4 is used exactly once, and for exactly its statement: some isomorphism `𝒵 ≅ P¹_{ℤ_(p)}`.

## 5. L4: analysis, candidate printed forms, formalization plan

### 5.1 Why there is no short proof

Any proof has to show that the special fibre `𝒵_s` is a geometrically connected curve of genus 0. Then it has to
lift `𝒵_s ≅ P¹_{𝔽_p}` (or the generic coordinate) to `𝒵`. The standard argument:

1. **Geometric connectedness.** `Γ(𝒵, 𝒪) = ℤ_(p)` because the generic fibre `P¹_ℚ` is geometrically integral and
   `𝒵` is flat. Then Zariski's connectedness theorem applies.
2. **Genus 0.** χ(𝒪) is constant in the flat proper family (EGA III 7.9.4), so `𝒵_s` has genus 0.
3. **A section.** The valuative criterion extends a `ℚ`-point to `σ : S → 𝒵`.
4. **A pencil.** `L = 𝒪(σ)` has degree 1 on each fibre and `h⁰ = 2` (Riemann–Roch). Cohomology and base change
   (EGA III 7.7.5) makes `f_*L` free of rank 2.
5. **The isomorphism.** Two generating sections give `φ : 𝒵 → P¹_S`. It is an isomorphism on each fibre (degree 1),
   hence an isomorphism.

The other routes are no shorter:
- Valuations: the generic point of `𝒵_s` gives a residually transcendental extension of `v_p` to `ℚ(t)`. Its residue
  field is ruled by Ohm's ruled residue theorem (J. Ohm, Proc. AMS 89 (1983), UNVERIFIED), so it is `𝔽_p(T)`. The
  lift to `𝒵` then needs divisors on the regular surface `𝒵` (Hartogs) or step 5.
- Brauer–Severi theory: Grothendieck, *Le groupe de Brauer* I §8 (UNVERIFIED). It needs step 2 first.

### 5.2 What the libraries have now

This corrects p1-quot2 §4, which said coherent cohomology over a DVR is not available.

What I read myself:
- `ZariskiConn.ZariskiConnectedness_proof : ZariskiConnectedness` (`Contrib/CloudW02Connectedness/Basic.lean` L47) is
  a **theorem**, built on vendored formal functions, finiteness of proper pushforward and flat base change. Step 1's
  "leaf" is therefore proved.
- `ZariskiConn.appTop_bijective_of_generic` (`Contrib/ZariskiConn/Basic.lean` L65) gives `R ≅ Γ(X, 𝒪)` for `X` flat
  and universally closed over an integrally closed `R`, with geometrically integral generic fibre. It applies to
  `R = ℤ_(p)`.

From a code-search survey of `Contrib/CloudW07JacobiansCurves` (declarations read in source by the survey, not
compiled by me):
- `Scheme.arithmeticGenus`, `Modules.H`, `Modules.eulerChar`, `Modules.hFiber`, `Modules.eulerCharFiber` (defs).
- `Modules.isLocallyConstant_eulerCharFiber` (`Cohomology/DirectImage/EulerCharacteristic.lean` L43): χ of a flat
  finitely presented module along a proper morphism is locally constant on the base (step 2).
- `Modules.eulerChar_unit_eq_one_sub_genus` (`Cohomology/DimensionOne.lean` L67).
- `ProjectiveLine.subsingleton_H_one_twist` (`ProjectiveLine/TwistCohomology.lean` L69): `H¹(P¹, 𝒪(d)) = 0` for
  `d ≥ −1`.
- `Scheme.Hom.isRelativeEffectiveCartier_ker_of_section` (`IdealSheaf/Section.lean` L49).
- `nonempty_iso_dual_zeroLocus`, `zeroLocus_finrank` (`Hilbert/SectionPencil/Divisor.lean`): `𝒪(D)` and its fibre
  degree (step 4).
- `hFiber_zero_eq_degree_add_one_sub_genus` and `isFiniteLocallyFreeInDegree_of_positive_fibres`
  (`Modules/PositiveFamilyCohomology.lean` L78, L103): Riemann–Roch on the fibres, and local freeness of `f_*L` with
  base change when the fibre degree exceeds `2g − 2`. This is step 4 for a family that is proper, smooth of relative
  dimension 1 and geometrically irreducible.
- `ProjectiveSpace.homOfSections`, `ProjectiveSpace.exists_hom_twistRestrict` (`ProjectiveSpace/OfSections.lean`,
  `Invertible.lean`): maps to `ℙ(Fin 2; S)` from generating sections (step 5, the map).
- p1-quot's `QuotientP1/P1Scheme.lean` already converts between `ℙ(ULift (Fin 2); Spec ℚ)` and `ToP1` charts over `ℚ`.

What is **missing**, per the survey:
- a theorem that a genus-0 curve with a degree-1 line bundle and two sections has no base points, or that the
  resulting map is an isomorphism onto `P¹`;
- a fibrewise isomorphism criterion for maps to `ℙ(Fin 2; S)`;
- a named theorem `arithmeticGenus (P¹_k) = 0`. Its pieces exist.

### 5.3 Candidate printed forms (rated)

| statement | printed? | use |
|---|---|---|
| L4 itself: a smooth proper model of `P¹_K` over a DVR is `P¹_R` | **not located**. It may be an exercise or remark in Liu, AGAC §9.3 or §10.1 (UNVERIFIED, unread) | would make L4 a LEAF, and the fold pay −1, if found and read |
| Over a field: a smooth proper geometrically connected curve of genus 0 with a rational point is `≅ P¹_k` | **yes, STANDARD** (e.g. Hartshorne IV Ex. 1.x; Liu §7.4; Stacks, *Algebraic Curves*, "curves of genus zero"; all UNVERIFIED) | step 5 on fibres; does not give L4 alone |
| A smooth proper `S`-curve with geometrically connected genus-0 fibres and a section, over a local base, is `P¹_S` (equivalently `P(f_*𝒪(σ))` with `f_*𝒪(σ)` free) | standard, but **not located** in print (UNVERIFIED) | steps 4–5; with steps 1–3 (Lean glue) it gives L4 |
| EGA III 7.7.5 / 7.9.4 (cohomology and base change; constancy of χ) | yes (UNVERIFIED locators) | **not needed as leaves**: the needed forms are proved in CloudW07 (above) |

**Verdict on L4: still a consequence (GLUE).** I could not name a printed statement with confidence. In my view it
should be formalized rather than cited: every textbook input in steps 1–4 is already a Lean theorem in the vendored
libraries.

### 5.4 Formalization plan for L4 (not started in Lean; SPECULATIVE sizes)

1. `GeometricallyConnected 𝒵.hom`. Inputs: `ZariskiConnectedness_proof`, `appTop_bijective_of_generic`, and
   `app_bijective_of_appTop_bijective`. The generic fibre is geometrically integral via `genFib ≅ ℙ(Fin 2; Spec ℚ)`
   (p1-quot's `p1SchemeQ_body`) and the CloudW07 `ProjectiveLine` instances. Smooth plus geometrically connected
   gives geometrically irreducible (Tau Ceti `Smooth.geometricallyIntegral`). ~300 lines.
2. Genus 0 of every fibre. Inputs: `isLocallyConstant_eulerCharFiber` (Spec of a DVR is connected), `H¹(P¹_ℚ, 𝒪) = 0`
   transported along the generic fibre, and `hFiber_pullback_of_isPullback`. ~400 lines.
3. A section, from the valuative criterion. ~200 lines.
4. `L = 𝒪(σ)` of fibre degree 1, then `isFiniteLocallyFreeInDegree_of_positive_fibres`: `f_*L` is free of rank 2 over
   the local ring. ~400 lines.
5. Base-point freeness on the genus-0 fibres. **Missing in the libraries**; needs `L(−x) ≅ 𝒪` and `h⁰(𝒪) = 1` on the
   fibre. ~600+ lines.
6. `φ : 𝒵 → ℙ(Fin 2; S)` by `exists_hom_twistRestrict`. ~200 lines.
7. `φ` is an isomorphism. **Missing**: degree-1 maps of smooth proper curves are isomorphisms, and a fibrewise
   isomorphism criterion (flat + proper + fibrewise iso). ~800+ lines.
8. `ℙ(Fin 2; Spec ℤ_(p)) ≅ 𝒵` to `IsP1Coordinate` charts, adapting `P1Scheme.lean` from `ℚ` to `ℤ_(p)`. ~300 lines.

Total is several thousand lines. Steps 5 and 7 carry most of the risk. If L4 is crowdsourced, I suggest splitting it
into steps 1–2 ("the fibres are geometrically integral of genus 0") and steps 3–8 ("lift").

## 6. Deliverables and reproduction

- `ZInQKernel/Contrib/OneProof/QuotientP1Smooth.lean`: `quotientP1Coordinate_of_fields4`. It imports
  `QuotientP1Printed`, `QuotientP1/TameQuotSmooth` and `DeligneComponentsY3Used`, never `Main`.
- `ZInQKernel/Contrib/OneProof/QuotientP1/TameQuotSmooth.lean`: the scheme part (§2.2). Generated from
  `scratch/p1-quot3/Scheme.lean` by adding a header and the two `HDec.MCRGlue` wrappers. It imports `TameInvariants`,
  p1-quot2's `QuotProper` and `TailR` (for `CurveSplit.RegularSmoothPerfect`).
- `ZInQKernel/Contrib/OneProof/QuotientP1/TameInvariants.lean`: the algebra (§2.1). Generated from
  `scratch/p1-quot3/Invariants.lean` by renaming the namespace. It imports Mathlib, `Contrib/Dim` and the vendored
  FLT theorem.
- `scratch/p1-quot3/autofold.json`: discharges `quotientP1Coordinate` by `quotientP1Coordinate_of_fields4`, with
  - new leaves `lichtenbaumProjective` (published), `finiteQuotientExists` (published), `smoothModelOfP1`
    (consequence) and `edixhovenFixedSmooth2` (published). Flags are left empty, so autofold marks the published ones
    "unread";
  - chain fields `{t}.regularSmoothPerfect`, `{t}.mumfordTorsionAlgClosed`, `{r}.mumfordGroupLaw`,
    `{r}.shimuraMainThmIDeligneY3AbU`, `{t}.uniformizationLeafAll` and `{t}.gagaMorphism`.

  The spec is independent of dcy3-used's pending bypass: it reads no field of `{l}`.
- Build tree: a copy of `~/dzq-wt/p1-quot2/.lake/build` and `lean/.lake/build` (19793c5d), then `lake build` of the
  merged tree (6 min).

```
lake build ZInQKernel.Contrib.OneProof.QuotientP1Smooth
lake env lean scratch/p1-quot3/Invariants.lean        # algebra, scratch copy
lake env lean scratch/p1-quot3/Scheme.lean            # scheme part, scratch copy
lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
lake env lean scratch/p1-quot3/Discharges.lean        # #discharges
python3 scripts/one_proof/autofold.py scratch/p1-quot3/autofold.json --dry-run
```
