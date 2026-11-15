# p1-quot3: `quotientP1Coordinate` now rests on printed leaves and chain fields only; the fold pays −1

Task p1-quot3, 2026-11-15. Base `wip/p1-quot2` (19793c5d), with `origin/wip/dcy3-used` (36240662, which contains
leaf-fold23) merged cleanly (6abfc715). Target: the bundle field `HDec.HSyn.OpenGlue7.quotientP1Coordinate`, of type
`HDec.MCRGlue.QuotientP1Coordinate` (`ZInQKernel/OneProof/H/TailW.lean`, unchanged). Scratch: `scratch/p1-quot3/`,
results log `scratch/p1-quot3/log.md`. No statement was changed. Nothing under `ZInQKernel/` was edited; new files
were added under `ZInQKernel/Contrib/OneProof/` only.

Marks: **VERIFIED** = compiled, or read in a source file. **STANDARD** = a published theorem with its reference.
**UNVERIFIED** = a locator recalled from memory (there is no network here).

## 1. Main result

**Both of p1-quot2's non-printed inputs are gone.**

1. **L3 is proved.** p1-quot2's residual glue `HDec.MCRGlue.TameQuotientSmoothRelDim` (the smoothness half of mcr-glue's
   L3) is now a theorem. It uses only the chain's existing textbook field `regularSmoothPerfect` (Stacks 00TV). With
   p1-quot2's properness half, all of L3 (`TameQuotientSmooth`) is proved (§2).
2. **L4 is bypassed.** L4 `SmoothModelOfP1` is no longer an input. It is not proved in its general form; the proof
   simply does not need it. p1-quot's route took some coordinate `ρ'₀ : 𝒵 ≅ P¹_{ℤ_(p)}` from L4 and then normalized
   it with the three CM sections. Now the generic coordinate itself is shown to extend to `𝒵 ≅ P¹_{ℤ_(p)}`, using
   that the CM sections are pairwise disjoint (§3). That disjointness was already proved by p1-quot, from Edixhoven's
   theorem.

```lean
-- ZInQKernel/Contrib/OneProof/QuotientP1Model.lean
theorem HDec.MCRQuot.quotientP1Coordinate_of_fields5
    (hL : QuotientP1Proof.LichtenbaumProjective)      -- printed leaf (Lichtenbaum 1968 Thm 2.8; p1-quot2)
    (hQE : FiniteQuotientExists)                      -- printed leaf (mcr-glue L2: SGA 1 Exp. V 1.8)
    (hE : EdixhovenFixedSmooth2)                      -- printed leaf (Edixhoven 1992 Prop. 3.4; p1-quot)
    (hRS : CurveSplit.RegularSmoothPerfect)           -- textbook field {t}
    (hMT : AvSplit.MumfordTorsionAlgClosed)           -- textbook field {t}
    (hM : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)        -- research field {r} (leaf-fold23)
    (hU3 : RayClassCFT.ShimuraMainThmIDeligneY3AbU)            -- research field {r} (dcy3-used's route)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll)     -- textbook field {t}
    (hG : ZInQ.HomLattice.GAGAMorphism) :                      -- textbook field {t}
    MCRGlue.QuotientP1Coordinate
```

Following the task's note, `HeckeIrreducible` comes from dcy3-used's `DCY3Used.y3Connected_of_leaves hM hU3`. p1-quot2
got it from `mumfordRigidityCore` and `deligneComponentsY3PrintedAb`. The first of those fields is now
`mumfordGroupLaw` (leaf-fold23), and the second is removed by dcy3-used's bypass.

Strict count, from `autofold.py --dry-run` (no `--allow-rise` needed):

| | GLUE inputs of the discharge | autofold strict count | strictest |
|---|---|---|---|
| p1-quot2 (`fields3`) | L3-smooth (composite), L4 (consequence) | 46/10 on 56 → 49/11 on 60 (+1) | 45/11 → 48/12 |
| p1-quot3 interim (`fields4`, L3 proved) | L4 | 46/10 on 56 → 49/10 on 59 (0) | 45/11 → 48/11 |
| **p1-quot3 (`fields5`)** | **none** | **46/10 on 56 → 49/9 on 58 (−1)** | **45/11 → 48/10** |

VERIFIED (compiled; outputs in `scratch/p1-quot3/`):

- `lake build ZInQKernel.Contrib.OneProof.QuotientP1Model` succeeds on the merged tree, with all helpers. There is no
  `sorry` and no `axiom`.
- `#discharges` (`Discharges5.lean`, output `discharges5_out.txt`) prints
  `DISCHARGES [OpenGlue7.quotientP1Coordinate] by HDec.MCRQuot.quotientP1Coordinate_of_fields5`. It still assumes
  exactly the three printed leaves and six chain fields above. Its axioms are `[propext, Classical.choice, Quot.sound]`
  (63 open hypotheses, 2614 theorems checked).
- `scratch/p1-quot3/autofold.json` passes `--dry-run` without `--allow-rise` (output `autofold_dryrun.txt`). With
  line 1 stripped, the generated module (`FoldDry.lean`: `OpenGlue8`, `sixContactMin_of_open30`) compiles against
  TailZ35, and `sixContactMin_of_open30` depends on the standard axioms only.
- The interim `quotientP1Coordinate_of_fields4` (L3 proved, L4 still assumed; `QuotientP1Smooth.lean`) also compiles
  and is discharged (`discharges_out.txt`).

## 2. L3: `TameQuotientSmoothRelDim` is proved

The statement is p1-quot2's, unchanged (`QuotientP1/QuotProper.lean`):
- `q : 𝒴 → 𝒵` over `ℤ_(p)` is an SGA 1 quotient (`IsGQuotient`) and is finite;
- `𝒴` is proper and smooth of relative dimension 1;
- `G` is finite with `p ∤ |G|`.

The conclusion is `SmoothOfRelativeDimension 1 𝒵.hom`. The result is
`HDec.MCRGlue.tameQuotientSmoothRelDim_of_regularSmoothPerfect` (`QuotientP1/TameQuotSmooth.lean`).

| step | Lean | how |
|---|---|---|
| normality descends to invariants | `QuotientP1Proof.TameQuot.isDomain_isIntegrallyClosed_atPrime` | elementwise: prime avoidance over `g • 𝔫`, then norms `∏ g • w`. It needs no decomposition into domains and no condition on `|G|` |
| over a perfect field | `smooth_of_invariants_field` | smooth algebras have normal local rings (vendored FLT). So invariants of dimension `≤ 1` are Dedekind, hence regular; then `RegularSmoothPerfect` (Stacks 00TV) |
| base change | `reynolds`, `exists_retraction`, `fibre_invariants` | the Reynolds operator `|G|⁻¹ Σ g` splits the invariants off, so they commute with `κ ⊗_R –` |
| over `ℤ_(p)` | `smooth_of_invariants` | flat as a retract; smooth fibres; Mathlib's `Algebra.Smooth.of_formallySmooth_fiber` (EGA IV 17.5.1) |
| on schemes | `invariant_setup`, `smooth_appLE`, `relDim_eq_one` | `G` acts on `Γ(𝒴, q⁻¹V)`; smooth on every affine chart; every standard smooth chart has relative dimension 1, because fibres of `𝒵` and of `𝒴` have equal dimension |

No new leaf. The one statement used is the chain field `CurveSplit.RegularSmoothPerfect`, a textbook field of
`OpenTextbookLeaves11`.

## 3. L4 bypassed: the generic coordinate extends to `P¹_{ℤ_(p)}`

**What L4 was used for** (p1-quot's `quotientP1Coordinate_of_printed2`):
1. `𝒵 = 𝒴/G` has generic fibre `P¹_ℚ` in the coordinate `σ'`, the descent of `π`.
2. L4 gave some isomorphism `ρ'₀ : 𝒵 ≅ P¹_{ℤ_(p)}`.
3. `coordinateFromSections_of''` moved `ρ'₀` by `PGL₂(ℤ_(p))` so that the three CM points take the values
   `0, ∞, −16/27`, which gives `CoordFibres`.

**New route.** By R2fp, `σ'` already takes the values `0, ∞, −16/27` at the CM points, and their closures in `𝒵` are
pairwise disjoint (p1-quot's `cMSectionsDisjoint'_of`, from Edixhoven). A standard argument then shows `σ'` extends to
an isomorphism `𝒵 ≅ P¹_{ℤ_(p)}`, so L4 is never needed. The theorem is `HDec.MCRGlue.P1Model.exists_p1Coordinate`
(`QuotientP1/P1ModelE.lean`):

> `𝒵` integral, proper, smooth of relative dimension 1 over `ℤ_(p)`, with generic fibre `P¹_ℚ` by charts `σ`, and
> three generic-fibre points (`σ = 0`, `σ = ∞`, `σ = c` with `c ∈ ℤ_(p)^×`) whose closures are pairwise disjoint.
> Then there is `ρ` with `IsP1Coordinate 𝒵 ρ` and `ρ = σ` on the generic fibre.

The proof (all compiled):

| step | Lean (helper) | how |
|---|---|---|
| `Γ(P¹ by charts over ℚ) = ℚ`; `Γ(𝒵, 𝒪) = ℤ_(p)` | `psiTop_surjective`, `appTop_bijective` (P1ModelA) | Laurent-polynomial degree argument; the zariski-conn argument with charts instead of geometric integrality |
| special fibre irreducible, generic point `ξ` | `geometricallyConnected`, `isIntegral_fiber`, `xi` (P1ModelA) | Zariski's connectedness theorem (**proved** in `Contrib/CloudW02Connectedness`); smooth plus connected gives integral fibres (Tau Ceti) |
| points of codimension `≤ 1` lie in `D(p) ∪ {ξ}` | `eq_xi_of_ringKrullDim_le_one` (P1ModelA) | coheight argument |
| sections extend over codimension `≥ 2` | `extend_open` (P1ModelB) | vendored FLT extension theorem for morphisms to affine schemes, with target `Spec ℤ[X]` |
| if `t ∈ 𝒪_ξ`, it extends off the pole | `extend_of_isInteger` (P1ModelC) | glue the chart section with a germ at `ξ`, then extend |
| the third section forces `t` to be a unit at `ξ` | `isUnit_germ_of_third` (P1ModelC) | at the point of the third section in the special fibre, both `t` and `t − c` would vanish |
| both chart coordinates extend; a chart structure `ρ` | `exists_extensions`, `exists_toP1` (P1ModelC) | `𝒪_ξ` is a DVR (vendored FLT), hence a valuation ring; `t·t⁻¹ = 1` on the overlap |
| chart rings are polynomial rings | `xi_mem_basicOpen_eval`, `eval_bijective` (P1ModelE) | the reduction of `t` at `ξ` is transcendental over `𝔽_p`, by induction on the degree, using the zero section. Then clear denominators |
| the map `φ : 𝒵 → P¹_{ℤ_(p)}` is finite, so the charts are affine | `finite_preimage_of_dim_le_one`, `isFinite_phi` (P1ModelE); P¹ by charts over any base (P1ModelD, from p1-quot's P1Scheme) | fibres of `φ` are finite: closed points map to closed points (Mathlib `closedPoints_subset_preimage_closedPoints`) and the fibres have dimension `≤ 1`. Then Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite` |

Assembly (`QuotientP1Model.lean`):
- `coordinateFromSectionsGen_of` is mcr-quot's glue C2 without the hypothesis `IsP1Coordinate 𝒵 ρ'₀`. Its proof
  reuses p1-quot's descent and fibre arguments, with the CM values read off `σ'`.
- `quotientP1Coordinate_of_printed3` adds `𝒵` integral: `q` is surjective and `𝒵` has domain stalks.
- `quotientP1Coordinate_of_fields5` instantiates the chain's fields.

**General L4 is not proved.** `SmoothModelOfP1` without sections stays open as a statement. It is no longer an input
of the discharge, and nothing else in the chain uses it. Report §5 of the interim version (in git history, commit
`p1-quot3: report`) gave the cohomological plan for the general statement.

## 4. Leaves of the fold, rated

| leaf | kind | printed form? | reason |
|---|---|---|---|
| `lichtenbaumProjective` | published | yes, special case; flag **unread** | p1-quot2 §3.1: Lichtenbaum, Amer. J. Math. 90 (1968) Thm 2.8; Liu, AGAC Thm 8.3.16 (UNVERIFIED) |
| `finiteQuotientExists` (L2) | published | yes, special case | SGA 1 Exp. V Prop. 1.8 with 1.1 (UNVERIFIED); mcr-glue's rating |
| `edixhovenFixedSmooth2` | published | yes, special case; flag **unread** | Edixhoven, Compositio 81 (1992) Prop. 3.4 (UNVERIFIED); p1-quot's rating |

I added no new leaf. Every other input is a field the chain already has. No new row is needed in
`docs/research/locators.md`; p1-quot2's proposed row for `LichtenbaumProjective` still stands. Vendored theorems
used, which are proved in their vendored trees:
- Zariski connectedness (CloudW02);
- FLT's normality and DVR stalks of smooth schemes over a DVR or a UFD;
- the extension theorem;
- Tau Ceti's integrality of smooth connected schemes over a field.

## 5. Deliverables and reproduction

New files under `ZInQKernel/Contrib/OneProof/`; none imports `Main`:
- `QuotientP1Model.lean`: the final theorem `quotientP1Coordinate_of_fields5`, plus `coordinateFromSectionsGen_of`
  and `quotientP1Coordinate_of_printed3`. From `scratch/p1-quot3/L4F.lean`.
- `QuotientP1Smooth.lean`: the interim `quotientP1Coordinate_of_fields4`.
- `QuotientP1/TameInvariants.lean` (algebra, from `Invariants.lean`) and `QuotientP1/TameQuotSmooth.lean` (schemes,
  from `Scheme.lean`): L3.
- `QuotientP1/P1ModelA.lean` … `P1ModelE.lean`: L4's bypass, from `L4A.lean` … `L4E.lean`.

Other deliverables:
- `scratch/p1-quot3/autofold.json`: discharges `quotientP1Coordinate` by `quotientP1Coordinate_of_fields5`, with
  - new leaves `lichtenbaumProjective`, `finiteQuotientExists` and `edixhovenFixedSmooth2`, all published. Flags are
    left empty, so autofold marks them "unread";
  - chain fields `{t}.regularSmoothPerfect`, `{t}.mumfordTorsionAlgClosed`, `{r}.mumfordGroupLaw`,
    `{r}.shimuraMainThmIDeligneY3AbU`, `{t}.uniformizationLeafAll` and `{t}.gagaMorphism`.

  It reads no field of `{l}`, so it is independent of dcy3-used's pending bypass.
- Build tree: a copy of `~/dzq-wt/p1-quot2/.lake/build` and `lean/.lake/build` (19793c5d), then `lake build` of the
  merged tree.

```
lake build ZInQKernel.Contrib.OneProof.QuotientP1Model
lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
lake env lean scratch/p1-quot3/Discharges5.lean       # #discharges
python3 scripts/one_proof/autofold.py scratch/p1-quot3/autofold.json --dry-run
```
