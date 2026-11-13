# neron-lg: the Néron glue `NeronLocalToGlobal` and `SemistableLocalToGlobal`

Status: research note (task neron-lg, 2026-11-13).

- **Lean:** `scratch/neron-lg/NeronLG.lean` (about 850 lines). It imports only
  `ZInQKernel.HDecomp.Faltings.H5BaseChange` and was checked with `lake env lean`. It has no `sorry`
  and no `axiom`. All 13 `#print axioms` list only `propext`, `Classical.choice` and `Quot.sound`
  (VERIFIED).
- **Results log:** `scratch/neron-lg/log.md`.
- **Statements under study:** the two glue Props of task tau-n1n2 (`scratch/tau-n1n2/N1N2.lean`,
  `docs/research/tau-n1n2.md`). §1 of the Lean file copies them verbatim, with every definition
  they use, by slicing the source lines with a script.
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = an estimate. **UNVERIFIED** = a locator from
memory (there is no network).

## 0. Main result

**Verdict.**
1. Both glue Props are true as stated and are not vacuous. An independent model review found no
   problem (§5).
2. Neither can be proved outright in Lean today. Every proof needs spreading out of schemes over
   `𝓞_L[1/f]` (EGA IV §8), gluing of group schemes, and identity components of group schemes.
   None of these is in Mathlib v4.35, and the project cannot yet build a nonzero `AbVar`.
3. Both are now **reduced in Lean** to smaller pieces. The reduction is proved and compiles
   (VERIFIED). The pieces are:
   - one new **leaf**, NL `NeronLocalOnBase` (BLR §1.2 Prop. 4: the Néron property is local on a
     Dedekind base);
   - six smaller **glue** statements, each doing one geometric step.

   The combinatorial and commutative-algebra parts of the old glue are now Lean proofs:
   - the finite subcover;
   - the classification of the DVRs of a number field;
   - the finiteness of the bad places;
   - composita of finitely many fields;
   - localization of Néron models.

```lean
theorem ZInQ.NeronLG.neronLocalToGlobal_of
    (hsp : AbVarSpreadsOut)       -- glue N1-g1: B spreads out to an abelian scheme over 𝓞_L[1/f]
    (hloc : NeronLocalOnBase)     -- leaf NL: BLR §1.2 Prop. 4
    (hnear : NeronNearPoint)      -- glue N1-g2: a local Néron model spreads out to some D(g) ∋ v
    (hglue : NeronGlueAway) :     -- glue N1-g3: Néron models glue along a finite Zariski cover
    NeronLocalToGlobal

theorem ZInQ.NeronLG.semistableLocalToGlobal_of
    (hloc : NeronLocalOnBase) (hsp : AbVarSpreadsOut)
    (h1 : GoodPlacesAnyField)     -- proved from glue N2-g1' GoodPlaceAnyField (goodPlacesAnyField_of)
    (h2 : LocalSemistableMono)    -- glue N2-g2: the local statement persists in larger fields
    (h3 : SemistableGlobalOfLocal) : -- glue N2-g3: with one field L₀ at all places, glue to 𝒩'⁰
    SemistableLocalToGlobal

theorem ZInQ.NeronLG.n1_n2_of_leaves_and_glue
    (hloc1 : LocalNeronModelExists) (hab : AbelianSchemeIsNeron)
    (hloc2 : LocalSemistableIdentityComponent) (hNL : NeronLocalOnBase)
    (g1 : AbVarSpreadsOut) (g2 : NeronNearPoint) (g3 : NeronGlueAway) (g4 : GoodPlaceAnyField)
    (g5 : LocalSemistableMono) (g6 : SemistableGlobalOfLocal) :
    NeronModelExists ∧ SemistableNeronIdentityComponent
```

The last theorem is the whole Néron package. N1 and N2 (h5-neron, in the build at
`ZInQKernel/HDecomp/Faltings/H5Neron.lean`) follow from four leaves (N1-loc, N1-ab and N2-loc of
tau-n1n2, plus NL) and six glue statements.

Other results, all proved (VERIFIED):

| Lean theorem | statement |
|---|---|
| `dvrAt_center` | every DVR valuation subring `O` of a number field `K` is `𝓞_{K,v}` (`dvrAt v`, the ring of the `v`-adic valuation) for its center `v = 𝔪_O ∩ 𝓞_K`, a nonzero prime |
| `ringOfIntegers_mem` | `𝓞_K ⊆ O` for every valuation subring `O` of `K` |
| `badPlaces_finite` | for `f ≠ 0` in `𝓞_K`, only finitely many DVRs `O ⊂ K` miss `1/f` |
| `neronModelOver_localize` | given NL, a Néron model over `𝓞_L` base-changes to a Néron model over every DVR `O ⊂ L` (with `gen` transported, as a group isomorphism: `isMonHom_bcGenO`) |
| `localNeronModelExists_of_self` | the leaf N1-loc follows from N1-self (BLR §1.4 Thm 3) and NL, so N1-loc is not stronger than the published statements |
| `localNeronModelsOf` | N1 and NL give Néron models of `A_{L₀}` over every DVR of every `L₀` |
| `neronOverAway_of_abelian` | given N1-ab, an abelian scheme over `𝓞_L[1/f]` (`f ≠ 0`) is a Néron model there. So N1-g2 is needed only at the primes dividing `f` (Mathlib supplies Dedekind, domain and fraction field for the localization) |
| `compositumFinset` | finitely many number fields over `K` embed in one number field (iterating `H5Neron.compositum`) |
| `semistableCommonField` | from N2-g1, N2-g2 and the local leaf at every DVR: one field `L₀` works at every DVR |
| `goodPlacesAnyField_of` | N2-g1 (a finite exceptional set of DVRs) from N2-g1' (one good DVR at a time) and `badPlaces_finite` |

## 1. The new leaf NL

`NeronLocalOnBase`. Let:
- `R` be a Dedekind domain whose fraction field is a number field `L`;
- `B` an abelian variety over `L`;
- `G` a smooth, separated, quasi-compact `R`-scheme, with an isomorphism `gen` from its generic
  fibre to `B`.

Then `G` has the Néron mapping property over `R` if and only if, for every DVR `O ⊂ L` containing
`R`, the base change `G ×_R O` has it over `O`. Over `O`, the generic-fibre identification is
`bcGenO`: `(G ×_R O) ×_O L ≅ G ×_R L ≅ B`.

Source: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Prop. 4 (UNVERIFIED locator). There it is
stated for any smooth separated `K`-scheme of finite type and any smooth separated `R`-model of
finite type, so NL is a special case. "Smooth and quasi-compact" gives finite type.

Checks:
- **Field case** (reviewer). If `R = L`, no DVR contains `R`, so the right side is vacuous. The
  left side holds trivially. So the equivalence holds.
- **Choice of `gen` is irrelevant.** Whether the mapping property holds does not depend on which
  isomorphism `gen` is used.

Use:
- the ⇐ direction is used by N1-g2;
- the ⇒ direction proves `neronModelOver_localize`.

It replaces two textbook facts that tau-n1n2's glue sketches used silently: Néron models are
compatible with localization, and the Néron property is local on the base.

## 2. `NeronLocalToGlobal` (tau-n1n2's N1-glue)

| name | kind | statement | proof sketch / source |
|---|---|---|---|
| `AbVarSpreadsOut` (N1-g1) | glue (candidate textbook leaf) | for every `B` over a number field `L` there is `f ≠ 0` in `𝓞_L` such that `B` extends to an abelian scheme (smooth, proper `GrpObj`, with `gen` a group isomorphism) over every presentation of `𝓞_L[1/f]` | EGA IV₃ 8.8.2 (schemes, morphisms, group axioms), 8.10.5 (xii) (proper), IV₄ 17.7.8 (smooth), UNVERIFIED. Mathlib has the descent of morphisms (AffineTransitionLimit, EGA IV 8.8.2) but not of schemes, properness or smoothness |
| `NeronNearPoint` (N1-g2) | glue (assumes N1-ab, NL) | given an abelian scheme over `𝓞_L[1/f]` and a Néron model over `𝓞_{L,v}`, there is `g ∉ v` with a Néron model over `𝓞_L[1/g]` | spread `𝒩_v` out to some `𝓞_L[1/h]`. The canonical map to the abelian scheme is an isomorphism off a finite set `Z ∌ v` of closed points. Choose `g ∉ v` by prime avoidance; then N1-ab holds at every `w ≠ v` and NL (⇐) applies |
| `NeronGlueAway` (N1-g3) | glue (no literature) | if `g₁,…,gₙ` generate `(1)` and `B` has Néron models over every `𝓞_L[1/gᵢ]`, it has one over `𝓞_L` | restrict to the overlaps; identify them by unique isomorphisms (`NeronProp.uniqueIso`), which satisfy the cocycle condition; glue the schemes, group laws and `gen`; morphisms from a smooth `Y` glue by uniqueness |

**Proved assembly** (`neronLocalToGlobal_of`):
1. Let `S` be the set of `g` with a Néron model over `𝓞_L[1/g]`.
2. If `span S ≠ (1)`, it lies in a maximal ideal `m`.
3. `m ≠ 0`, because `𝓞_L` is not a field (`Ring.ne_bot_of_isMaximal_of_not_isField`). So `m` is a
   nonzero prime `v`.
4. The hypothesis of the glue gives a Néron model over the DVR `dvrAt v` (its DVR instance is in
   Mathlib).
5. N1-g2 gives `g ∉ v` with `g ∈ S ⊆ m = v`, a contradiction.
6. So `span S = (1)`, and `Ideal.span_eq_top_iff_finite` gives a finite subfamily. N1-g3 finishes.

The statements quantify over every presentation `R` of `𝓞_L[1/g]`: an `𝓞_L`-algebra with
`IsLocalization.Away g R` and a compatible map to `L`. This avoids choosing an algebra map
`Localization.Away g → L`. Two remarks:
- **Harmless.** All presentations are isomorphic.
- **`g = 0`.** It is vacuous, since the zero ring has no map to `L`. That is harmless in N1-g3
  (reviewer).

## 3. `SemistableLocalToGlobal` (tau-n1n2's N2-glue)

`LocalSemistableWith A O L₀` is the body of `LocalSemistableAt A O` for a fixed field `L₀`
(`localSemistableAt_iff`, `Iff.rfl`).

| name | kind | statement | proof sketch |
|---|---|---|---|
| `GoodPlaceAnyField` (N2-g1') | glue (assumes N1-ab) | if `A` extends to an abelian scheme over `𝓞_K[1/f]` and `1/f ∈ O`, then `LocalSemistableWith A O L₀` holds for **every** `L₀` | the base changes of the abelian scheme to `O₀` and `O'` are Néron by N1-ab. So `𝒩₀`, `𝒩'` are those base changes (`NeronModelOver.uniqueIso`). Take `U = 𝒩'`, `i = 𝟙`, `j` the composite isomorphism |
| `LocalSemistableMono` (N2-g2) | glue (assumes local Néron models of `A`, `LocalNeronModelsOf A`, which N1 and NL give: `localNeronModelsOf`) | `LocalSemistableWith A O L₀ → LocalSemistableWith A O L₁` for `L₁ ⊇ L₀` | let `O₀ = O₁ ∩ L₀`. Apply the `L₀`-statement to `L'` and to `L₁`, base-change the second to `O'`, and intersect the two open subgroups of `𝒩₀ ×_{O₀} O'` |
| `SemistableGlobalOfLocal` (N2-g3) | glue (assumes NL) | if `LocalSemistableWith A O L₀` holds at every DVR `O ⊂ K`, then for all Néron `𝒩₀` over `𝓞_{L₀}`, `𝒩'` over `𝓞_{L'}` and base change `𝒱` of `𝒩₀`, some `𝒰` is an open subgroup of `𝒩'` and of `𝒱` | locally `i = c ∘ j` for the canonical `c : 𝒱 → 𝒩'` (schematic density of the generic fibre of a flat `U`, separatedness). Take `𝒰 = 𝒱⁰` (SGA 3 VI_B 3.10). Being an open immersion spreads out (EGA IV 8.10.5) and is local on the base |

**Proved assembly** (`goodPlacesAnyField_of`, `semistableCommonField`, `semistableLocalToGlobal_of`):
1. By N1-g1, `A` has an abelian scheme over `𝓞_K[1/f]`.
2. The DVRs missing `1/f` form a finite set `T` (`badPlaces_finite`, which rests on
   `dvrAt_center` and `Ideal.finite_factors`). Outside `T`, N2-g1' gives every `L₀`.
3. For `O ∈ T`, choose the field `L₀(O)` of the hypothesis. Take the compositum `M` of these
   finitely many fields (`compositumFinset`). N2-g2 lifts each local statement to `M`.
4. N1 gives `𝒩₀` over `𝓞_M`. The proved glue H4b (`H5Neron.groupModelBaseChangeExists`) gives
   `𝒱`. N2-g3 gives `𝒰`.

## 4. What remains

- **Leaves** (literature):
  - N1-loc, N1-ab, N2-loc (tau-n1n2);
  - NL (new; BLR §1.2 Prop. 4, locator UNVERIFIED and to be checked).
- **Glue** (algebraic geometry missing from Mathlib, to be done by the project):
  - N1-g1 (spreading out; a candidate textbook leaf);
  - N1-g2 (spreading out a local model plus NL);
  - N1-g3 (Zariski gluing of Néron models; no literature input);
  - N2-g1' (base change of abelian schemes plus uniqueness; no new geometry beyond N1-ab);
  - N2-g2 (intersections of open subgroup schemes);
  - N2-g3 (identity components, schematic density, spreading out of open immersions).
- **Not done:** none of the six glue statements is proved in Lean.
  - N2-g1' is the closest. Its proof uses only base change, N1-ab and `NeronModelOver.uniqueIso`.
    What remains is a diagram chase through pullback-composition isomorphisms
    (SPECULATIVE: a few hundred lines in the style of `H5BaseChange.bcGen'`).
  - The others need Mathlib infrastructure:
    - descent of schemes and of properties along limits;
    - gluing of `Over`-group objects;
    - the identity component.

**Integration suggestion.**
1. Add `NeronLocalOnBase` to `TextbookLeaves`.
2. Replace tau-n1n2's `NeronLocalToGlobal` and `SemistableLocalToGlobal` in `GluePieces` by the
   six glue Props here. Then `n1_n2_of_leaves_and_glue` supplies `t41` (N1) and N2.
3. Everything is in the single file `scratch/neron-lg/NeronLG.lean`. Its §1 and §5 copies of
   tau-n1n2's statements are verbatim, so after adoption they can be replaced by the originals.

## 5. Independent review

A read-only model review (subagent) checked every new `def` of §2–§4. It found no PROBLEM: each
statement is true and not vacuous, NL is a special case of BLR 1.2/4, and each glue decomposition
is honest. Its points:
- **Assumptions.** The only new outside theorem is NL. Everything else is EGA IV §8, §11 and §17,
  SGA 3 VI_B, and uniqueness of Néron models.
- **Assembly theorems.** They do not exploit a vacuous hypothesis: the set `S` contains `0`
  vacuously, but the argument only uses `g ∉ v`.
- **Five MINOR docstring gaps, all fixed:**
  - N1-g2: the choice of `h' ∉ v` needs prime avoidance, and at `v` itself when `f ∉ v`;
  - N1-g3: elements `gᵢ = 0` are harmless;
  - N2-g1: superfluous locators;
  - N2-g2: details of the generic-fibre equation, including
    `bcProj A L₀ L' = bcProj A L₁ L' ≫ bcProj A L₀ L₁`;
  - N2-g3: `c` is built from the isomorphism of `IsBaseChangeOf` and `𝒩₀.gen`, not from `𝒱.gen`.

There has been no human review.

## 6. Lean notes (VERIFIED)

- **Kernel timeout on one-term chains.** The chain
  `(bcGenO …).hom = pbCompInv ≫ pbEq ≫ gen.hom`, written as one term
  (`(congrArg Iso.hom bcGenO_def).trans ((Iso.trans_hom _ _).trans (congrArg₂ …))`), makes the
  kernel report "deterministic timeout". This happens even with `bcGenO` an `irreducible_def`. The
  same chain split into four separately stated lemmas composed by `.trans` checks at once. This is
  another instance of the iso-chain pattern of h5-neron and tau-n1n2.
- **`mul_one` is shadowed.** `open … MonObj` makes `mul_one` resolve to `MonObj.mul_one`; write
  `_root_.mul_one`.
- **`ι` is a token.** It cannot be used as a binder name here (an open namespace gives it notation).
