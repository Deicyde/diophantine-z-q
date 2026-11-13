# neron-lg: the Néron glue `NeronLocalToGlobal` and `SemistableLocalToGlobal`

Status: research note (task neron-lg, 2026-11-13).

- **Lean:** `scratch/neron-lg/NeronLG.lean` (about 1300 lines). It imports only
  `ZInQKernel.HDecomp.Faltings.H5BaseChange` and was checked with `lake env lean`. It has no `sorry`
  and no `axiom`. All 22 `#print axioms` list only `propext`, `Classical.choice` and `Quot.sound`
  (VERIFIED).
- **Results log:** `scratch/neron-lg/log.md`.
- **Statements under study:** the two glue Props of task tau-n1n2 (`scratch/tau-n1n2/N1N2.lean`,
  `docs/research/tau-n1n2.md`). §1 of the Lean file copies them verbatim, with every definition
  they use, by slicing the source lines with a script (checked again at the end).
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = an estimate. **UNVERIFIED** = a locator from
memory (there is no network).

## 0. Main result

**Verdict.**
1. Both glue Props are true as stated and are not vacuous. An independent model review found no
   problem (§6).
2. Neither can be proved outright in Lean today. Every proof needs spreading out of schemes over
   `𝓞_L[1/f]` (EGA IV §8), gluing of group schemes, and identity components. None of these is in
   Mathlib v4.35, and the project cannot yet build a nonzero `AbVar`.
3. Both are now **reduced in Lean** to:
   - one new **leaf**, NL `NeronLocalOnBase` (BLR §1.2 Prop. 4: the Néron property is local on a
     Dedekind base);
   - **five** smaller **glue** statements, each one geometric step.

   **A sixth glue piece is proved.** N2-g1' (`GoodPlaceAnyField`: at a place where `A` has an
   abelian-scheme model, no field extension is needed) is a Lean theorem from the leaf N1-ab
   (`goodPlaceAnyField`, §4).

   **Alternatively** (§4b), the glue N2-g2 can be removed by stating tau-n1n2's local leaf N2-loc
   with persistence under field extension built in (N2-loc⁺; same sources, SGA 7 IX 3.6 + 3.3).
   That leaves four glue statements (`h5neron_n1_n2_of_leaves_and_glue_mono`).

   The commutative-algebra and combinatorial parts of the old glue are Lean proofs:
   - the finite subcover;
   - the classification of the DVRs of a number field;
   - the finiteness of the bad places;
   - composita of finitely many fields;
   - localization of Néron models.

The whole Néron package (VERIFIED):

```lean
theorem ZInQ.NeronLG.n1_n2_of_leaves_and_glue''
    (hloc1 : LocalNeronModelExists)          -- leaf N1-loc (tau-n1n2): BLR §1.4 Thm 3 over a DVR
    (hab : AbelianSchemeIsNeron)             -- leaf N1-ab  (tau-n1n2): BLR §1.2 Prop 8
    (hloc2 : LocalSemistableIdentityComponent) -- leaf N2-loc (tau-n1n2): SGA 7 IX 3.6 + 3.3
    (hNL : NeronLocalOnBase)                 -- leaf NL (new): BLR §1.2 Prop 4
    (g1 : AbVarSpreadsOut)                   -- glue N1-g1: spreading out to an abelian scheme
    (g2 : NeronNearBadPoint)                 -- glue N1-g2: local Néron model at a bad prime spreads out
    (g3 : NeronGlueAway)                     -- glue N1-g3: Néron models glue on a Zariski cover
    (g5 : LocalSemistableMono)               -- glue N2-g2: local statement persists in larger fields
    (g6 : SemistableGlobalOfLocal) :         -- glue N2-g3: local identity components glue
    NeronModelExists ∧ SemistableNeronIdentityComponent
```

N1 and N2 are h5-neron's Props, in the build at `ZInQKernel/HDecomp/Faltings/H5Neron.lean`.
`h5neron_n1_n2_of_leaves_and_glue` states the same conclusion with the build's own declarations
(`ZInQ.H5Neron.NeronModelExists ∧ ZInQ.H5Neron.SemistableNeronIdentityComponent`), via `Iff.rfl`.
The two glue Props of the task reduce as follows (VERIFIED):

```lean
theorem neronLocalToGlobal_of (hsp : AbVarSpreadsOut) (hloc : NeronLocalOnBase)
    (hnear : NeronNearPoint) (hglue : NeronGlueAway) : NeronLocalToGlobal
theorem neronNearPoint_of (h : NeronNearBadPoint) : NeronNearPoint
theorem semistableLocalToGlobal_of' (hloc : NeronLocalOnBase) (hsp : AbVarSpreadsOut)
    (h2 : LocalSemistableMono) (h3 : SemistableGlobalOfLocal) : SemistableLocalToGlobal
theorem goodPlaceAnyField : GoodPlaceAnyField
```

Other results, all proved (VERIFIED):

| Lean theorem | statement |
|---|---|
| `dvrAt_center` | every DVR valuation subring `O` of a number field `K` is `𝓞_{K,v}` (`dvrAt v`, the ring of the `v`-adic valuation) for its center `v = 𝔪_O ∩ 𝓞_K`, a nonzero prime |
| `ringOfIntegers_mem` | `𝓞_K ⊆ O` for every valuation subring `O` of `K` |
| `badPlaces_finite` | for `f ≠ 0` in `𝓞_K`, only finitely many DVRs `O ⊂ K` miss `1/f` |
| `neronModelOver_localize` | given NL, a Néron model over `𝓞_L` base-changes to a Néron model over every DVR `O ⊂ L` (with `gen` transported, as a group isomorphism: `isMonHom_bcGenO`) |
| `localNeronModelExists_of_self` | the leaf N1-loc follows from N1-self (BLR §1.4 Thm 3) and NL, so N1-loc is not stronger than the published statements |
| `localNeronModelsOf` | N1 and NL give Néron models of `A_{L₀}` over every DVR of every `L₀` |
| `neronOverAway_of_abelian` | given N1-ab, an abelian scheme over `𝓞_L[1/f]` (`f ≠ 0`) is a Néron model there (Mathlib supplies domain, Dedekind and fraction field for the localization) |
| `compositumFinset` | finitely many number fields over `K` embed in one number field (iterating `H5Neron.compositum`) |
| `semistableCommonField` | from N2-g1, N2-g2 and the local leaf at every DVR: one field `L₀` works at every DVR |
| `goodPlacesAnyField_of`, `goodPlacesAnyField` | N2-g1 (a finite exceptional set of DVRs) from N2-g1' and `badPlaces_finite`; hence a theorem |
| `isProper_of_abelian` | where `A` has an abelian-scheme model, every local Néron model `𝒩₀` is proper (N1-ab and uniqueness) |
| `iso_baseChange_of_proper` | if `𝒩₀` is proper, every Néron model `𝒩'` over `O'` is isomorphic to `𝒩₀ ×_{O₀} O'` by a group isomorphism compatible with `gen` (N1-ab and uniqueness) |
| `hasAbelianSchemeAway_zero` | sanity: the conclusion of N1-g1 holds for the zero abelian variety, for every `f` and every presentation of `𝓞_L[1/f]` |
| `genSq`, `genSq_fst`, `genSq_compat`, `bcA`, `bcA_proj`, `pbCompInv_fst` | reusable pasting lemmas for `Over.pullback`. The generic-fibre identification transported along a commutative square of base changes is a group isomorphism and is compatible with the projections. In particular, the first projection of `Over.pullbackComp` is computed (`pbCompInv_fst`, via `conjugateEquiv_counit`) |

## 1. The new leaf NL

`NeronLocalOnBase`. Let:
- `R` be a Dedekind domain whose fraction field is a number field `L`;
- `B` an abelian variety over `L`;
- `G` a smooth, separated, quasi-compact `R`-scheme, with an isomorphism `gen` from its generic
  fibre to `B`.

Then `G` has the Néron mapping property over `R` if and only if, for every DVR `O ⊂ L` containing
`R`, the base change `G ×_R O` has it over `O`. Over `O`, the generic-fibre identification is
`bcGenO`: `(G ×_R O) ×_O L ≅ G ×_R L ≅ B`.

Source: Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Prop. 4 (UNVERIFIED locator; it must be
checked). There it is stated for any smooth separated `K`-scheme of finite type and any smooth
separated `R`-model of finite type, so NL is a special case. "Smooth and quasi-compact" gives
finite type.

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
| `NeronNearBadPoint` (N1-g2) | glue (assumes N1-ab, NL) | given an abelian scheme over `𝓞_L[1/f]`, a prime `v ∋ f` and a Néron model over `𝓞_{L,v}`, there is `g ∉ v` with a Néron model over `𝓞_L[1/g]`. At `v ∌ f`, `g = f` works (`neronNearPoint_of`) | spread `𝒩_v` out to some `𝓞_L[1/h]`. The canonical map to the abelian scheme is an isomorphism off a finite set `Z ∌ v` of closed points. Choose `g ∉ v` by prime avoidance; then N1-ab holds at every `w ≠ v` and NL (⇐) applies |
| `NeronGlueAway` (N1-g3) | glue (no literature) | if `g₁,…,gₙ` generate `(1)` and `B` has Néron models over every `𝓞_L[1/gᵢ]`, it has one over `𝓞_L` | restrict to the overlaps; identify them by unique isomorphisms (`NeronProp.uniqueIso`), which satisfy the cocycle condition; glue the schemes, group laws and `gen`; morphisms from a smooth `Y` glue by uniqueness |

**Proved assembly** (`neronLocalToGlobal_of`):
1. Let `S` be the set of `g` with a Néron model over `𝓞_L[1/g]`.
2. If `span S ≠ (1)`, it lies in a maximal ideal `m`.
3. `m ≠ 0`, because `𝓞_L` is not a field. So `m` is a nonzero prime `v`.
4. The glue's hypothesis gives a Néron model over the DVR `dvrAt v`.
5. N1-g2 gives `g ∉ v` with `g ∈ S ⊆ v`, a contradiction.
6. So `span S = (1)`, and `Ideal.span_eq_top_iff_finite` gives a finite subfamily. N1-g3 finishes.

The statements quantify over every presentation `R` of `𝓞_L[1/g]`: an `𝓞_L`-algebra with
`IsLocalization.Away g R` and a compatible map to `L`. Two remarks:
- **Harmless.** All presentations are isomorphic.
- **`g = 0`.** It is vacuous, since the zero ring has no map to `L`. That is harmless in N1-g3
  (reviewer).

## 3. `SemistableLocalToGlobal` (tau-n1n2's N2-glue)

`LocalSemistableWith A O L₀` is the body of `LocalSemistableAt A O` for a fixed field `L₀`
(`localSemistableAt_iff`, `Iff.rfl`).

| name | kind | statement | proof sketch |
|---|---|---|---|
| `GoodPlaceAnyField` (N2-g1') | **proved** (from N1-ab; §4) | if `A` extends to an abelian scheme over `𝓞_K[1/f]` and `1/f ∈ O`, then `LocalSemistableWith A O L₀` holds for **every** `L₀` | — |
| `LocalSemistableMono` (N2-g2) | glue (assumes local Néron models of `A`, `LocalNeronModelsOf A`, which N1 and NL give: `localNeronModelsOf`) | `LocalSemistableWith A O L₀ → LocalSemistableWith A O L₁` for `L₁ ⊇ L₀` | let `O₀ = O₁ ∩ L₀`. Apply the `L₀`-statement to `L'` and to `L₁`, base-change the second to `O'`, and intersect the two open subgroups of `𝒩₀ ×_{O₀} O'`. Then the generic-fibre equation follows (docstring) |
| `SemistableGlobalOfLocal` (N2-g3) | glue (assumes NL) | if `LocalSemistableWith A O L₀` holds at every DVR `O ⊂ K`, then for all Néron `𝒩₀` over `𝓞_{L₀}`, `𝒩'` over `𝓞_{L'}` and base change `𝒱` of `𝒩₀`, some `𝒰` is an open subgroup of `𝒩'` and of `𝒱` | locally `i = c ∘ j` for the canonical `c : 𝒱 → 𝒩'` (schematic density of the generic fibre of a flat `U`, separatedness). Take `𝒰 = 𝒱⁰` (SGA 3 VI_B 3.10). Being an open immersion spreads out (EGA IV 8.10.5) and is local on the base |

**Proved assembly** (`goodPlacesAnyField_of`, `semistableCommonField`, `semistableLocalToGlobal_of`):
1. By N1-g1, `A` has an abelian scheme over `𝓞_K[1/f]`.
2. The DVRs missing `1/f` form a finite set `T` (`badPlaces_finite`, which rests on
   `dvrAt_center` and `Ideal.finite_factors`). Outside `T`, N2-g1' (proved) gives every `L₀`.
3. For `O ∈ T`, choose the field `L₀(O)` of the hypothesis. Take the compositum `M` of these
   finitely many fields (`compositumFinset`). N2-g2 lifts each local statement to `M`.
4. N1 gives `𝒩₀` over `𝓞_M`. The proved glue H4b (`H5Neron.groupModelBaseChangeExists`) gives
   `𝒱`. N2-g3 gives `𝒰`.

## 4. N2-g1' proved (`goodPlaceAnyField`)

The data: the abelian scheme `𝒜` over `R = Localization.Away f`, with `R → K` given by
`IsLocalization.Away.lift`.
1. **Map to `O₀`.** `1/f ∈ O` gives a ring map `ψ : R → O₀` (`𝓞_K ⊆ O`, `ringOfIntegers_mem`)
   and the commutative square `Spec L₀ → Spec O₀ → Spec R = Spec L₀ → Spec K → Spec R`
   (`IsLocalization.ringHom_ext`).
2. **`𝒩₀` is proper.** `𝒜 ×_R O₀` is smooth and proper, with generic fibre `≅ A_{L₀}` as group
   schemes (`genSq`, `isMonHom_genSq`). By N1-ab it is a Néron model over `O₀`, so it is
   isomorphic to `𝒩₀` (`NeronModelOver.uniqueIso`), and `𝒩₀` is proper (`isProper_of_abelian`).
3. **`𝒩' ≅ 𝒱`.** `𝒱 = 𝒩₀ ×_{O₀} O'` is smooth and proper, with generic fibre
   `(𝒩₀ ×_{O₀} O') ×_{O'} L' ≅ A_{L₀} ×_{L₀} L' ≅ A_{L'}` (`genSq ≪≫ bcA`, a group isomorphism).
   By N1-ab it is Néron, so `φ : 𝒩' ≅ 𝒱` is compatible with `gen` and is a group isomorphism
   (`iso_baseChange_of_proper`).
4. **The witness.** Take `U = 𝒩'`, `i = 𝟙` and `j = φ`. The generic-fibre equation of
   `LocalSemistableAt` reduces, via `gen' = φ_{L'} ≫ gen𝒱`, to the compatibility of `gen𝒱` with
   the projections to `𝒩₀`. That compatibility is `genSq_compat` with `bcA_proj`, which rest on
   `pbCompInv_fst`, `pbCompHom_fst`, `pbEq_fst` and `pbMap_fst`.

## 4b. Alternative: N2-loc⁺ instead of N2-loc and N2-g2

`LocalSemistableIdentityComponentMono` (N2-loc⁺) says: for `A` over `K` and a DVR `O ⊂ K` there is
`L₀` such that `LocalSemistableWith A O L₁` holds for **every** finite `L₁ ⊇ L₀`, not only for
`L₀`. Sources and argument:
- SGA 7 IX Thm 3.6 gives semistable reduction over some `L₀` at the places above `O`.
- Prop./Cor. 3.3 says semistable reduction persists under any further extension, and that the
  identity components of the Néron models then base-change.
- So the canonical choice `U = 𝒩'⁰ ≅ (𝒩₁⁰)_{O'}` works over every `L₁ ⊇ L₀`.

Locators UNVERIFIED. Proved consequences (VERIFIED):
- N2-loc⁺ implies tau-n1n2's N2-loc (`localSemistableIdentityComponent_of_mono`, taking
  `L₁ = L₀`).
- With N2-loc⁺ the compositum argument needs no N2-g2 (`semistableCommonField_mono`).
- `h5neron_n1_n2_of_leaves_and_glue_mono` proves the build's N1 ∧ N2 from:
  - the leaves N1-loc, N1-ab, N2-loc⁺ and NL;
  - the four glue statements N1-g1, N1-g2 (bad primes), N1-g3 and N2-g3.

Which form to adopt is the owner's choice. N2-loc⁺ is closer to how SGA 7 IX is used in practice
("after a finite extension, A has semistable reduction"). N2-loc plus N2-g2 keeps the leaf weaker
and moves the persistence argument into glue.

## 5. What remains

- **Leaves** (literature):
  - N1-loc, N1-ab, N2-loc (tau-n1n2);
  - NL (new; BLR §1.2 Prop. 4, locator UNVERIFIED and to be checked).
- **Glue** (algebraic geometry missing from Mathlib, to be done by the project):
  - N1-g1 (spreading out; a candidate textbook leaf);
  - N1-g2 at bad primes (spreading out a local model plus NL);
  - N1-g3 (Zariski gluing of Néron models; no literature input);
  - N2-g2: intersections of open subgroup schemes and a diagram chase. This is the next candidate:
    the pullback of two open-immersion monoid morphisms is an open subgroup, and the chase is like
    §4's (SPECULATIVE: a day of work);
  - N2-g3 (identity components, schematic density, spreading out of open immersions).
- **Not done:** N1-g1, N1-g2, N1-g3, N2-g2 and N2-g3 are not proved in Lean. Beyond N2-g2, they
  need Mathlib infrastructure:
  - descent of schemes and of properties along limits;
  - gluing of `Over`-group objects;
  - the identity component.

**Integration suggestion.**
1. Add `NeronLocalOnBase` to `TextbookLeaves`.
2. Replace tau-n1n2's `NeronLocalToGlobal` and `SemistableLocalToGlobal` in `GluePieces` by the
   five glue Props here. Then `h5neron_n1_n2_of_leaves_and_glue` supplies `t41` (N1) and N2.
   Alternatively, use N2-loc⁺ and four glue Props (`h5neron_n1_n2_of_leaves_and_glue_mono`).
3. §1, §5 and the start of §6 of `NeronLG.lean` copy tau-n1n2's statements and lemmas verbatim, so
   after adoption they can be replaced by the originals.
4. The pasting lemmas of §6 (`pbCompInv_fst`, `genSq`, `bcA_proj`) are general and could go into
   `H5BaseChange`.

## 6. Independent review

A read-only model review (subagent) checked every new `def` of §2–§4 (before N2-g1' was proved
and before N1-g2 was restricted to bad primes; neither change alters a reviewed statement except
that `NeronNearBadPoint` adds the hypothesis `f ∈ v`). It found no PROBLEM: each statement is true
and not vacuous, NL is a special case of BLR 1.2/4, and each glue decomposition is honest. Its
points:
- **Assumptions.** The only new outside theorem is NL. Everything else is EGA IV §8, §11 and §17,
  SGA 3 VI_B, and uniqueness of Néron models.
- **Assembly theorems.** They do not exploit a vacuous hypothesis.
- **Five MINOR docstring gaps, all fixed:**
  - N1-g2: prime avoidance for `h' ∉ v`, and the case `f ∉ v`;
  - N1-g3: `gᵢ = 0` is harmless;
  - N2-g1: superfluous locators;
  - N2-g2: details of the generic-fibre equation;
  - N2-g3: `c` is built from the isomorphism of `IsBaseChangeOf` and `𝒩₀.gen`, not from `𝒱.gen`.

There has been no human review.

## 7. Lean notes (VERIFIED)

- **Iso defs containing `eqToIso`.** If an iso def contains `pbEqIso` (an `eqToIso`), make it an
  `irreducible_def` from the start. With `genSq` a plain `def`, every declaration that applied N1-ab
  to `genSq …` made the kernel report "deterministic timeout". Elaboration was fine, and an isolated
  `IsMonHom` check passed. Bisected with test lemmas; `irreducible_def` fixed all of them.
- **One-term chains time out.** The chain `(bcGenO …).hom = pbCompInv ≫ pbEq ≫ gen.hom`, written as
  one term, also timed out in the kernel, even with `bcGenO` irreducible. Four separately stated
  one-step lemmas composed by `.trans` check at once.
- **Syntactic pullback types.** `(A.baseChange L).X.left` is not syntactically
  `pullback A.X.hom κ`, which blocks `rw` ("not type-correct at implicit transparency"). State the
  lemmas at the pullback types (`bcA'`, `bcProj'`) and transfer them by `exact`.
- **`Over.pullbackComp` components.** Its components are computable:
  `simp [pbCompInv, Over.pullbackComp, conjugateIsoEquiv, Over.mapComp]` proves `pbCompInv_fst`.
- **`mul_one` is shadowed.** `open … MonObj` shadows `mul_one`; write `_root_.mul_one`.
- **`ι` is a token.** It cannot be used as a binder name here.
