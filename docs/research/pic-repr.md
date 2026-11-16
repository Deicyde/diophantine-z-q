# pic-repr: `picRepresentableAbVar` cannot be proved from the tree; it is discharged by its printed form, which also absorbs pic-dict's `PicLocFinType`

Task pic-repr. Base: origin/main 0caafe66. The field is `picRepresentableAbVar : T09Pic.PicRepresentableAbVar`
(`ZInQKernel/OneProof/H/TailZ24.lean` L289), in bundle `HDec.HSyn.OpenAddedLeaves17`.

## 1. Verdict

1. **Proving it outright is out of reach** (VERIFIED by a library search, §2). Nothing in Mathlib, the vendored
   libraries or `ZInQKernel/` constructs a scheme that represents the Picard functor of a variety of dimension `≥ 2`:
   * the Hilbert schemes in the tree parametrize finite flat subschemes (points) only;
   * there are no Quot schemes;
   * there is no quotient by a finite flat group scheme or by a flat equivalence relation;
   * there is no dual abelian variety.

   The only representability theorem for the full Picard sheaf, Jacobian-Challenge's
   `exists_representableBy_picardFunctor`, covers smooth proper curves over separably closed fields.
2. **No narrowing makes it provable** (VERIFIED by reading the consumers, §4). The only consumer applies the field
   over number fields to **abelian surfaces** (`G12Det`, `A.dim = 2`). The case the tree supports, dimension 1 over a
   separably closed field, is proved (§3.1) but never reaches the consumer.
3. **The chart route is a reformulation, not a reduction** (§3.2). The vendored group criterion turns
   representability into "a representable open chart whose rational translates cover the field-valued points". That
   chart Prop is *equivalent* to the field: `⇐` is compiled, and `⇒` takes `F = ⊤`. The same section shows every
   other ingredient is already proved for abelian varieties over every field.
4. **Deliverable: the field discharged by its printed form** (§3.3). The new file is
   `ZInQKernel/Contrib/OneProof/PicRepresentableAbVar.lean`. Its leaf `PicRepr.PicRepresentableLFTAbVar` says that
   `Pic_{A/K}` is representable by a scheme locally of finite type over `K`, which is the Murre–Oort / FGA /
   Kleiman 9.4.8 / BLR 8.2 Thm 3 statement without the group structure. That leaf proves:
   * the field (`picRepresentableAbVar_of_lft`);
   * pic-dict's leaf `PicDict.PicLocFinType` ("every representing object is locally of finite type",
     `picLocFinType_of_lft`).

   Conversely, the conjunction of those two implies the leaf. Counts:
   * **on main alone:** a LEAF swapped for a LEAF, net **0**. The swap makes the leaf the literal print;
   * **with pic-dict / pic-smooth's `picZeroAbVar` reduction folded** (it adds `PicLocFinType`): **−1**, because one
     printed leaf replaces two.

   The −1 target with no new leaf is not reached.

## 2. What the tree has (VERIFIED by reading)

| need | in the tree? | where / why not |
|---|---|---|
| Representability of `Pic` of a curve | yes, over separably closed fields | `CloudW07JacobiansCurves/.../Picard/Representability.lean`, `exists_representableBy_picardFunctor`. The proof uses the cohomology chart into the Hilbert scheme of points (`Hilbert/CurveRepresentability`) and the group criterion |
| Descent to an arbitrary field | `Pic⁰` of curves only | `Picard/FieldDescent.lean`, `exists_abelianVariety_picardDegreeZero` |
| Hilbert / Quot schemes of positive-dimensional subschemes | no | only finite flat subschemes of `𝔸ⁿ` and of curves (`Hilbert/`) |
| Quotient `A/G` by a finite group scheme, or `(A×A)/A` | no | MilneQuasiInverse has annihilators, isogeny flatness and fpqc power descent, but no quotients |
| Dual abelian variety, Poincaré bundle, seesaw, theorem of the square | no | none of them is a Lean object (pic-dict's `PicZeroAbVar` is a leaf) |
| Normalized Picard group functor, Zariski sheaf property, `Pic` small, normalization iso at a rational point (Kleiman 9.2.5 form) | **yes, general** | `picardFunctorNormalizedGrp`, `isSheaf_zariski_picardFunctorNormalized`, `isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral`, `normalizedPicardIso`, and `small_picard` (private; copied verbatim) |
| Group chart criterion | **yes, any field** | `Group/Representability.lean`, `isRepresentable_of_representable_open_subfunctor` |

Abelian varieties of dimension `g ≥ 2` have effective divisors of positive dimension. The construction from
Hilbert schemes of points therefore does not apply. Mumford's route (`Â = A/K(L)` together with the theory of §§8–13)
and Grothendieck's route (Hilbert scheme of divisors, Castelnuovo–Mumford regularity) each need a library that is
not in the tree (STANDARD).

## 3. Compiled results

All results below compile with axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED).

### 3.1 `scratch/pic-repr/Narrow.lean`: the dimension-1 case

* `PicRepr.smoothOfRelativeDimension_of_dim`: a smooth irreducible `K`-scheme of Krull dimension `n` is
  `SmoothOfRelativeDimension n`. Each standard smooth chart contains a closed point, whose local ring has the chart's
  relative dimension, and that equals `dim X`; the proof uses the infra-smooth-dim lemmas in `LF2SmoothDim`.
* `PicRepr.picRepresentable_dimOne_sepClosed (K) [IsSepClosed K] (A : AbVar K) (hA : A.dim = 1)`: the field's
  conclusion, obtained from the vendored curve theorem.

This shows the leaf is satisfiable and not inert in dimension 1. It does not serve the consumer (§4).

### 3.2 `scratch/pic-repr/Chart.lean`: the chart route

* `PicRepr.PicChart f σ hσ`: the three chart hypotheses of `isRepresentable_of_representable_open_subfunctor`
  (`hFrep`, `hFopen`, `hgen`), copied from that theorem, for the normalized Picard group functor at the section `σ`.
* `representable_of_picChart`: for `f` proper and geometrically integral over **any** field with a section, a chart
  gives a representation of `(picardFunctor f).obj`.
* `picChart_of_representable` (take `F = ⊤`, which is open by `relative_isOpenImmersion_of_exists_opens` with
  `U = ⊤`) and `picChart_iff`: the chart Prop is **equivalent** to representability.
* `PicChartAbVar` (at the zero section `η[A.X].left`), `picRepresentableAbVar_of_chart`, `picChartAbVar_of_field`.

Use for crowdsourcing: anyone who formalizes this leaf only has to construct an open representable chart of the
normalized Picard functor of an abelian variety whose `K`-rational translates cover the field points. The group
structure, the sheaf property, smallness, normalization and gluing are already done. As a fold, the chart Prop is
not strictly smaller than the field, so it is **not** proposed as a leaf.

### 3.3 `ZInQKernel/Contrib/OneProof/PicRepresentableAbVar.lean`: the deliverable

The file imports only `ZInQKernel.OneProof.H.TailZ24`. Namespace `PicRepr`.

```lean
def PicRepresentableLFTAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ∃ (P : Over (Spec (CommRingCat.of K))) (_ : (picardFunctor A.X.hom).obj.RepresentableBy P),
      LocallyOfFiniteType P.hom
theorem picRepresentableAbVar_of_lft (h : PicRepresentableLFTAbVar) : T09Pic.PicRepresentableAbVar
def PicLocFinType : Prop := -- verbatim copy of PicDict.PicLocFinType (wip/pic-dict 4e95795b, L2201)
theorem picLocFinType_of_lft (h : PicRepresentableLFTAbVar) : PicLocFinType
theorem picRepresentableAbVar_and_picLocFinType_of_lft (h) : T09Pic.PicRepresentableAbVar ∧ PicLocFinType
theorem lft_of_picRepresentableAbVar_of_picLocFinType (h1) (h2) : PicRepresentableLFTAbVar
```

`picLocFinType_of_lft` uses `RepresentableBy.uniqueUpToIso`: two representing objects are isomorphic over `K`, and
being locally of finite type is stable under composition with an isomorphism.

**Rating of the new leaf `PicRepresentableLFTAbVar`: LEAF, printed form.** It is the `S = Spec K` case of the
printed statements, minus "group scheme":
* Murre (1964) and Oort (1962), for `X` proper over a field: represented by a group scheme locally of finite type;
* FGA Exp. 232, Thm 3.1, and Kleiman, *The Picard scheme*, Thm 9.4.8, for `X/S` projective and flat with
  geometrically integral fibres: exists, locally of finite presentation;
* BLR §8.2, Thm 3.

The group structure is dropped because it is a theorem in the tree (`picardFunctorCommGrpObj`). All locators are
UNVERIFIED; no source was read in this task.

Every print states representability of the **étale or fppf sheafified** relative Picard functor. Two facts connect
it to the Lean functor (the fppf sheafification of `T ↦ Pic(A_T)`):
* the agreement of these sheaves is Kleiman 9.2.5, and the existing leaf already relies on the same reading;
* the vendored `normalizedPicardIso` proves, for the Lean functor, that it agrees with `T ↦ ker(Pic(A_T) → Pic(T))`.

Kleiman 9.4.8 needs `A` projective, which is Mumford §6 App. 1. The vendored
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral` gives an immersion into projective
space; Murre–Oort needs only properness. The leaf is never stronger than any of these prints.

### 3.4 `#discharges` (VERIFIED; full output in `scratch/pic-repr/discharges.txt`)

```
DISCHARGES [OpenAddedLeaves17.picRepresentableAbVar] by PicRepr.picRepresentableAbVar_of_lft
  still assumes: [PicRepr.PicRepresentableLFTAbVar]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 2867 theorems checked, 8 discharge one
```

`PicRepr.PicLocFinType` is checked against pic-dict's `PicDict.PicLocFinType` (4e95795b, L2201) only as text: the
two are identical, since pic-dict's `AbVar` is `PkgI3.AbVar` under its `open PkgI3`. pic-dict is not on main, so no
`rfl` check was possible.

## 4. Consumers and narrowing (VERIFIED by reading; no field-read probe was run)

* The only reader of the field is `T09Pic.t09SymmIsogenyExists_of_four` (TailZ24.lean L807, via
  `t09SymmIsogenyExists_of_leaves`). In later generations the field is only forwarded (TailZ26/30/31/34).
* It fills `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` (∀ fields, ∀ abelian varieties). That field
  is read by two paths:
  * **(a)** `HSyn.tatePairingZl_of_leaves4` → `detTate_of_leaves4` → `G0Galois.DetTate` (`[NumberField K]`,
    TailA L2392) → `g12Det_of`, applied at `A.dim = 2` (`G12Det`, TailA L2078: `A.dim = 2 →`);
  * **(b)** `t9_of_leaves5` (TailN L217 / TailO L2867) → old T9 (`LeafPush.T09_WeilPairing`) → `g8_g12_of_leaves3`
    (`[NumberField K] [IsGalois ℚ K]`, TailD L125) and `G12Det`.
* **Narrowing that suffices:** `K` a number field and `A` an abelian surface (the QM fibres). pic-smooth reached the
  same number-field restriction for `picZeroAbVar`.
* **Narrowing that is provable:** dimension 1 over separably closed fields (§3.1). It does not meet the consumers.
* Narrowing to characteristic 0 or to number fields does not help: representability for surfaces is just as far
  from the library.

## 5. Integrator notes

* `scratch/pic-repr/autofold.json` discharges `picRepresentableAbVar` with the leaf `picRepresentableLFTAbVar`
  (kind published, no flag, so autofold flags it "unread"). On main this exchanges one LEAF for another. Dry run
  (VERIFIED):
  * `strict count: 34/11 on 45 -> 34/11 on 45; strictest 34/11 -> 34/11`;
  * the generated module (`scratch/pic-repr/DryRunFold.lean`, the dry-run output without its first line) compiles;
  * `sixContactMin_of_open36` has the standard axioms.
* **When pic-dict / pic-smooth's reduction of `picZeroAbVar` is folded**, its new leaf `PicDict.PicLocFinType` is
  discharged by `PicRepr.picLocFinType_of_lft` from the same leaf: net −1. This requires:
  * a check that `PicRepr.PicLocFinType` is `PicDict.PicLocFinType` (verbatim copy; check by `rfl` once both are in
    the tree);
  * a second discharge entry `{"field": "picLocFinType", "proof": "_root_.PicRepr.picLocFinType_of_lft {n}.picRepresentableLFTAbVar"}`,
    if `PicLocFinType` becomes a bundle field. If pic-dict's theorem instead takes it as a hypothesis, pass
    `picLocFinType_of_lft` there.
* locators.md rows to add, all UNVERIFIED:
  * Murre, Publ. Math. IHÉS 23 (1964);
  * Oort, Bull. SMF 90 (1962);
  * FGA Exp. 232, Thm 3.1;
  * Kleiman, *The Picard scheme*, Thm 9.4.8 and 9.2.5;
  * BLR, *Néron models*, §8.2, Thm 3.

## 6. Checks

* Lean checks are listed in `scratch/pic-repr/log.md`, with compile outcomes.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PicRepresentableAbVar`
  completed (13699 jobs). `ZInQ.OneProof.frozenTarget` has the axioms `[propext, Classical.choice, Quot.sound]`
  (VERIFIED).
* Hash guard and OPEN.md regeneration were not run: no fold was applied to the tree.
