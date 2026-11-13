# spread-out: neron-lg's glue N1-g1 `AbVarSpreadsOut` reduced to three EGA IV leaves

Task spread-out, 2026-11-13. Branch wip/spread-out (merged origin/wip/frob-pieces at the start).

## 1. Main result

`AbVarSpreadsOut` (neron-lg's N1-g1, `scratch/neron-lg/NeronLG.lean:468`) is **reduced** to three
published theorems of EGA IV, stated as leaf `Prop`s in their published form. Everything around
them is proved: the colimit `L = colim 𝓞_L[1/n!]`, the descent of the group law, unit, inverse and
group axioms (from Mathlib's EGA IV₃ 8.8.2 (i)), and the transfer to every presentation of
`𝓞_L[1/f]`. `AbVarSpreadsOut` itself is **not proved outright**: the three leaves are open (not in
Mathlib 4.35 or Tau Ceti, see §4).

Proved (no `sorry`, axioms `[propext, Classical.choice, Quot.sound]` for each, VERIFIED):

```lean
-- scratch/spread-out/SpreadOut.lean (AbVarSpreadsOut and HasAbelianSchemeAway copied verbatim
-- from scratch/neron-lg/NeronLG.lean, same opens, namespace ZInQ.SpreadOutN1)
theorem ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hsm : EGAIV_17_7_8_ii) : AbVarSpreadsOut

-- ZInQKernel/Contrib/SpreadOut/NumberField.lean (the body of AbVarSpreadsOut, unfolded)
theorem ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega (h882 : EGAIV_8_8_2_ii)
    (hpr : EGAIV_8_10_5_xii) (hsm : EGAIV_17_7_8_ii) (L : Type) [Field L] [NumberField L]
    (B : PkgI3.AbVar L) :
    ∃ f : 𝓞 L, f ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
        [IsScalarTower (𝓞 L) R L],
        ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom)
          (_ : IsProper G.hom)
          (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
          letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
            Functor.grpObjObj
          IsMonHom gen.hom

-- ZInQKernel/Contrib/SpreadOut/Spread.lean (general spreading out of smooth proper group schemes)
theorem ZInQ.Contrib.SpreadOut.exists_grpObj_descend {J : Type} [Preorder J] [IsDirectedOrder J]
    [Nonempty J] (D : Jᵒᵖ ⥤ Scheme) [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D)
    (hc : IsLimit c) (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii) (hsm : EGAIV_17_7_8_ii)
    (B : Over c.pt) [GrpObj B] [IsProper B.hom] [Smooth B.hom] :
    ∃ (k : Jᵒᵖ) (G : Over (D.obj k)) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (c.π.app k)).obj G ≅ B),
      letI : GrpObj ((Over.pullback (c.π.app k)).obj G) := Functor.grpObjObj
      IsMonHom gen.hom

-- scratch/spread-out/SpreadOutFull.lean (frob-pieces' FrobPiecesFull.lean + this task)
theorem ZInQ.SpreadOutFull.algFrobRed_of_ega_nmp (h882 : EGAIV_8_8_2_ii)
    (hpr : EGAIV_8_10_5_xii) (hsm : EGAIV_17_7_8_ii)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed
theorem ZInQ.SpreadOutFull.tateBridge35_of_ega_nmp (hT : PkgI3.TateModuleFree)
    (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii) (hsm : EGAIV_17_7_8_ii)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35
theorem ZInQ.SpreadOutFull.frobPiecesNeron_abVarSpreadsOut (h882 : EGAIV_8_8_2_ii)
    (hpr : EGAIV_8_10_5_xii) (hsm : EGAIV_17_7_8_ii) : FrobPiecesNeron.AbVarSpreadsOut
```

(`EGAIV_*` are `ZInQ.Contrib.SpreadOut.EGAIV_*`.) So `FrobTrace.AlgFrobRed` (and `TateBridge35`
given I3.M0) now rests on the three EGA IV leaves, `ProperSmoothGenConnected` (Zariski
connectedness), I2-Red and I2-NMP; N1-g1 is no longer needed.

`#print axioms` (scratch/spread-out/run3.txt, `lake env lean scratch/spread-out/SpreadOut.lean`,
exit 0):
```
'ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.SpreadOut.exists_grpObj_descend' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.SpreadOut.exists_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.SpreadOut.exists_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.SpreadOut.NF.specConeIsLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.SpreadOut.isMonHom_descend' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`lake env lean scratch/spread-out/SpreadOutFull.lean`: exit 0, 2 min 23 s, 117 axiom prints, all
standard, no `sorry` (scratch/spread-out/run_full1.txt), including
```
'ZInQ.SpreadOutFull.frobPiecesNeron_abVarSpreadsOut' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.SpreadOutFull.algFrobRed_of_ega_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.SpreadOutFull.tateBridge35_of_ega_nmp' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Verbatim check: `python3 scratch/spread-out/py/verbatim_check.py` → ALL VERBATIM
(`HasAbelianSchemeAway`, `AbVarSpreadsOut` in part_n1.lean and SpreadOut.lean).

## 2. The leaves (new; `ZInQKernel/Contrib/SpreadOut/Spread.lean`)

All three: published theorems, locators quoted from memory and **UNVERIFIED** (no network). Index:
a nonempty directed preorder `J` (EGA's "ensemble préordonné filtrant"), diagram `Jᵒᵖ ⥤ Scheme`,
quasi-compact quasi-separated terms, affine transition maps (the setting of EGA IV₃ §8.2 with all
`S_λ` qcqs, as in Stacks Tag 01ZM, UNVERIFIED). "Finite presentation" = locally of finite
presentation + quasi-compact + quasi-separated (EGA IV₁ 1.6.1).

```lean
/-- EGA IV₃ 8.8.2 (ii) (descent of schemes of finite presentation; Stacks 01ZM). -/
def EGAIV_8_8_2_ii : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (X : Over c.pt), LocallyOfFinitePresentation X.hom → QuasiCompact X.hom →
      QuasiSeparated X.hom →
      ∃ (i : Jᵒᵖ) (Xi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom ∧
        QuasiCompact Xi.hom ∧ QuasiSeparated Xi.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X)

/-- EGA IV₃ 8.10.5 (xii) (descent of properness; Stacks 081F). -/
def EGAIV_8_10_5_xii : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : Jᵒᵖ) (Xi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → IsProper ((Over.pullback (c.π.app i)).obj Xi).hom →
      ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsProper ((Over.pullback (D.map a)).obj Xi).hom

/-- EGA IV₄ 17.7.8 (ii) (descent of smoothness; Stacks 07RP). -/
def EGAIV_17_7_8_ii : Prop :=   -- same as EGAIV_8_10_5_xii with `Smooth` for `IsProper`
```
(The full docstrings are in the file; the Stacks tags are also UNVERIFIED.)

## 3. Proof structure (all VERIFIED by compilation)

1. `GrpDescent.lean` (pure category theory, cartesian monoidal categories). For a monoidal functor
   `F` and raw data `m, u, i` on `M`: the data induced on `F M` satisfies the group axioms iff `F`
   identifies both sides of each axiom for `M` (`grpAx_map_iff`); "compatible with a group object
   `N` via `e : F M ≅ N`" (`CompatM/U/I`) implies that `F` identifies the axioms (`fAx_of_compat`);
   compatibility transports along `θ : P ⋙ F' ≅ F` (monoidality of `θ` is automatic,
   `NatTrans.IsMonoidal.of_cartesianMonoidalCategory`); `isMonHom_descend` builds the group object
   on `P M` and shows `θ_M ≫ e` is a morphism of group objects.
2. `Limit.lean`. For `Y, Z` over a stage `D k`: the diagram `l ↦ Y ×_{D k} D l` on `Over k` has
   limit `Y ×_{D k} lim` (`bcConeIsLimit`, via `isLimitOfIsPullbackOfIsConnected`), affine
   transition maps and qcqs terms; Mathlib's Stacks 01ZC lemmas then give `exists_lift`
   (morphisms of base changes descend, up to the explicit comparison `pbNat`) and `exists_map_eq`
   (equalities descend).
3. `Spread.lean`. Leaf 8.8.2 (ii) gives `X₀/D_{i₀}`; leaf 8.10.5 (xii) and leaf 17.7.8 (ii) make
   it proper and smooth at a later stage; `exists_lift` three times gives `μ, η, ι` compatible with
   `B` (each later stage transports the earlier data); `fAx_of_compat` + `exists_map_eq` five
   times (combined along the cofiltered index, `Ev.and`) make the axioms hold after one more base
   change; `isMonHom_descend` concludes (`exists_grpObj_descend`).
4. `NumberField.lean`. `L = colim_n 𝓞_L[1/n!]` (`ringCoconeIsColimit`: `y • x` is integral for
   some `0 ≠ y ∈ ℤ`, and `y ∣ |y|!`; the maps `𝓞_L[1/n!] → L` are injective), hence
   `Spec L = lim Spec 𝓞_L[1/n!]` (`specConeIsLimit`). Apply step 3 to `B.X`; `f := n!`. For a
   presentation `R` of `𝓞_L[1/f]`, base change along `Spec R ≅ Spec (Localization.Away f)`
   (`IsLocalization.algEquiv`); the composite `𝓞_L[1/f] ≅ R → L` equals `𝓞_L[1/f] → L`
   (`IsLocalization.ringHom_ext`), so `pbNat` and the transport lemmas give the group isomorphism.

## 4. Survey (Mathlib 4.35 pin 56a00585; Tau Ceti oct16/nov01/main and the vendored modules)

VERIFIED by reading the sources (details in scratch/spread-out/log.md):
* Mathlib has `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` (EGA IV 8 / Stacks 01YT):
  descent of morphisms, both halves (`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`,
  `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`, Stacks 01ZC), `preservesColimit_yoneda`,
  descent of finite affine open covers of the limit, nonemptiness and quasi-compactness of the
  limit, sections of the limit, and affineness descent (`exists_isAffine_of_isLimit`).
* Mathlib does **not** have: descent of schemes of finite presentation (8.8.2 (ii)), descent of
  properness (8.10.5) or smoothness (17.7.8), descent of finitely presented algebras over filtered
  colimits (only morphisms: `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`), generic
  flatness. It has the smooth locus (`Mathlib/RingTheory/Smooth/Locus.lean`),
  `Smooth.of_smooth_fiberToSpecResidueField` (flat + lfp + smooth fibres ⇒ smooth) and
  Chevalley's theorem, which a later proof of 17.7.8 for Dedekind bases could use (SPECULATIVE).
* Tau Ceti: nothing on limits of schemes / spreading out (grep for 8.8.2, 8.10.5, 17.7.8,
  01ZM, 081F, 07RP, "spread" in AlgebraicGeometry: no hits). Nothing vendored by this task
  (diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0).

## 5. What remains

* The three leaves `EGAIV_8_8_2_ii`, `EGAIV_8_10_5_xii`, `EGAIV_17_7_8_ii` (open; textbook-level
  but large formalizations: 8.8.2 (ii) needs descent of fp algebras plus descent of gluing data;
  8.10.5 (xii) and 17.7.8 (ii) need constructibility arguments).
* No statement change is needed. Optional proposal for neron-lg's report: N1-g1 may be replaced by
  the three leaves above (exact text in §2), using `ZInQ.SpreadOutN1.abVarSpreadsOut_of_ega`.

## 6. Files

* `ZInQKernel/Contrib/SpreadOut/{GrpDescent,Limit,Spread,NumberField}.lean` (new; `lake build
  ZInQKernel.Contrib.SpreadOut.NumberField` succeeds).
* `scratch/spread-out/part_n1.lean`, `build.sh` → `SpreadOut.lean` (single-file check, exit 0);
  `part_full.lean`, `build_full.sh` → `SpreadOutFull.lean` (combined with frob-pieces, exit 0);
  `py/verbatim_check.py`; run logs `run3.txt`, `run_full1.txt`; `log.md`.
