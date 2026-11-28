# HeightModelM5: the sheaves `e*Ω¹` and `ε*Ω^g`, their stalks and global sections

`HeightModelM3/README.md` (remaining reading 1) and the last paragraph of `HeightModelM4/README.md`
record a definitional reading: Mathlib has no sheaf of relative differentials, so the tree's
`HeightModelM3.stalkOmega 𝒢 s` is the stalk formula `𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]`
and `HeightModelM2.globalOmega 𝒢` stands in for `Γ(S, e*Ω¹)`. This directory builds the sheaf
`e*Ω¹_{𝒢/𝓞_L}` from Mathlib's presheaf of relative differentials, sheafification and pullback. It
proves that its stalk at `s` is linearly isomorphic to the stalk formula, that `Γ(S, e*Ω¹)` maps
injectively onto `globalOmega`, and that the global sections of the top exterior power `ε*Ω^g`,
taken as `⋀^g e*Ω¹` or as `e^*(⋀^g Ω¹)`, map injectively onto `printedDetLattice`. It restates the
rows `GaudronRemondThm14GR1` and `GaudronRemondSec9LowerGR1Weak` over the sheaf (not the
unweakened `GaudronRemondSec9LowerGR1`).

Below, `f : X ⟶ S = Spec R` is a morphism of schemes and `e : S ⟶ X` any morphism (the ring is
`R₀` in the `GG` namespace). For a group model `𝒢 : GroupModel A L`, `f = 𝒢.G.hom`,
`e = 𝒢.unitSection`, `S = Spec 𝓞_L` and `η` is its generic point; `f` is smooth, since `GroupModel`
carries `Smooth G.hom` as an instance. This directory's `stalkOmega f x` is the stalk of `Ω¹_{X/R}`
at `x : X`, not the tree's `HeightModelM3.stalkOmega`.

- **The sheaf** (`Defs.lean`). `preOmega f` is Mathlib's presheaf `U ↦ Ω[Γ(X, U)/R]`
  (`PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'` of `baseHom f`,
  the map to `X.presheaf` from the constant presheaf `R`). `relOmega f : X.Modules` is its
  sheafification (`PresheafOfModules.sheafification`) and `pullOmega f e` is
  `(Scheme.Modules.pullback e).obj (relOmega f)`. The differential
  `dSheaf f U : Γ(X, U) → Γ(U, Ω¹_{X/R})` is additive, satisfies the Leibniz rule, vanishes on the
  image of `R` and commutes with restriction (`dSheaf_add`, `dSheaf_mul`, `dSheaf_baseHom`,
  `dSheaf_map`).
- **Stalks.** `stalkOmegaEquiv f x : stalkOmega f x ≃ₗ[𝒪_{X,x}] Ω[𝒪_{X,x}/R]` sends the germ of
  `dSheaf f U b` to `D (germ b)` (`stalkOmegaEquiv_germ_dSheaf`, `StalkOmega.lean`). For any scheme
  `S`, morphism `e : S ⟶ X` and `M : X.Modules`, `stalkPullbackEquiv e M s` is an
  `𝒪_{S,s}`-linear isomorphism `(e^* M)_s ≃ 𝒪_{S,s} ⊗[𝒪_{X,e(s)}] M_{e(s)}` sending the germ of
  the unit image of `m` to `1 ⊗ₜ germ m` (`stalkPullbackEquiv_unitGerm`, `PullbackStalk.lean`).
  Composing the two, `GG.pullStalkEquiv f e s` (`GenericGerm.lean`) is an `𝒪_{S,s}`-linear
  isomorphism from the stalk of `pullOmega f e` at `s` to `𝒪_{S,s} ⊗_{𝒪_{X,e(s)}} Ω[𝒪_{X,e(s)}/R₀]`
  (`GG.StalkT`). For a group model, `GG.StalkT` and `GG.stalkToGeneric` are by definition the
  tree's `HeightModelM3.stalkOmega 𝒢 s` and `HeightModelM3.stalkToGeneric 𝒢 s`
  (`stalkToGeneric_injective_sheaf`, in `GlobalOmega.lean`, is the term
  `HeightModelM3.stalkToGeneric_injective 𝒢 s`). The image of the stalk of `e*Ω¹` at `s` in the
  generic fibre under `GG.phi` (`GenericGerm.lean`), which is `GG.pullStalkEquiv` followed by
  `GG.stalkToGeneric`, is `printedOmegaAt 𝒢 s` (`phi_mem_printedOmegaAt`, `exists_phi_eq`,
  `DetLattice.lean`). `BS.stalkOmegaBaseEquiv f x` (`BaseStalk.lean`) is an `𝒪_{X,x}`-linear
  isomorphism from `stalkOmega f x` to `Ω[𝒪_{X,x}/𝒪_{S,f(x)}]`, the differentials over the base
  stalk, since `𝒪_{S,f(x)}` is a localization of `R` (`BS.isLocalization_baseStalk`,
  `BS.kaehlerLocalizationEquiv`).
- **Global sections of `e*Ω¹`.** `germ_injective_of_specializes` and
  `range_germ_eq_iInter_specializes` (`IrreducibleSections.lean`): for a sheaf `F` valued in a
  concrete category with limits and colimits whose forgetful functor preserves limits and filtered
  colimits and reflects isomorphisms (abelian groups, for instance), and `η ∈ U` specializing to
  every point of `U`, if every specialization map `F_s ⟶ F_η` is injective, then `F(U) ⟶ F_η` is
  injective with image the intersection of the images of the `F_s`. Applied to `e*Ω¹`
  (`GenericGerm.lean`): if `η` specializes to every point and every `GG.stalkToGeneric s` is
  injective, the generic germ `GG.genericGerm` from `Γ(S, e*Ω¹)` to `𝒪_{S,η} ⊗ Ω[𝒪_{X,e(η)}/R₀]`
  is injective with image `⋂ s, range (GG.stalkToGeneric s)` (`GG.genericGerm_injective`,
  `GG.range_genericGerm`). For a group model (`GlobalOmega.lean`), `genericGermPullOmega 𝒢 :
  GlobalPullOmega 𝒢 →ₗ[𝓞 L] (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]` is injective
  (`genericGermPullOmega_injective`) with range `HeightModelM2.globalOmega 𝒢`
  (`range_genericGermPullOmega`): `Γ(S, e*Ω¹)` maps injectively onto `globalOmega`.
  `printedOmega_eq_sheaf`: `printedOmega 𝒢` is the preimage of that range under `theta' 𝒢`.
- **The top exterior power.** For a presheaf of modules `M` on a scheme, `schemeWedge M n`
  (`ExteriorSheaf.lean`) is the sheafification of `U ↦ ⋀^n_{Γ(X, U)} M(U)`, and
  `schemeWedgeStalkEquiv` is an additive isomorphism from its stalk at `x` to `⋀^n` over `𝒪_{X,x}`
  of the stalk of `M`, linear by `GG.schemeWedgeStalkEquiv_smul` (`GenericGermTop.lean`).
  `exteriorPowerBaseChange A B M n : ⋀[B]^n (B ⊗[A] M) ≃ₗ[B] B ⊗[A] ⋀[A]^n M`
  (`ExteriorBaseChange.lean`). For `f` smooth, `η` specializing to every point and injective
  specializations `GG.sig hη s : 𝒪_{S,s} → 𝒪_{S,η}`, the generic germ `GG.genericGermTop` of
  `GG.pullOmegaTop f e n = ⋀^n e*Ω¹` is injective with image `⋂ s, range (GG.rhoTop s)`
  (`GG.genericGermTop_injective`, `GG.range_genericGermTop`, `GenericGermTop.lean`). For any scheme
  `S`, morphism `e : S ⟶ X` and `M : X.Modules`, `PW.wedgePullMap e M n : e^*(⋀^n M) ⟶ ⋀^n (e^* M)`
  (`PullbackWedge.lean`) is bijective on stalks and on sections over every open
  (`PW.wedgePullMap_stalk_bijective`, `PW.wedgePullMap_app_bijective`) and an isomorphism of
  sheaves of abelian groups (`PW.isIso_abSheafHom`). `GG.globalPullWedgeEquiv` is the resulting
  `Γ(S, e^*(⋀^n Ω¹)) ≃ₗ Γ(S, ⋀^n e*Ω¹)`.
- **`printedDetLattice`** (`DetLattice.lean`, `SheafRows2.lean`). For a group model and
  `hg : A.dim = g`, `printedDetLattice_eq_sheaf`: `genericGermPullOmegaTop 𝒢 g :
  GlobalPullOmegaTop 𝒢 g →ₗ[𝓞 L] 𝒢.hodgeSpace g` is injective with range `printedDetLattice 𝒢 g`,
  so `Γ(S, ⋀^g e*Ω¹)` maps injectively onto `printedDetLattice`. The injective map from `⋀^g` of
  the generic fibre into the Hodge line, `toHodgeLine` (`toHodgeLine_injective`), goes through
  `HeightModelM3.thetaEquiv` and `HeightModelM4.etaFieldEquiv` and is linear by
  `HeightModelM4.etaFieldEquiv_smul_wedge`. `printedDetLattice_eq_pullTop` is the same statement
  for the map `genericGermPullTopOmega 𝒢 g` on `GlobalPullTopOmega 𝒢 g`, the global sections of
  `e^*(⋀^g Ω¹)` (`globalPullTopOmega_eq`); that map is `globalPullTopEquiv` followed by
  `genericGermPullOmegaTop 𝒢 g`.
- **The GR1 rows** (`SheafRows.lean`, `SheafRows2.lean`). `IsGR1StableHeightSheaf` and
  `IsGR1StableHeightSheaf'` are `IsGR1StableHeightOriginal` with the lattice taken to be
  `M = GlobalPullOmegaTop 𝒜 g`, resp. `M = GlobalPullTopOmega 𝒜 g`: a nonzero `eta ∈ M` with
  `[M : 𝓞 eta] ≠ 0`, the metrics of its image in the Hodge line, and `[M : 𝓞 eta]` in place of
  `secIndex`. Both are equivalent to `IsGR1StableHeightOriginal` (`isGR1StableHeightSheaf_iff`,
  `isGR1StableHeightSheaf'_iff`); `secIndex_genericGermPullOmegaTop` and
  `secIndex_genericGermPullTopOmega` carry the index to `secIndex`. The rows over them,
  `GaudronRemondThm14GR1Sheaf`, `GaudronRemondSec9LowerGR1WeakSheaf` and their primed forms, are
  equivalent to `GaudronRemondThm14GR1` and `GaudronRemondSec9LowerGR1Weak`
  (`gaudronRemondThm14GR1Sheaf_iff`, `gaudronRemondSec9LowerGR1WeakSheaf_iff` and the primed
  forms).

## Files

| File | Imports inside the tree | Content |
|---|---|---|
| `PullbackStalk.lean` | none (Mathlib only) | `stalkModule`; `stalkPullbackEquiv` and `stalkPullbackFormula`, through the skyscraper `skyMod` and `e^* ⊣ e_*` |
| `Defs.lean` | `PullbackStalk` | `baseHom`, `preOmega`, `relOmega`, `pullOmega`, `globalPullOmega`, `stalkOmega`, `dSheaf` and its lemmas, `moduleStalkOmega` |
| `StalkOmega.lean` | `Defs` | `stalkUnitEquiv` (sheafification), `S1.stalkPreEquiv` (presheaf), `stalkOmegaEquiv`, `stalkOmegaFormulaCanonical` |
| `BaseStalk.lean` | `StalkOmega` | `BS.kaehlerLocalizationEquiv`, `BS.stalkOmegaBaseEquiv`, `BS.stalkOmegaBaseFormula` |
| `IrreducibleSections.lean` | none (Mathlib only) | `germ_injective_of_specializes`, `range_germ_eq_iInter_specializes`, the `Scheme.Modules` forms, `spec_modules_sections_generic` |
| `GenericGerm.lean` | `StalkOmega`, `IrreducibleSections` | `GG.pullStalkEquiv`, `GG.stalkToGeneric`, `GG.phi_modSpec`, `GG.genericGerm` with its injectivity and range |
| `GlobalOmega.lean` | `HeightModelM3.StalkInjective`, `GenericGerm` | `GlobalPullOmega`, `genericGermPullOmega` (injective, range `globalOmega`), `printedOmega_eq_sheaf` |
| `ExteriorSheaf.lean` | none (Mathlib only) | `wedgeMap`, `wedgePresheaf`, `wedgeSheaf`, `stalkWedgeEquiv`, `stalkWedgeSheafEquiv`, `schemeWedge`, `schemeWedgeStalkEquiv` |
| `ExteriorBaseChange.lean` | none (Mathlib only) | `exteriorPowerBaseChange`; `exteriorPowerToBaseChange` injective when `⋀[A]^n M` is flat and `A → B` injective |
| `GenericGermTop.lean` | `GenericGerm`, `ExteriorSheaf`, `ExteriorBaseChange` | `GG.wedgeGen_injective`, `GG.pullOmegaTop`, `GG.rhoTop`, `GG.genericGermTop` with its injectivity and range, `GG.toHodge` |
| `PullbackWedge.lean` | `GenericGermTop` | `PW.wedgePullMap`, bijective on stalks and sections; `GG.pullTopOmega`, `GG.globalPullWedgeEquiv` |
| `DetLattice.lean` | `HeightModelM4.Wedge`, `GlobalOmega`, `GenericGermTop` | `toHodgeLine`, `genericGermPullOmegaTop`, `phi_mem_printedOmegaAt`, `exists_phi_eq`, `printedDetLattice_eq_sheaf` |
| `SheafRows.lean` | `HeightModelM2.GR1Rows`, `DetLattice` | `IsGR1StableHeightSheaf`, `isGR1StableHeightSheaf_iff`, the Thm 1.4 and weak Cor. 8.4 rows over it (`GaudronRemondThm14GR1Sheaf`, `GaudronRemondSec9LowerGR1WeakSheaf`) |
| `SheafRows2.lean` | `SheafRows`, `PullbackWedge` | `GlobalPullTopOmega`, `globalPullTopEquiv`, `printedDetLattice_eq_pullTop`, `IsGR1StableHeightSheaf'` and the rows over it (`GaudronRemondThm14GR1Sheaf'`, `GaudronRemondSec9LowerGR1WeakSheaf'`) |
| `CheckN01.lean` | `Defs`, `StalkOmega` | `#print axioms` |
| `CheckN2.lean` | `PullbackStalk` | `#print axioms` |
| `CheckN3.lean` | `IrreducibleSections` | `#print axioms` |
| `CheckN5a.lean` | `ExteriorSheaf` | `#print axioms` |
| `CheckExteriorBaseChange.lean` | `ExteriorBaseChange` | `#print axioms` |
| `CheckAll.lean` | `Defs`, `StalkOmega`, `PullbackStalk`, `IrreducibleSections`, `ExteriorSheaf`, `GenericGerm`, `GenericGermTop` | `#print axioms`; the instance check |
| `CheckSheafRows.lean` | `GlobalOmega`, `DetLattice`, `SheafRows` | `#print axioms` |
| `CheckCompletion.lean` | `PullbackWedge`, `BaseStalk`, `SheafRows2` | `#print axioms` |

The Check files run `#print axioms` on declarations of the files they import; `CheckAll.lean` also
checks that `moduleStalkOmega f x` is `stalkModule (relOmega f) x` at instance transparency. The
directory's sources contain no `sorry` and declare no `axiom`.

## Not proved here

That the sheaves built here are GR1's `e*Ω¹` and `ε*Ω^g` is a reading of their construction.
`relOmega f` is relative to the constant presheaf `R`, not to `f⁻¹𝒪_S`, and `⋀^n` of a sheaf of
modules is this directory's `schemeWedge`. Mathlib has neither a sheaf of relative differentials
nor exterior powers of sheaves of modules to compare them with. The Lean computes their stalks
(`BS.stalkOmegaBaseEquiv` gives `Ω[𝒪_{X,x}/𝒪_{S,f(x)}]`, `schemeWedgeStalkEquiv` gives `⋀^n` of
the stalk) and proves the statements above. The rows restated over the sheaf are
`GaudronRemondThm14GR1` and `GaudronRemondSec9LowerGR1Weak`, with the height formula of
`IsGR1StableHeightOriginal`. Nothing under `ZInQKernel/OneProof/` imports this directory, directly
or through other modules (`ZInQKernel/Contrib/AllContrib.lean` does), and the bundle's fields
`gaudronRemondThm14GR1` and `gaudronRemondSec9LowerGR1Weak` are stated over
`IsGR1StableHeightOriginal`; the bundle is the hypothesis `r` of `ZInQ.OneProof.frozenTarget`
(`ZInQKernel/OneProof/Main.lean`).
