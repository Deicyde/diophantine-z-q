# HeightModelM3: the readings of HeightModelM2 as Lean theorems

`HeightModelM2` stated three readings that were not Lean theorems. Each is proved here.

1. **`θ` is an isomorphism** (`Theta.lean`). `theta_surjective`: the comparison map
   `θ : 𝔪_ξ/𝔪_ξ² → 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]` is surjective, by the conormal sequence and
   `Ω[𝒪_{S,η}/𝓞_L] = 0`. With the tree's `theta_injective` this gives `thetaEquiv`. So `detSec`,
   which wedges sections in the image of `θ`, wedges all sections (`map_comap_secOmega`).
2. **Sections of `e*Ω¹` itself** (`StalkInjective.lean`). `stalkToGeneric_injective`: the stalk
   `𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]` of `e*Ω¹` injects into the generic fibre. The
   proof uses that `Ω` of a smooth algebra is projective, and that the local rings are
   localizations of an affine chart. `range_stalkToGeneric`: its image is `printedOmegaAt s`.
   `mem_globalOmega_iff`: `globalOmega` is the module of compatible families of germs of
   `e*Ω¹`, one in each stalk.
3. **Spans** (`Spans.lean`). `secOmega V W` is an `𝒪_S(V)`-module (`germEta_smul_mem_secOmega`);
   the generating wedges of `detSec` are closed under multiplying one factor by a lift of `c`
   (`smul_wedge_mem_detSec`).

`GR1Rows.lean` restates the implications from the GR1 rows over `IsGR1StableHeightGlobal` to the
bundle's fields. `Check.lean` prints the axioms.

Remaining readings (not Lean theorems in this directory):
1. Mathlib has no sheaf of relative differentials. `stalkOmega s` is defined by the stalk formula
   `(e*Ω¹)_s = 𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]`, and `globalOmega` (elements that are
   sections near every point, `HeightModelM2`) stands in for `Γ(S, e*Ω¹)`. That these are the
   stalk and the global sections of the sheaf `e*Ω¹_{𝒢/S}` is a reading here; `HeightModelM5`
   proves it for the sheaf it builds from Mathlib's presheaf of relative differentials,
   sheafification and pullback (`GG.pullStalkEquiv` for the stalk, `genericGermPullOmega_injective`
   and `range_genericGermPullOmega` for the global sections).
2. `smul_wedge_mem_detSec` shows that multiplying one factor of a wedge by a lift `x` of
   `c ∈ 𝒪_S(V)` stays in `detSec`. That this element is `c|_η · (v₁ ∧ ⋯ ∧ v_g)` in the Hodge line
   (`𝒪_{S,η} ≅ L`, compatible with the action of `𝒪_{𝒢,ξ}` on `𝔪_ξ/𝔪_ξ²`) is not proved here;
   `HeightModelM4` proves it (`germEtaField_smul_wedge`, `hodgeAction_smul_wedge`).
