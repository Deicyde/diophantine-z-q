# HeightModelM4: the `𝒪_S(V)`-action on the Hodge line and the wedge identity

`HeightModelM3/README.md` left two readings. This directory closes the second one, the one-factor
wedge identity in the Hodge line, as Lean theorems (`Wedge.lean`).

- **Scalars of the Hodge line.** `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`, an `L`-module
  through its left factor. The generic stalk `𝒪_{S,η}` of `S = Spec 𝓞_L` is identified with `L`
  (`etaFieldEquiv : 𝒪_{S,η} ≃ₐ[𝓞_L] L`, both being the localization of `𝓞_L` at the zero ideal).
- **The action.** `c ∈ 𝒪_S(V)`, for an open `V ∋ η`, restricts to `c|_η ∈ 𝒪_{S,η} ≅ L`
  (`germEtaField V hV`, a ring map). `hodgeAction` is the `𝒪_S(V)`-module structure on the Hodge
  line in which `c` acts as the scalar `c|_η`.
- **`x` acts through the section.** `smul_cotangent_eq_of_algebraMap_eq`: `x ∈ 𝒪_{𝒢,ξ}` acts on
  `𝔪_ξ/𝔪_ξ²` through `e^♯(x) ∈ 𝒪_{S,η}`, since `ker e^♯ = 𝔪_ξ` kills `𝔪_ξ/𝔪_ξ²`.
- **The wedge identity.** `etaFieldEquiv_smul_wedge`: for every `x ∈ 𝒪_{𝒢,ξ}`,
  `e^♯(x) • (1 ⊗ v₁ ∧ ⋯ ∧ v_g) = 1 ⊗ v₁ ∧ ⋯ ∧ (x • v_i) ∧ ⋯ ∧ v_g`, by multilinearity (write
  `e^♯(x) = a/t`; then `x` acts as `a · t⁻¹`). `germEtaField_smul_wedge` and
  `hodgeAction_smul_wedge`: for a lift `x` of `c ∈ 𝒪_S(V)`,
  `c|_η • (v₁ ∧ ⋯ ∧ v_g) = v₁ ∧ ⋯ ∧ (x • v_i) ∧ ⋯ ∧ v_g` in the Hodge line.
- **Submodules.** For `g ≥ 1`: `germEtaField_smul_mem_detSec` and `detSecSubmodule` (`detSec V W`
  is an `𝒪_S(V)`-submodule for this action), `germEtaField_smul_mem_detSecNear` (the sections near
  `s ∈ V` are stable under `𝒪_S(V)`), and `germEtaField_smul_mem_globalDetLattice` and
  `globalDetLatticeSubmodule` (the global lattice `globalDetLattice` is a `Γ(S, 𝒪_S)`-submodule).
  For `g = 0` nothing is claimed: `⋀^0 e*Ω¹ = 𝒪_S`, while the tree's `detSec` is an `𝓞_L`-span.

`GR1Rows.lean` restates the implications from the GR1 rows over `IsGR1StableHeightGlobal` to the
bundle's fields. `Check.lean` prints the axioms.

Reading not proved here, the only one left from `HeightModelM3/README.md`: Mathlib
has no sheaf of relative differentials. `stalkOmega s` is defined by the stalk formula
`(e*Ω¹)_s = 𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]`, and `globalOmega` stands in for
`Γ(S, e*Ω¹)`. That these are the stalk and the global sections of the sheaf `e*Ω¹_{𝒢/S}` is a
definitional reading here; `HeightModelM5` proves it for the sheaf it builds from Mathlib's
presheaf of relative differentials, sheafification and pullback: `GG.pullStalkEquiv` (the
stalks), `genericGermPullOmega_injective` and `range_genericGermPullOmega` (`Γ(S, e*Ω¹)` maps
injectively onto `globalOmega`).
