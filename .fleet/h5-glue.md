# h5-glue (fleet note)

**Main result.** H5 in the multi-field form R19-R21 need (`stableFaltingsHeight_eq_neron_all`,
same conclusion as h5-neron's) now rests on leaves N1, N2 and three glue Props instead of six:
`HeightAntitone`, `OpenImmersionHeightLe`, `ModelHeightBaseChange`
(`scratch/h5-glue/H5Glue.lean`, compiled, standard axioms only, no sorry).
- **Proved:** `GroupModelBaseChangeExists` (H4b). h5-neron's kernel timeout is avoided by proving
  the IsMonHom fact over abstract morphisms and then instantiating.
- **Proved:** the Néron comparison map is a group homomorphism and a generic iso.
  `NeronModelMinimal ⇐ HeightAntitone`.
- **Proved:** an open immersion of group models is an iso on generic fibres.
  `OpenSubgroupHeight ⇐ HeightAntitone + OpenImmersionHeightLe`.
- Additivity `h(A)+h(B) ≤ h(A×B)` from N1, `HeightAntitone`, `ProductModelHeight` (`Additivity.lean`).
- **Most of `HeightAntitone` is proved** (`Stalk.lean`, `JacDet.lean`):
  - local ring at ξ: a generic iso gives an iso of local rings, and ξ ↦ ξ;
  - bijection on complex points;
  - transport of analytic uniformizations and their Jacobian determinants;
  - the 𝓞_L-linear map f^* on cotangent spaces.

**Finding.** `NeronModelMinimal` and `HeightAntitone` are true, but their proof needs the
full-rank half of `HodgeLatticeTheorem` for the Néron model. It enters through
`HodgeData.isLattice`: ⋀^g ω_𝒩 ≠ 0 does not follow from ω_𝒩 ↪ ω_𝒢. So `NeronModelMinimal` is
not pure glue over the mapping property, which corrects h5-neron (d). hodge-lattice reduces
`HodgeLatticeTheorem` to `TangentDimAtOrigin` + `DimBaseChange`. An independent model review
confirmed this and found no false or vacuous statement.

**Remains.**
- For `HeightAntitone` (docs §4):
  - R1: f^* maps ω_𝒩 into ω_𝒢 (a check at each prime).
  - R2: L ⊗ ⋀^g f^* is an isomorphism of Hodge lines.
  - R4: HodgeData transport plus `modelHeight_le_of_le`.
- `OpenImmersionHeightLe`: the inverse transport.
- `ModelHeightBaseChange` (the largest piece: flat base change of ω, Arakelov degree, inf/sum exchange).
- `ProductModelHeight`.
- N1 and N2 stay as hypotheses. Locators are UNVERIFIED.

Report: `docs/research/h5-glue.md`. Log: `scratch/h5-glue/log.md`.
