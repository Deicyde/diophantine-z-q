# h5-glue (fleet note)

**Main result.** Four of h5-neron's glue statements are now Lean theorems:
- `NeronModelMinimal` (the project's Prop in Height.lean);
- `OpenSubgroupHeight` (M6);
- `GroupModelBaseChangeExists` (H4b);
- behind the first two, `HeightAntitone` (a homomorphism of group models that is a generic iso
  does not increase the height) and `OpenImmersionHeightLe`.

H5 in the multi-field form R19-R21 need (`stableFaltingsHeight_eq_neron_all'`, same conclusion as
h5-neron's) now rests on leaves N1, N2 and one glue Prop, `ModelHeightBaseChange` (H4a);
h5-neron's version needed six. Additivity h(A)+h(B) ≤ h(A×B) needs only N1 and
`ProductModelHeight`.

**What compiles.** `scratch/h5-glue/H5Final.lean` (self-contained, about 2630 lines, about 19 s):
0 errors, no sorry or axiom, 9 `#print axioms`, each only propext/Classical.choice/Quot.sound.
Its main pieces:
- The full transport of metrized models along a generic isomorphism, and backwards through open
  immersions:
  - local ring at ξ;
  - ℂ-points;
  - analytic uniformizations and their Jacobian determinants;
  - f^* on cotangent spaces, with f^*ω_𝒩 ⊆ ω_𝒢 at every prime, and equality for open immersions;
  - the Hodge-line isomorphism;
  - pulling back HodgeData lowers the height.
- H4b: h5-neron's kernel timeout is avoided by proving the IsMonHom fact over abstract morphisms.
- Open immersions of group models are generic isomorphisms.

**Findings.**
- The nonvanishing of ⋀^g ω needed for `HodgeData.isLattice` comes from hodge-lattice's theorem
  `OmegaSpans` (copied verbatim), not from dimension theory. So `NeronModelMinimal` is genuine
  glue, as h5-neron (d) said. An earlier draft and the model review thought the rank half of
  `HodgeLatticeTheorem` was needed; that is superseded.
- `ProductModelHeight` probably needs AN3-type analytic input: a product uniformization has to
  split into uniformizations of the factors (SPECULATIVE).
- The model review of the statements found nothing false or vacuous.

**Remains.**
- `ModelHeightBaseChange`: flat base change of ω and ⋀^g, Arakelov degree, ℂ-points, a min ≤ avg
  over embeddings; size L.
- `ProductModelHeight` (with AN3).
- N1 and N2 stay as hypotheses. Locators are UNVERIFIED.

Report: `docs/research/h5-glue.md`. Log: `scratch/h5-glue/log.md`.
