# h5-glue (fleet note)

**Main result.** `NeronModelMinimal` (the project's Prop in Height.lean) is now a theorem:
`ZInQ.H5Glue.neronModelMinimal`. Behind it, `heightAntitone` is proved: a homomorphism of group
models that is an isomorphism on generic fibres does not increase the height. H5 in the
multi-field form R19-R21 need (`stableFaltingsHeight_eq_neron_all`, same conclusion as h5-neron's)
now rests on leaves N1, N2 and only two glue Props, `OpenImmersionHeightLe` and
`ModelHeightBaseChange`; h5-neron's version needed six. Additivity h(A)+h(B) ≤ h(A×B) needs only
N1 and `ProductModelHeight`.

**What compiles.** `scratch/h5-glue/H5Final.lean` (self-contained, about 2360 lines, about 18 s):
0 errors, no sorry or axiom, 8 `#print axioms`, each only propext/Classical.choice/Quot.sound.
Also proved in it:
- `GroupModelBaseChangeExists` (H4b). h5-neron's kernel timeout is avoided by proving the
  monoid-morphism property over abstract morphisms and then instantiating.
- Open immersions of group models are isomorphisms on generic fibres, so
  `OpenSubgroupHeight ⇐ OpenImmersionHeightLe`.
- The full transport of metrized models along a generic isomorphism:
  - the local ring at ξ;
  - ℂ-points;
  - analytic uniformizations and their Jacobian determinants;
  - f^* on cotangent spaces, with f^*ω_𝒩 ⊆ ω_𝒢 at every prime;
  - the Hodge-line isomorphism;
  - the pullback of HodgeData lowers the height.

**Finding.** The nonvanishing of ⋀^g ω_𝒩, needed for `HodgeData.isLattice`, comes from
hodge-lattice's theorem `OmegaSpans` (copied verbatim, §1-§5), not from dimension theory. So
`NeronModelMinimal` is genuine glue, as h5-neron (d) said. An earlier draft and the model review
thought the rank half of `HodgeLatticeTheorem` was needed; that is superseded. The model review of
the statements found nothing false or vacuous.

**Remains.**
- `OpenImmersionHeightLe`: the inverse transport, ω_𝒰 ⊆ f^*ω_𝒢 plus pulling uniformizations back
  through an open immersion; about 150 lines (SPECULATIVE).
- `ModelHeightBaseChange`: the largest piece (flat base change of ω and the Arakelov degree,
  plus an inf/sum exchange over embeddings).
- `ProductModelHeight`.
- N1 and N2 stay as hypotheses. Locators are UNVERIFIED.

Report: `docs/research/h5-glue.md`. Log: `scratch/h5-glue/log.md`.
