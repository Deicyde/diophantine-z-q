# hodge-lattice (fleet summary)

**Result.** `HodgeLatticeTheorem` (ZInQKernel/HDecomp/Faltings/Models.lean) is proved from four
statements that say nothing about models, `ω_𝒢`, `⋀^g` or `secIndex`:
`hodgeLatticeTheorem_of_abVar : OriginStalkIso → RegularAtOrigin → DimAtOrigin → DimBaseChange →
HodgeLatticeTheorem` (scratch/hodge-lattice/HodgeLattice.lean, compiled, 0 errors, no sorry,
axioms propext/Classical.choice/Quot.sound).
- `OriginStalkIso`: `𝒪_{𝒢,ξ} ≅ 𝒪_{A_L,0}` (stalks of a base change along `Spec L → Spec 𝓞_L`).
- `RegularAtOrigin`: the local ring of an abelian variety at 0 is regular (smooth ⇒ regular).
- `DimAtOrigin`: it has Krull dimension `dim B`.
- `DimBaseChange`: `dim A_L = dim A`.
All true (standard; locators UNVERIFIED), stated over Mathlib's objects and the project's `AbVar`.

**Proved in Lean along the way:** the exterior-algebra lemma (`hodgeLattice_of_lattice`: f.g. +
full rank-g lattice ⇒ line + full lattice, with no exterior-power base change in Mathlib);
`omegaLocal` (`ω_𝒢 = ⋂_s omegaAt s` is a finitely generated full `𝓞_L`-lattice, from affine charts,
noetherian `Γ(U)`, stalks as localizations and a residue lemma); the tangent glue
`rank_L (L ⊗ 𝔪_ξ/𝔪_ξ²) = finrank_{κ(ξ)} 𝔪_ξ/𝔪_ξ²`; corollary: `ω_𝒢`, `⋀^g ω_𝒢` f.g. and
`L·⋀^g ω_𝒢 = hodgeSpace g`.

**Mathlib v4.35 lacks:** dimension theory of varieties (dimension at closed points; invariance
under field extension), smooth ⇒ regular, stalks of a pullback along a localization. Projectivity
of `⋀^g ω_𝒢` (f.g. torsion-free over Dedekind) is standard, not formalized, and not part of the
Lean statement.

**Remains:** the four Props (the first is glue, the others textbook facts about varieties); AN3's
analytic Props are untouched. Report: docs/research/hodge-lattice.md; log: scratch/hodge-lattice/log.md.
