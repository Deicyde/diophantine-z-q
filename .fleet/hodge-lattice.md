# hodge-lattice (fleet summary)

**Result.** `HodgeLatticeTheorem` (ZInQKernel/HDecomp/Faltings/Models.lean) is proved from two
textbook facts about abelian varieties over a field:
`hodgeLatticeTheorem_of_tangent : TangentDimAtOrigin → DimBaseChange → HodgeLatticeTheorem`
(scratch/hodge-lattice/HodgeLattice.lean, compiled, 0 errors, no sorry, axioms
propext/Classical.choice/Quot.sound).
- `TangentDimAtOrigin`: for `B : AbVar L` with `B.dim = g`, the cotangent space of `𝒪_{B,0}` has
  dimension `g` over the residue field. It follows from `RegularAtOrigin` + `DimAtOrigin` (proved).
- `DimBaseChange`: `(A.baseChange L).dim = A.dim`.
Both are true (standard; locators UNVERIFIED), stated over Mathlib's objects and the project's
`AbVar`; neither mentions models, `ω_𝒢`, `⋀^g` or `secIndex`.

**Proved in Lean:** the exterior-algebra lemma (`hodgeLattice_of_lattice`; no exterior-power base
change needed); `omegaLocal` (`ω_𝒢 = ⋂_s omegaAt s` is a finitely generated full `𝓞_L`-lattice:
affine charts, noetherian `Γ(U)`, stalks as localizations, a residue lemma); the tangent glue
`rank_L (L ⊗ 𝔪_ξ/𝔪_ξ²) = finrank_{κ(ξ)} 𝔪_ξ/𝔪_ξ²`; `genericFibreStalkIso` (base change along
`Spec L → Spec 𝓞_L` is iso on all local rings, for any scheme); the identity of the generic fibre
maps to `ξ` and to the origin of `A_L` (`originStalkIso_of`); corollary: `ω_𝒢`, `⋀^g ω_𝒢` f.g. and
`L·⋀^g ω_𝒢 = hodgeSpace g`.

**Mathlib v4.35 lacks:** dimension theory of varieties (dimension at closed points; invariance
under field extension) and smooth ⇒ regular. Projectivity of `⋀^g ω_𝒢` (f.g. torsion-free over
Dedekind) is standard, not formalized, and not part of the Lean statement.

**Remains:** the two Props; AN3's analytic Props are untouched. Report:
docs/research/hodge-lattice.md; log: scratch/hodge-lattice/log.md.
