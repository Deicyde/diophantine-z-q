import ZInQKernel.OneProof.H.TailW
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset

/-!
# `HDec.MCRGlue.FiniteQuotientExists` (H-90, mcr-glue's leaf L2) is a theorem

`HDec.MCRGlue.FiniteQuotientExists` (`ZInQKernel/OneProof/H/TailW.lean`; SGA 1 Exp. V, Prop. 1.8
with Prop. 1.1): for `𝒴` proper over `ℤ_(p)` such that every finite set of points lies in an
affine open, and `G` a finite group of `ℤ_(p)`-automorphisms of `𝒴`, there is `q : 𝒴 → 𝒵` over
`ℤ_(p)` with `IsGQuotient G q.left` and `q.left` finite.

The proof applies two theorems of the Anthropic FLT development
(anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0),
ported to this repository's Lean v4.35.0 / Mathlib 56a00585 in
`ZInQKernel/Contrib/CloudB3W12FiniteQuotient/` (see `NOTICE.md` there):

* `forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset`: over a separated base, every
  point has a `G`-invariant affine open neighbourhood (the intersection of the translates of an
  affine open containing its orbit);
* `exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant`: then the quotient
  `π : 𝒴 → Y` exists (constructed in the source as the coequalizer of the action in locally
  ringed spaces): `π` is integral and affine, `𝒪_Y = (π_* 𝒪_𝒴)^G` on every open, and `π` is
  universal among `G`-invariant morphisms.

The universal property gives the structure map `Y → Spec ℤ_(p)`; `π` is locally of finite type
because `𝒴` is (it is proper), so `π` is finite (integral and locally of finite type).
-/

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudB3W12

/-- **H-90 (mcr-glue L2), `HDec.MCRGlue.FiniteQuotientExists`, proved.** -/
theorem finiteQuotientExists_proof : HDec.MCRGlue.FiniteQuotientExists := by
  intro p _ 𝒴 hprop hAF G hG hGS
  have : Finite G := hG
  have : IsProper 𝒴.hom := hprop
  -- `G`-invariant affine neighbourhoods (the base `Spec ℤ_(p)` is affine and `𝒴` is separated)
  have hadm :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset
      𝒴.hom inferInstance hAF G.subtype
  -- the quotient
  obtain ⟨Y, π, hπ, hint, haff, -, -, hinj, hrange, -, huniv⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
      G.subtype hadm
  -- the structure map `Y → Spec ℤ_(p)`, from the universal property
  obtain ⟨f', hf', -⟩ := huniv _ 𝒴.hom fun g => hGS g g.2
  -- `π` is an SGA 1 quotient in the sense of `IsGQuotient`
  have hQ : HDec.MCRGlue.IsGQuotient G π := by
    refine ⟨fun g hg => hπ ⟨g, hg⟩, haff, fun W _ => ⟨hinj W, ?_⟩⟩
    rw [hrange W]
    ext s
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  -- `π` is finite: integral, and locally of finite type since `π ≫ f' = 𝒴.hom` is
  have hF : IsFinite π := by
    have : LocallyOfFiniteType (π ≫ f') := by rw [hf']; infer_instance
    have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π f'
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType π).mpr ⟨hint, this⟩
  exact ⟨Over.mk f', Over.homMk π hf', hQ, hF⟩

end ZInQ.Contrib.CloudB3W12
