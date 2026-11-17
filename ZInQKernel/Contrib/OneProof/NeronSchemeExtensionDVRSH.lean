import ZInQKernel.Contrib.OneProof.NeronDVRLocalSH

/-! # neron-flt: group-law-dvr's leaf `NeronSchemeExtensionDVR` from the same descent leaf `NeronDescentSH`

group-law-dvr (branch wip/group-law-dvr, `ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean`, not in this base)
reduced `MumfordGroupLawDVR` (GIT Thm 6.14 over a DVR) to the leaf `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDVR`
(BLR §1.4 Thm 3 over an arbitrary DVR) and a glue statement. This file copies that `Prop` verbatim (with its
abbreviation `genMap`), under `NeronFLT.GLD`, and proves it from `NeronFLT.NeronDescentSH`, using the vendored FLT
existence over henselian DVRs. When both files are in one tree, the copy is definitionally the original
(`Iff.rfl`), so `NeronDescentSH` replaces both `neronSchemeExtensionExists` and `neronSchemeExtensionDVR`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace NeronFLT.GLD

open PkgI3

/-- Verbatim copy of `ZInQ.Contrib.GroupLawNeron.genMap` (group-law-dvr). -/
abbrev genMap (R K : Type) [CommRing R] [Field K] [Algebra R K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- Verbatim copy of group-law-dvr's **LEAF `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDVR`** (BLR §1.4 Thm 3
over a discrete valuation ring, with §1.2 Def. 1; numbers UNVERIFIED). -/
def NeronSchemeExtensionDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K]
    [IsFractionRing R K] (A : AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of R))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (ε : (Over.pullback (genMap R K)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N => (Over.pullback (genMap R K)).map f ≫ ε.hom

/-- **`NeronSchemeExtensionDVR` from the descent leaf.** -/
theorem neronSchemeExtensionDVR_of_descentSH (h : NeronDescentSH) : NeronSchemeExtensionDVR := by
  intro R _ _ _ K _ _ _ A
  obtain ⟨N, hN, ⟨ε⟩⟩ := exists_neron_of_descentSH R K h A
  obtain ⟨hS, hSep, -, hQC, hB⟩ := hN
  refine ⟨N, hS, hSep, hQC, ε, fun Y _ g => ?_⟩
  obtain ⟨f, hf⟩ := (hB Y).2 (g ≫ ε.inv)
  refine ⟨f, ?_⟩
  have hf' : (Over.pullback (genMap R K)).map f = g ≫ ε.inv := hf
  change (Over.pullback (genMap R K)).map f ≫ ε.hom = g
  rw [hf', Category.assoc, Iso.inv_hom_id, Category.comp_id]

end NeronFLT.GLD

end
