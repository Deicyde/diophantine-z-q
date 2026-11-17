import ZInQKernel.Contrib.OneProof.MumfordGroupLawDescent
import ZInQKernel.OneProof.H.TailM
import ZInQKernel.Contrib.OneProof.NeronDVR
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_finiteEtale
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing

/-!
# neron-descent: the target Prop, copied verbatim, and the reductions that exist

Task neron-descent (2026-11-17); report docs/research/neron-descent.md.

* `NeronDescent.NeronSchemeExtensionDedekind` is the research field
  `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` (MumfordGroupLawNeron.lean L56) copied verbatim;
  `copy_iff` checks the copy is the same Prop.
* The reductions on this branch (all compiled, standard axioms):
  - dedekind-free: GIT 6.14 needs no Néron leaf (`mumfordGroupLawDVR_proof`), and the remaining readers need only
    `NeronExt.NeronDVRLocal` (`neronSchemeExtensionExists_of_dvrLocal`), which the field implies
    (`neronDVRLocal_of_dedekind`);
  - neron-flt: `NeronFLT.NeronDescentSH → NeronExt.NeronDVRLocal`.
* No proof of `NeronDVRLocal` is given: it needs effective descent of a scheme along `R → R^h` (or `R → R^sh`),
  which is not a finite map; the vendored FLT library has effective descent only along finite étale maps
  (`DescentAction.effective_of_finiteEtale`) or when the quotient is given
  (`DescentAction.effective_of_isPullback_of_flat_surjective`). See the report, §§2-3.
-/

set_option linter.style.longLine false

open CategoryTheory Limits AlgebraicGeometry ZInQ.Contrib.GroupLawNeron LeafQM.AV.R1UnivRigid PkgI3

namespace NeronDescent

/-- **Verbatim copy** of `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` (BLR, *Néron models*, §1.4
Thm 3 with §1.2 Def. 1 over an affine Dedekind scheme `Spec D`, `D` not a field; numbers UNVERIFIED). -/
def NeronSchemeExtensionDedekind : Prop :=
  ∀ (D : Type) [CommRing D] [IsDedekindDomain D] (L : Type) [Field L] [Algebra D L] [IsFractionRing D L]
    (A : AbVar L) (_ : ¬ IsField D),
    ∃ (N : Over (Spec (CommRingCat.of D))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (ε : (Over.pullback (genMap D L)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of D))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N => (Over.pullback (genMap D L)).map f ≫ ε.hom

theorem copy_iff :
    NeronSchemeExtensionDedekind ↔ ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind := Iff.rfl

/-! ## The existing reductions (compiled) -/

/-- GIT 6.14 over every DVR, with no Néron leaf (dedekind-free). -/
example : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR := ZInQ.Contrib.GroupLawDescent.mumfordGroupLawDVR_proof

/-- The field gives the local leaf (so the narrowing is a weakening). -/
example (h : NeronSchemeExtensionDedekind) : NeronExt.NeronDVRLocal :=
  ZInQ.Contrib.GroupLawDescent.neronDVRLocal_of_dedekind (copy_iff.mp h)

/-- The local leaf gives the old textbook field over `𝓞_L` (the readers T41, r6, SS1, SS3). -/
example (h : NeronExt.NeronDVRLocal) : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists :=
  ZInQ.Contrib.GroupLawDescent.neronSchemeExtensionExists_of_dvrLocal h

/-- The T41 reader: global Néron group models over `𝓞_L` at every number field `L`. -/
example (h : NeronExt.NeronDVRLocal) : ZInQ.H5Neron.NeronModelExists :=
  HDec.HSyn.t41_of_extension5 (ZInQ.Contrib.GroupLawDescent.neronSchemeExtensionExists_of_dvrLocal h)

/-- The r6/SS1/SS3 reader: Néron models over every DVR of a number field. -/
example (h : NeronExt.NeronDVRLocal) : GapNeron.NeronSchemeModelExistsDVRNF :=
  GapNeron.neronSchemeModelExistsNF (ZInQ.Contrib.GroupLawDescent.neronSchemeExtensionExists_of_dvrLocal h)

/-- neron-flt: descent from the strict henselization implies the local leaf. -/
example (h : NeronFLT.NeronDescentSH) : NeronExt.NeronDVRLocal := NeronFLT.neronDVRLocal_of_descentSH h

/-! ## The descent tools on this host (statements checked) -/

-- Effective descent along a finite étale faithfully flat ring map, for schemes in which every finite set of points
-- lies in an affine open (FLT).
#check @AlgebraicGeometry.DescentAction.effective_of_finiteEtale
-- Effective descent when a flat surjective quasi-compact map to a candidate quotient is already given (FLT).
#check @AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
-- One affine open containing every fibre-generic point of a smooth separated qc scheme over a DVR (FLT).
#check @AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing
-- AF property of smooth group schemes over a henselian DVR (FLT).
#check @GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
-- Néron models over henselian DVRs (FLT, neron-flt).
#check @NeronFLT.exists_neron_of_henselian

end NeronDescent

#print axioms NeronDescent.copy_iff
#print axioms ZInQ.Contrib.GroupLawDescent.neronSchemeExtensionExists_of_dvrLocal
#print axioms NeronFLT.neronDVRLocal_of_descentSH
