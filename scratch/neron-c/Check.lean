import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.NeronC.NeronGroup

/-! neron-c single-file check (assembled by `scratch/neron-c/assemble.py`; do not edit by hand).
The leaf statements T3 and T41 are copied verbatim (sliced from the kernel files, whose text
leaf-fold3's `Leaves3.lean` repeats verbatim) into the namespaces `NeronCCheck.PkgI2` and
`NeronCCheck.H5Neron`, and the reductions of `ZInQKernel/Contrib/NeronC` are applied to the copies. -/

namespace NeronCCheck.PkgI2

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj
open _root_.PkgI2

/-- **Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base). -/
def NeronMappingAbelianScheme : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

end NeronCCheck.PkgI2

namespace NeronCCheck.H5Neron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

/-- **Leaf N1 (Néron)**, as in `Reduction.lean` (BLR §1.4 Thm 3, UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

end NeronCCheck.H5Neron

/-- T3 (verbatim copy) from its surjective half. -/
theorem NeronCCheck.t3_of_surj (h : ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}) :
    NeronCCheck.PkgI2.NeronMappingAbelianScheme.{0} :=
  ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj h

/-- The copy is the kernel's statement. -/
theorem NeronCCheck.t3_iff : NeronCCheck.PkgI2.NeronMappingAbelianScheme.{0} ↔
    _root_.PkgI2.NeronMappingAbelianScheme.{0} := Iff.rfl

/-- T41 (verbatim copy) from the scheme-level existence theorem. -/
theorem NeronCCheck.t41_of_scheme (h : ZInQ.Contrib.NeronC.NeronSchemeModelExists) :
    NeronCCheck.H5Neron.NeronModelExists :=
  ZInQ.Contrib.NeronC.neronModelExists_of_scheme h

/-- The copy is the kernel's statement. -/
theorem NeronCCheck.t41_iff : NeronCCheck.H5Neron.NeronModelExists ↔
    ZInQ.H5Neron.NeronModelExists := Iff.rfl

#print axioms NeronCCheck.t3_of_surj
#print axioms NeronCCheck.t3_iff
#print axioms NeronCCheck.t41_of_scheme
#print axioms NeronCCheck.t41_iff
#print axioms ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective
#print axioms ZInQ.Contrib.NeronC.neronMappingAbelianSchemeSurj_of_nmp
#print axioms ZInQ.Contrib.NeronC.neronSchemeModelExists_of_neronModelExists
