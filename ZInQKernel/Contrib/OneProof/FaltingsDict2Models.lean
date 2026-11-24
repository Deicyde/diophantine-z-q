import ZInQKernel.Contrib.OneProof.FaltingsDict2Torus
import ZInQKernel.Contrib.OneProof.FaltingsDict2
import ZInQKernel.Contrib.OneProof.FaltingsRestate

/-! Specialize the printed lemma using the scheme-level fibre conditions,
and pass the print-form leaf to its height consumer. -/

noncomputable section

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open ReductSplit ZInQ.HeightSplit ZInQ.HeightFix ZInQ.SSFaltings

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

set_option linter.style.haveILetI false

/-- The fibrewise definition on p. 350, with the torus exhibited as a
group scheme on each residue-field fibre. -/
def FaltingsSemiabelianDefScheme [IsDiscreteValuationRing O] (G : GroupModelO A O) : Prop :=
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  letI : GrpObj (closedFibre G) := Functor.grpObjObj
  Smooth G.G.hom ∧ IsSeparated G.G.hom ∧ LocallyOfFiniteType G.G.hom ∧
    QuasiCompact G.G.hom ∧ IsCommMonObj G.G ∧
    ConnectedSpace (F.obj G.G).left ∧ HasTorusExtensionScheme (F.obj G.G) ∧
    ConnectedSpace (closedFibre G).left ∧ HasTorusExtensionScheme (closedFibre G) ∧
    ∃ g : ℕ, A.dim = g ∧ topologicalKrullDim (F.obj G.G).left = g ∧
      topologicalKrullDim (closedFibre G).left = g

/-- Both fibres of a model in the DVR leaf satisfy the scheme-level definition. -/
theorem isSemiabelianModelO_imp_faltingsDefScheme [IsDiscreteValuationRing O]
    (G : GroupModelO A O) (h : IsSemiabelianModelO G) : FaltingsSemiabelianDefScheme G := by
  letI : GrpObj ((Over.pullback (jO O)).obj G.G) := Functor.grpObjObj
  letI : GrpObj (closedFibre G) := Functor.grpObjObj
  obtain ⟨hs, hsep, hlft, hqc, hcomm, hηc, hηt, hsc, hst, hd⟩ :=
    isSemiabelianModelO_imp_faltingsDef G h
  exact ⟨hs, hsep, hlft, hqc, hcomm, hηc, hasTorusExtensionScheme_of_hasTorusExtension _ hηt,
    hsc, hasTorusExtensionScheme_of_hasTorusExtension _ hst, hd⟩

/-- The printed morphism extension theorem for the scheme-level fibre
conditions implies both equivalent DVR statements. -/
theorem faltingsLemma1DVRPrint_of_printed
    (extend : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (A B : PkgI3.AbVar K) (G : GroupModelO A O) (H : GroupModelO B O),
      IsIntegrallyClosed O →
      FaltingsSemiabelianDefScheme G → FaltingsSemiabelianDefScheme H →
      ∀ {U : Scheme.{0}} (j : U ⟶ Spec (CommRingCat.of O)), IsOpenImmersion j → DenseRange j →
      let F := Over.pullback j
      letI : GrpObj (F.obj G.G) := Functor.grpObjObj
      letI : GrpObj (F.obj H.G) := Functor.grpObjObj
      ∀ f : F.obj G.G ⟶ F.obj H.G, IsMonHom f →
        ∃! g : G.G ⟶ H.G, F.map g = f) :
    FaltingsLemma1DVRPrint ∧ FaltingsLemma1DVR := by
  suffices h : FaltingsLemma1DVRPrint from ⟨h, faltingsLemma1DVR_iff_print.mpr h⟩
  intro K _ O _ A B G H hG hH
  obtain ⟨hj, hd, _⟩ := jO_genericOpen O
  exact extend K O A B G H inferInstance
    (isSemiabelianModelO_imp_faltingsDefScheme G hG)
    (isSemiabelianModelO_imp_faltingsDefScheme H hH) (jO O) hj hd

/-- The height comparison uses the print-form leaf in place of the
homomorphism form, with the same two existing inputs. -/
theorem faltingsSemistableHeightBC_of_faltingsLemma1Print (hF : FaltingsLemma1DVRPrint)
    (hR : SZRaynaud.SilverbergZarhinThm35) (hD : Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    FaltingsSemistableHeightBC :=
  faltingsSemistableHeightBC_of_faltingsLemma1 (faltingsLemma1DVR_iff_print.mpr hF) hR hD

end ZInQ.FaltingsRestate
