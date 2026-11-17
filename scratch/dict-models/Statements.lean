import ZInQKernel.Contrib.OneProof.SGA7PersistsNF
import ZInQKernel.Contrib.OneProof.MumfordRigidity

/-! Verbatim copies of the four field statements (dict-models), each checked `rfl` against the original. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue CToPrinted

namespace DictModelsCopy
open SGA7PersistsNF LeafQM.AV.R1UnivRigid PkgI3 GapSHPair in
def CopySGA7_IX_3_3_SH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], IsStrictlyHenselianDVR O' →
    ∀ (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    ∀ c : bcO hO 𝒩.G ⟶ 𝒩'.G, IsMonHom c → IsIso ((Over.pullback (jO O')).map c) →
    ∀ U : (bcO hO 𝒩.G).left.Opens, (U : Set (bcO hO 𝒩.G).left) = idCompSet (bcO hO 𝒩.G) →
      IsOpenImmersion (U.ι ≫ c.left) ∧ Set.range (U.ι ≫ c.left).base = idCompSet 𝒩'.G

example : CopySGA7_IX_3_3_SH = SGA7PersistsNF.SGA7_IX_3_3_SH := rfl
end DictModelsCopy

namespace DictModelsCopy
open ReductGlue LeafQM.AV.R1UnivRigid PkgI3 GapSHPair in
def CopyRaynaudSemistableSH : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

example : CopyRaynaudSemistableSH = ReductGlue.RaynaudSemistableSH := rfl
end DictModelsCopy

namespace DictModelsCopy
open ZInQ.Contrib.MumfordRigidity LeafQM.AV.R1UnivRigid PkgI3 GapSHPair in
def CopyMumfordGroupLaw : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

example : CopyMumfordGroupLaw = ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw := rfl
end DictModelsCopy

namespace DictModelsCopy
open GapSHPair LeafQM.AV.R1UnivRigid PkgI3 GapSHPair in
def CopyNeronBaseChangeStrictHenselization : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = O), IsSHSep O O₁ hO →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

example : CopyNeronBaseChangeStrictHenselization = GapSHPair.NeronBaseChangeStrictHenselization := rfl
end DictModelsCopy

end