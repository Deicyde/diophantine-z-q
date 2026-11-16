import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization

/-! Verbatim copies of the target Prop and the chain Prop proved alongside it, checked `rfl` against the
originals (`ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean:1520-1531`,
`ZInQKernel/OneProof/H/TailZ14.lean:1502-1509`). -/

namespace NeronSHCopy

open IsLocalRing ReductSplit ReductGlue GapSHPair

def IsSHSep {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] (O : ValuationSubring K)
    (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O) : Prop :=
  IsStrictlyHenselianDVR O₁ ∧ Algebra.IsSeparable K K₁ ∧
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) ∧
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O₁))

def NeronBaseChangeStrictHenselization : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = O), IsSHSep O O₁ hO →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

def NeronBaseChangeUnramifiedDVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (K' : Type)
    [Field K'] [Algebra K K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O), Algebra.IsSeparable K K' →
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) →
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')) →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

example : NeronBaseChangeStrictHenselization = GapSHPair.NeronBaseChangeStrictHenselization := rfl
example : NeronBaseChangeUnramifiedDVR = ReductGlue.NeronBaseChangeUnramifiedDVR := rfl

theorem copy_proved : NeronBaseChangeStrictHenselization := NeronSH.neronBaseChangeStrictHenselization_proof
theorem copy_proved' : NeronBaseChangeUnramifiedDVR := NeronSH.neronBaseChangeUnramifiedDVR_proof

end NeronSHCopy

#print axioms NeronSHCopy.copy_proved
#print axioms NeronSHCopy.copy_proved'
