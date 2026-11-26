import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtShortExactV2
import ZInQKernel.Contrib.OneProof.EllAdic.ExtOneShortExactKernelV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- Degree-zero surjectivity for the actual product difference follows from
sectionwise surjectivity at the terminal object of the same site. -/
theorem finiteResidueProEtSubShift_H0_surjective (S : Scheme.{u}) (p : ℕ) :
    Function.Surjective (Sheaf.H.map (finiteResidueProEtSubShift S p) 0) := by
  intro y
  let P := finiteResidueProEtProduct S p
  let hT := terminalIsTerminal (C := S.ProEt)
  let e := Sheaf.H.equiv₀ P hT
  obtain ⟨x, hx⟩ := finiteResidueProEtSubShift_sections_surjective S p (op (⊤_ S.ProEt)) (e y)
  refine ⟨e.symm x, ?_⟩
  let d : P ⟶ P := finiteResidueProEtSubShift S p
  have hnat : Sheaf.H.map d 0 (e.symm x) = e.symm (d.hom.app (op (⊤_ S.ProEt)) x) :=
    Sheaf.H.equiv₀_symm_naturality hT d x
  have hcongr : e.symm (d.hom.app (op (⊤_ S.ProEt)) x) = e.symm (e y) :=
    congrArg (fun z : P.obj.obj (op (⊤_ S.ProEt)) => e.symm z) hx
  exact hnat.trans (hcongr.trans (e.symm_apply_apply y))

/-- Before any comparison of the products in degree one, the original
pro-étale first cohomology maps bijectively onto the kernel in the cohomology
of the product via its canonical reduction arrow. -/
theorem padicProEt_H1_toProductKernel_bijective (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (extOneToNextKernel
        ((constantSheaf (Scheme.ProEt.topology S) Ab.{u+1}).obj
          (AddCommGrpCat.of (ULift.{u+1} ℤ)))
        (padicCoefficientProductSequence S p)) :=
  extOneToNextKernel_bijective _ _ (padicCoefficientProductSequence_shortExact S p)
    (finiteResidueProEtSubShift_H0_surjective S p)

end RC53.EllAdic
