import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneActualV1
import ZInQKernel.Contrib.OneProof.EllAdic.EtaleConstantResidueHOneTorsionV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicResidueKernelLinearV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite

namespace RC53.EllAdic

universe u

local instance integralLinearEtaleSheafify (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology Ab.{u+1} := Scheme.hasSheafify_smallEtaleTopology.{u, 0} S

local instance integralLinearProEtSheafify (S : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology S) Ab.{u+1} := ProEtale.hasSheafify_proetale.{u, 0} S

local instance integralLinearEtaleGrothendieck (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

local instance integralLinearEtaleExt (S : Scheme.{u}) :
    HasExt.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) :=
  IsGrothendieckAbelian.hasExt (Sheaf S.smallEtaleTopology Ab.{u+1})

private theorem etaleDepthKill (S : Scheme.{u}) (p : ℕ) (n : ℕ)
    (x : etaleResidueHOne S p n) : (p ^ n : ℕ) • x = 0 :=
  etaleConstantResidue_hOne_nsmul_eq_zero S p n x

private theorem etaleDepthDifference (S : Scheme.{u}) (p : ℕ)
    (x : ∀ n, etaleResidueHOne S p n) (n : ℕ) :
    etaleResidueHOneSubShift S p x n = x n - etaleResidueHOneReduction S p n (x (n + 1)) := rfl

/-- The original compatible-family kernel with its coordinatewise residue action. -/
@[instance_reducible]
noncomputable def etaleResidueHOneKernelModule (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Module ℤ_[p] ↥(etaleResidueHOneSubShift S p).ker :=
  padicResidueKernelModule (p := p) (etaleDepthKill S p) (etaleResidueHOneReduction S p)
    (etaleResidueHOneSubShift S p) (etaleDepthDifference S p)

/-- On the literal kernel, scalar multiplication at depth `n` is repeated
addition by the natural representative modulo `p ^ n`. -/
theorem etaleResidueHOneKernel_smul_coordinate (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (a : ℤ_[p]) (x : ↥(etaleResidueHOneSubShift S p).ker) (n : ℕ) :
    letI := etaleResidueHOneKernelModule S p
    (a • x).val n = (PadicInt.toZModPow n a).val • x.val n := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  let r := (PadicInt.toZModPow n a).val
  have hr : (r : ZMod (p ^ n)) = PadicInt.toZModPow n a := ZMod.natCast_zmod_val _
  exact (padicResidueKernelModule_smul_coordinate (p := p) (etaleDepthKill S p)
      (etaleResidueHOneReduction S p) (etaleResidueHOneSubShift S p) (etaleDepthDifference S p)
      a x n).trans
    (padicResidueDepth_smul_eq_nsmul (p := p) (etaleDepthKill S p) n r a (x.val n) hr)

/-- On the supplied source module, the integral comparison is the same map,
now linear for the canonical residue action on the target. -/
noncomputable def ellAdicHOne_actualEtale_linearEquiv (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] [Module ℤ_[p] (S.EllAdicCohomology p 1)] :
    letI := etaleResidueHOneKernelModule S p
    S.EllAdicCohomology p 1 ≃ₗ[ℤ_[p]] ↥(etaleResidueHOneSubShift S p).ker :=
  padicResidueKernelLinearEquiv (p := p) (etaleDepthKill S p) (etaleResidueHOneReduction S p)
    (etaleResidueHOneSubShift S p) (etaleDepthDifference S p) (ellAdicHOne_actualEtale_equiv S p)

theorem ellAdicHOne_actualEtale_linearEquiv_apply (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] [Module ℤ_[p] (S.EllAdicCohomology p 1)] (x : S.EllAdicCohomology p 1) :
    ellAdicHOne_actualEtale_linearEquiv S p x = ellAdicHOne_actualEtale_equiv S p x :=
  padicResidueKernelLinearEquiv_apply (p := p) (etaleDepthKill S p) (etaleResidueHOneReduction S p)
    (etaleResidueHOneSubShift S p) (etaleDepthDifference S p) (ellAdicHOne_actualEtale_equiv S p) x

/-- The comparison still gives the original cone projection after the literal
finite étale-to-pro-étale map. -/
theorem ellAdicHOne_actualEtale_linearEquiv_coordinate (S : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] [Module ℤ_[p] (S.EllAdicCohomology p 1)]
    (x : S.EllAdicCohomology p 1) (n : ℕ) :
    smallEtaleResidueHOneForward S p n ((ellAdicHOne_actualEtale_linearEquiv S p x).val n) =
      Sheaf.H.map ((continuousResidueProEtSheafCone S p).π.app (op n)) 1 x :=
  (congrArg (fun y : ↥(etaleResidueHOneSubShift S p).ker =>
    smallEtaleResidueHOneForward S p n (y.val n))
    (ellAdicHOne_actualEtale_linearEquiv_apply S p x)).trans
      (ellAdicHOne_actualEtale_equiv_apply S p x n)

end RC53.EllAdic
