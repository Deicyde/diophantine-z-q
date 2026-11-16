import ZInQKernel.Contrib.OneProof.UniformizationPrinted
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailC

set_option linter.all false
noncomputable section

namespace PELHodge

open CategoryTheory AlgebraicGeometry Limits Topology Filter Set MonObj
open PkgI3 (AbVar)
open BPAnalytic
open LeafQM LeafQM.AV
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt cDom)
open ZInQ.HomLattice (IsAnalyticHom IsStrongUnif)
open UnifPrinted (CPt classicalTopology XPtIn XevalAt)

attribute [local instance] UnifPrinted.classicalTopology

example (A : AbVar ℂ) : TopologicalSpace (A.Pt ℂ) := inferInstance

def H1 (A : AbVar ℂ) : Type := Abelianization (FundamentalGroup (A.Pt ℂ) 1)

instance (A : AbVar ℂ) : CommGroup (H1 A) := by unfold H1; infer_instance

def loopClass {A : AbVar ℂ} (lp : Path (1 : A.Pt ℂ) 1) : H1 A :=
  Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk lp))

def IsHodgeFibre (τ : UpperHalfPlane) (P : QML3 ℂ) : Prop :=
  ∃ e : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
    IsAnalyticHom (RingHom.id ℂ) e ∧ HDec.HSyn.G0Split.FibreQM.IotaCompatible P e ∧
    (∀ v ∈ QM.qmLattice τ.im_pos.ne', e v = 1) ∧
    ∃ lp : QM.qmLattice τ.im_pos.ne' → Path (1 : P.A.Pt ℂ) 1,
      (∀ v (t : unitInterval), lp v t = e (((t : ℝ) : ℂ) • (v : Fin 2 → ℂ))) ∧
      Function.Bijective (fun v => loopClass (lp v))

example (g : ℕ) : SimplyConnectedSpace (Fin g → ℂ) := inferInstance

end PELHodge
