import ZInQKernel.Contrib.OneProof.CMjReroute.Dictionary
import ZInQKernel.Contrib.OneProof.GAGAMorphism
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-!
# The CM dictionary, unconditionally

The Hom–lattice correspondence over `ℂ` (lifting of homomorphisms through uniformizations and
realization of lattice maps by unique homomorphisms) is proved in the tree, from the uniformization of
complex abelian varieties and GAGA for morphisms. So the dictionary `q⁻¹(𝒪) ≃+* End_𝒪(Q)` at a CM
point holds without hypotheses, and its image is central.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory
open _root_.LeafQM _root_.LeafQM.AV ShimuraCFT RayClassCFT
open _root_.ZInQ.LeafPush2 (CPts IsUniformization)

/-- The Hom–lattice correspondence over `ℂ`, proved. -/
theorem homLatticeCorr_proved : ZInQ.HomUnify.HomLatticeCorr :=
  AvSplit.Final.h69 _root_.uniformizationLeafAll_proof
    _root_.ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof

variable {K : Type} [Field K] [NumberField K] {τ : UpperHalfPlane} {Q : QML3 ℂ}
  {Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)}

/-- **The CM dictionary at a CM point, for every order** `q⁻¹(𝒪)`: a ring isomorphism
`q⁻¹(𝒪) ≃+* End_𝒪(Q)`, `t ↦` the endomorphism inducing multiplication by `κ(t)` on `ℂ²`. -/
def comEquivCM (hK : Module.finrank ℚ K = 2)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) : ordR q ≃+* com Q.q :=
  comEquiv homLatticeCorr_proved hK hU hι q κ hcm

theorem comEquivCM_spec (hK : Module.finrank ℚ K = 2)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) (z : Fin 2 → ℂ) :
    Φu (κ t • z) = Φu z ≫ ((comEquivCM hK hU hι q κ hcm t : com Q.q) : PkgI3.AbVar.End Q.A).hom :=
  endOf_spec homLatticeCorr_proved hU q κ hcm t z

/-- The image of the dictionary is central in `End(Q.A)`. -/
theorem comEquivCM_mem_center (hK : Module.finrank ℚ K = 2)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) :
    ((comEquivCM hK hU hι q κ hcm t : com Q.q) : PkgI3.AbVar.End Q.A) ∈
      Subring.center (PkgI3.AbVar.End Q.A) :=
  Subring.mem_center_iff.mpr fun g => (endOf_mem_center homLatticeCorr_proved hU q κ hcm t g).symm

end HDec.CMBranch.CMjReroute
