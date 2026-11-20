import ZInQKernel.Contrib.OneProof.CMjBridgesDiscriminant
import ZInQKernel.Contrib.OneProof.CMBranch.PeriodLattice
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.GAGAMorphism
import ZInQKernel.Contrib.CloudW06PoincareRigidity.T11bRigidity

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry Limits
open scoped UpperHalfPlane
open _root_.ZInQ.Contrib.CloudW06PoincareRigidity (T11b_Rigidity_proof)

local notation "AbVar" => ZInQ.DefFaltings.AbVar

/-- T35, in the point form for arbitrary embeddings. The torsion count fixes the
dimension in the coordinate uniformization, and the existing base change
dictionary transports it from the actual complex scheme. -/
theorem uniformization_exists : ZInQ.LeafPush2.UniformizationExists :=
  AvSplit.Final.h38 uniformizationLeafAll_proof
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

/-- Step 2, geometric part: for each embedding the actual complex base change
of the curve (obtained along an extension of `σ` to the algebraic closure)
has dimension one and its endomorphism ring is still `R`. -/
theorem exists_complex_baseChange_cm {L : Type} [Field L] [NumberField L]
    (E : AbVar L) (hE : E.dim = 1) {k : Type} [Field k] (R : Subring k)
    (hCM : IsCMBy E k R) (σ : L →+* ℂ) :
    ∃ (B : PkgI3.AbVar ℂ) (p : B.X.left ⟶ E.X.left),
      IsPullback p B.X.hom E.X.hom (Spec.map (CommRingCat.ofHom σ)) ∧
        B.dim = 1 ∧ Nonempty (PkgI3.AbVar.End B ≃+* R) := by
  let A := LeafAdopt.abVarEquiv L E
  let : Algebra L ℂ := σ.toAlgebra
  let σbar : AlgebraicClosure L →ₐ[L] ℂ := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure L) ℂ := σbar.toRingHom.toAlgebra
  let Abar := A.baseChange (AlgebraicClosure L)
  let B := Abar.baseChange ℂ
  let f := Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))
  let g := Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure L) ℂ))
  have S₁ : IsPullback (pullback.fst Abar.X.hom g) (pullback.snd Abar.X.hom g) Abar.X.hom g :=
    IsPullback.of_hasPullback _ _
  have S₂ : IsPullback (pullback.fst A.X.hom f) (pullback.snd A.X.hom f) A.X.hom f :=
    IsPullback.of_hasPullback _ _
  have hσ : g ≫ f = Spec.map (CommRingCat.ofHom σ) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact σbar.commutes x
  have hd : B.dim = 1 :=
    (PkgI3.AbVar.dim_baseChange Abar ℂ).trans
      ((PkgI3.AbVar.dim_baseChange A (AlgebraicClosure L)).trans
        ((LeafAdopt.abVarEquiv_dim L E).trans hE))
  obtain ⟨e⟩ := end_ringEquiv_baseChange T11b_Rigidity_proof (AlgebraicClosure L) ℂ Abar
  obtain ⟨r⟩ := hCM
  exact ⟨B, pullback.fst Abar.X.hom g ≫ pullback.fst A.X.hom f,
    hσ ▸ S₁.paste_horiz S₂, hd, ⟨e.symm.trans r⟩⟩

/-- Steps 2 and 3: every embedded CM elliptic curve has a rank-two period lattice
whose multiplier ring is its full geometric endomorphism ring. All three
suppliers (T35, the lattice correspondence, and rigidity) are theorems. -/
theorem cmPeriodLattice_proof : CMPeriodLattice :=
  cmPeriodLattice_of uniformization_exists
    (AvSplit.Final.h69 uniformizationLeafAll_proof
      ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof)
    T11b_Rigidity_proof

/-- With an oriented basis of the actual period lattice, the modular j of the
period is a singular modulus of the discriminant of the given CM order. -/
theorem exists_cm_period {L : Type} [Field L] [NumberField L] (E : AbVar L)
    (hE : E.dim = 1) {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : IsImagQuadOrder k R) (hCM : IsCMBy E k R) (σ : L →+* ℂ) :
    ∃ τ : ℍ, IsPeriodAt (LeafAdopt.abVarEquiv L E) σ τ ∧
      PeriodDiscriminant τ (orderDisc R) := by
  obtain ⟨Λ, Φ, hU, ⟨hD, hZ⟩, hRing⟩ := cmPeriodLattice_proof L E hE k R hR hCM σ
  let : DiscreteTopology Λ := hD
  let : IsZLattice ℝ Λ := hZ
  obtain ⟨s, t, hs, ht, hΛ⟩ := exists_basis_upper Λ
  let τ : ℍ := ⟨t, ht⟩
  exact ⟨τ, ⟨Λ, Φ, hU, s, hs, hΛ⟩,
    (periodDiscriminant_iff_orderDisc R hR hs τ hΛ hRing _).mpr rfl⟩

end HDec.CMBranch.CMjBridges
