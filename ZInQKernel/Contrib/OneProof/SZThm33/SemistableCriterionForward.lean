import ZInQKernel.Contrib.OneProof.SZThm33.TateWeilSpecialization
import ZInQKernel.Contrib.OneProof.SZThm33.ClosureInertiaTransfer
import ZInQKernel.Contrib.OneProof.SZThm33.StrictInertiaCriterion
import ZInQKernel.Contrib.OneProof.SZThm33.WildInertiaOfSquare

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue
open scoped CategoryTheory.MonObj

namespace SZRaynaud

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 160000 in
/-- The forward implication of the Silverberg–Zarhin semistability criterion
on the specified rational Tate space, over an arbitrary DVR. -/
theorem levelTwo_of_semistableReductionSZ
    (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O)) (hA : HasSemistableReductionSZ A O) :
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  obtain ⟨M, hM, hSemi⟩ := hA
  let E := GapSHPair.inertiaField (K := K) w
  let V := GapSHPair.wE (K := K) w
  let hV := GapSHPair.hE_eq w hw
  let N := bcDVR hV M
  have : IsDiscreteValuationRing V := (GapSHPair.isSHSep_inertia w hw).1.1
  have hS : N.IsSemistable := strictModel_isSemistable w hw M (isSemistable_of_sz M hSemi)
  obtain ⟨hN, H, i, L, hOpen, hMon, hi, hGeom, hgen, hInv, hVery⟩ :=
    Relative.exists_inertiaFieldModelLine w hw M hM
  have : IsAlgClosure E Ω := isAlgClosure_over_inertiaField w
  let e : AlgebraicClosure E ≃ₐ[E] Ω := IsAlgClosure.equiv E _ _
  let v := w.comap (e : AlgebraicClosure E →+* Ω)
  have hv : v.comap (algebraMap E (AlgebraicClosure E)) = V :=
    comap_closureEquiv_eq e w V rfl
  have huV : IsUnit (ℓ : V) := by
    simpa only [map_natCast] using hu.map (comapHom hV)
  apply levelTwo_of_strictInertia w A ℓ
  apply levelTwo_of_closureEquiv e w (A.baseChange E) ℓ
  exact Ambient.levelTwo_of_semistable_identityModel hv (A.baseChange E) H N huV hN hS
    i hi hgen L hVery

/-- The manuscript's wild inertia statement on its actual Tate towers. -/
theorem elliotWildInertiaTrivial_proof : ElliotWildInertiaTrivial :=
  elliot_of_semistable_levelTwo levelTwo_of_semistableReductionSZ

end SZRaynaud
