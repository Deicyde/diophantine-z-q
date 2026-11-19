import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionE1a
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.ActualFullModel
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.RepresentativeIndependence

/-!
# Representative independence at the native full-condition interface

The original full-condition coordinate retains the same cohomology class and
paired-functional class.  Changes of representatives are degreewise unipotent
shears of determinant one, including at zero coordinates.  The statements use
Identification3 and OrigCoordLink3 directly; no conversion to the legacy
identification or coordinate-identity assumption is used.
The locators are TeX 3837–3862, 3877–3892 and 5509–5516.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.NativeRepresentatives

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.CoordLink (kmCoord_congr)
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Determinant (OO Lam SignGroup evK sgnChar)
open ZInQ.Contrib.RC53Assist.CoordProvenance (classBoundaryCycle functionalBoundaryClosed
  kmCoord_class_boundary kmCoord_functional_boundary)
open ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- A retained class boundary is unchanged by actual sign evaluation. -/
theorem native_class_coordinate_eq (M : Identification3 K S S' hS b dK hK cE tK)
    (z z' : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (lam : (M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (hz : (M.C.map (φO b)).toFour.d1 *ᵥ z = 0)
    (hz' : (M.C.map (φO b)).toFour.d1 *ᵥ z' = 0)
    (hlam : lam ᵥ* (M.C.map (φO b)).toFour.d1 = 0)
    (a : Fin M.C.m0 → MonoidAlgebra OO (SignGroup b))
    (ha : z - z' = (M.C.map (φO b)).toFour.d0 *ᵥ a) (x : Addr b) :
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam)
      (hzev3 hz x) (hlamev3 hlam x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) =
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z') (evK (sgnChar x) ∘ lam)
      (hzev3 hz' x) (hlamev3 hlam x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) := by
  let C : FourCx (FractionRing OO) (Fin M.C.m0)
      ((M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N)
      ((M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N) (Fin M.C.m2) :=
    (Cev3 (M.C.map (φO b)) x).toFour
  let f : MonoidAlgebra OO (SignGroup b) →+* FractionRing OO := evK (sgnChar x)
  have he : f ∘ z = f ∘ z' + C.d0 *ᵥ (f ∘ a) := by
    funext i
    change f (z i) = f (z' i) +
      (fromRows ((M.C.map (φO b)).c0.map f) ((M.C.map (φO b)).Y.map f) *ᵥ (f ∘ a)) i
    erw [← fromRows_map, ← RingHom.map_mulVec, ← map_add]
    exact congrArg f ((congrFun (eq_add_of_sub_eq ha) i).trans (add_comm _ _))
  have hplus := classBoundaryCycle C (f ∘ z') (hzev3 hz' x) (f ∘ a)
  calc
    kmCoord C (f ∘ z) (f ∘ lam) (hzev3 hz x) (hlamev3 hlam x) _ =
        kmCoord C (f ∘ z' + C.d0 *ᵥ (f ∘ a)) (f ∘ lam) hplus (hlamev3 hlam x) _ :=
      kmCoord_congr rfl he rfl _ _ _ _ _
    _ = kmCoord C (f ∘ z') (f ∘ lam) (hzev3 hz' x) (hlamev3 hlam x) _ :=
      kmCoord_class_boundary C (f ∘ z') (f ∘ lam) (hzev3 hz' x) (hlamev3 hlam x) (f ∘ a) hplus _

/-- A retained functional boundary is unchanged by actual sign evaluation. -/
theorem native_functional_coordinate_eq (M : Identification3 K S S' hS b dK hK cE tK)
    (z : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (lam lam' : (M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (hz : (M.C.map (φO b)).toFour.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* (M.C.map (φO b)).toFour.d1 = 0)
    (hlam' : lam' ᵥ* (M.C.map (φO b)).toFour.d1 = 0)
    (r : Fin M.C.m2 → MonoidAlgebra OO (SignGroup b))
    (hr : lam - lam' = r ᵥ* (M.C.map (φO b)).toFour.d2) (x : Addr b) :
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam)
      (hzev3 hz x) (hlamev3 hlam x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) =
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam')
      (hzev3 hz x) (hlamev3 hlam' x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) := by
  let C : FourCx (FractionRing OO) (Fin M.C.m0)
      ((M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N)
      ((M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N) (Fin M.C.m2) :=
    (Cev3 (M.C.map (φO b)) x).toFour
  let f : MonoidAlgebra OO (SignGroup b) →+* FractionRing OO := evK (sgnChar x)
  have he : f ∘ lam = f ∘ lam' + (f ∘ r) ᵥ* C.d2 := by
    funext i
    change f (lam i) = f (lam' i) +
      ((f ∘ r) ᵥ* fromCols ((M.C.map (φO b)).U.map f) ((M.C.map (φO b)).V.map f)) i
    erw [← fromCols_map, ← RingHom.map_vecMul, ← map_add]
    exact congrArg f ((congrFun (eq_add_of_sub_eq hr) i).trans (add_comm _ _))
  have hplus := functionalBoundaryClosed C (f ∘ lam') (hlamev3 hlam' x) (f ∘ r)
  calc
    kmCoord C (f ∘ z) (f ∘ lam) (hzev3 hz x) (hlamev3 hlam x) _ =
        kmCoord C (f ∘ z) (f ∘ lam' + (f ∘ r) ᵥ* C.d2) (hzev3 hz x) hplus _ :=
      kmCoord_congr rfl rfl he _ _ _ _ _
    _ = kmCoord C (f ∘ z) (f ∘ lam') (hzev3 hz x) (hlamev3 hlam' x) _ :=
      kmCoord_functional_boundary C (f ∘ z) (f ∘ lam') (hzev3 hz x) (hlamev3 hlam' x) (f ∘ r) hplus _

/-- The original full-condition coordinate of two lifts of the same actual
family class agrees in the fixed native determinant basis. -/
theorem actual_lifts_coordinate_eq (M : Identification3 K S S' hS b dK hK cE tK)
    (z z' : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (lam : (M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (hz : (M.C.map (φO b)).toFour.d1 *ᵥ z = 0)
    (hz' : (M.C.map (φO b)).toFour.d1 *ᵥ z' = 0)
    (hlam : lam ᵥ* (M.C.map (φO b)).toFour.d1 = 0)
    (a : (familyCx M).X 0)
    (ha : modelMap1 M z - modelMap1 M z' = (familyCx M).d 0 1 rfl a) (x : Addr b) :
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z) (evK (sgnChar x) ∘ lam)
      (hzev3 hz x) (hlamev3 hlam x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) =
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z') (evK (sgnChar x) ∘ lam)
      (hzev3 hz' x) (hlamev3 hlam x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) := by
  obtain ⟨c, hc⟩ := actual_class_lifts_differ M z z' hz hz' a ha
  exact native_class_coordinate_eq M z z' lam hz hz' hlam c hc x

/-- The actual paired-functional representative may change by the retained
conjugate boundary without changing the original coordinate. -/
theorem actual_paired_rows_coordinate_eq (M : Identification3 K S S' hS b dK hK cE tK)
    (z : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (hz : (M.C.map (φO b)).toFour.d1 *ᵥ z = 0)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))} (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc zc' : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0)
    (hzc' : (selCx Dp).d 1 2 rfl zc' = 0) (a : (selCx Dp).X 0)
    (ha : zc - zc' = (selCx Dp).d 0 1 rfl a) (x : Addr b) :
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z)
      (evK (sgnChar x) ∘ pairedRow M P tr zc) (hzev3 hz x)
      (hlamev3 (pairedRow_closed M P tr htr zc hzc) x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) =
    kmCoord (Cev3 (M.C.map (φO b)) x).toFour (evK (sgnChar x) ∘ z)
      (evK (sgnChar x) ∘ pairedRow M P tr zc') (hzev3 hz x)
      (hlamev3 (pairedRow_closed M P tr htr zc' hzc') x) (σFull M.C.m0 M.C.m1 M.C.m2 M.C.N) :=
  native_functional_coordinate_eq M z _ _ hz (pairedRow_closed M P tr htr zc hzc)
    (pairedRow_closed M P tr htr zc' hzc') (pairedRowPrimitive M P tr a)
    (pairedRow_boundary M P tr htr zc zc' a ha) x

/-- OrigCoordLink3 depends on the same actual class, not on its finite-model
lift.  This is representative independence, not a hypothesis proving the
missing arithmetic endpoint identification. -/
theorem origCoordLink3_class_iff {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification3 K S S' hS F.b dK hK cE tK)
    (z z' : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (lam : (M.C.map (φO F.b)).D2 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
    (hz' : (M.C.map (φO F.b)).toFour.d1 *ᵥ z' = 0)
    (hlam : lam ᵥ* (M.C.map (φO F.b)).toFour.d1 = 0)
    (a : (familyCx M).X 0)
    (ha : modelMap1 M z - modelMap1 M z' = (familyCx M).d 0 1 rfl a)
    (eta : MonoidAlgebra OO (SignGroup F.b)) :
    OrigCoordLink3 D F M z lam hz hlam eta ↔ OrigCoordLink3 D F M z' lam hz' hlam eta := by
  constructor <;> intro h e g hrep x hΔ
  · exact (h e g hrep x hΔ).trans (congrArg (evK (sgnChar x) eta * ·)
      (actual_lifts_coordinate_eq M z z' lam hz hz' hlam a ha x))
  · exact (h e g hrep x hΔ).trans (congrArg (evK (sgnChar x) eta * ·)
      (actual_lifts_coordinate_eq M z z' lam hz hz' hlam a ha x).symm)

/-- OrigCoordLink3 retains the same actual conjugate-functional class and the
same correction while its cochain representative changes by a boundary. -/
theorem origCoordLink3_pairing_iff {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification3 K S S' hS F.b dK hK cE tK)
    (z : (M.C.map (φO F.b)).D1 ⊕ (M.C.map (φO F.b)).N → MonoidAlgebra OO (SignGroup F.b))
    (hz : (M.C.map (φO F.b)).toFour.d1 *ᵥ z = 0)
    {Dp : SelData (MonoidAlgebra OO (SignGroup F.b))} (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup F.b)] MonoidAlgebra OO (SignGroup F.b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc zc' : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0)
    (hzc' : (selCx Dp).d 1 2 rfl zc' = 0) (a : (selCx Dp).X 0)
    (ha : zc - zc' = (selCx Dp).d 0 1 rfl a) (eta : MonoidAlgebra OO (SignGroup F.b)) :
    OrigCoordLink3 D F M z (pairedRow M P tr zc) hz (pairedRow_closed M P tr htr zc hzc) eta ↔
      OrigCoordLink3 D F M z (pairedRow M P tr zc') hz (pairedRow_closed M P tr htr zc' hzc') eta := by
  constructor <;> intro h e g hrep x hΔ
  · exact (h e g hrep x hΔ).trans (congrArg (evK (sgnChar x) eta * ·)
      (actual_paired_rows_coordinate_eq M z hz P tr htr zc zc' hzc hzc' a ha x))
  · exact (h e g hrep x hΔ).trans (congrArg (evK (sgnChar x) eta * ·)
      (actual_paired_rows_coordinate_eq M z hz P tr htr zc zc' hzc hzc' a ha x).symm)

end ZInQ.Contrib.RC53Assist.CoordProvenance.NativeRepresentatives
