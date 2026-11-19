import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionIdentification
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionCoord
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.GenuineRetention
import ZInQKernel.Contrib.RC53Assist.CoordProvenance.CohomologyLift

/-!
# Actual classes and paired rows in the full-condition finite model

The original cochain class is lifted through the given genuine family
quasi-isomorphism of Identification3.  The functional is the traced pairing
PD(-, conjugate class), represented in the original degree-two model basis.
Both constructions retain their cochain boundaries and apply at zero classes.
No scalar coordinate is newly defined, and no coordinate-link identity is an
input.  The locators are TeX 3844–3861, 3877–3892 and 5398–5403.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup)
open ZInQ.Contrib.RC53Assist.CoordProvenance (exists_lift_with_boundary lifts_differ_by_boundary
  rowOf rowOf_apply rowOf_closed)

section Pairing

variable {R : Type} [CommRing R] {D Dp : SelData R}

/-- The manuscript's pairing order, with the actual conjugate class in degree one. -/
def rightFunctional (P : SelPairData D Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[R] R) (zc : (selCx Dp).X 1) :
    (selCx D).X 2 →ₗ[R] R :=
  tr.comp ((selCup P 2 1 3 rfl).flip zc)

/-- The actual paired functional is closed on the actual Selmer cochains. -/
theorem rightFunctional_closed (P : SelPairData D Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0)
    (v : (selCx D).X 1) :
    rightFunctional P tr zc ((selCx D).d 1 2 rfl v) = 0 := by
  have hl := selmerCupLeibniz_proof R D Dp P 1 2 1 2 2 3 rfl rfl rfl rfl v zc
  rw [hzc] at hl
  erw [map_zero, smul_zero, add_zero] at hl
  exact (congrArg tr hl).symm.trans (htr (selCup P 1 1 2 rfl v zc))

/-- Changing the conjugate representative by a retained boundary changes the
functional by a degree-three primitive, not necessarily by the zero cochain. -/
theorem rightFunctional_boundary (P : SelPairData D Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[R] R)
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc zc' : (selCx Dp).X 1) (b : (selCx Dp).X 0)
    (hb : zc - zc' = (selCx Dp).d 0 1 rfl b) (v : (selCx D).X 2) :
    rightFunctional P tr zc v - rightFunctional P tr zc' v =
      -tr (selCup P 3 0 3 rfl ((selCx D).d 2 3 rfl v) b) := by
  have hl := selmerCupLeibniz_proof R D Dp P 2 3 0 1 2 3 rfl rfl rfl rfl v b
  have ht := htr (selCup P 2 0 2 rfl v b)
  have hh := congrArg tr hl
  erw [map_add] at hh
  simp only [sgn_two, one_smul] at hh
  have hsum : 0 = tr (selCup P 3 0 3 rfl ((selCx D).d 2 3 rfl v) b) +
      tr (selCup P 2 1 3 rfl v ((selCx Dp).d 0 1 rfl b)) := ht.symm.trans hh
  change tr (selCup P 2 1 3 rfl v zc) - tr (selCup P 2 1 3 rfl v zc') = _
  erw [← map_sub, ← map_sub, hb]
  exact eq_neg_of_add_eq_zero_right hsum.symm

end Pairing

section Model

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- The actual family data carried by the native full-condition identification. -/
abbrev familyData (M : Identification3 K S S' hS b dK hK cE tK) :
    SelData (MonoidAlgebra OO (SignGroup b)) :=
  galoisSelData K S' (MonoidAlgebra OO (SignGroup b)) M.Mf M.Δf

abbrev familyCx (M : Identification3 K S S' hS b dK hK cE tK) :
    GCx (MonoidAlgebra OO (SignGroup b)) := selCx (familyData M)

abbrev modelCx (M : Identification3 K S S' hS b dK hK cE tK) :
    GCx (MonoidAlgebra OO (SignGroup b)) := (M.C.map (φO b)).toGCx

/-- Explicitly typed components of the native model map keep the actual
cochain modules as their targets. -/
abbrev modelMap1 (M : Identification3 K S S' hS b dK hK cE tK) :
    (((M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N) → MonoidAlgebra OO (SignGroup b)) →ₗ[
      MonoidAlgebra OO (SignGroup b)] (familyCx M).X 1 :=
  (M.ψf.f 1).hom

abbrev modelMap2 (M : Identification3 K S S' hS b dK hK cE tK) :
    (((M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N) → MonoidAlgebra OO (SignGroup b)) →ₗ[
      MonoidAlgebra OO (SignGroup b)] (familyCx M).X 2 :=
  (M.ψf.f 2).hom

abbrev modelMap3 (M : Identification3 K S S' hS b dK hK cE tK) :
    (Fin M.C.m2 → MonoidAlgebra OO (SignGroup b)) →ₗ[
      MonoidAlgebra OO (SignGroup b)] (familyCx M).X 3 :=
  (M.ψf.f 3).hom

/-- Lift the same actual family class to the full-condition graded model,
with the boundary supplied by the actual family quasi-isomorphism. -/
theorem actual_class_lift (M : Identification3 K S S' hS b dK hK cE tK)
    (z : (familyCx M).X 1) (hz : (familyCx M).d 1 2 rfl z = 0) :
    ∃ zm : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b),
      (M.C.map (φO b)).toFour.d1 *ᵥ zm = 0 ∧
      ∃ a : (familyCx M).X 0,
        modelMap1 M zm - z = (familyCx M).d 0 1 rfl a := by
  obtain ⟨zm, hzm, a, ha⟩ := exists_lift_with_boundary M.ψf M.qisf 1 z hz
  exact ⟨zm, hzm, a, ha⟩

/-- Two actual-class lifts differ by a boundary in the same full model. -/
theorem actual_class_lifts_differ (M : Identification3 K S S' hS b dK hK cE tK)
    (z z' : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b))
    (hz : (M.C.map (φO b)).toFour.d1 *ᵥ z = 0)
    (hz' : (M.C.map (φO b)).toFour.d1 *ᵥ z' = 0)
    (a : (familyCx M).X 0)
    (ha : modelMap1 M z - modelMap1 M z' = (familyCx M).d 0 1 rfl a) :
    ∃ c : Fin M.C.m0 → MonoidAlgebra OO (SignGroup b),
      z - z' = (M.C.map (φO b)).toFour.d0 *ᵥ c := by
  exact lifts_differ_by_boundary M.ψf M.qisf 1 z z' hz hz' a ha

/-- Pull the actual degree-two functional through the native family model map. -/
abbrev modelFunctional (M : Identification3 K S S' hS b dK hK cE tK)
    (L : (familyCx M).X 2 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b)) :
    (((M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N) → MonoidAlgebra OO (SignGroup b)) →ₗ[
      MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b) :=
  L.comp (modelMap2 M)

/-- The actual paired functional in the original degree-two model basis. -/
def pairedRow (M : Identification3 K S S' hS b dK hK cE tK)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))}
    (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (zc : (selCx Dp).X 1) :
    (M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b) :=
  rowOf (modelFunctional M (rightFunctional P tr zc))

/-- Its value is the value of the same actual pairing, not an independently
normalized scalar row. -/
theorem pairedRow_value (M : Identification3 K S S' hS b dK hK cE tK)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))}
    (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (zc : (selCx Dp).X 1)
    (v : (M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b)) :
    pairedRow M P tr zc ⬝ᵥ v = rightFunctional P tr zc (modelMap2 M v) :=
  (rowOf_apply (modelFunctional M (rightFunctional P tr zc)) v).symm

/-- Closure follows from the genuine family map and the actual traced cup product. -/
theorem pairedRow_closed (M : Identification3 K S S' hS b dK hK cE tK)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))}
    (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0) :
    pairedRow M P tr zc ᵥ* (M.C.map (φO b)).toFour.d1 = 0 := by
  apply rowOf_closed
  intro v
  have hc := congrArg (fun f => f.hom v) (M.ψf.comm 1 2)
  simp only [ModuleCat.hom_comp] at hc
  have he : (familyCx M).d 1 2 rfl (modelMap1 M v) =
      modelMap2 M ((M.C.map (φO b)).toFour.d1 *ᵥ v) := hc
  change rightFunctional P tr zc (modelMap2 M ((M.C.map (φO b)).toFour.d1 *ᵥ v)) = 0
  exact (congrArg (rightFunctional P tr zc) he).symm.trans
    (rightFunctional_closed P tr htr zc hzc (modelMap1 M v))

/-- The actual class and functional have representatives in the same native
full-condition finite model; no endpoint coordinate equality is an input. -/
theorem exists_same_actual_class_and_pairing (M : Identification3 K S S' hS b dK hK cE tK)
    (z : (familyCx M).X 1) (hz : (familyCx M).d 1 2 rfl z = 0)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))}
    (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc : (selCx Dp).X 1) (hzc : (selCx Dp).d 1 2 rfl zc = 0) :
    ∃ zm : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b),
      (M.C.map (φO b)).toFour.d1 *ᵥ zm = 0 ∧
      (pairedRow M P tr zc) ᵥ* (M.C.map (φO b)).toFour.d1 = 0 ∧
      ∃ a : (familyCx M).X 0,
        modelMap1 M zm - z = (familyCx M).d 0 1 rfl a := by
  obtain ⟨zm, hzm, a, ha⟩ := actual_class_lift M z hz
  exact ⟨zm, hzm, pairedRow_closed M P tr htr zc hzc, a, ha⟩

/-- The retained degree-three primitive of a changed conjugate representative
is constructed from the same actual trace and native model map. -/
def pairedRowPrimitive (M : Identification3 K S S' hS b dK hK cE tK)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))}
    (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (a : (selCx Dp).X 0) : Fin M.C.m2 → MonoidAlgebra OO (SignGroup b) :=
  rowOf ((-(tr.comp ((selCup P 3 0 3 rfl).flip a))).comp (modelMap3 M))

/-- The native paired rows differ by the explicitly constructed functional
boundary.  A nonzero coboundary row is retained rather than replaced by zero. -/
theorem pairedRow_boundary (M : Identification3 K S S' hS b dK hK cE tK)
    {Dp : SelData (MonoidAlgebra OO (SignGroup b))}
    (P : SelPairData (familyData M) Dp)
    (tr : (coneCx P.resE).X 3 →ₗ[MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx P.resE).d 2 3 rfl c) = 0)
    (zc zc' : (selCx Dp).X 1) (a : (selCx Dp).X 0)
    (ha : zc - zc' = (selCx Dp).d 0 1 rfl a) :
    pairedRow M P tr zc - pairedRow M P tr zc' =
      pairedRowPrimitive M P tr a ᵥ* (M.C.map (φO b)).toFour.d2 := by
  funext i
  let v : (M.C.map (φO b)).D2 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b) := Pi.single i 1
  have h := rightFunctional_boundary P tr htr zc zc' a ha (modelMap2 M v)
  have hc := congrArg (fun f => f.hom v) (M.ψf.comm 2 3)
  simp only [ModuleCat.hom_comp] at hc
  have he : (familyCx M).d 2 3 rfl (modelMap2 M v) =
      modelMap3 M ((M.C.map (φO b)).toFour.d2 *ᵥ v) := hc
  have hm : -tr (selCup P 3 0 3 rfl ((familyCx M).d 2 3 rfl (modelMap2 M v)) a) =
      pairedRowPrimitive M P tr a ⬝ᵥ ((M.C.map (φO b)).toFour.d2 *ᵥ v) := by
    rw [he]
    exact rowOf_apply ((-(tr.comp ((selCup P 3 0 3 rfl).flip a))).comp (modelMap3 M)) _
  have hs := h.trans hm
  erw [dotProduct_mulVec] at hs
  change rightFunctional P tr zc (modelMap2 M v) - rightFunctional P tr zc' (modelMap2 M v) = _
  simpa only [v, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hs

section GenuinePairing

variable (M : Identification3 K S S' hS b dK hK cE tK)
  {A T : Type}
  [AddCommGroup A] [Module (MonoidAlgebra OO (SignGroup b)) A]
  [DistribMulAction (GKS K S') A] [SMulCommClass (GKS K S') (MonoidAlgebra OO (SignGroup b)) A]
  [TopologicalSpace A] [ContinuousAdd A]
  [ContinuousConstSMul (MonoidAlgebra OO (SignGroup b)) A] [ContinuousSMul (GKS K S') A]
  [AddCommGroup T] [Module (MonoidAlgebra OO (SignGroup b)) T]
  [DistribMulAction (GKS K S') T] [SMulCommClass (GKS K S') (MonoidAlgebra OO (SignGroup b)) T]
  [TopologicalSpace T] [ContinuousAdd T]
  [ContinuousConstSMul (MonoidAlgebra OO (SignGroup b)) T] [ContinuousSMul (GKS K S') T]
  (β : M.Mf →ₗ[MonoidAlgebra OO (SignGroup b)] A →ₗ[MonoidAlgebra OO (SignGroup b)] T)
  (hβ : ∀ (g : GKS K S') (x : M.Mf) (y : A), β (g • x) (g • y) = g • β x y)
  (hβc : Continuous fun p : M.Mf × A => β p.1 p.2)
  (Δc : GaloisLocalConditions K S' (MonoidAlgebra OO (SignGroup b)) A)
  (I : IsotropyData (MonoidAlgebra OO (SignGroup b)) (GKS K S')
    (fun v : Places K S' => Gloc K v.1) (fun v => locMap K S' v.1)
    β hβ hβc M.Δf Δc)

/-- The pairing is the genuine global/local continuous-cochain cup pairing
with the actual retained isotropy data, not an abstract substitute pairing. -/
abbrev genuinePair : SelPairData (familyData M)
    (galoisSelData K S' (MonoidAlgebra OO (SignGroup b)) A Δc) :=
  genuinePairData (MonoidAlgebra OO (SignGroup b)) (GKS K S')
    (fun v : Places K S' => Gloc K v.1) (fun v => locMap K S' v.1)
    β hβ hβc M.Δf Δc I

/-- The same actual family class and the genuinely paired conjugate class
have closed representatives in the native full-condition model. -/
theorem exists_genuine_class_and_pairing
    (z : (familyCx M).X 1) (hz : (familyCx M).d 1 2 rfl z = 0)
    (tr : (coneCx (genuinePair M β hβ hβc Δc I).resE).X 3 →ₗ[
      MonoidAlgebra OO (SignGroup b)] MonoidAlgebra OO (SignGroup b))
    (htr : ∀ c, tr ((coneCx (genuinePair M β hβ hβc Δc I).resE).d 2 3 rfl c) = 0)
    (zc : (selCx (galoisSelData K S' (MonoidAlgebra OO (SignGroup b)) A Δc)).X 1)
    (hzc : (selCx (galoisSelData K S' (MonoidAlgebra OO (SignGroup b)) A Δc)).d 1 2 rfl zc = 0) :
    ∃ zm : (M.C.map (φO b)).D1 ⊕ (M.C.map (φO b)).N → MonoidAlgebra OO (SignGroup b),
      (M.C.map (φO b)).toFour.d1 *ᵥ zm = 0 ∧
      pairedRow M (genuinePair M β hβ hβc Δc I) tr zc ᵥ* (M.C.map (φO b)).toFour.d1 = 0 ∧
      ∃ a : (familyCx M).X 0,
        modelMap1 M zm - z = (familyCx M).d 0 1 rfl a :=
  exists_same_actual_class_and_pairing M z hz (genuinePair M β hβ hβc Δc I) tr htr zc hzc

end GenuinePairing

end Model

end ZInQ.Contrib.RC53Assist.CoordProvenance.ActualFull
