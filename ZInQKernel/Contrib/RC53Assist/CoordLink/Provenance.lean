import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG

/-!
# Coordinate provenance is not supplied by the correction interface

Manuscript ex:arith-coordinate, TeX 3877–3892, specifies the same actual class,
paired functional, complex, and retained determinant basis.  The bare coordinate
and correction records do not impose that specification.

The example below assigns the scalar one to both primitive and relaxed
coordinates, with an empty unused-prime set.  Its correction identity and
support-triangle record hold.  At any nonzero-denominator address of any given
family identification, the zero cycle instead has original coordinate zero,
so neither original-coordinate link can hold for that choice of cycle.

This is a conditional obstruction for a given identification and address, not
an assertion that a genuine family identification has been constructed.  It
does not assert an error in the manuscript or use emptiness of an interface.
No additional printed proposition is used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordLink

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Wiring (UTildeRep OrigCoordLink)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

/-- Interface coordinates equal to one, without a claim about arithmetic provenance. -/
def oneCoordinateData (ℓ : ℕ) : RCData ℓ :=
  { ddZero ℓ with uPrim := fun _ _ => 1, uTilde := fun _ _ => 1 }

/-- The constant-one coordinate has the integral representation with exponent zero. -/
theorem oneCoordinate_rep (ℓ : ℕ) (F : Family) :
    UTildeRep (oneCoordinateData ℓ) F (fun _ => 0) (fun _ => 1) := by
  intro x j
  by_cases hj : j = 0 <;> simp [oneCoordinateData, hj]

/-- Correction data hold for the constant-one coordinate and correction one. -/
theorem oneCoordinate_corrected (ℓ : ℕ) (F : Family) :
    CorrectedIsEta (oneCoordinateData ℓ) F 1 (fun _ => 1) := by
  intro e g hrep x
  rw [uK_rep_indep hrep (oneCoordinate_rep ℓ F) x]
  simp [Determinant.uK]

/-- The existing support-triangle record also permits the unrelated constant-one
coordinates: there are no unused primes and all step conditions are vacuous. -/
def oneCoordinate_triangles (ℓ : ℕ) (F : Family) (x : Addr F.b) :
    CommonCoordinateTrianglesN (oneCoordinateData ℓ) F x where
  R := PowerSeries ℚ_[2]
  chi := RingHom.id _
  Q := ∅
  v _ := 0
  g _ := 1
  l _ := 1
  e _ := 1
  ei _ := 1
  hsign := by simp
  hratio := by simp
  hinv := by simp
  urel := 1
  U := ∅
  hU := by simp
  hutilde := by simp [oneCoordinateData, Central.eta]
  qn _ := 1
  hodd := by simp
  F _ := 1
  a _ := 0
  z _ := 1
  zi _ := 1
  ha := by simp
  hd := by simp
  hl := by simp
  he := by simp
  u _ := 1
  hrel := rfl
  hprim := rfl
  eps _ := 1
  hstep := by simp

section Original

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- The original coordinate of a zero cycle is zero for every functional. -/
theorem kmOrig_zero_cycle (M : Identification2G K S S' hS b dK hK cE tK)
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) : kmOrig M 0 lam (mulVec_zero _) hlam x = 0 := by
  have hz : evK (sgnChar x) ∘
      (0 : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b)) = 0 := by
    funext i
    simp
  exact (kmCoord_congr rfl hz rfl _ _ (mulVec_zero _) (hlamev hlam x) _).trans
    (kmCoord_zero_class _ _ _ _ _)

/-- An arbitrary nonzero relaxed scalar cannot be identified with the zero-cycle
coordinate, independently of any correction-unit issue. -/
theorem zero_cycle_not_relIsKMG (M : Identification2G K S S' hS b dK hK cE tK)
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0)
    (x : Addr b) (hΔ : evK (sgnChar x) M.toIdentification.B.Δ ≠ 0) :
    ¬ ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M (fun _ => 1) 0 lam (mulVec_zero _) hlam := by
  intro h
  have hx := h x hΔ
  rw [kmOrig_zero_cycle] at hx
  exact one_ne_zero hx

/-- The corrected coordinate one cannot be the correction of the zero-cycle
coordinate, for any correction in the completed coefficient group algebra. -/
theorem zero_cycle_not_origCoordLink (ℓ : ℕ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (x : Addr F.b)
    (hΔ : evK (sgnChar x) M.toIdentification.B.Δ ≠ 0) :
    ¬ OrigCoordLink (oneCoordinateData ℓ) F M 0 lam (mulVec_zero _) hlam η := by
  intro h
  have hx := h (fun _ => 0) (fun _ => 1) (oneCoordinate_rep ℓ F) x hΔ
  change uK 0 (1 : Lam) = evK (sgnChar x) η * kmOrig M 0 lam (mulVec_zero _) hlam x at hx
  rw [kmOrig_zero_cycle, mul_zero] at hx
  have h1 : uK (O := OO) 0 (1 : Lam) = 1 := by simp [Determinant.uK]
  rw [h1] at hx
  exact one_ne_zero hx

/-- The correction identity and support-triangle interface do not identify an
independently supplied cycle.  All components of this obstruction are explicit,
conditional only on the given identification and nonzero-denominator address. -/
theorem correction_interface_provenance_obstruction (ℓ : ℕ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (x : Addr F.b) (hΔ : evK (sgnChar x) M.toIdentification.B.Δ ≠ 0) :
    CorrectedIsEta (oneCoordinateData ℓ) F 1 (fun _ => 1) ∧
      Nonempty (CommonCoordinateTrianglesN (oneCoordinateData ℓ) F x) ∧
      (¬ ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M (fun _ => 1) 0 lam (mulVec_zero _) hlam) ∧
      ¬ OrigCoordLink (oneCoordinateData ℓ) F M 0 lam (mulVec_zero _) hlam 1 :=
  ⟨oneCoordinate_corrected ℓ F, ⟨oneCoordinate_triangles ℓ F x⟩,
    zero_cycle_not_relIsKMG M lam hlam x hΔ,
    zero_cycle_not_origCoordLink ℓ F M lam hlam 1 x hΔ⟩

end Original

set_option pp.universes false

end ZInQ.Contrib.RC53Assist.CoordLink
