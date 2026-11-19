import ZInQKernel.Contrib.RC53Assist.CoordLink.Transport

/-!
# The existing relaxation scalar in a common coefficient realization

The endpoint scalar of the support-triangle data already occurs in the
adjugate identity of the last relaxation step.  It must not be replaced by a
new independently defined coordinate.  The results below extract this identity
and give its common numerator and denominator under two injective coefficient
realizations.  The scalar carrier may be a Laurent field.

The locators are ex:arith-common-coordinate, TeX 4142–4240, and
ex:arith-coordinate, TeX 3877–3892.  No new printed proposition, coordinate-link
premise, or power-series-unit correction is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar

open Matrix
open ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Contrib.CloudB3RC53.CoordLink (adjugate_map_apply)

/-- The existing relaxed endpoint occurs in the last step's original-basis
adjugate identity.  No coordinate identity with an independently given
original complex is assumed. -/
theorem existing_relaxation_endpoint {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {x : Addr F.b}
    (T : CommonCoordinateTrianglesN Dd F x) (hU : T.U.Nonempty) :
    ∃ (n : ℕ)
      (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (PowerSeries ℚ_[2]))
      (z w : Fin n ⊕ (Fin 2 ⊕ Fin 2) → PowerSeries ℚ_[2]),
      IsCoordOn D z w T.urel := by
  obtain ⟨p, hp⟩ := hU
  have h := (T.hstep (T.U.erase p) (Finset.erase_subset _ _) p hp (Finset.notMem_erase _ _)).toActualStep
  rw [Finset.insert_erase hp, T.hrel] at h
  obtain ⟨n, DP, PP, QP, DR, PR, QR, X, zP, wP, zR, wR,
    _, _, _, _, _, _, _, hR, _, _, _, _, _⟩ := h
  exact ⟨n, DR, zR, wR, hR⟩

/-- The same endpoint extraction for a general scalar carrier, including a
Laurent field.  The finite support is the actual support of the supplied steps. -/
theorem existing_endpoint_on_carrier {A : Type} [CommRing A]
    (U : Finset ℕ) (hU : U.Nonempty) (F : ℕ → Matrix (Fin 2) (Fin 2) A)
    (q qi a z zi eps : ℕ → A) (u : Finset ℕ → A) (unitR unitP : A → Prop)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      ActualStep (F p) (q p) (qi p) (a p) (z p) (zi p)
        (u T) (u (insert p T)) (eps p) unitR unitP) :
    ∃ (n : ℕ) (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) A)
      (zc wc : Fin n ⊕ (Fin 2 ⊕ Fin 2) → A), IsCoordOn D zc wc (u U) := by
  obtain ⟨p, hp⟩ := hU
  have h := hstep (U.erase p) (Finset.erase_subset _ _) p hp (Finset.notMem_erase _ _)
  rw [Finset.insert_erase hp] at h
  obtain ⟨n, DP, PP, QP, DR, PR, QR, X, zP, wP, zR, wR,
    _, _, _, _, _, _, _, hR, _, _, _, _, _⟩ := h
  exact ⟨n, DR, zR, wR, hR⟩

section CommonRealization

variable {R A K : Type} [CommRing R] [CommRing A] [Field K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonzero maximal minor fixes the given existing scalar in a common
coefficient realization.  The denominator may be a nonunit of the common ring. -/
theorem existing_scalar_common_fraction (f : R →+* A) (hf : Function.Injective f)
    (g : R →+* K) (hg : Function.Injective g) (D : Matrix ι ι R) (z w : ι → R)
    (u : A) (hu : IsCoordOn (D.map f) (f ∘ z) (f ∘ w) u) (hadj : D.adjugate ≠ 0) :
    ∃ num den : R, den ≠ 0 ∧ f den * u = f num ∧
      IsCoordOn (D.map g) (g ∘ z) (g ∘ w) (g num / g den) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, D.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hadj (Matrix.ext h)
  let num := z i * w j
  let den := D.adjugate i j
  have hclear : f den * u = f num := by
    have h := congrFun (congrFun hu i) j
    simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply,
      smul_eq_mul] at h
    have hm := RingHom.map_adjugate f D
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hm
    have he := congrFun (congrFun hm i) j
    change f (D.adjugate i j) = (D.map f).adjugate i j at he
    dsimp [den, num]
    rw [map_mul, he, mul_comm]
    exact h.symm
  have hR : ∀ i j, den * z i * w j = num * D.adjugate i j := by
    intro i j
    apply hf
    have h := congrFun (congrFun hu i) j
    have hm := RingHom.map_adjugate f D
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hm
    have he := congrFun (congrFun hm i) j
    change f (D.adjugate i j) = (D.map f).adjugate i j at he
    simp only [vecMulVec_apply, Function.comp_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [map_mul]
    rw [← he] at h
    calc f den * f (z i) * f (w j) = f den * (f (z i) * f (w j)) := by ring
         _ = f den * (u * f (D.adjugate i j)) := congrArg (f den * ·) h
         _ = f num * f (D.adjugate i j) := by rw [← mul_assoc, hclear]
  have hgd : g den ≠ 0 := (map_ne_zero_iff g hg).mpr hij
  refine ⟨num, den, hij, hclear, ?_⟩
  ext i j
  have h := congrArg g (hR i j)
  simp only [map_mul] at h
  have hm := RingHom.map_adjugate g D
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hm
  have he := congrFun (congrFun hm i) j
  change g (D.adjugate i j) = (D.map g).adjugate i j at he
  change g (z i) * g (w j) = (g num / g den) * (D.map g).adjugate i j
  rw [← he, div_mul_eq_mul_div]
  apply (eq_div_iff hgd).mpr
  linear_combination h

/-- Equality of adjugate coordinates of the same realized matrix, class and
functional is forced by a nonzero maximal minor. -/
theorem existing_scalar_unique (D : Matrix ι ι K) (z w : ι → K) (u v : K)
    (hadj : D.adjugate ≠ 0) (hu : IsCoordOn D z w u) (hv : IsCoordOn D z w v) : u = v := by
  obtain ⟨i, j, hij⟩ : ∃ i j, D.adjugate i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hadj (Matrix.ext h)
  have h1 := congrFun (congrFun hu i) j
  have h2 := congrFun (congrFun hv i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 h2
  exact mul_right_cancel₀ hij (h1.symm.trans h2)

/-- The correction identity transports the already existing relaxed scalar to
the clearing field using its common representative.  No unit lift is assumed. -/
theorem existing_scalar_from_corrected_representative
    (f : R →+* A) (hf : Function.Injective f) (g : R →+* K) (hg : Function.Injective g)
    (uA : A) (uK correctedK : K) (eta num den correctedNum correctedDen : R)
    (hden : den ≠ 0) (hcorrectedDen : correctedDen ≠ 0)
    (hclear : f den * uA = f num)
    (hcorrectedA : f correctedDen * (f eta * uA) = f correctedNum)
    (hcorrectedK : g correctedDen * correctedK = g correctedNum)
    (hη : correctedK = g eta * uK) (heta : g eta ≠ 0) :
    uK = g num / g den := by
  have hR : correctedDen * eta * num = correctedNum * den := by
    apply hf
    simp only [map_mul]
    calc f correctedDen * f eta * f num = f den * (f correctedDen * (f eta * uA)) := by rw [← hclear]; ring
         _ = f correctedNum * f den := by rw [hcorrectedA]; ring
  have hgR := congrArg g hR
  simp only [map_mul] at hgR
  have hn1 : g den ≠ 0 := (map_ne_zero_iff g hg).mpr hden
  have hn2 : g correctedDen ≠ 0 := (map_ne_zero_iff g hg).mpr hcorrectedDen
  apply (eq_div_iff hn1).mpr
  apply mul_left_cancel₀ (mul_ne_zero hn2 heta)
  rw [hη] at hcorrectedK
  linear_combination (g den) * hcorrectedK - hgR

end CommonRealization

section LaurentCarrier

/-- The actual rational power-series inclusion into its Laurent field. -/
abbrev toLaurent : PowerSeries ℚ_[2] →+* LaurentSeries ℚ_[2] :=
  algebraMap (PowerSeries ℚ_[2]) (LaurentSeries ℚ_[2])

/-- The Laurent inclusion is injective, not a map out of the completed ring. -/
theorem toLaurent_injective : Function.Injective toLaurent :=
  IsFractionRing.injective (PowerSeries ℚ_[2]) (LaurentSeries ℚ_[2])

/-- The adjugate identity is compatible with an actual coefficient homomorphism. -/
theorem isCoordOn_map {R S : Type} [CommRing R] [CommRing S]
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : R →+* S)
    (D : Matrix ι ι R) (z w : ι → R) (u : R) (h : IsCoordOn D z w u) :
    IsCoordOn (D.map f) (f ∘ z) (f ∘ w) (f u) := by
  have hm := RingHom.map_adjugate f D
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hm
  ext i j
  have he := congrFun (congrFun h i) j
  have hf := congrArg f he
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at hf
  have ha := congrFun (congrFun hm i) j
  change f (D.adjugate i j) = (D.map f).adjugate i j at ha
  change f (z i) * f (w j) = f u * (D.map f).adjugate i j
  exact hf.trans (congrArg (f u * ·) ha)

/-- The existing endpoint scalar survives the actual Laurent inclusion with
its same matrix, class and functional. -/
theorem existing_relaxation_endpoint_laurent {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {x : Addr F.b}
    (T : CommonCoordinateTrianglesN Dd F x) (hU : T.U.Nonempty) :
    ∃ (n : ℕ)
      (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (PowerSeries ℚ_[2]))
      (z w : Fin n ⊕ (Fin 2 ⊕ Fin 2) → PowerSeries ℚ_[2]),
      IsCoordOn (D.map toLaurent) (toLaurent ∘ z) (toLaurent ∘ w) (toLaurent T.urel) := by
  obtain ⟨n, D, z, w, h⟩ := existing_relaxation_endpoint T hU
  exact ⟨n, D, z, w, isCoordOn_map toLaurent D z w T.urel h⟩

/-- With no unused prime, the existing relaxed scalar is the existing primitive
scalar.  No vacuous last-step model is manufactured. -/
theorem existing_scalar_no_unused {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {x : Addr F.b}
    (T : CommonCoordinateTrianglesN Dd F x) (hU : T.U = ∅) : T.urel = Dd.uPrim F x := by
  rw [← T.hrel, hU, T.hprim]

/-- Relabel the same endpoint matrix and cochains, preserving the scalar. -/
theorem isCoordOn_relabel {R : Type} [CommRing R]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (D : Matrix ι ι R) (z w : ι → R) (u : R) (h : IsCoordOn D z w u) :
    IsCoordOn (D.submatrix e e) (z ∘ e) (w ∘ e) u := by
  rw [IsCoordOn, adjugate_submatrix_equiv_self]
  ext i j
  exact congrFun (congrFun h (e i)) (e j)

/-- The stored relaxation endpoint has a positive finite core index, so it
can be passed to the homotopy-aware finite-core comparison without changing
its scalar. -/
theorem existing_relaxation_endpoint_finite {ℓ : ℕ} {Dd : RCData ℓ} {F : Family} {x : Addr F.b}
    (T : CommonCoordinateTrianglesN Dd F x) (hU : T.U.Nonempty) :
    ∃ (m : ℕ) (D : Matrix (Fin (m + 1)) (Fin (m + 1)) (PowerSeries ℚ_[2]))
      (z w : Fin (m + 1) → PowerSeries ℚ_[2]), IsCoordOn D z w T.urel := by
  obtain ⟨n, D, z, w, h⟩ := existing_relaxation_endpoint T hU
  let e : Fin (n + 3 + 1) ≃ Fin n ⊕ (Fin 2 ⊕ Fin 2) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  exact ⟨n + 3, D.submatrix e e, z ∘ e, w ∘ e,
    isCoordOn_relabel e D z w T.urel h⟩

/-- A common coefficient model gives a numerator and a nonunit denominator
for the already stored scalar in the Laurent carrier. -/
theorem existing_laurent_scalar_common_fraction {R : Type} [CommRing R] {m : ℕ}
    (f : R →+* LaurentSeries ℚ_[2]) (hf : Function.Injective f)
    (g : R →+* FractionRing ZInQ.Manuscript.RC.Determinant.OO) (hg : Function.Injective g)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (z w : Fin (m + 1) → R)
    (urel : LaurentSeries ℚ_[2]) (hurel : IsCoordOn (D.map f) (f ∘ z) (f ∘ w) urel)
    (hadj : D.adjugate ≠ 0) :
    ∃ num den : R, den ≠ 0 ∧ f den * urel = f num ∧
      IsCoordOn (D.map g) (g ∘ z) (g ∘ w) (g num / g den) :=
  existing_scalar_common_fraction f hf g hg D z w urel hurel hadj

end LaurentCarrier

end ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar
