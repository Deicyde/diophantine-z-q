import ZInQKernel.Contrib.RC53Assist.CoordLink.Comparison

/-!
# Regularity of the stored relaxation core

The adjugate of the same stored endpoint is nonzero once its actual local
singular block is regular.  The proof uses the primitive adjugate already
present in the relaxation step and its block matrix identity.  No coordinate
identity with an independent complex, or nonzero class or functional, is
assumed.  The locators are TeX 4181–4193 and 4208–4220.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordProvenance.StoredRegularity

open Matrix
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.Central
open ZInQ.Manuscript.RC.Determinant (OO)

variable {K : Type} [CommRing K] [IsDomain K]

/-- The actual regular local block preserves a nonzero primitive adjugate. -/
theorem triangular_adjugate_ne_zero {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) κ K) (B : Matrix κ κ K)
    (hA : A.adjugate ≠ 0) (hB : B.det ≠ 0) :
    (fromBlocks A X 0 B).adjugate ≠ 0 := by
  intro hzero
  apply hA
  ext i j
  have h := congrFun (congrFun hzero (Sum.inl i)) (Sum.inl j)
  rw [adjugate_fromBlocks_inl_inl, Matrix.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left hB

/-- The same matrix in the stored original bases is regular. -/
theorem original_adjugate_ne_zero {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (D P Q : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) K)
    (A : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) κ K) (B : Matrix κ κ K)
    (hmodel : P * D * Q = fromBlocks A X 0 B) (hA : A.adjugate ≠ 0) (hB : B.det ≠ 0) :
    D.adjugate ≠ 0 := by
  intro hzero
  apply triangular_adjugate_ne_zero A X B hA hB
  rw [← hmodel, adjugate_mul_distrib, adjugate_mul_distrib, hzero, Matrix.zero_mul, Matrix.mul_zero]

/-- Extract the already stored scalar and its regular matrix from the same step. -/
theorem actualStep_regular_endpoint (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi uP uR eps : K)
    (unitR unitP : K → Prop) (h : ActualStep F q qi a z zi uP uR eps unitR unitP)
    (hB : (twoPlaceBlock F q z zi).det ≠ 0) :
    ∃ (n : ℕ) (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
      (zc wc : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K), IsCoordOn D zc wc uR ∧ D.adjugate ≠ 0 := by
  obtain ⟨n, DP, PP, QP, DR, PR, QR, X, zP, wP, zR, wR,
    _, _, _, _, hmodel, _, _, hR, _, hA, _, _, _⟩ := h
  exact ⟨n, DR, zR, wR, hR, original_adjugate_ne_zero DR PR QR (PP * DP * QP) X _ hmodel hA hB⟩

/-- A regular actual quotient factor makes the actual two-place block regular. -/
theorem twoPlaceBlock_regular (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (hq : q * qi = 1) (ha : F.trace = a) (hd : F.det = q)
    (hl : quotientFactor F qi z zi ≠ 0) : (twoPlaceBlock F q z zi).det ≠ 0 := by
  have hq0 : q ≠ 0 := left_ne_zero_of_mul (by rw [hq]; exact one_ne_zero)
  rw [det_twoPlaceBlock, quotientDet_eq z zi hq ha hd]
  exact mul_ne_zero (pow_ne_zero 4 hq0) hl

/-- The same final endpoint is regular throughout the actual support relaxation. -/
theorem existing_support_regular_endpoint (U : Finset ℕ) (hU : U.Nonempty)
    (F : ℕ → Matrix (Fin 2) (Fin 2) K) (q qi a z zi eps : ℕ → K)
    (u : Finset ℕ → K) (unitR unitP : K → Prop)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hl : ∀ p ∈ U, quotientFactor (F p) (qi p) (z p) (zi p) ≠ 0)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      ActualStep (F p) (q p) (qi p) (a p) (z p) (zi p) (u T) (u (insert p T)) (eps p) unitR unitP) :
    ∃ (n : ℕ) (D : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
      (zc wc : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K), IsCoordOn D zc wc (u U) ∧ D.adjugate ≠ 0 := by
  obtain ⟨p, hp⟩ := hU
  have hs := hstep (U.erase p) (Finset.erase_subset _ _) p hp (Finset.notMem_erase _ _)
  rw [Finset.insert_erase hp] at hs
  exact actualStep_regular_endpoint (F p) (q p) (qi p) (a p) (z p) (zi p)
    (u (U.erase p)) (u U) (eps p) unitR unitP hs
    (twoPlaceBlock_regular (F p) (q p) (qi p) (a p) (z p) (zi p) (hq p hp) (ha p hp) (hd p hp) (hl p hp))

/-- The actual completed-ring norm relation supplies regularity, without a
power-series-unit lift of the correction. -/
theorem completed_ratio_regular {R A : Type} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : Function.Injective f) (g : R →+* OO)
    (l ei : R) (v : OO) (hratio : g l * (g ei) ^ 2 = 1 + 2 * v) : f l ≠ 0 := by
  intro hzero
  have hl0 : l = 0 := hf (hzero.trans (map_zero f).symm)
  have hηUnit := ZInQ.Manuscript.RC.Determinant.isUnit_one_add_two_mul_OO v
  apply hηUnit.ne_zero
  rw [← hratio, hl0, map_zero, zero_mul]

end ZInQ.Contrib.RC53Assist.CoordProvenance.StoredRegularity
