import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Wiring
import ZInQKernel.Contrib.CloudB3RC53.MinimalComplexes.CoordinateUnit

/-!
# Common coordinate, part 5: the basis-comparison unit in `ε_q`

Lemma `ex:arith-common-coordinate`, tex L4185–4193:

> In the original integral determinant bases, the support triangle therefore gives
> `l_q u_rel = e_q² ε_q u_prim`, `ε_q ∈ Λ^×`. To see the unit assertion, retain the finite
> mapping-cone bases. Their comparison is a sign; replacing them by the retained homotopy equivalent
> free models contributes only determinants of unit disks. These are `A_i`-units. Their limits and
> inverse limits are `Λ`-units, and `q^{-4}` is one also.

`Triangular.lean` proves (4.7) in the bases of the triangular model, with `ε_q = q⁻⁴`. Here the
actual coordinates are those of the **original** models `D_R`, `D_P`, related to the triangular
model by integral changes of bases `P_R D_R Q_R = [[D_P', X], [0, D_W]]`, `P_P D_P Q_P = D_P'`
(determinants `c_R = det P_R det Q_R`, `c_P = det P_P det Q_P`, `Λ`-units: signs and determinants
of unit disks). By the base-change formula for the class-functional coordinate (the general-index
form of `MinimalComplexes`' `CoordinateBaseChangeUnit`), the coordinates change by `c⁻¹`, so

`l_q u_rel = e_q² ε_q u_prim` with `ε_q = q⁻⁴ c_R c_P⁻¹ ∈ Λ^×`.

* `isCoordOn_baseChange`: the coordinate of `(P D Q, Q⁻¹ z, w P⁻¹)` is `(det P det Q)⁻¹ u`.
* `single_prime_47_of_actual`: (4.7) in the original bases with the full unit.
* `prod_relax_of_actual_models`, `commonCoordinate_h47_of_actual_models`: RC0's field `h47` with
  `ε_q` the full unit; `lamUnit_eps`: RC0's field `hunit` for it.
* `commonCoordinateModel_of_actual_models`: a `CommonCoordinateModel` carrying the full unit.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Wiring

variable {K : Type*} [CommRing K]

/-- **Base change of the coordinate on any index type** (the general-index form of
`MinimalComplexes.CoordinateBaseChangeUnit`, tex L4363–4366): for invertible `P, Q`, `u` is the
coordinate of `(D, z, w)` iff `(det P det Q)⁻¹ u` is the coordinate of `(P D Q, Q⁻¹ z, w P⁻¹)`. -/
theorem isCoordOn_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι] (D P Q : Matrix ι ι K)
    (z w : ι → K) (u : K) (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    IsCoordOn D z w u ↔
      IsCoordOn (P * D * Q) (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹) (Ring.inverse (P.det * Q.det) * u) := by
  have hadj : (P * D * Q).adjugate = Q.adjugate * D.adjugate * P.adjugate := by
    rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc]
  have hvv : vecMulVec (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹) = Q⁻¹ * vecMulVec z w * P⁻¹ := by
    rw [← mul_vecMulVec, ← vecMulVec_mul, Matrix.mul_assoc]
  have hinv : Ring.inverse (P.det * Q.det) = Ring.inverse P.det * Ring.inverse Q.det := by
    rw [Ring.mul_inverse_rev, mul_comm]
  unfold IsCoordOn
  constructor
  · intro h
    rw [hvv, h, hadj, Matrix.inv_def Q, Matrix.inv_def P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hinv]
    congr 1
    ring
  · intro h
    have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
    have hzw : vecMulVec z w = Q * vecMulVec (Q⁻¹ *ᵥ z) (w ᵥ* P⁻¹) * P := by
      rw [hvv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_assoc, hPP,
        Matrix.mul_one]
    rw [hzw, h, hadj, Matrix.mul_smul, Matrix.smul_mul]
    have e : Q * (Q.adjugate * D.adjugate * P.adjugate) * P =
        (Q * Q.adjugate) * D.adjugate * (P.adjugate * P) := by
      simp only [Matrix.mul_assoc]
    rw [e, mul_adjugate, adjugate_mul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hinv]
    congr 1
    calc Ring.inverse P.det * Ring.inverse Q.det * u * (P.det * Q.det)
        = (Ring.inverse P.det * P.det) * (Ring.inverse Q.det * Q.det) * u := by ring
      _ = u := by rw [Ring.inverse_mul_cancel _ hP, Ring.inverse_mul_cancel _ hQ]; ring

/-- **(4.7) in the original integral bases** (tex L4185–4193). The actual relaxed model `DRa`
(index `Fin n ⊕ (Fin 2 ⊕ Fin 2)`) and primitive model `DPa` are carried to the triangular model by
`P_R DRa Q_R = [[D_P, X], [0, D_W]]` and `P_P DPa Q_P = D_P`; in the triangular bases the relaxed
cycle and functional restrict to `e_q` times the primitive ones. Then
`l_q u_rel = e_q² (q⁻⁴ c_R c_P⁻¹) u_prim` with `c_R = det P_R det Q_R`, `c_P = det P_P det Q_P`. -/
theorem single_prime_47_of_actual {K : Type} [CommRing K] [IsDomain K] {n : ℕ} (DPa PP QP : Matrix (Fin n) (Fin n) K)
    (DRa PR QR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
    (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (hq : q * qi = 1) (ha : F.trace = a) (hd : F.det = q)
    (hPP : IsUnit PP.det) (hQP : IsUnit QP.det) (hPR : IsUnit PR.det) (hQR : IsUnit QR.det)
    (hRmodel : PR * DRa * QR = fromBlocks (PP * DPa * QP) X 0 (twoPlaceBlock F q z zi))
    (zPa wPa : Fin n → K) (zRa wRa : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K) (uprim urel : K)
    (hz : ∀ i, (QR⁻¹ *ᵥ zRa) (Sum.inl i) = pointFactor a z zi * (QP⁻¹ *ᵥ zPa) i)
    (hw : ∀ i, (wRa ᵥ* PR⁻¹) (Sum.inl i) = pointFactor a z zi * (wPa ᵥ* PP⁻¹) i)
    (hR : IsCoordOn DRa zRa wRa urel) (hP : IsClassFunctionalCoord DPa zPa wPa uprim)
    (hadj : (PP * DPa * QP).adjugate ≠ 0) :
    quotientFactor F qi z zi * urel =
      pointFactor a z zi ^ 2 * (qi ^ 4 * (PR.det * QR.det) * Ring.inverse (PP.det * QP.det)) *
        uprim := by
  have hR' := (isCoordOn_baseChange DRa PR QR zRa wRa urel hPR hQR).1 hR
  rw [hRmodel] at hR'
  have hP' := (ZInQ.Contrib.CloudB3RC53.MinimalComplexes.coordinateBaseChangeUnit_proof K n DPa
    PP QP zPa wPa uprim hPP hQP).1 hP
  obtain ⟨h47, -⟩ := single_prime_47_of_model (PP * DPa * QP) X F q qi a z zi hq ha hd _ _ _ _ _ _
    hz hw hR' hP' hadj
  have hcR : IsUnit (PR.det * QR.det) := hPR.mul hQR
  have hcP : IsUnit (PP.det * QP.det) := hPP.mul hQP
  -- multiply by `c_R` and use `c_R c_R⁻¹ = 1`
  have e1 : urel = (PR.det * QR.det) * (Ring.inverse (PR.det * QR.det) * urel) := by
    rw [← mul_assoc, Ring.mul_inverse_cancel _ hcR, one_mul]
  rw [e1, mul_left_comm, h47]
  ring

/-- `Λ`-units are closed under `Ring.inverse` (the inverse of the image of a unit of `Λ`). -/
theorem LamUnit.ring_inverse {ε : PowerSeries ℚ_[2]} (h : LamUnit ε) : LamUnit (Ring.inverse ε) := by
  obtain ⟨e, rfl⟩ := h
  refine ⟨e⁻¹, ?_⟩
  have hu : IsUnit (PowerSeries.map PadicInt.Coe.ringHom (e : PowerSeries ℤ_[2])) :=
    e.isUnit.map _
  rw [← hu.unit_spec, Ring.inverse_unit]
  apply Units.inv_eq_of_mul_eq_one_left
  rw [IsUnit.unit_spec, ← map_mul, Units.inv_mul, map_one]

/-- The full unit `ε_q = q⁻⁴ c_R c_P⁻¹` is a `Λ`-unit when `q` is odd and `c_R`, `c_P` are
`Λ`-units (signs and determinants of unit disks, tex L4189–4193). -/
theorem lamUnit_eps (qn : ℕ) (hodd : Odd qn) {cR cP : PowerSeries ℚ_[2]} (hR : LamUnit cR)
    (hP : LamUnit cP) :
    LamUnit (PowerSeries.C ((qn : ℚ_[2])⁻¹) ^ 4 * cR * Ring.inverse cP) :=
  Wiring.LamUnit.mul (Wiring.LamUnit.mul (lamUnit_inv_odd_pow qn hodd) hR)
    (LamUnit.ring_inverse hP)

/-- The data of one relaxation step in the original bases (tex L4166–4193): actual primitive and
relaxed models `DPa`, `DRa` with coordinates `uprim`, `urel`, integral changes of bases to the
triangular model at the prime (Frobenius `F`, `q`, `qi = q⁻¹`, `z`, `zi`), the norm identity and
`λ_R ∘ i = e_q λ_P` in the triangular bases, and the step unit `ε = q⁻⁴ c_R c_P⁻¹`.

Superseded by `NaturalStep` (`CommonCoordinate/NaturalStep`), which derives the functional relation
`w_R|old = e_q w_P` assumed here; `NaturalStep.toActualStep`. -/
def ActualStep {K : Type} [CommRing K] (F : Matrix (Fin 2) (Fin 2) K) (q qi a z zi : K)
    (uprim urel ε : K) (unitR unitP : K → Prop) : Prop :=
  ∃ (n : ℕ) (DPa PP QP : Matrix (Fin n) (Fin n) K)
    (DRa PR QR : Matrix (Fin n ⊕ (Fin 2 ⊕ Fin 2)) (Fin n ⊕ (Fin 2 ⊕ Fin 2)) K)
    (X : Matrix (Fin n) (Fin 2 ⊕ Fin 2) K) (zPa wPa : Fin n → K)
    (zRa wRa : Fin n ⊕ (Fin 2 ⊕ Fin 2) → K),
    IsUnit PP.det ∧ IsUnit QP.det ∧ IsUnit PR.det ∧ IsUnit QR.det ∧
    PR * DRa * QR = fromBlocks (PP * DPa * QP) X 0 (twoPlaceBlock F q z zi) ∧
    (∀ i, (QR⁻¹ *ᵥ zRa) (Sum.inl i) = pointFactor a z zi * (QP⁻¹ *ᵥ zPa) i) ∧
    (∀ i, (wRa ᵥ* PR⁻¹) (Sum.inl i) = pointFactor a z zi * (wPa ᵥ* PP⁻¹) i) ∧
    IsCoordOn DRa zRa wRa urel ∧ IsClassFunctionalCoord DPa zPa wPa uprim ∧
    (PP * DPa * QP).adjugate ≠ 0 ∧
    unitR (PR.det * QR.det) ∧ unitP (PP.det * QP.det) ∧
    ε = qi ^ 4 * (PR.det * QR.det) * Ring.inverse (PP.det * QP.det)

theorem ActualStep.eq47 {K : Type} [CommRing K] [IsDomain K] {F : Matrix (Fin 2) (Fin 2) K}
    {q qi a z zi uprim urel ε : K} {unitR unitP : K → Prop} (hq : q * qi = 1) (ha : F.trace = a)
    (hd : F.det = q) (h : ActualStep F q qi a z zi uprim urel ε unitR unitP) :
    quotientFactor F qi z zi * urel = pointFactor a z zi ^ 2 * ε * uprim := by
  obtain ⟨n, DPa, PP, QP, DRa, PR, QR, X, zPa, wPa, zRa, wRa, hPP, hQP, hPR, hQR, hRm, hz, hw,
    hR, hP, hadj, -, -, hε⟩ := h
  rw [hε]
  exact single_prime_47_of_actual DPa PP QP DRa PR QR X F q qi a z zi hq ha hd hPP hQP hPR hQR hRm
    zPa wPa zRa wRa uprim urel hz hw hR hP hadj

/-- **Relaxing the unused primes in the original bases** (tex L4185–4193, L4222): if each step
`T → insert p T` is an `ActualStep` with step unit `eps p`, then
`(∏_U l_p) u_rel = (∏_U e_p² ε_p) u_prim` with the full units `ε_p`. -/
theorem prod_relax_of_actual_models {K : Type} [CommRing K] [IsDomain K] {ι : Type*}
    [DecidableEq ι] (U : Finset ι) (F : ι → Matrix (Fin 2) (Fin 2) K) (q qi a z zi eps : ι → K)
    (u : Finset ι → K) (unitR unitP : K → Prop)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      ActualStep (F p) (q p) (qi p) (a p) (z p) (zi p) (u T) (u (insert p T)) (eps p) unitR unitP) :
    (∏ p ∈ U, quotientFactor (F p) (qi p) (z p) (zi p)) * u U =
      (∏ p ∈ U, pointFactor (a p) (z p) (zi p) ^ 2 * eps p) * u ∅ :=
  prod_relax U (fun p => quotientFactor (F p) (qi p) (z p) (zi p))
    (fun p => pointFactor (a p) (z p) (zi p)) eps u fun T hT p hp hpT =>
      (hstep T hT p hp hpT).eq47 (hq p hp) (ha p hp) (hd p hp)

/-- **RC0's field `h47` with the full unit** (tex L4166–4193): as `commonCoordinate_h47_of_models`,
in the original integral bases, with `ε_p` the step units `q_p⁻⁴ c_R c_P⁻¹` of `ActualStep`. -/
theorem commonCoordinate_h47_of_models_full {R : Type*} [CommRing R]
    (chi : R →+* PowerSeries ℚ_[2]) (U : Finset ℕ) (l e : ℕ → R) (urel uprim : PowerSeries ℚ_[2])
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2]))
    (q qi a z zi eps : ℕ → PowerSeries ℚ_[2]) (u : Finset ℕ → PowerSeries ℚ_[2])
    (hl : ∀ p ∈ U, chi (l p) = quotientFactor (F p) (qi p) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (hrel : u U = urel) (hprim : u ∅ = uprim)
    (hq : ∀ p ∈ U, q p * qi p = 1) (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = q p)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      ActualStep (F p) (q p) (qi p) (a p) (z p) (zi p) (u T) (u (insert p T)) (eps p)
        LamUnit LamUnit) :
    (∏ q ∈ U, chi (l q)) * urel = (∏ q ∈ U, chi (e q) ^ 2 * eps q) * uprim := by
  have h := prod_relax_of_actual_models U F q qi a z zi eps u LamUnit LamUnit hq ha hd hstep
  rw [hrel, hprim] at h
  have e1 : ∏ q ∈ U, chi (l q) = ∏ p ∈ U, quotientFactor (F p) (qi p) (z p) (zi p) :=
    Finset.prod_congr rfl hl
  have e2 : ∏ q ∈ U, chi (e q) ^ 2 * eps q = ∏ p ∈ U, pointFactor (a p) (z p) (zi p) ^ 2 * eps p :=
    Finset.prod_congr rfl fun p hp => by rw [he p hp]
  rw [e1, e2]
  exact h

/-- **A `CommonCoordinateModel` with the full unit** (tex L4142–4328): as
`commonCoordinateModel_of_models`, but in the original integral bases, each relaxation step an
`ActualStep` whose basis comparisons have `Λ`-unit determinants; `ε_p = q_p⁻⁴ c_R c_P⁻¹` is then the
full unit of (4.7) and is a `Λ`-unit. -/
noncomputable def commonCoordinateModel_of_actual_models {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (x : Addr Fam.b) (R : Type) [CommRing R] (chi : R →+* PowerSeries ℚ_[2]) (Q : Finset ℕ)
    (v g l e ei : ℕ → R)
    (hsign : ∀ q ∈ Q, chi (g q) = 1 ∨ chi (g q) = -1)
    (hratio : ∀ q ∈ Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q))
    (hinv : ∀ q ∈ Q, chi (e q) * chi (ei q) = 1) (urel : PowerSeries ℚ_[2]) (U : Finset ℕ)
    (hU : ∀ q, q ∈ U ↔ (q ∈ Q ∧ chi (g q) = 1))
    (hutilde : D.uTilde Fam x = chi (Central.eta Q v g) * urel)
    (qn : ℕ → ℕ) (hodd : ∀ p ∈ U, Odd (qn p))
    (F : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])) (a z zi eps : ℕ → PowerSeries ℚ_[2])
    (ha : ∀ p ∈ U, (F p).trace = a p)
    (hd : ∀ p ∈ U, (F p).det = PowerSeries.C (qn p : ℚ_[2]))
    (hl : ∀ p ∈ U, chi (l p) =
      quotientFactor (F p) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (z p) (zi p))
    (he : ∀ p ∈ U, chi (e p) = pointFactor (a p) (z p) (zi p))
    (u : Finset ℕ → PowerSeries ℚ_[2]) (hrel : u U = urel) (hprim : u ∅ = D.uPrim Fam x)
    (hstep : ∀ T ⊆ U, ∀ p ∈ U, p ∉ T →
      ActualStep (F p) (PowerSeries.C (qn p : ℚ_[2])) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (a p)
        (z p) (zi p) (u T) (u (insert p T)) (eps p) LamUnit LamUnit) :
    CommonCoordinateModel D Fam x where
  R := R
  chi := chi
  Q := Q
  v := v
  g := g
  l := l
  e := e
  ei := ei
  eps := eps
  hsign := hsign
  hratio := hratio
  hinv := hinv
  urel := urel
  U := U
  hU := hU
  h47 := by
    have hq : ∀ p ∈ U, PowerSeries.C (qn p : ℚ_[2]) * PowerSeries.C ((qn p : ℚ_[2])⁻¹) = 1 := by
      intro p hp
      have hne : (qn p : ℚ_[2]) ≠ 0 := by exact_mod_cast (hodd p hp).pos.ne'
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    have h := prod_relax_of_actual_models U F (fun p => PowerSeries.C (qn p : ℚ_[2]))
      (fun p => PowerSeries.C ((qn p : ℚ_[2])⁻¹)) a z zi eps u LamUnit LamUnit hq ha hd hstep
    rw [hrel, hprim] at h
    have e1 : ∏ q ∈ U, chi (l q) =
        ∏ p ∈ U, quotientFactor (F p) (PowerSeries.C ((qn p : ℚ_[2])⁻¹)) (z p) (zi p) :=
      Finset.prod_congr rfl hl
    have e2 : ∏ q ∈ U, chi (e q) ^ 2 * eps q =
        ∏ p ∈ U, pointFactor (a p) (z p) (zi p) ^ 2 * eps p :=
      Finset.prod_congr rfl fun p hp => by rw [he p hp]
    rw [e1, e2]
    exact h
  hunit := fun p hp => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hcR, hcP, hε⟩ :=
      hstep ∅ (Finset.empty_subset U) p hp (Finset.notMem_empty p)
    rw [hε]
    exact lamUnit_eps (qn p) (hodd p hp) hcR hcP
  hutilde := hutilde

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
