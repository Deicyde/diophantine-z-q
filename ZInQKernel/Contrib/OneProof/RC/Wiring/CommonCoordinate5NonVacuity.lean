import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5

/-!
# Theorem 5.3, Lane RC32: non-vacuity of the common-coordinate leaf over the text's objects

`CommonCoordinateTrianglesL` (`CommonCoordinate5.lean`) is inhabited at families with graph primes
and unused primes, with the genuine local objects: the curve's `a_q`, the scalar Frobenius value
`z = x(ε(F̃r_q))(1 + t)`, `e_q(x)`, `l_q(x)` and the evaluated correction `η_x` (which may have a
pole at `t = 0`). The support triangles are realized by explicit models over `F = Frac Λ`, with
batch 3's retention example for the functionals.

* `selmerFunctionals_anyF`: batch 3's retention example over `F` at any point factor `e`;
* `naturalStepF_of`: a `NaturalStep` over `F` for **any** Frobenius block of nonzero determinant
  `δ` and any `Λ`-unit `c`, between coordinates `u`, `u'` with `δ u' = c e² u`; its step unit is
  `q⁻⁴ c` (the relaxed model `[[0, 0], [0, B]]`, carried to the triangular model by
  `diag(c, 1)`; the coordinate is computed through `diag(0, 1, 1, 1, 1)`);
* `quotFac_ne_zero`: `l_q(x) ≠ 0` (so `δ_q = q⁴ l_q ≠ 0`);
* `trianglesL_of_eq`: a `CommonCoordinateTrianglesL` at every address of every family with odd
  prime graph primes, as soon as the primitive coordinate is the `t`-expansion of an element of `F`,
  `ũ_x = ε u_{prim,x}` with `ε ∈ Λ^×`, and `ε = 1` where no graph prime is unused;
* non-vacuity with an unused graph prime: `famFive` (one address bit, the graph prime `5`, `λ_5(x) = x₀`), the address `0` (where
  `5` is unused), and the data `constData ℓ` (`u_prim = ũ = 1`): `nonempty_trianglesL_famFive`; and
  `commonCoordinateInputsL_constData : CommonCoordinateInputsL (constData ℓ)`.

Everything here is PROVED; nothing is used by the deduction.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix CategoryTheory ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ## Batch 3's retention example over `F` -/

/-- **Batch 3's retention example over `F = Frac Λ` at an arbitrary point factor** (PROVED): the
place-by-place retention `examplePlaceRetention`, the trace `fst`, the strict class `(e, 0, 0)`, the
orthogonal class `(1, 0, 0)` and the cocycle `(1, 1, 0)` give the functionals `(e, 0, 0, 0, 0)`
and `(1)`. -/
theorem selmerFunctionals_anyF (e : FracLam) :
    SelmerFunctionals (κ := Fin 2 ⊕ Fin 2) (Sum.elim (fun _ => e) (fun _ => 0))
      (fun _ : Fin 1 => (1 : FracLam)) e := by
  refine ⟨CommRingCat.of FracLam, relSel FracLam, constSel FracLam, constCx FracLam,
    constCx FracLam, constId FracLam, constId FracLam, examplePlaceRetention FracLam,
    LinearMap.fst FracLam ((constCx FracLam).X 3) ((constCx FracLam).X (3 - 1)), fun _ => rfl,
    (show selT _ 1 from (e, (0 : FracLam), (0 : FracLam))),
    (show selT _ 1 from ((1 : FracLam), (0 : FracLam), (0 : FracLam))), e,
    (show selT _ 0 from ((0 : FracLam), (0 : FracLam), (0 : FracLam))), ?_,
    fun _ => (show selT _ 2 from ((1 : FracLam), (1 : FracLam), (0 : FracLam))), ?_,
    Sum.elim (fun _ => (changeMap (relSel FracLam) (constId FracLam)).f 2 2 rfl
      (show selT _ 2 from ((1 : FracLam), (1 : FracLam), (0 : FracLam)))) (fun _ => 0),
    fun _ => rfl, RingHom.id FracLam, ?_, ?_, ?_⟩
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change e = e * 1 + 0
      ring
    · change (0 : FracLam) = e * 0 + 0
      ring
    · change (0 : FracLam) = e * 0 + (0 - 0 - 0)
      ring
  · intro i
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    · rfl
    · change (1 : FracLam) - 1 - 0 = 0
      ring
  · rfl
  · rintro (j | j)
    · change e = e * 1
      ring
    · change (0 : FracLam) = e * 0
      ring
  · intro i
    change (1 : FracLam) = 1 * 1
    ring

/-! ## A support-triangle model for any Frobenius block -/

/-- `diag(0, 1, 1, 1, 1)`. -/
def diagF : Fin 1 ⊕ (Fin 2 ⊕ Fin 2) → FracLam := Sum.elim (fun _ => 0) (fun _ => 1)

theorem diagF_eq : Matrix.diagonal diagF =
    fromBlocks (0 : Matrix (Fin 1) (Fin 1) FracLam) 0 0 1 := by
  rw [← diagonal_zero, ← diagonal_one, fromBlocks_diagonal]
  rfl

theorem LamUnitF.ne_zero {c : FracLam} (hc : LamUnitF c) : c ≠ 0 := by
  obtain ⟨w, rfl⟩ := hc
  exact (map_ne_zero_iff _ (IsFractionRing.injective Lambda FracLam)).mpr w.ne_zero

/-- **A support-triangle model** (PROVED): for a Frobenius block `B = twoPlaceBlock Fr q z z⁻¹`
with `δ = det B ≠ 0`, a `Λ`-unit `c` and coordinates with `δ u' = c e² u` (`e` the point factor),
the relaxation step is a `NaturalStep` with step unit `q⁻⁴ c`. -/
theorem naturalStepF_of {Fr : Matrix (Fin 2) (Fin 2) FracLam} {q qi a z zi c u u' : FracLam}
    (hc : LamUnitF c) (hB : (twoPlaceBlock Fr q z zi).det ≠ 0)
    (hu' : (twoPlaceBlock Fr q z zi).det * u' = c * pointFactor a z zi ^ 2 * u) :
    NaturalStep Fr q qi a z zi u u' (qi ^ 4 * c) LamUnitF LamUnitF := by
  set B := twoPlaceBlock Fr q z zi with hBdef
  set e := pointFactor a z zi with hedef
  have hcne : c ≠ 0 := hc.ne_zero
  set QR : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) FracLam :=
    fromBlocks (c • (1 : Matrix (Fin 1) (Fin 1) FracLam)) 0 0 1 with hQR
  have hdetQ : QR.det = c := by
    rw [hQR, det_fromBlocks_zero₂₁, det_smul, det_one, det_one]
    simp
  set zR : Fin 1 ⊕ (Fin 2 ⊕ Fin 2) → FracLam := Sum.elim (fun _ => c * e * u) (fun _ => 0)
    with hzR
  set zR' : Fin 1 ⊕ (Fin 2 ⊕ Fin 2) → FracLam := Sum.elim (fun _ => e * u) (fun _ => 0)
    with hzR'
  set wR : Fin 1 ⊕ (Fin 2 ⊕ Fin 2) → FracLam := Sum.elim (fun _ => e) (fun _ => 0) with hwR
  have hmul : QR *ᵥ zR' = zR := by
    funext i
    rcases i with i | i
    · fin_cases i
      simp [hQR, hzR, hzR', Matrix.mulVec, dotProduct, mul_assoc]
    · simp [hQR, hzR, hzR', Matrix.mulVec, dotProduct]
  have hQunit : IsUnit QR.det := by rw [hdetQ]; exact isUnit_iff_ne_zero.mpr hcne
  have hinv : QR⁻¹ *ᵥ zR = zR' := by
    rw [← hmul, mulVec_mulVec, nonsing_inv_mul _ hQunit, one_mulVec]
  set Y : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) FracLam :=
    fromBlocks (1 : Matrix (Fin 1) (Fin 1) FracLam) 0 0 B with hY
  have hdetY : Y.det = B.det := by rw [hY, det_fromBlocks_zero₂₁, det_one, one_mul]
  have hYunit : IsUnit Y.det := by rw [hdetY]; exact isUnit_iff_ne_zero.mpr hB
  set DR : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) FracLam :=
    fromBlocks (0 : Matrix (Fin 1) (Fin 1) FracLam) 0 0 B with hDR
  have hDRY : DR = Matrix.diagonal diagF * Y := by
    rw [diagF_eq, hY, hDR, fromBlocks_multiply]
    simp
  have hYz : Y *ᵥ zR = zR := by
    funext i
    rcases i with i | i
    · fin_cases i
      simp [hY, hzR, Matrix.mulVec, dotProduct]
    · simp [hY, hzR, Matrix.mulVec, dotProduct]
  refine ⟨1, 0, 1, 1, DR, 1, QR, 0, fun _ => u, fun _ => 1, zR, wR,
    by simp, by simp, by simp, hQunit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the triangular model
    rw [Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hDR, hQR, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rfl
  · -- the norm identity on the old part
    intro i
    rw [hinv, inv_one, one_mulVec]
    rfl
  · -- the functionals are paired functionals of retained Selmer data
    rw [inv_one, inv_one, vecMul_one, vecMul_one]
    exact selmerFunctionals_anyF e
  · -- the relaxed coordinate, through `diag(0, 1, 1, 1, 1)`
    have hYi : IsUnit (Y⁻¹).det := by
      rw [det_nonsing_inv, Ring.inverse_eq_inv', hdetY]
      exact isUnit_iff_ne_zero.mpr (inv_ne_zero hB)
    refine (isCoordOn_baseChange DR 1 Y⁻¹ zR wR u' (by simp) hYi).mpr ?_
    have e1 : 1 * DR * Y⁻¹ = Matrix.diagonal diagF := by
      rw [Matrix.one_mul, hDRY, Matrix.mul_assoc, mul_nonsing_inv _ hYunit, Matrix.mul_one]
    have e2 : Y⁻¹⁻¹ *ᵥ zR = zR := by rw [nonsing_inv_nonsing_inv _ hYunit, hYz]
    have e3 : Ring.inverse ((1 : Matrix (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 2 ⊕ Fin 2))
        FracLam).det * (Y⁻¹).det) * u' = B.det * u' := by
      rw [det_one, one_mul, det_nonsing_inv, Ring.inverse_eq_inv', inv_inv, hdetY]
    rw [e1, e2, inv_one, vecMul_one, e3, hu']
    unfold IsCoordOn
    rw [adjugate_diagonal]
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · fin_cases x; fin_cases y
      simp only [vecMulVec_apply, hzR, hwR, Sum.elim_inl, Matrix.smul_apply, diagonal_apply_eq,
        smul_eq_mul]
      rw [Finset.prod_eq_one]
      · ring
      · intro j hj
        rcases j with j | j
        · fin_cases j; exact absurd rfl (Finset.ne_of_mem_erase hj)
        · rfl
    · simp [vecMulVec_apply, diagonal_apply_ne, hzR, hwR]
    · simp [vecMulVec_apply, diagonal_apply_ne, hzR, hwR]
    · simp only [vecMulVec_apply, hzR, hwR, Sum.elim_inr, mul_zero, Matrix.smul_apply,
        smul_eq_mul]
      by_cases hxy : x = y
      · subst hxy
        rw [diagonal_apply_eq, Finset.prod_eq_zero (i := Sum.inl 0)]
        · simp
        · simp
        · rfl
      · rw [diagonal_apply_ne _ (fun h => hxy (Sum.inr_injective h)), mul_zero]
  · -- the primitive coordinate of the model `(0)`
    unfold IsClassFunctionalCoord
    ext i j
    fin_cases i; fin_cases j
    simp [vecMulVec_apply, adjugate_fin_one]
  · rw [Matrix.one_mul, Matrix.mul_one, adjugate_fin_one]
    exact one_ne_zero
  · rw [det_one, one_mul, hdetQ]; exact hc
  · simpa using lamUnitF_one
  · rw [hdetQ]; simp

/-! ## `l_q(x) ≠ 0` -/

/-- A unit `w` of `ℤ₂` (here `q⁻¹`) as a constant series is not zero (PROVED). -/
theorem qInv_ne_zero {q : ℕ} (hq : Odd q) : qInv q ≠ 0 := by
  intro h
  have hu := isUnit_natCast_zTwo hq
  have := Ring.mul_inverse_cancel _ hu
  rw [← qInv, h, mul_zero] at this
  exact zero_ne_one this

theorem natCast_mul_qInv {q : ℕ} (hq : Odd q) : (q : ℤ_[2]) * qInv q = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_natCast_zTwo hq)

/-- **`l_q(x) ≠ 0` in `Λ`** (PROVED): both factors `1 − q⁻¹ z a_q + q⁻¹ z²` and
`1 − q⁻¹ z⁻¹ a_q + q⁻¹ z⁻²` are nonzero (their `t²` coefficients after clearing `(1 + t)` are
`q⁻¹` and `1`). -/
theorem quotFac_ne_zero (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) {q : ℕ} (hq : Odd q) :
    quotFac ℓ Fam x q ≠ 0 := by
  set σ : ℤ := (frobSign Fam x q : ℤ) with hσdef
  set w : Lambda := ((onePlusT⁻¹ : Lambdaˣ) : Lambda) with hw
  have hσσ : (σ : Lambda) * (σ : Lambda) = 1 := by
    rw [hσdef, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hzw : (1 + PowerSeries.X : Lambda) * w = 1 := by rw [hw, ← onePlusT_val, Units.mul_inv]
  have hz : ((zAt Fam x q : Lambdaˣ) : Lambda) = (σ : Lambda) * (1 + PowerSeries.X) := by
    simp [zAt, hσdef, frobSign]
  have hzi : ((zAt Fam x q)⁻¹ : Lambdaˣ) = (σ : Lambda) * w := by
    rw [zAt, mul_inv, Units.val_mul, ← map_inv, mul_comm]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, eq_intCast,
      Int.units_inv_eq_self, hσdef, frobSign, hw]
    ring
  have hqq : (q : Lambda) * PowerSeries.C (qInv q) = 1 := by
    rw [← map_natCast PowerSeries.C, ← map_mul, natCast_mul_qInv hq, map_one]
  set qi : Lambda := PowerSeries.C (qInv q) with hqi
  set a : Lambda := (apE ℓ q : Lambda) with ha
  unfold quotFac quotPoly
  rw [hz, hzi]
  refine mul_ne_zero ?_ ?_
  · -- `1 − q⁻¹σ a (1 + t) + q⁻¹ (1 + t)²`, `t²`-coefficient `q⁻¹`
    intro h0
    have key : 1 - qi * ((σ : Lambda) * (1 + PowerSeries.X)) * a +
        (qi * ((σ : Lambda) * (1 + PowerSeries.X))) ^ 2 * (q : Lambda) =
        PowerSeries.C (1 - qInv q * (σ : ℤ_[2]) * (apE ℓ q : ℤ_[2]) + qInv q) +
          PowerSeries.C (2 * qInv q - qInv q * (σ : ℤ_[2]) * (apE ℓ q : ℤ_[2])) * PowerSeries.X +
            PowerSeries.C (qInv q) * PowerSeries.X ^ 2 := by
      have : qi * qi * (q : Lambda) = qi := by
        rw [mul_assoc, mul_comm qi (q : Lambda), hqq, mul_one]
      simp only [map_sub, map_add, map_mul, map_one, map_intCast, map_ofNat, ← hqi, ← ha]
      linear_combination ((σ : Lambda) * (σ : Lambda) * (1 + PowerSeries.X) ^ 2) * this +
        (qi * (1 + PowerSeries.X) ^ 2) * hσσ
    rw [key] at h0
    have h2 := congrArg (PowerSeries.coeff 2) h0
    rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, map_zero] at h2
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow] at h2
    exact qInv_ne_zero hq h2
  · -- `(1 + t)² (1 − q⁻¹σ a (1 + t)⁻¹ + q⁻¹ (1 + t)⁻²) = (1 + t)² − q⁻¹σ a (1 + t) + q⁻¹`
    intro h0
    have key : (1 + PowerSeries.X) ^ 2 * (1 - qi * ((σ : Lambda) * w) * a +
        (qi * ((σ : Lambda) * w)) ^ 2 * (q : Lambda)) =
        PowerSeries.C (1 - qInv q * (σ : ℤ_[2]) * (apE ℓ q : ℤ_[2]) + qInv q) +
          PowerSeries.C (2 - qInv q * (σ : ℤ_[2]) * (apE ℓ q : ℤ_[2])) * PowerSeries.X +
            PowerSeries.X ^ 2 := by
      have : qi * qi * (q : Lambda) = qi := by
        rw [mul_assoc, mul_comm qi (q : Lambda), hqq, mul_one]
      simp only [map_sub, map_add, map_mul, map_one, map_intCast, map_ofNat, ← hqi, ← ha]
      linear_combination (-(qi * (σ : Lambda) * a) * (1 + PowerSeries.X)) * hzw +
        ((σ : Lambda) * (σ : Lambda) * ((1 + PowerSeries.X) * w) ^ 2) * this +
        (qi * ((1 + PowerSeries.X) * w) ^ 2) * hσσ +
        (qi * ((1 + PowerSeries.X) * w + 1)) * hzw
    have h1 : (1 + PowerSeries.X : Lambda) ^ 2 *
        (1 - qi * ((σ : Lambda) * w) * a + (qi * ((σ : Lambda) * w)) ^ 2 * (q : Lambda)) = 0 := by
      rw [h0, mul_zero]
    rw [key] at h1
    have h2 := congrArg (PowerSeries.coeff 2) h1
    rw [map_add, map_add, PowerSeries.coeff_C_mul, map_zero] at h2
    simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow] at h2

theorem lF_ne_zero (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) {q : ℕ} (hq : Odd q) :
    lF ℓ Fam x q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective Lambda FracLam)).mpr (quotFac_ne_zero ℓ Fam x hq)

/-! ## The leaf from (4.7) on data with coordinates in `F` -/

/-- `p` is a `Λ`-unit for odd `p` (PROVED). -/
theorem lamUnitF_natCast {p : ℕ} (hp : Odd p) : LamUnitF (p : FracLam) := by
  obtain ⟨w, hw⟩ := isUnit_natCast_zTwo hp
  refine ⟨Units.map (PowerSeries.C : ℤ_[2] →+* Lambda).toMonoidHom w, ?_⟩
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hw, map_natCast]

/-- The coordinates relaxed at `T` in the construction below:
`(∏_{r ∈ T} e_r(x)²/l_r(x)) · d_T · u_prim`, with `d_T = E` at `T = U_x ≠ ∅` and `1` otherwise. -/
def relaxedCoord (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (E uprim : FracLam) (T : Finset ℕ) :
    FracLam :=
  (∏ r ∈ T, eF ℓ Fam x r ^ 2 / lF ℓ Fam x r) *
    (if T = unusedAt Fam x ∧ (unusedAt Fam x).Nonempty then E else 1) * uprim

/-- The step units of the construction: `q⁻⁴ (q⁴ d)`, `d = E` on the steps into `U_x`. -/
def stepUnit (Fam : Family) (x : Addr Fam.b) (E : FracLam) (T : Finset ℕ) (p : ℕ) : FracLam :=
  (p : FracLam)⁻¹ ^ 4 * ((p : FracLam) ^ 4 * (if insert p T = unusedAt Fam x then E else 1))

/-- **The leaf at one address from (4.7) on data with coordinates in `F`** (PROVED): if the graph
primes are odd, the primitive coordinate is the `t`-expansion of some `u_prim ∈ F`,
`ũ_x = ε u_{prim,x}` with `ε ∈ Λ^×`, and `ε = 1` when no graph prime is unused, then
`CommonCoordinateTrianglesL D Fam x` is inhabited: the Frobenius matrices are companion matrices,
the relaxed coordinates are `relaxedCoord`, and each step is `naturalStepF_of`. -/
def trianglesL_of_eq {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b)
    (hodd : ∀ q ∈ Fam.Q, Odd q) (uprim : FracLam) (hprim : IsTExpansion uprim (D.uPrim Fam x))
    (e : Lambdaˣ) (htilde : D.uTilde Fam x = lamIncl (e : Lambda) * D.uPrim Fam x)
    (hone : unusedAt Fam x = ∅ → D.uTilde Fam x = D.uPrim Fam x) :
    CommonCoordinateTrianglesL D Fam x where
  Fr q := companion (apE ℓ q : ℤ_[2]) (q : ℤ_[2])
  hFtr q _ := companion_trace _ _
  hFdet q _ := companion_det _ _
  u := relaxedCoord ℓ Fam x (lamToF (e : Lambda)) uprim
  hprim := by
    have h : relaxedCoord ℓ Fam x (lamToF (e : Lambda)) uprim ∅ = uprim := by
      rw [relaxedCoord, Finset.prod_empty, one_mul]
      have : ¬ (∅ = unusedAt Fam x ∧ (unusedAt Fam x).Nonempty) := by
        rintro ⟨h1, h2⟩; rw [← h1] at h2; exact Finset.not_nonempty_empty h2
      rw [ite_eq_right this, one_mul]
    rw [h]; exact hprim
  eps := stepUnit Fam x (lamToF (e : Lambda))
  hstep T hT p hp hpT := by
    have hpQ : p ∈ Fam.Q := (mem_unusedAt.mp hp).1
    have hpo := hodd p hpQ
    have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpo.pos.ne'
    obtain ⟨ha, hd⟩ := trace_det_map_zTwoToF (companion_trace (apE ℓ p : ℤ_[2]) (p : ℤ_[2]))
      (companion_det (apE ℓ p : ℤ_[2]) (p : ℤ_[2]))
    have hq : (p : FracLam) * (p : FracLam)⁻¹ = 1 := mul_inv_cancel₀ hp0
    have hdet : (twoPlaceBlock ((companion (apE ℓ p : ℤ_[2]) (p : ℤ_[2])).map zTwoToF)
        (p : FracLam) (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).det =
        (p : FracLam) ^ 4 * lF ℓ Fam x p := by
      rw [det_twoPlaceBlock, quotientDet_eq _ _ hq ha hd, quotientFactor_eq_quotPoly _ _ _ ha hd,
        lF_eq_quotPoly hpo]
    have hl := lF_ne_zero ℓ Fam x hpo
    have hdu : (if insert p T = unusedAt Fam x then lamToF (e : Lambda) else 1) =
        (if insert p T = unusedAt Fam x ∧ (unusedAt Fam x).Nonempty
          then lamToF (e : Lambda) else 1) := by
      by_cases h : insert p T = unusedAt Fam x
      · rw [ite_eq_left h, ite_eq_left ⟨h, ⟨p, hp⟩⟩]
      · rw [ite_eq_right h, ite_eq_right fun h' => h h'.1]
    have hTU : ¬ (T = unusedAt Fam x ∧ (unusedAt Fam x).Nonempty) := by
      rintro ⟨h1, -⟩; rw [← h1] at hp; exact hpT hp
    refine naturalStepF_of ?_ ?_ ?_
    · exact (((lamUnitF_natCast hpo).pow 4).mul (by
        by_cases h : insert p T = unusedAt Fam x
        · rw [ite_eq_left h]; exact ⟨e, rfl⟩
        · rw [ite_eq_right h]; exact lamUnitF_one))
    · rw [hdet]; exact mul_ne_zero (pow_ne_zero 4 hp0) hl
    · rw [hdet, ← eF_eq_pointFactor, relaxedCoord, relaxedCoord, Finset.prod_insert hpT,
        ite_eq_right hTU, ← hdu]
      field_simp
  htilde := by
    have hprod : etaF ℓ Fam x * (∏ r ∈ unusedAt Fam x, eF ℓ Fam x r ^ 2 / lF ℓ Fam x r) = 1 := by
      rw [etaF_eq, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun r hr => ?_
      have hro := hodd r (mem_unusedAt.mp hr).1
      have he := eF_ne_zero ℓ Fam x r
      have hl := lF_ne_zero ℓ Fam x hro
      field_simp [he, hl]
    have hu : etaF ℓ Fam x * relaxedCoord ℓ Fam x (lamToF (e : Lambda)) uprim (unusedAt Fam x) =
        (if (unusedAt Fam x).Nonempty then lamToF (e : Lambda) else 1) * uprim := by
      rw [relaxedCoord, ← mul_assoc, ← mul_assoc, hprod, one_mul]
      congr 1
      by_cases h : (unusedAt Fam x).Nonempty
      · rw [ite_eq_left ⟨rfl, h⟩, ite_eq_left h]
      · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]
    change IsTExpansion (etaF ℓ Fam x *
      relaxedCoord ℓ Fam x (lamToF (e : Lambda)) uprim (unusedAt Fam x)) (D.uTilde Fam x)
    rw [hu]
    by_cases h : (unusedAt Fam x).Nonempty
    · rw [ite_eq_left h, htilde]
      exact (isTExpansion_algebraMap (e : Lambda)).mul hprim
    · rw [ite_eq_right h, one_mul, hone (Finset.not_nonempty_iff_eq_empty.mp h)]
      exact hprim

theorem nonempty_trianglesL_of_eq {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b)
    (hodd : ∀ q ∈ Fam.Q, Odd q) (uprim : FracLam) (hprim : IsTExpansion uprim (D.uPrim Fam x))
    (e : Lambdaˣ) (htilde : D.uTilde Fam x = lamIncl (e : Lambda) * D.uPrim Fam x)
    (hone : unusedAt Fam x = ∅ → D.uTilde Fam x = D.uPrim Fam x) :
    Nonempty (CommonCoordinateTrianglesL D Fam x) :=
  ⟨trianglesL_of_eq D Fam x hodd uprim hprim e htilde hone⟩

/-! ## Non-vacuity with a graph prime that is unused -/

/-- `1 ∈ F` has `t`-expansion `1` (PROVED). -/
theorem isTExpansion_one : IsTExpansion (1 : FracLam) 1 := by
  have h := isTExpansion_algebraMap (1 : Lambda)
  rwa [map_one, map_one] at h

/-- Data with `u_{prim,x} = ũ_x = 1` at every family and address (the other fields are
irrelevant to (4.7)). -/
def constData (ℓ : ℕ) : RCData ℓ where
  S := ∅
  prepared := fun _ => True
  Lstar := fun _ => 0
  jgen := fun _ => 0
  jrc := fun _ _ => 0
  hstar := 0
  stages := pure 0
  Mθ := fun _ => 0
  aθ := fun _ _ => 0
  admissible := fun _ _ => True
  δo := 0
  kfin := 1
  uPrim := fun _ _ => 1
  uTilde := fun _ _ => 1

/-- The family with one address bit and the single graph prime `5`, `λ_5(x) = x₀`. -/
def famFive : Family := ⟨1, {5}, fun _ => LinearMap.proj 0⟩

/-- At the address `0` the graph prime `5` is unused (PROVED). -/
theorem unusedAt_famFive : unusedAt famFive 0 = {5} := unusedAt_zero famFive

/-- **Non-vacuity: the leaf is inhabited with an unused graph prime** (PROVED): at the address `0` of
`famFive`, for every `ℓ`, with the genuine `a_5` of `E_ℓ`, `z = 1 + t`, `e_5(0)`, `l_5(0)` and
`η_0 = l_5/e_5²` (`etaF_eq`), and one relaxation step at `5` that is a `NaturalStep`. -/
theorem nonempty_trianglesL_famFive (ℓ : ℕ) :
    Nonempty (CommonCoordinateTrianglesL (constData ℓ) famFive 0) :=
  nonempty_trianglesL_of_eq _ _ _ (fun q hq => by
      rw [show famFive.Q = {5} from rfl, Finset.mem_singleton] at hq
      subst hq; decide)
    1 isTExpansion_one 1 (by simp [constData]) (fun _ => rfl)

/-- **The leaf `CommonCoordinateInputsL` holds for `constData ℓ`** (PROVED), at every address of
every final family. -/
theorem commonCoordinateInputsL_constData (ℓ : ℕ) : CommonCoordinateInputsL (constData ℓ) :=
  fun _ _ F hF x => nonempty_trianglesL_of_eq _ F x (odd_of_finalFamilyAt hF) 1 isTExpansion_one 1
    (by simp [constData]) (fun _ => rfl)

/-- Data with `u_{prim,x} = 1` and `ũ_x = −1` exactly where some graph prime is unused. -/
def signData (ℓ : ℕ) : RCData ℓ :=
  { constData ℓ with
    uTilde := fun F x => if (unusedAt F x).Nonempty then -1 else 1 }

/-- **Non-vacuity with a nontrivial unit `ε_x = −1`** (PROVED): the leaf holds for `signData ℓ` at every
address of every family with odd graph primes; the step at an unused prime carries `ε = −1`. -/
theorem nonempty_trianglesL_signData (ℓ : ℕ) (F : Family) (hodd : ∀ q ∈ F.Q, Odd q)
    (x : Addr F.b) : Nonempty (CommonCoordinateTrianglesL (signData ℓ) F x) := by
  by_cases h : (unusedAt F x).Nonempty
  · refine nonempty_trianglesL_of_eq _ F x hodd 1 isTExpansion_one (-1) ?_ ?_
    · simp [signData, constData, h]
    · intro h0; rw [h0] at h; exact absurd h Finset.not_nonempty_empty
  · refine nonempty_trianglesL_of_eq _ F x hodd 1 isTExpansion_one 1 ?_ ?_
    · simp [signData, constData, h]
    · intro _; simp [signData, constData, h]

end ZInQ.Manuscript.RC.Wiring
