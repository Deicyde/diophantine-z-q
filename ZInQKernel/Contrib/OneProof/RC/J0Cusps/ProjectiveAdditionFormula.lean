import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-! A second polynomial addition formula, covering the diagonal of the short
Weierstrass equation where Mathlib's secant formula vanishes. The comparison
with Mathlib's chord-and-tangent law is an on-the-spot calculation (c),
tex 1785–1787. -/

noncomputable section

open WeierstrassCurve
open scoped WeierstrassCurve.Projective

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The symmetric addition triple of bidegree `(2,2)` for
`Y² Z = X³ + a X Z² + b Z³`. It is allowed to vanish off the diagonal. -/
def symmetricAddition {R : Type*} [CommRing R] (a b : R)
    (P Q : Fin 3 → R) : Fin 3 → R :=
  let xx := P 0 * Q 0
  let yy := P 1 * Q 1
  let zz := P 2 * Q 2
  let xy := P 0 * Q 1 + P 1 * Q 0
  let xz := P 0 * Q 2 + P 2 * Q 0
  let yz := P 1 * Q 2 + P 2 * Q 1
  let r := 3 * xx + a * zz
  let w := a * xz + 3 * b * zz
  let j := 3 * b * xz + a * (xx - a * zz)
  ![xy * (yy - w) - yz * j, (yy - w) * (yy + w) + r * j, yz * (yy + w) + xy * r]

theorem symmetricAddition_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) (P Q : Fin 3 → R) :
    f ∘ symmetricAddition a b P Q =
      symmetricAddition (f a) (f b) (f ∘ P) (f ∘ Q) := by
  funext i
  fin_cases i <;> simp [symmetricAddition, map_ofNat]

theorem symmetricAddition_smul {R : Type*} [CommRing R] (a b : R)
    (P Q : Fin 3 → R) (u v : R) :
    symmetricAddition a b (u • P) (v • Q) =
      (u * v) ^ 2 • symmetricAddition a b P Q := by
  funext i
  fin_cases i <;> simp [symmetricAddition, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem symmetricAddition_comm {R : Type*} [CommRing R] (a b : R)
    (P Q : Fin 3 → R) :
    symmetricAddition a b P Q = symmetricAddition a b Q P := by
  funext i
  fin_cases i <;> simp [symmetricAddition] <;> ring

private theorem symmetricAddition_atInfinity {R : Type*} [CommRing R] (a b y : R)
    (Q : Fin 3 → R) :
    symmetricAddition a b ![0, y, 0] Q = (y ^ 2 * Q 1) • Q := by
  funext i
  fin_cases i <;> simp [symmetricAddition, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The polynomial identities for the affine secant, before any division.
The two coordinates are compared to the usual secant triple after
multiplying across by its last coordinate. -/
private theorem symmetricAddition_secant {F : Type*} [Field F]
    (a b x y u v : F) (hP : y ^ 2 - (x ^ 3 + a * x + b) = 0)
    (hQ : v ^ 2 - (u ^ 3 + a * u + b) = 0) :
    let D := x - u
    let S := y - v
    let A := S ^ 2 - (x + u) * D ^ 2
    let T := symmetricAddition a b ![x, y, 1] ![u, v, 1]
    T 0 * D ^ 3 = T 2 * (D * A) ∧
      T 1 * D ^ 3 = T 2 * (S * (x * D ^ 2 - A) - y * D ^ 3) := by
  dsimp
  simp [symmetricAddition]
  constructor
  · linear_combination (-2 * u * v * b - 1 * u * v ^ 3 + 3 * u * y * b - 1 * u * y * v ^ 2 + u * y ^ 2 * v -
          3 * u ^ 2 * v * a + 2 * u ^ 2 * y * a - 2 * u ^ 4 * v + 2 * x * v * b + x * v ^ 3 - 3
          * x * y * b + x * y * v ^ 2 - 1 * x * y ^ 2 * v + 4 * x * u * v * a - 1 * x * u * y *
          a - 1 * x * u ^ 3 * v + 3 * x * u ^ 3 * y - 1 * x ^ 2 * v * a - 1 * x ^ 2 * y * a + 6
          * x ^ 2 * u ^ 2 * v - 3 * x ^ 2 * u ^ 2 * y - 3 * x ^ 3 * u * v) * hP +
      (2 * u * v * b - 3 * u * y * b + u * y * v ^ 2 + u ^ 2 * v * a + u ^ 2 * y * a - 2 * x
          * v * b + 3 * x * y * b - 1 * x * y * v ^ 2 - 5 * x * u * y * a + 3 * x * u ^ 3 * y -
          1 * x ^ 2 * v * a + 4 * x ^ 2 * y * a + 3 * x ^ 2 * u ^ 2 * v - 6 * x ^ 2 * u ^ 2 * y
          - 4 * x ^ 3 * u * v + x ^ 4 * v + 3 * x ^ 4 * y) * hQ
  · linear_combination (3 * b ^ 2 - 2 * v ^ 2 * b + 2 * v ^ 4 - 5 * y * v * b + 3 * y ^ 2 * b - 2 * y ^ 2 * v
          ^ 2 + y ^ 3 * v + 2 * u * a * b + 3 * u * v ^ 2 * a - 5 * u * y * v * a + 2 * u * y ^
          2 * a - 6 * u ^ 3 * b - 2 * u ^ 3 * v ^ 2 - 2 * u ^ 3 * y * v - 4 * u ^ 4 * a + 4 * x
          * a * b - 5 * x * v ^ 2 * a + x * y ^ 2 * a + 2 * x * u * a ^ 2 + 12 * x * u ^ 2 * b
          + 15 * x * u ^ 2 * v ^ 2 - 6 * x * u ^ 2 * y * v + 3 * x * u ^ 2 * y ^ 2 + 4 * x * u
          ^ 3 * a - 6 * x * u ^ 5 + x ^ 2 * a ^ 2 - 15 * x ^ 2 * u * v ^ 2 + 3 * x ^ 2 * u * y
          * v + 6 * x ^ 2 * u ^ 2 * a + 9 * x ^ 2 * u ^ 4) * hP +
      (-3 * b ^ 2 - 1 * v ^ 2 * b + 5 * y * v * b - 1 * y * v ^ 3 + u * a * b - 1 * u * v ^
          2 * a - 1 * u ^ 2 * a ^ 2 - 7 * x * a * b + 5 * x * y * v * a + 3 * x * u * a ^ 2 +
          15 * x * u ^ 2 * b - 3 * x * u ^ 2 * y * v - 5 * x ^ 2 * a ^ 2 - 27 * x ^ 2 * u * b -
          3 * x ^ 2 * u * v ^ 2 + 6 * x ^ 2 * u * y * v + 9 * x ^ 2 * u ^ 2 * a + 6 * x ^ 3 * b
          + 2 * x ^ 3 * v ^ 2 + 2 * x ^ 3 * y * v - 14 * x ^ 3 * u * a - 1 * x ^ 4 * a + 6 * x
          ^ 4 * u ^ 2 - 9 * x ^ 5 * u) * hQ

private theorem symmetricAddition_opposite {F : Type*} [Field F]
    (a b x y : F) :
    let T := symmetricAddition a b ![x, y, 1] ![x, -y, 1]
    T 0 = 0 ∧ T 2 = 0 := by
  dsimp
  simp [symmetricAddition, mul_comm]

private theorem short_eqn_affine {F : Type*} [Field F]
    (W : Projective F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    {x y : F} (h : W.Equation ![x, y, 1]) :
    y ^ 2 - (x ^ 3 + W.a₄ * x + W.a₆) = 0 := by
  simpa [h₁, h₂, h₃, add_assoc] using (Projective.equation_iff _).mp h

/-- At an affine point on the diagonal the second triple is literally
Mathlib's doubling triple, including the case of a vertical tangent. -/
private theorem symmetricAddition_dbl_affine {F : Type*} [Field F]
    (W : Projective F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    {x y : F} (h : W.Equation ![x, y, 1]) :
    symmetricAddition W.a₄ W.a₆ ![x, y, 1] ![x, y, 1] = W.dblXYZ ![x, y, 1] := by
  have eqn := short_eqn_affine W h₁ h₂ h₃ h
  have hx := W.dblX_eq' h
  have hy := W.negDblY_eq' h
  rw [Projective.eval_polynomialX] at hx hy
  simp [Projective.negY_eq, h₁, h₂, h₃] at hx hy
  funext i
  fin_cases i
  · change symmetricAddition _ _ _ _ 0 = W.dblXYZ _ 0
    rw [Projective.dblXYZ_X, hx]
    simp [symmetricAddition]
    linear_combination 18 * x * y * eqn
  · change symmetricAddition _ _ _ _ 1 = W.dblXYZ _ 1
    rw [Projective.dblXYZ_Y, Projective.dblY, Projective.negY_eq, hy, h₁, h₃]
    simp [symmetricAddition]
    linear_combination (9 * W.a₆ + 9 * y ^ 2 - 3 * x * W.a₄ - 27 * x ^ 3) * eqn
  · change symmetricAddition _ _ _ _ 2 = W.dblXYZ _ 2
    rw [Projective.dblXYZ_Z, Projective.dblZ]
    simp [symmetricAddition, Projective.negY_eq, h₁, h₃]
    linear_combination -6 * y * eqn


private theorem symmetricAddition_affine {F : Type*} [Field F]
    (W : Projective F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    {x y u v : F} (hP : W.Equation ![x, y, 1]) (hQ : W.Equation ![u, v, 1]) :
    ∃ c : F, symmetricAddition W.a₄ W.a₆ ![x, y, 1] ![u, v, 1] =
      c • W.add ![x, y, 1] ![u, v, 1] := by
  classical
  let T := symmetricAddition W.a₄ W.a₆ ![x, y, 1] ![u, v, 1]
  change ∃ c : F, T = c • W.add ![x, y, 1] ![u, v, 1]
  by_cases hx : x = u
  · subst u
    by_cases hy : y = v
    · subst v
      exact ⟨1, by simpa only [one_smul, Projective.add_self] using
        symmetricAddition_dbl_affine W h₁ h₂ h₃ hP⟩
    · have e : y = -v := by
        simpa [Projective.negY, h₁, h₃] using
          W.Y_eq_of_Y_ne hP hQ (by simp) (by simp) (by simp) (by simpa using hy)
      have e' : v = -y := by rw [e, neg_neg]
      have ht : T 0 = 0 ∧ T 2 = 0 := by
        dsimp [T]
        rw [e']
        exact symmetricAddition_opposite W.a₄ W.a₆ x y
      have ha := W.add_of_Y_ne hP hQ (by simp) (by simp) (by simp) (by simpa using hy)
      let A : F := Projective.addU ![x, y, 1] ![x, v, 1]
      have hA : A ≠ 0 := Projective.addU_ne_zero_of_Y_ne (by simp) (by simp) (by simpa using hy)
      refine ⟨T 1 / A, ?_⟩
      rw [ha, smul_smul, div_mul_cancel₀ _ hA]
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, ht.1, ht.2]
  · let D := x - u
    have hD : D ≠ 0 := sub_ne_zero.mpr hx
    have hPx : (![x, y, 1] : Fin 3 → F) 0 * (![u, v, 1] : Fin 3 → F) 2 ≠
        (![u, v, 1] : Fin 3 → F) 0 * (![x, y, 1] : Fin 3 → F) 2 := by simpa using hx
    have hZ : W.addZ ![x, y, 1] ![u, v, 1] = D ^ 3 := by
      rw [W.addZ_eq hP hQ (by simp) (by simp)]
      simp [D]
    have ha : W.add ![x, y, 1] ![u, v, 1] = D ^ 3 •
        ![W.toAffine.addX x u ((y - v) / D), W.toAffine.addY x u y ((y - v) / D), 1] := by
      simpa [hZ, Affine.slope_of_X_ne hx, D] using
        W.add_of_X_ne hP hQ (by simp) (by simp) hPx
    have ha₁ : W.toAffine.a₁ = 0 := h₁
    have ha₂ : W.toAffine.a₂ = 0 := h₂
    have ha₃ : W.toAffine.a₃ = 0 := h₃
    have hs := symmetricAddition_secant W.a₄ W.a₆ x y u v
      (short_eqn_affine W h₁ h₂ h₃ hP) (short_eqn_affine W h₁ h₂ h₃ hQ)
    change _ * D ^ 3 = _ ∧ _ * D ^ 3 = _ at hs
    refine ⟨T 2 / D ^ 3, ?_⟩
    rw [ha, smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hD)]
    funext i
    fin_cases i
    · change T 0 = _
      apply mul_right_cancel₀ (pow_ne_zero 3 hD)
      rw [show T 0 * D ^ 3 = _ from hs.1]
      simp [Pi.smul_apply, smul_eq_mul, Affine.addX, ha₁, ha₂]
      dsimp [D] at hD ⊢
      field_simp
      ring
    · change T 1 = _
      apply mul_right_cancel₀ (pow_ne_zero 3 hD)
      rw [show T 1 * D ^ 3 = _ from hs.2]
      simp [Pi.smul_apply, smul_eq_mul, Affine.addY,
        Affine.negY, Affine.negAddY, Affine.addX, ha₁, ha₂, ha₃]
      dsimp [D] at hD ⊢
      field_simp
      ring
    · simp [Pi.smul_apply, smul_eq_mul]

private theorem vector_atInfinity {F : Type*} [Field F] (W : Projective F)
    {P : Fin 3 → F} (hP : W.Equation P) (hPz : P 2 = 0) :
    P = ![0, P 1, 0] := by
  funext i
  fin_cases i
  · exact Projective.X_eq_zero_of_Z_eq_zero hP hPz
  · rfl
  · exact hPz

/-- At every pair of nonsingular field points the symmetric triple is a
scalar multiple, possibly zero, of Mathlib's sum representative. -/
theorem symmetricAddition_eq_smul_add {F : Type*} [Field F]
    (W : Projective F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    ∃ c : F, symmetricAddition W.a₄ W.a₆ P Q = c • W.add P Q := by
  classical
  by_cases hPz : P 2 = 0
  · rw [(congrArg (fun t => symmetricAddition W.a₄ W.a₆ t Q)
      (vector_atInfinity W hP.1 hPz)), symmetricAddition_atInfinity]
    by_cases hQz : Q 2 = 0
    · rw [W.add_of_Z_eq_zero hP hQ hPz hQz]
      refine ⟨P 1 ^ 2 * Q 1 ^ 2 / P 1 ^ 4, ?_⟩
      rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ (W.Y_ne_zero_of_Z_eq_zero hP hPz))]
      rw [congrArg (fun t => (P 1 ^ 2 * Q 1) • t) (vector_atInfinity W hQ.1 hQz)]
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
      ring
    · rw [Projective.add_of_Z_eq_zero_left hP.1 hPz hQz]
      refine ⟨Q 1 / Q 2, ?_⟩
      rw [smul_smul]
      congr 1
      field_simp
  · by_cases hQz : Q 2 = 0
    · rw [symmetricAddition_comm, (congrArg (fun t => symmetricAddition W.a₄ W.a₆ t P)
        (vector_atInfinity W hQ.1 hQz)), symmetricAddition_atInfinity,
        Projective.add_of_Z_eq_zero_right hQ.1 hPz hQz]
      refine ⟨-(P 1 / P 2), ?_⟩
      rw [smul_smul]
      congr 1
      field_simp
    · let p : Fin 3 → F := ![P 0 / P 2, P 1 / P 2, 1]
      let q : Fin 3 → F := ![Q 0 / Q 2, Q 1 / Q 2, 1]
      obtain ⟨u, hu⟩ : P ≈ p := Projective.equiv_some_of_Z_ne_zero hPz
      obtain ⟨v, hv⟩ : Q ≈ q := Projective.equiv_some_of_Z_ne_zero hQz
      have hp : W.Equation p := (Projective.equation_of_equiv ⟨u, hu⟩).mp hP.1
      have hq : W.Equation q := (Projective.equation_of_equiv ⟨v, hv⟩).mp hQ.1
      obtain ⟨c, hc⟩ := symmetricAddition_affine W h₁ h₂ h₃ hp hq
      obtain ⟨w, hw⟩ : W.add p q ≈ W.add P Q :=
        Setoid.symm (Projective.add_equiv ⟨u, hu⟩ ⟨v, hv⟩)
      change u • p = P at hu
      change v • q = Q at hv
      change w • W.add P Q = W.add p q at hw
      refine ⟨((u : F) * (v : F)) ^ 2 * c * (w : F), ?_⟩
      calc
        _ = symmetricAddition W.a₄ W.a₆ ((u : F) • p) ((v : F) • q) := by
          rw [← Units.smul_def, ← Units.smul_def, hu, hv]
        _ = _ := by
          rw [symmetricAddition_smul, hc, ← hw, Units.smul_def, smul_smul, smul_smul, mul_assoc]

private theorem symmetricAddition_diagonal {F : Type*} [Field F]
    (W : Projective F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    {P : Fin 3 → F} (hP : W.Equation P) :
    symmetricAddition W.a₄ W.a₆ P P = W.dblXYZ P := by
  by_cases hPz : P 2 = 0
  · rw [W.dblXYZ_of_Z_eq_zero hP hPz]
    have h := vector_atInfinity W hP hPz
    rw [congrArg (fun t => symmetricAddition W.a₄ W.a₆ t P) h, symmetricAddition_atInfinity,
      congrArg (fun t => (P 1 ^ 2 * P 1) • t) h]
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    ring
  · let p : Fin 3 → F := ![P 0 / P 2, P 1 / P 2, 1]
    obtain ⟨u, hu⟩ : P ≈ p := Projective.equiv_some_of_Z_ne_zero hPz
    have hp : W.Equation p := (Projective.equation_of_equiv ⟨u, hu⟩).mp hP
    have h := symmetricAddition_dbl_affine W h₁ h₂ h₃ hp
    change u • _ = _ at hu
    rw [← hu, Units.smul_def, symmetricAddition_smul, h, Projective.dblXYZ_smul]
    congr 1
    ring

theorem projectiveNonsingular_ne_zero {F : Type*} [Field F] {W : Projective F}
    {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by
  intro e
  exact W.Y_ne_zero_of_Z_eq_zero hP (by simp [e]) (by simp [e])

/-- The two triples cover all pairs: if the secant triple is zero, the
points coincide and the symmetric triple is a nonzero doubling triple
up to rescaling. -/
theorem projectiveAddition_cover {F : Type*} [Field F]
    (W : Projective F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ∨ symmetricAddition W.a₄ W.a₆ P Q ≠ 0 := by
  by_cases h : P ≈ Q
  · right
    obtain ⟨u, hu⟩ := h
    change u • _ = _ at hu
    rw [← hu, Units.smul_def,
      ← congrArg (fun q => symmetricAddition W.a₄ W.a₆ ((u : F) • Q) q) (one_smul F Q),
      symmetricAddition_smul, symmetricAddition_diagonal W h₁ h₂ h₃ hQ.1, ← Projective.add_self]
    exact smul_ne_zero (pow_ne_zero _ (mul_ne_zero u.ne_zero one_ne_zero))
      (projectiveNonsingular_ne_zero (W.nonsingular_add hQ hQ))
  · left
    rw [← Projective.add_of_not_equiv h]
    exact projectiveNonsingular_ne_zero (W.nonsingular_add hP hQ)








end ZInQ.Manuscript.RC.J0Cusps
