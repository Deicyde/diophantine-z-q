import ZInQKernel.Contrib.CloudB3RC53.Torsion.Operations

/-!
# Torsion, part 10: derived Nakayama for based complexes over a local ring

Lemma `ex:arith-local-kummer`, tex L3452–3453: "Reduction modulo two, including the torsion in
degree zero, gives the perfect quotient-to-dual comparison; derived Nakayama lifts it." This is one
of Elliot's own steps in the derived Kummer lemma.

At chain level, a comparison of bounded complexes of finite free modules is a homotopy equivalence
iff its cone is contractible. So the step is: **a bounded complex of finite free modules over a
local ring whose reduction modulo the maximal ideal is contractible is itself contractible**
(`nakayama_contraction`). Applied to the (based) cone of a comparison, contractibility of the
reduced cone lifts to contractibility of the cone, i.e. the comparison is a homotopy equivalence.
(The project's `BasedCx.cone` is stated over a field; over a local ring the cone of a comparison is
again a based complex, to which `nakayama_contraction` applies.)

The proof is elementary:
* lift the residue contraction `h̄` entrywise to `h`, keeping its degree (`exists_lift_hasDeg`);
* `U = dh + hd` reduces to the identity, so it is invertible (its determinant is a unit,
  `isUnit_det_of_map_eq_one`), has degree `0`, and commutes with `d`;
* `U⁻¹` again has degree `0` (`HasDeg.nonsing_inv`, via the degree projections) and commutes
  with `d`, so `h U⁻¹` is a contraction.

* `BasedCx.map`: coefficient change of a based complex along a ring map.
* Non-vacuity: `nakayama_example` — for any local ring `R` and `x` in its maximal ideal, the disk
  `R --(1 + x)--> R` has a contractible reduction, and the theorem produces an integral contraction.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R] {κe κo : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe]
  [DecidableEq κo]

/-- **Coefficient change of a based complex** along a ring map. -/
def BasedCx.map {S : Type*} [CommRing S] (f : R →+* S) (C : BasedCx R κe κo) :
    BasedCx S κe κo where
  degE := C.degE
  degO := C.degO
  even_degE := C.even_degE
  odd_degO := C.odd_degO
  dOE := C.dOE.map f
  dEO := C.dEO.map f
  dd_E := by rw [← Matrix.map_mul, C.dd_E, Matrix.map_zero _ (map_zero f)]
  dd_O := by rw [← Matrix.map_mul, C.dd_O, Matrix.map_zero _ (map_zero f)]
  deg_dOE i j h := C.deg_dOE i j fun h0 => h (by simp [h0])
  deg_dEO i j h := C.deg_dEO i j fun h0 => h (by simp [h0])

/-- A homogeneous matrix over the target of a surjective ring map lifts to a homogeneous matrix of
the same degree. -/
theorem exists_lift_hasDeg {S : Type*} [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    {m n : Type*} {X : Matrix m n S} {bm : m → ℤ} {bn : n → ℤ} {a : ℤ} (hX : HasDeg X bm bn a) :
    ∃ Y : Matrix m n R, Y.map f = X ∧ HasDeg Y bm bn a := by
  classical
  refine ⟨fun i j => if X i j = 0 then 0 else Function.surjInv hf (X i j), ?_, fun i j h => ?_⟩
  · refine Matrix.ext fun i j => ?_
    show f (if X i j = 0 then 0 else Function.surjInv hf (X i j)) = X i j
    split_ifs with h
    · rw [map_zero, h]
    · exact Function.surjInv_eq hf _
  · apply hX i j
    intro h0
    apply h
    simp [h0]

variable [IsLocalRing R]

/-- A square matrix reducing to the identity has unit determinant. -/
theorem isUnit_det_of_map_eq_one {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m R}
    (hU : U.map (IsLocalRing.residue R) = 1) : IsUnit U.det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  change ((IsLocalRing.residue R).mapMatrix U).det ≠ 0
  rw [RingHom.mapMatrix_apply, hU, det_one]
  exact one_ne_zero

omit [IsLocalRing R] in
/-- The degree projection `E_k`. -/
theorem HasDeg.commute_proj {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m R}
    {b : m → ℤ} (hU : HasDeg U b b 0) (k : ℤ) :
    U * diagonal (fun x => if b x = k then (1 : R) else 0) =
      diagonal (fun x => if b x = k then (1 : R) else 0) * U := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases h : U i j = 0
  · simp [h]
  · have := hU i j h
    simp only [add_zero] at this
    rw [this, mul_comm]

omit [IsLocalRing R] in
/-- **The inverse of an invertible degree-zero matrix has degree zero.** -/
theorem HasDeg.nonsing_inv {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m R}
    {b : m → ℤ} (hU : HasDeg U b b 0) (hdet : IsUnit U.det) : HasDeg U⁻¹ b b 0 := by
  intro i j hij
  set E := diagonal (fun x => if b x = b j then (1 : R) else 0)
  have hc : U⁻¹ * E = E * U⁻¹ := by
    have h := hU.commute_proj (b j)
    calc U⁻¹ * E = U⁻¹ * E * (U * U⁻¹) := by rw [mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = U⁻¹ * (E * U) * U⁻¹ := by simp only [Matrix.mul_assoc]
      _ = U⁻¹ * (U * E) * U⁻¹ := by rw [h]
      _ = E * U⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
  have e := congrFun (congrFun hc i) j
  simp only [E, mul_diagonal, diagonal_mul, ↓reduceIte, mul_one] at e
  by_contra hne
  have hne' : ¬ b i = b j := by omega
  simp only [hne', ↓reduceIte, zero_mul] at e
  exact hij e

/-- **Derived Nakayama for based complexes** (tex L3452–3453): a based complex over a local ring
whose reduction modulo the maximal ideal is contractible is contractible. PROVED. -/
theorem nakayama_contraction (C : BasedCx R κe κo)
    (hbar : Contraction (C.map (IsLocalRing.residue R))) : Nonempty (Contraction C) := by
  set π := IsLocalRing.residue R
  obtain ⟨hOE, hOE_map, hOE_deg⟩ := exists_lift_hasDeg π IsLocalRing.residue_surjective
    hbar.deg_hOE
  obtain ⟨hEO, hEO_map, hEO_deg⟩ := exists_lift_hasDeg π IsLocalRing.residue_surjective
    hbar.deg_hEO
  set UE := C.dEO * hOE + hEO * C.dOE
  set UO := C.dOE * hEO + hOE * C.dEO
  have hUE : UE.map π = 1 := by
    rw [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_mul, hOE_map, hEO_map]
    exact hbar.htpy_E
  have hUO : UO.map π = 1 := by
    rw [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_mul, hOE_map, hEO_map]
    exact hbar.htpy_O
  have dE := isUnit_det_of_map_eq_one hUE
  have dO := isUnit_det_of_map_eq_one hUO
  have degUE : HasDeg UE C.degE C.degE 0 :=
    ((C.deg_dEO.mul hOE_deg).of_eq (by ring)).add ((hEO_deg.mul C.deg_dOE).of_eq (by ring))
  have degUO : HasDeg UO C.degO C.degO 0 :=
    ((C.deg_dOE.mul hEO_deg).of_eq (by ring)).add ((hOE_deg.mul C.deg_dEO).of_eq (by ring))
  -- `d U = U d`
  have cOE : C.dOE * UE = UO * C.dOE := by
    simp only [UE, UO, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, C.dd_O,
      Matrix.zero_mul]
    simp only [Matrix.mul_assoc, C.dd_E, Matrix.mul_zero, zero_add, add_zero]
  have cEO : C.dEO * UO = UE * C.dEO := by
    simp only [UE, UO, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, C.dd_E,
      Matrix.zero_mul]
    simp only [Matrix.mul_assoc, C.dd_O, Matrix.mul_zero, zero_add, add_zero]
  -- `U⁻¹ d = d U⁻¹`
  have iOE : UO⁻¹ * C.dOE = C.dOE * UE⁻¹ := by
    calc UO⁻¹ * C.dOE = UO⁻¹ * C.dOE * (UE * UE⁻¹) := by
          rw [mul_nonsing_inv _ dE, Matrix.mul_one]
      _ = UO⁻¹ * (C.dOE * UE) * UE⁻¹ := by simp only [Matrix.mul_assoc]
      _ = UO⁻¹ * (UO * C.dOE) * UE⁻¹ := by rw [cOE]
      _ = C.dOE * UE⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ dO, Matrix.one_mul]
  have iEO : UE⁻¹ * C.dEO = C.dEO * UO⁻¹ := by
    calc UE⁻¹ * C.dEO = UE⁻¹ * C.dEO * (UO * UO⁻¹) := by
          rw [mul_nonsing_inv _ dO, Matrix.mul_one]
      _ = UE⁻¹ * (C.dEO * UO) * UO⁻¹ := by simp only [Matrix.mul_assoc]
      _ = UE⁻¹ * (UE * C.dEO) * UO⁻¹ := by rw [cEO]
      _ = C.dEO * UO⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ dE, Matrix.one_mul]
  refine ⟨{ hOE := hOE * UE⁻¹
            hEO := hEO * UO⁻¹
            deg_hOE := (hOE_deg.mul (degUE.nonsing_inv dE)).of_eq (by ring)
            deg_hEO := (hEO_deg.mul (degUO.nonsing_inv dO)).of_eq (by ring)
            htpy_E := ?_
            htpy_O := ?_ }⟩
  · calc C.dEO * (hOE * UE⁻¹) + hEO * UO⁻¹ * C.dOE
        = C.dEO * hOE * UE⁻¹ + hEO * (UO⁻¹ * C.dOE) := by simp only [Matrix.mul_assoc]
      _ = UE * UE⁻¹ := by rw [iOE, Matrix.add_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := mul_nonsing_inv _ dE
  · calc C.dOE * (hEO * UO⁻¹) + hOE * UE⁻¹ * C.dEO
        = C.dOE * hEO * UO⁻¹ + hOE * (UE⁻¹ * C.dEO) := by simp only [Matrix.mul_assoc]
      _ = UO * UO⁻¹ := by rw [iEO, Matrix.add_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := mul_nonsing_inv _ dO

/-- **Non-vacuity**: for `x` in the maximal ideal, the reduction of the disk `R --(1 + x)--> R` is
contractible (by the identity), so `nakayama_contraction` gives an integral contraction. -/
theorem nakayama_example (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    Nonempty (Contraction (diskEven 0 even_zero (1 + x))) := by
  have hπ : IsLocalRing.residue R (1 + x) = 1 := by
    rw [map_add, map_one, (IsLocalRing.residue_eq_zero_iff x).mpr hx, add_zero]
  have hsc : (sc (1 + x)).map (IsLocalRing.residue R) = 1 := by
    ext i j
    simp [sc, hπ]
  refine nakayama_contraction _
    { hOE := 0
      hEO := 1
      deg_hOE := fun _ _ h => absurd rfl h
      deg_hEO := fun _ _ _ => by
        change (0 : ℤ) = 0 + 1 + -1
        ring
      htpy_E := ?_
      htpy_O := ?_ }
  · change (0 : Matrix Unit Unit R).map (IsLocalRing.residue R) * 0 +
      1 * (sc (1 + x)).map (IsLocalRing.residue R) = 1
    rw [hsc]; simp
  · change (sc (1 + x)).map (IsLocalRing.residue R) * 1 +
      0 * (0 : Matrix Unit Unit R).map (IsLocalRing.residue R) = 1
    rw [hsc]; simp

end ZInQ.Contrib.CloudB3RC53.Torsion
