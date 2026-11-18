import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.CoordE1b

/-!
# E1a, part 1: the new-local cancellation multiplies the Knudsen–Mumford coordinate by `det B`

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5509–5516: "first perform the simultaneous new-local cancellation … Its determinant comparison
factor `κ` is an `S`-unit … Retain this factor … Transport the actual cycle `z` and the closed
functional `μ` to the remaining complex `D`."

Over a field `K`, for the pre-cancellation complex `C` of the clearing (`PreComplex`:
`C⁰ = E₀`, `C¹ = D¹`, `C² = D² ⊕ N`, `C³ = B₃ ⊕ N`, differential `(P Q; T B)` in degrees `2 → 3`)
with the new local block `B` invertible, a cycle `z ∈ C¹` and a closed functional `λ` on `C²`:

* `PreComplex.toFour`: `C` as a four-term complex (lane Torsion's `FourCx`);
* `transportFun`: the transported functional `μ = λ ∘ incl = λ_D − λ_N B⁻¹ T` on `D²` (the
  inclusion `incl : D → C`, `x ↦ (x, −B⁻¹ T x)`, of lane ClearingComplex's `PreComplex.incl`);
  `hz_cancel`, `hμ_cancel`: `z` is a cycle and `μ` is closed on the remaining complex;
* `kmCoord_preCancel` (**PROVED**): with the orientation `σPre` (the remaining complex's `σBlock`
  and the identity on the cancelled pair `N → N`),
  `kmCoord(C, z, λ) = det B · kmCoord(D, z, μ)`, `D = C.cancel`: the determinant comparison factor
  of the new-local cancellation is `κ = det B` (lane ClearingComplex's `torsion_cancelE`: the two
  elementary matrices have determinant one and the cancelled disk `N --B--> N`, from degree two to
  degree three, contributes `det B`).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex

variable {K : Type} [Field K]

namespace PreComplex'

variable (C : ClearingComplex.PreComplex K)

/-- The pre-cancellation complex as a four-term complex. -/
def toFour : FourCx K (Fin C.m0) (Fin C.m0 ⊕ Unit ⊕ Fin C.m1)
    ((Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N) (Fin C.m2 ⊕ C.N) where
  d0 := C.c0
  d1 := fromRows C.X C.Y
  d2 := fromBlocks C.P C.Q C.T C.B
  d10 := C.c1_c0
  d21 := C.c2_c1

end PreComplex'

section Ring

variable {R : Type} [CommRing R] (C : ClearingComplex.PreComplex R) (hB : IsUnit C.B.det)

/-- **The transported functional** `μ = λ ∘ incl = λ_D − λ_N B⁻¹ T` on `D²`. -/
def transportFun (lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → R) :
    Fin C.m1 ⊕ Unit ⊕ Fin C.m2 → R :=
  (lam ∘ Sum.inl) - ((lam ∘ Sum.inr) ᵥ* C.B⁻¹) ᵥ* C.T

theorem hz_cancel {z : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → R}
    (hz : fromRows C.X C.Y *ᵥ z = 0) :
    (C.cancel hB).d1 *ᵥ z = 0 := by
  have h := hz
  rw [fromRows_mulVec] at h
  funext i
  exact congrFun h (Sum.inl i)

theorem hμ_cancel {lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → R}
    (hlam : lam ᵥ* fromRows C.X C.Y = 0) :
    transportFun C lam ᵥ* (C.cancel hB).d1 = 0 := by
  have h := hlam
  have hsplit : lam ᵥ* fromRows C.X C.Y = (lam ∘ Sum.inl) ᵥ* C.X + (lam ∘ Sum.inr) ᵥ* C.Y := by
    funext j; simp [vecMul, dotProduct, Fintype.sum_sum_type]
  rw [hsplit, PreComplex.Y_eq hB] at h
  change ((lam ∘ Sum.inl) - ((lam ∘ Sum.inr) ᵥ* C.B⁻¹) ᵥ* C.T) ᵥ* C.X = 0
  rw [sub_vecMul, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc]
  rw [vecMul_neg] at h
  rw [← sub_eq_add_neg] at h
  exact h

end Ring

/-! ### Relabelling for the cancellation of `N --B--> N` -/

variable (m0 m1 m2 : ℕ) (N : Type)

/-- Even bases: `(C⁰ ⊕ K₀) ⊕ (D² ⊕ N) ≃ ((C⁰ ⊕ K₀) ⊕ D²) ⊕ N`. -/
def eEp : (Fin m0 ⊕ Unit) ⊕ ((Fin m1 ⊕ Unit ⊕ Fin m2) ⊕ N) ≃
    ((Fin m0 ⊕ Unit) ⊕ (Fin m1 ⊕ Unit ⊕ Fin m2)) ⊕ N where
  toFun
    | .inl a => .inl (.inl a)
    | .inr (.inl d) => .inl (.inr d)
    | .inr (.inr n) => .inr n
  invFun
    | .inl (.inl a) => .inl a
    | .inl (.inr d) => .inr (.inl d)
    | .inr n => .inr (.inr n)
  left_inv := by rintro (a | (d | n)) <;> rfl
  right_inv := by rintro ((a | d) | n) <;> rfl

/-- Odd bases: `D¹ ⊕ ((B₃ ⊕ N) ⊕ K₃) ≃ (D¹ ⊕ (B₃ ⊕ K₃)) ⊕ N`. -/
def eOp : (Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ ((Fin m2 ⊕ N) ⊕ Unit) ≃
    ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit)) ⊕ N where
  toFun
    | .inl c => .inl (.inl c)
    | .inr (.inl (.inl b)) => .inl (.inr (.inl b))
    | .inr (.inl (.inr n)) => .inr n
    | .inr (.inr u) => .inl (.inr (.inr u))
  invFun
    | .inl (.inl c) => .inl c
    | .inl (.inr (.inl b)) => .inr (.inl (.inl b))
    | .inl (.inr (.inr u)) => .inr (.inr u)
    | .inr n => .inr (.inl (.inr n))
  left_inv := by rintro (c | ((b | n) | u)) <;> rfl
  right_inv := by rintro ((c | (b | u)) | n) <;> rfl

/-- **The orientation of the pre-cancellation complex**: `σBlock` on the remaining complex and the
identity on the cancelled pair. -/
def σPre : (Fin m0 ⊕ Unit) ⊕ ((Fin m1 ⊕ Unit ⊕ Fin m2) ⊕ N) ≃
    (Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ ((Fin m2 ⊕ N) ⊕ Unit) :=
  (eEp m0 m1 m2 N).trans (((σBlock m0 m1 m2).sumCongr (Equiv.refl N)).trans
    (eOp m0 m1 m2 N).symm)

/-! ### The cancellation -/

variable {C : ClearingComplex.PreComplex K} (hB : IsUnit C.B.det)

variable (z : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → K)
  (lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → K) (hz : (PreComplex'.toFour C).d1 *ᵥ z = 0)
  (hlam : lam ᵥ* (PreComplex'.toFour C).d1 = 0)

/-- The augmented pre-cancellation complex, relabelled. -/
def Xp : BasedCx K (((Fin C.m0 ⊕ Unit) ⊕ (Fin C.m1 ⊕ Unit ⊕ Fin C.m2)) ⊕ C.N)
    (((Fin C.m0 ⊕ Unit ⊕ Fin C.m1) ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) :=
  ((PreComplex'.toFour C).aug z lam hz hlam).toBased.reindex (eEp C.m0 C.m1 C.m2 C.N)
    (eOp C.m0 C.m1 C.m2 C.N)

theorem Xp_degE (n : C.N) : (Xp z lam hz hlam).degE (Sum.inr n) = 2 := rfl
theorem Xp_degO (n : C.N) : (Xp z lam hz hlam).degO (Sum.inr n) = 2 + 1 := rfl

theorem Xp_blkA : blkA (Xp z lam hz hlam) = C.B := by
  ext n m; rfl

variable {z lam hz hlam}

include hB in
theorem Xp_hA : IsUnit (blkA (Xp z lam hz hlam)).det := by
  rw [Xp_blkA]; exact hB

/-- **The Schur complement of the relabelled augmented pre-cancellation complex is the augmented
remaining complex** at the transported functional. -/
theorem schurE_Xp :
    schurE (C := Xp z lam hz hlam) 2 (Xp_degE z lam hz hlam) (Xp_degO z lam hz hlam)
        (Xp_hA hB) =
      ((C.cancel hB).toFour.aug z (transportFun C lam) (hz_cancel C hB hz)
        (hμ_cancel C hB hlam)).toBased := by
  apply BasedCx.ext'
  · funext x; rcases x with (a | a) | d <;> rfl
  · funext x; rcases x with c | (b | u) <;> rfl
  · change (Xp z lam hz hlam).dOE.toBlocks₁₁ - (Xp z lam hz hlam).dOE.toBlocks₁₂ *
        (blkA (Xp z lam hz hlam))⁻¹ * (Xp z lam hz hlam).dOE.toBlocks₂₁ = _
    rw [Xp_blkA]
    ext i j
    rcases i with c | (b | u) <;> rcases j with a | d
    all_goals first
      | rfl
      | (simp [Xp, BasedCx.reindex, FourCx.toBased_dOE, FourCx.aug, eEp, eOp, mul_apply,
          toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, PreComplex'.toFour]; rfl)
  · ext i j
    rcases i with (a | a) | d <;> rcases j with c | (b | u) <;> rfl

/-- **The new-local cancellation multiplies the Knudsen–Mumford coordinate by `det B`** (tex
5509–5516): `kmCoord(C, z, λ) = det B · kmCoord(C.cancel, z, μ)`, `μ = λ ∘ incl`. -/
theorem kmCoord_preCancel :
    kmCoord (PreComplex'.toFour C) z lam hz hlam (σPre C.m0 C.m1 C.m2 C.N) =
      C.B.det * kmCoord (C.cancel hB).toFour z (transportFun C lam) (hz_cancel C hB hz)
        (hμ_cancel C hB hlam) (σBlock C.m0 C.m1 C.m2) := by
  unfold kmCoord
  have t0 : torsion (Xp z lam hz hlam) ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl _)) =
      torsion ((PreComplex'.toFour C).aug z lam hz hlam).toBased (σPre C.m0 C.m1 C.m2 C.N) := by
    have := torsion_reindex' ((PreComplex'.toFour C).aug z lam hz hlam).toBased
      (σPre C.m0 C.m1 C.m2 C.N) (eEp C.m0 C.m1 C.m2 C.N) (eOp C.m0 C.m1 C.m2 C.N)
    rw [σPre, transport_eq] at this
    exact this
  have t1 := torsion_cancelE (C := Xp z lam hz hlam) 2 (Xp_degE z lam hz hlam)
    (Xp_degO z lam hz hlam) (Xp_hA hB) (by decide) (σBlock C.m0 C.m1 C.m2)
  rw [← t0, t1, schurE_Xp hB, Xp_blkA, mul_comm, mul_neg]
  rfl

end ZInQ.Contrib.CloudB3RC53.CoordLink
