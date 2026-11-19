import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionCancel
import ZInQKernel.Contrib.CloudB3RC53.CoordLink.PreCancel

/-!
# The cancellation of the full-condition singular summands divides the coordinate by `det B`

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
5509–5516 (the simultaneous new-local cancellation and its determinant comparison factor), with
the singular quotients in degrees one and two (tex 3479–3481, 5320–5322) and the disk rule of
tex 5545–5595 ("a disk in degrees `i, i+1` contributes `δ_i^{(−1)^i}`": for `i = 1`, `det B⁻¹`).

Over a field `K`, for a `FullPreComplex` `C` (`C¹ = D¹ ⊕ N`, `C² = D² ⊕ N`,
`d¹ = (P Q; T B)`) with `B` invertible, a cycle `z ∈ C¹` and a closed functional `λ` on `C²`:

* `FullPreComplex.toFour`: `C` as a four-term complex;
* the transported cycle `z ∘ inl` and functional `λ ∘ inl` on the remaining complex
  `D = C.cancel` (`z = incl (z ∘ inl)` for a cycle; `λ ∘ inl = λ ∘ incl` in degree two):
  `hz_full`, `hλ_full`;
* `kmCoord_fullCancel` (PROVED): `kmCoord(C, z, λ) = det(B)⁻¹ · kmCoord(D, z ∘ inl, λ ∘ inl)`
  for the orientation `σFull` (the remaining complex's `σBlock` and the identity on the cancelled
  pair): the disk `N --B--> N` from degree one to degree two contributes `det(B)⁻¹`
  (`torsion_cancelO`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.CoordLink (eEp)

namespace FullPreComplex

variable {R : Type} [CommRing R] (C : FullPreComplex R)

/-- The full-condition pre-cancellation complex as a four-term complex. -/
def toFour : FourCx R (Fin C.m0) (C.D1 ⊕ C.N) (C.D2 ⊕ C.N) (Fin C.m2) where
  d0 := fromRows C.c0 C.Y
  d1 := fromBlocks C.P C.Q C.T C.B
  d2 := fromCols C.U C.V
  d10 := C.c1_c0
  d21 := C.c2_c1

variable {C} (hB : IsUnit C.B.det)

include hB in
/-- A cycle of `C¹` restricts to a cycle of the remaining complex. -/
theorem hz_full {z : C.D1 ⊕ C.N → R} (hz : C.toFour.d1 *ᵥ z = 0) :
    (C.cancel hB).d1 *ᵥ (z ∘ Sum.inl) = 0 := by
  have h1 : C.P *ᵥ (z ∘ Sum.inl) + C.Q *ᵥ (z ∘ Sum.inr) = 0 := by
    have h := congrArg (· ∘ Sum.inl) hz
    simp only [toFour] at h
    rw [← Sum.elim_comp_inl_inr z, fromBlocks_mulVec] at h
    simpa using h
  have h2 : C.T *ᵥ (z ∘ Sum.inl) + C.B *ᵥ (z ∘ Sum.inr) = 0 := by
    have h := congrArg (· ∘ Sum.inr) hz
    simp only [toFour] at h
    rw [← Sum.elim_comp_inl_inr z, fromBlocks_mulVec] at h
    simpa using h
  have hN : z ∘ Sum.inr = -((C.B⁻¹ * C.T) *ᵥ (z ∘ Sum.inl)) := by
    have e : C.B *ᵥ (z ∘ Sum.inr) = -(C.T *ᵥ (z ∘ Sum.inl)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    have e2 := congrArg (C.B⁻¹ *ᵥ ·) e
    simp only [mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec, mulVec_neg] at e2
    exact e2
  change (C.P - C.Q * C.B⁻¹ * C.T) *ᵥ (z ∘ Sum.inl) = 0
  rw [hN, mulVec_neg, mulVec_mulVec, ← sub_eq_add_neg] at h1
  rw [sub_mulVec, Matrix.mul_assoc]
  exact h1

include hB in
/-- A closed functional on `C²` restricts to a closed functional on the remaining complex. -/
theorem hlam_full {lam : C.D2 ⊕ C.N → R} (hlam : lam ᵥ* C.toFour.d1 = 0) :
    (lam ∘ Sum.inl) ᵥ* (C.cancel hB).d1 = 0 := by
  have hsplit : lam ᵥ* fromBlocks C.P C.Q C.T C.B =
      Sum.elim ((lam ∘ Sum.inl) ᵥ* C.P + (lam ∘ Sum.inr) ᵥ* C.T)
        ((lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B) := by
    rw [← Sum.elim_comp_inl_inr lam, vecMul_fromBlocks]
  have h : lam ᵥ* fromBlocks C.P C.Q C.T C.B = 0 := hlam
  rw [hsplit] at h
  have h1 : (lam ∘ Sum.inl) ᵥ* C.P + (lam ∘ Sum.inr) ᵥ* C.T = 0 := by
    have := congrArg (· ∘ Sum.inl) h
    simpa using this
  have h2 : (lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B = 0 := by
    have := congrArg (· ∘ Sum.inr) h
    simpa using this
  have hN : lam ∘ Sum.inr = -((lam ∘ Sum.inl) ᵥ* (C.Q * C.B⁻¹)) := by
    have e : (lam ∘ Sum.inr) ᵥ* C.B = -((lam ∘ Sum.inl) ᵥ* C.Q) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    have e2 := congrArg (· ᵥ* C.B⁻¹) e
    simp only [vecMul_vecMul, mul_nonsing_inv _ hB, vecMul_one, neg_vecMul] at e2
    exact e2
  change (lam ∘ Sum.inl) ᵥ* (C.P - C.Q * C.B⁻¹ * C.T) = 0
  rw [hN, neg_vecMul, vecMul_vecMul, ← sub_eq_add_neg] at h1
  rw [vecMul_sub]
  exact h1

end FullPreComplex

/-! ### Relabelling for the cancellation of `N --B--> N` from degree one to degree two -/

section Relabel

variable (m0 m1 m2 : ℕ) (N : Type)

/-- Odd bases: `(D¹ ⊕ N) ⊕ (B₃ ⊕ K₃) ≃ (D¹ ⊕ (B₃ ⊕ K₃)) ⊕ N`. -/
def eOf : ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ N) ⊕ (Fin m2 ⊕ Unit) ≃
    ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ (Fin m2 ⊕ Unit)) ⊕ N where
  toFun
    | .inl (.inl c) => .inl (.inl c)
    | .inl (.inr n) => .inr n
    | .inr b => .inl (.inr b)
  invFun
    | .inl (.inl c) => .inl (.inl c)
    | .inl (.inr b) => .inr b
    | .inr n => .inl (.inr n)
  left_inv := by rintro ((c | n) | b) <;> rfl
  right_inv := by rintro ((c | b) | n) <;> rfl

/-- **The orientation of the full-condition pre-cancellation complex**: `σBlock` on the remaining
complex and the identity on the cancelled pair. -/
def σFull : (Fin m0 ⊕ Unit) ⊕ ((Fin m1 ⊕ Unit ⊕ Fin m2) ⊕ N) ≃
    ((Fin m0 ⊕ Unit ⊕ Fin m1) ⊕ N) ⊕ (Fin m2 ⊕ Unit) :=
  (eEp m0 m1 m2 N).trans (((σBlock m0 m1 m2).sumCongr (Equiv.refl N)).trans
    (eOf m0 m1 m2 N).symm)

end Relabel

/-! ### The cancellation -/

section Cancel

variable {K : Type} [Field K] {C : FullPreComplex K} (hB : IsUnit C.B.det)
  (z : C.D1 ⊕ C.N → K) (lam : C.D2 ⊕ C.N → K) (hz : C.toFour.d1 *ᵥ z = 0)
  (hlam : lam ᵥ* C.toFour.d1 = 0)

/-- The augmented full-condition complex, relabelled. -/
def Xf : BasedCx K (((Fin C.m0 ⊕ Unit) ⊕ C.D2) ⊕ C.N) ((C.D1 ⊕ (Fin C.m2 ⊕ Unit)) ⊕ C.N) :=
  (C.toFour.aug z lam hz hlam).toBased.reindex (eEp C.m0 C.m1 C.m2 C.N)
    (eOf C.m0 C.m1 C.m2 C.N)

theorem Xf_degO (n : C.N) : (Xf z lam hz hlam).degO (Sum.inr n) = 1 := rfl
theorem Xf_degE (n : C.N) : (Xf z lam hz hlam).degE (Sum.inr n) = 1 + 1 := rfl

theorem Xf_blk : (Xf z lam hz hlam).dEO.toBlocks₂₂ = C.B := by
  ext n m; rfl

variable {z lam hz hlam}

include hB in
theorem Xf_hA : IsUnit ((Xf z lam hz hlam).dEO.toBlocks₂₂).det := by
  rw [Xf_blk]; exact hB

/-- **The odd-to-even Schur complement of the relabelled augmented complex is the augmented
remaining complex** at the restricted cycle and functional. -/
theorem schurO_Xf :
    schurO (Xf z lam hz hlam) 1 (Xf_degO z lam hz hlam) (Xf_degE z lam hz hlam) (Xf_hA hB) =
      ((C.cancel hB).toFour.aug (z ∘ Sum.inl) (lam ∘ Sum.inl)
        (FullPreComplex.hz_full hB hz) (FullPreComplex.hlam_full hB hlam)).toBased := by
  apply BasedCx.ext'
  · funext x; rcases x with (a | a) | d <;> rfl
  · funext x; rcases x with c | (b | u) <;> rfl
  · ext i j
    rcases i with c | (b | u) <;> rcases j with (a | a) | d <;> rfl
  · change (Xf z lam hz hlam).dEO.toBlocks₁₁ - (Xf z lam hz hlam).dEO.toBlocks₁₂ *
        ((Xf z lam hz hlam).dEO.toBlocks₂₂)⁻¹ * (Xf z lam hz hlam).dEO.toBlocks₂₁ = _
    rw [Xf_blk]
    ext i j
    rcases i with (a | a) | d <;> rcases j with c | (b | u)
    all_goals first
      | rfl
      | (simp [Xf, BasedCx.reindex, FourCx.toBased_dEO, FourCx.aug, eEp, eOf, mul_apply,
          toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, FullPreComplex.toFour]; rfl)

/-- **The cancellation of the full-condition singular summands divides the Knudsen–Mumford
coordinate by `det B`** (tex 5509–5516, 5545–5595; the disk `N --B--> N` in degrees one and two):
`kmCoord(C, z, λ) = det(B)⁻¹ · kmCoord(C.cancel, z ∘ inl, λ ∘ inl)`. PROVED. -/
theorem kmCoord_fullCancel :
    kmCoord C.toFour z lam hz hlam (σFull C.m0 C.m1 C.m2 C.N) =
      (C.B.det)⁻¹ * kmCoord (C.cancel hB).toFour (z ∘ Sum.inl) (lam ∘ Sum.inl)
        (FullPreComplex.hz_full hB hz) (FullPreComplex.hlam_full hB hlam)
        (σBlock C.m0 C.m1 C.m2) := by
  unfold kmCoord
  have t0 : torsion (Xf z lam hz hlam) ((σBlock C.m0 C.m1 C.m2).sumCongr (Equiv.refl _)) =
      torsion (C.toFour.aug z lam hz hlam).toBased (σFull C.m0 C.m1 C.m2 C.N) := by
    have := torsion_reindex' (C.toFour.aug z lam hz hlam).toBased
      (σFull C.m0 C.m1 C.m2 C.N) (eEp C.m0 C.m1 C.m2 C.N) (eOf C.m0 C.m1 C.m2 C.N)
    rw [σFull, transport_eq] at this
    exact this
  have t1 := torsion_cancelO (Xf z lam hz hlam) 1 (Xf_degO z lam hz hlam)
    (Xf_degE z lam hz hlam) odd_one (Xf_hA hB) (σBlock C.m0 C.m1 C.m2)
  rw [← t0, t1, schurO_Xf hB, Xf_blk, mul_comm, mul_neg]
  rfl

end Cancel

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
