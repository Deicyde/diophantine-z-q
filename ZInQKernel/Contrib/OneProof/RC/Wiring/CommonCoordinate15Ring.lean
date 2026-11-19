import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10TwoSing

/-!
# The model of the relaxed complex over a commutative ring

Manuscript `diophantine_zq.tex`, the support triangle of Lemma `ex:arith-common-coordinate`
(tex 4157–4194) and the graded model of the inclusion with its quotient (tex 5398–5424), at the
finite coefficient stages of the inner limit (tex 4385–4451): coefficients in a commutative ring.

Round six's `relModel`, `relRetract` (`CommonCoordinate10Model.lean`) and the bases of the two
places (`CommonCoordinate10TwoSing.lean`) are stated over a field; their ingredients (lane RC31's
`splitRetract₂`, the split pre-cancellation complex `fullPreOfSplit`, its coordinates
`splitCoordL`, `triIncl`, `triQBasis`, `twoPlaceCoord`, `twoSing_matrix`) are over a commutative
ring. This file re-declares them over a commutative ring `A`:

* `triModelA`, `triModelInclA`, `relB1A`, `relB2A`, **`relModelA`**: the full-condition model of
  the relaxed complex (`c⁰ = d⁰`, `Y = 0`, `P = d¹`, `T = 0`, `U = d²`); `relModelA_B`: its new
  block is the matrix of the quotient differential;
* `relCoordEquivA`, `relCoordEquivA_comm`, **`relRetractA`**: the retract of the relaxed complex
  onto its model;
* `relRetractA_p_i_one`, `relRetractA_i_two_inl`, `funVec_relRetractA_inl`: the old part in model
  coordinates;
* `twoSingB1A`, `twoSingB2A`, **`toMatrix_twoSingA`**, `twoSing_subsingletonA`: the bases of the
  two places and the two-place block over a ring.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock)
open ZInQ.Manuscript.RC.Local (twoSingCx twoSingD12 twoPlaceCoord twoSingD12_eq twoSing_matrix)

section ModelA

variable {A : Type} [CommRing A] {CP CR : GCx A} (E : SplitInclusion CP CR) {D : BlockComplex A}
  (R : GRetract CP D.toGCx) {Q' : GCx A} (RQ : GRetract E.quotientCx Q') {N : Type} [Fintype N]
  [DecidableEq N] (b1 : Basis N A (Q'.X 1)) (b2 : Basis N A (Q'.X 2))

/-- The triangular model `D ⊕ Q'` of the relaxed complex over a ring (tex 5398–5403).
Kind: definition. -/
abbrev triModelA : GCx A :=
  triCx D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)

/-- The split inclusion `D ⊂ D ⊕ Q'` of the triangular model over a ring (tex 5398–5403).
Kind: definition. -/
abbrev triModelInclA : SplitInclusion D.toGCx (triModelA E R RQ) :=
  triIncl D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq)

/-- The basis of the degree-one complement of the model inclusion (tex 5398–5424).
Kind: definition. -/
abbrev relB1A : Basis N A ((triModelInclA E R RQ).Qc 1) :=
  triQBasis D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq) 1 b1

/-- The basis of the degree-two complement of the model inclusion (tex 5398–5424).
Kind: definition. -/
abbrev relB2A : Basis N A ((triModelInclA E R RQ).Qc 2) :=
  triQBasis D.toGCx Q' (R.triδ₂ RQ E.offDiag) (R.triδ₂_sq RQ E.offDiag E.offDiag_sq) 2 b2

/-- **The full-condition model of the relaxed complex over a ring** (tex 5398–5424): the matrices
of the triangular model `D ⊕ Q'` in the standard bases of `D` and the bases `b1, b2` of `Q'¹`,
`Q'²`. Kind: definition. -/
def relModelA : FullPreComplex A :=
  fullPreOfSplit D (triModelInclA E R RQ) (relB1A E R RQ b1) (relB2A E R RQ b2)

/-- **The new block of the model is the matrix of the quotient differential** (tex 5420–5424).
Kind: PROVED. -/
theorem relModelA_B : (relModelA E R RQ b1 b2).B = LinearMap.toMatrix b1 b2 (Q'.d 1 2 rfl) :=
  toMatrix_triIncl_dQ D.toGCx Q' _ _ b1 b2

variable (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))

include hQ' in
/-- The complements of the model inclusion vanish outside degrees one and two (tex 5398–5424).
Kind: PROVED. -/
theorem triModelInclA_Qc (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    (triModelInclA E R RQ).Qc n = ⊥ :=
  triIncl_Qc_eq_bot _ _ _ _ n (hQ' n h1 h2)

/-- **The comparison of the model with the triangular model**, a degreewise isomorphism
(tex 5398–5424). Kind: definition. -/
def relCoordEquivA (n : ℤ) :
    (relModelA E R RQ b1 b2).toGCx.X n ≃ₗ[A] (triModelA E R RQ).X n :=
  LinearEquiv.ofBijective (splitCoordL D (triModelInclA E R RQ) _ _ n)
    (splitCoordL_bijective D (triModelInclA E R RQ) _ _
      (fun m h1 h2 => triModelInclA_Qc E R RQ hQ' m h1 h2) n)

/-- The comparison commutes with the differentials (tex 5398–5424). Kind: PROVED. -/
theorem relCoordEquivA_comm (a b : ℤ) (h : a + 1 = b)
    (y : (relModelA E R RQ b1 b2).toGCx.X a) :
    (triModelA E R RQ).d a b h (relCoordEquivA E R RQ b1 b2 hQ' a y) =
      relCoordEquivA E R RQ b1 b2 hQ' b ((relModelA E R RQ b1 b2).toGCx.d a b h y) := by
  subst h
  exact (splitCoordL_comm D (triModelInclA E R RQ) _ _
    (triModelInclA_Qc E R RQ hQ' 3 (by omega) (by omega)) a y).symm

/-- **The retract of the relaxed complex onto its full-condition model, over a ring**
(tex 5398–5424, 4423–4437). Kind: definition. -/
def relRetractA : GRetract CR (relModelA E R RQ b1 b2).toGCx :=
  retractOfModelEquiv (splitRetract₂ E R RQ) (relCoordEquivA E R RQ b1 b2 hQ')
    (relCoordEquivA_comm E R RQ b1 b2 hQ')

omit [Fintype N] [DecidableEq N] in
/-- The block equivalence sends `(x, 0)` to `i x` (tex 5398–5403). Kind: PROVED. -/
theorem blockEquiv_symm_iA (n : ℤ) (x : CP.X n) :
    (E.blockEquiv n).symm (E.i.f n n rfl x) = (x, 0) := by
  rw [LinearEquiv.symm_apply_eq, SplitInclusion.blockEquiv_apply, ZeroMemClass.coe_zero,
    add_zero]

omit [Fintype N] [DecidableEq N] in
/-- The projection of `splitRetract₂` sends `i x` to `(p x, 0)` (tex 5398–5403).
Kind: PROVED. -/
theorem splitRetract₂_p_iA (n : ℤ) (x : CP.X n) :
    (splitRetract₂ E R RQ).p.f n n rfl (E.i.f n n rfl x) =
      ((R.p.f n n rfl x, 0) : D.toGCx.X n × Q'.X n) := by
  change (R.triExt₂ RQ E.offDiag E.offDiag_sq).p.f n n rfl ((E.blockEquiv n).symm
    (E.i.f n n rfl x)) = _
  rw [blockEquiv_symm_iA]
  refine (GRetract.triExt₂_p_apply R RQ E.offDiag E.offDiag_sq n x 0).trans ?_
  refine Prod.ext ?_ ?_
  · have h1 : (RQ.h n (n - 1) (by omega) 0 : E.Qc (n - 1)) = 0 := map_zero _
    have h2 : E.offDiag (n - 1) n (by omega) (RQ.h n (n - 1) (by omega) 0) = 0 :=
      (congrArg (E.offDiag (n - 1) n (by omega)) h1).trans (map_zero _)
    change R.p.f n n rfl x - R.p.f n n rfl (E.offDiag (n - 1) n (by omega)
      (RQ.h n (n - 1) (by omega) 0)) = R.p.f n n rfl x
    rw [h2, map_zero, sub_zero]
  · exact map_zero _

omit [Fintype N] [DecidableEq N] in
/-- The inclusion of `splitRetract₂` sends `(y, 0)` to `i (i_D y)` (tex 5398–5403).
Kind: PROVED. -/
theorem splitRetract₂_i_inlA (n : ℤ) (y : D.toGCx.X n) :
    (splitRetract₂ E R RQ).i.f n n rfl ((y, 0) : D.toGCx.X n × Q'.X n) =
      E.i.f n n rfl (R.i.f n n rfl y) := by
  change E.blockEquiv n ((R.triExt₂ RQ E.offDiag E.offDiag_sq).i.f n n rfl
    ((y, 0) : D.toGCx.X n × Q'.X n)) = _
  have h : (R.triExt₂ RQ E.offDiag E.offDiag_sq).i.f n n rfl
      ((y, 0) : D.toGCx.X n × Q'.X n) = ((R.i.f n n rfl y, 0) : CP.X n × E.quotientCx.X n) := by
    refine (GRetract.triExt₂_i_apply R RQ E.offDiag E.offDiag_sq n y 0).trans ?_
    refine Prod.ext ?_ ?_
    · have h1 : (RQ.i.f n n rfl 0 : E.Qc n) = 0 := map_zero _
      have h2 : E.offDiag n (n + 1) rfl (RQ.i.f n n rfl 0) = 0 :=
        (congrArg (E.offDiag n (n + 1) rfl) h1).trans (map_zero _)
      change R.i.f n n rfl y - R.h (n + 1) n rfl (E.offDiag n (n + 1) rfl
        (RQ.i.f n n rfl 0)) = R.i.f n n rfl y
      rw [h2, map_zero, sub_zero]
    · exact map_zero _
  rw [h]
  change E.blockEquiv n ((R.i.f n n rfl y, (0 : E.Qc n)) : CP.X n × E.Qc n) = _
  rw [SplitInclusion.blockEquiv_apply, ZeroMemClass.coe_zero, add_zero]

/-- The comparison sends `(y, 0)` in degree one to `(y, 0)` (tex 5398–5424). Kind: PROVED. -/
theorem relCoordEquivA_one_inl (y : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → A) :
    relCoordEquivA E R RQ b1 b2 hQ' 1 (Sum.elim y (0 : N → A)) =
      ((y, 0) : D.toGCx.X 1 × Q'.X 1) := by
  change (triModelInclA E R RQ).i.f 1 1 rfl y +
    ((relB1A E R RQ b1).equivFun.symm (0 : N → A) : (triModelA E R RQ).X 1) = _
  simp only [map_zero, ZeroMemClass.coe_zero, add_zero]
  rfl

/-- The comparison sends `(y, 0)` in degree two to `(y, 0)` (tex 5398–5424). Kind: PROVED. -/
theorem relCoordEquivA_two_inl (y : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → A) :
    relCoordEquivA E R RQ b1 b2 hQ' 2 (Sum.elim y (0 : N → A)) =
      ((y, 0) : D.toGCx.X 2 × Q'.X 2) := by
  change (triModelInclA E R RQ).i.f 2 2 rfl y +
    ((relB2A E R RQ b2).equivFun.symm (0 : N → A) : (triModelA E R RQ).X 2) = _
  simp only [map_zero, ZeroMemClass.coe_zero, add_zero]
  rfl

/-- **The model of an old cycle, over a ring**: the projection of the relaxed retract sends
`i x` to `(p x, 0)` (tex 4166–4170, 5398–5424). Kind: PROVED. -/
theorem relRetractA_p_i_one (x : CP.X 1) :
    (relRetractA E R RQ b1 b2 hQ').p.f 1 1 rfl (E.i.f 1 1 rfl x) =
      (Sum.elim (R.p.f 1 1 rfl x) (0 : N → A) : (relModelA E R RQ b1 b2).toGCx.X 1) := by
  rw [relRetractA, retractOfModelEquiv_p, splitRetract₂_p_iA]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  exact (relCoordEquivA_one_inl E R RQ b1 b2 hQ' _).symm

/-- **The model of an old functional, over a ring**: the inclusion of the relaxed retract sends
`(y, 0)` in degree two to `i (i_D y)` (tex 4166–4172, 5398–5424). Kind: PROVED. -/
theorem relRetractA_i_two_inl (y : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → A) :
    (relRetractA E R RQ b1 b2 hQ').i.f 2 2 rfl (Sum.elim y (0 : N → A)) =
      E.i.f 2 2 rfl (R.i.f 2 2 rfl y) := by
  change (splitRetract₂ E R RQ).i.f 2 2 rfl
    (relCoordEquivA E R RQ b1 b2 hQ' 2 (Sum.elim y 0)) = _
  exact (congrArg ((splitRetract₂ E R RQ).i.f 2 2 rfl)
    (relCoordEquivA_two_inl E R RQ b1 b2 hQ' y)).trans (splitRetract₂_i_inlA E R RQ 2 y)

omit [CommRing A] in
/-- A standard basis vector on the old part, over a ring (tex 5398–5424). Kind: PROVED. -/
theorem single_inl_eqA [CommRing A] {α β : Type} [DecidableEq α] [DecidableEq β] (j : α) :
    (Pi.single (Sum.inl j) (1 : A) : α ⊕ β → A) = Sum.elim (Pi.single j 1) 0 := by
  funext k
  rcases k with k | k
  · simp [Pi.single_apply]
  · simp

/-- **The model functional on the old part, over a ring** (tex 4166–4172). Kind: PROVED. -/
theorem funVec_relRetractA_inl (lam : CR.X 2 →ₗ[A] A) :
    funVec (ι := (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N)
        (lam ∘ₗ (relRetractA E R RQ b1 b2 hQ').i.f 2 2 rfl) ∘ Sum.inl =
      funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ((lam ∘ₗ E.i.f 2 2 rfl) ∘ₗ R.i.f 2 2 rfl) := by
  funext j
  change lam ((relRetractA E R RQ b1 b2 hQ').i.f 2 2 rfl
      (Pi.single (Sum.inl j) 1 : (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ⊕ N → A)) =
    lam (E.i.f 2 2 rfl (R.i.f 2 2 rfl (Pi.single j 1 : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → A)))
  rw [single_inl_eqA]
  exact congrArg lam (relRetractA_i_two_inl E R RQ b1 b2 hQ' _)

end ModelA

/-! ### The bases of the two places over a ring -/

section TwoSingA

variable {A : Type} [CommRing A] (Fr : Matrix (Fin 2) (Fin 2) A) (q : ℕ) (z zi : A)

/-- The basis of degree one of the two singular blocks over a ring (tex 4176–4184).
Kind: definition. -/
abbrev twoSingB1A : Basis (Fin 2 ⊕ Fin 2) A ((twoSingCx Fr q z zi).X 1) :=
  (Pi.basisFun A (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := A))

/-- The basis of degree two of the two singular blocks over a ring (tex 4176–4184).
Kind: definition. -/
abbrev twoSingB2A : Basis (Fin 2 ⊕ Fin 2) A ((twoSingCx Fr q z zi).X 2) :=
  (Pi.basisFun A (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := A))

/-- **The matrix of the two singular blocks is the two-place block, over a ring**
(tex 4176–4184): `twoPlaceBlock Fr q z z⁻¹ = diag(z Fr − q, z⁻¹ Fr − q)` in the coordinates of the
two places. Kind: PROVED. -/
theorem toMatrix_twoSingA :
    LinearMap.toMatrix (twoSingB1A Fr q z zi) (twoSingB2A Fr q z zi)
        ((twoSingCx Fr q z zi).d 1 2 rfl) = twoPlaceBlock Fr (q : A) z zi := by
  rw [← twoSing_matrix Fr q z zi]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply]
  have hb1 : (twoSingB1A Fr q z zi) j =
      (twoPlaceCoord (A := A) (Pi.single j 1) : (twoSingCx Fr q z zi).X 1) := by
    change ((Pi.basisFun A (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := A))) j = _
    rw [Basis.map_apply, Pi.basisFun_apply]
  have hrepr : ∀ x : (Fin 2 → A) × (Fin 2 → A),
      ((Pi.basisFun A (Fin 2 ⊕ Fin 2)).map (twoPlaceCoord (A := A))).repr x i =
        (twoPlaceCoord (A := A)).symm x i := fun x => by
    rw [Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr]
  rw [hb1]
  refine (hrepr _).trans ?_
  have e2 := congrArg (twoPlaceCoord (A := A)).symm (twoSingD12_eq Fr q z zi (Pi.single j 1))
  rw [LinearEquiv.symm_apply_apply] at e2
  exact congrFun e2.symm i

/-- The two singular blocks vanish outside degrees one and two, over a ring (tex 4176–4184).
Kind: PROVED. -/
theorem twoSing_subsingletonA (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((twoSingCx Fr q z zi).X n) := by
  have h : ∀ (Φ : (Fin 2 → A) →ₗ[A] (Fin 2 → A)),
      Subsingleton ((ZInQ.Manuscript.RC.Local.singCx Φ q).X n) := fun Φ => by
    rcases n with (_ | _ | _ | n) | n
    · exact inferInstanceAs (Subsingleton PUnit)
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact inferInstanceAs (Subsingleton PUnit)
    · exact inferInstanceAs (Subsingleton PUnit)
  change Subsingleton ((ZInQ.Manuscript.RC.Local.singCx (Matrix.toLin' (z • Fr)) q).X n ×
    (ZInQ.Manuscript.RC.Local.singCx (Matrix.toLin' (zi • Fr)) q).X n)
  infer_instance

end TwoSingA

end ZInQ.Manuscript.RC.Wiring
