import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Chain

/-!
# Independence of the order of the primes: graded changes of basis of the coordinate

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4185–4193):

> To see the unit assertion, retain the finite mapping-cone bases. Their comparison is a sign;
> replacing them by the retained homotopy equivalent free models contributes only determinants of
> unit disks.

The Knudsen–Mumford coordinate `kmCoord C z λ σ` is minus the torsion of the augmented complex
`C⁰ ⊕ R --(d⁰, z)--> C¹ --d¹--> C² --(d², λ)--> C³ ⊕ R`. This file computes how it changes under
a graded change of basis of `C`, over a domain `R` (in particular over a field).

* `torsion_rebase_domain`: lane Torsion's change-of-basis formula for the torsion
  (`τ(C') = det P_od · τ(C) · det Q_ev`) over a domain, with no contraction hypothesis.
* `FourBasisChange`, `fourRebase`: invertible matrices `P₀, …, P₃` (inverses `Q₀, …, Q₃`) and the
  conjugated complex `(P₁ d⁰ Q₀, P₂ d¹ Q₁, P₃ d² Q₂)`; the cycle is carried to `P₁ z`, the closed
  functional to `λ Q₂` (`fourRebase_cycle`, `fourRebase_closed`).
* `aug_fourRebase`: the augmented complex of the new complex is the new augmented complex, for
  the change of basis `diag(P₀, 1), P₁, P₂, diag(P₃, 1)` (`FourBasisChange.aug`): the augmentation
  lines are unchanged. On the based complex this is `diag(P₀, 1) ⊕ P₂` on the even part
  `(C⁰ ⊕ R) ⊕ C²` and `P₁ ⊕ diag(P₃, 1)` on the odd part `C¹ ⊕ (C³ ⊕ R)`
  (`FourBasisChange.toGraded`, `toBased_fourRebase`).
* **(a)** `kmCoord_fourRebase`: `u' = det P₁ det P₃ det Q₀ det Q₂ · u`; cleared form
  `kmCoord_fourRebase_mul`: `det P₀ det P₂ · u' = det P₁ det P₃ · u` (the sign pattern
  `∏_k (det P_k)^{(−1)^{k+1}}` of lane Torsion's `tau_rebase_graded`); over a field
  `kmCoord_fourRebase_div`: `u' = det P₁ det P₃ / (det P₀ det P₂) · u`.
* **(b)** `kmCoord_fourRebase_of_det_eq_one`: if every `det P_k = 1` the coordinate is unchanged;
  `kmCoord_fourRebase_sign`: if every `det P_k = ±1` it changes by a sign.
* **(c)** `IsBlockUnipotent`: block triangular for an integer labelling of the basis, with
  identity diagonal blocks (upper or lower); `IsBlockUnipotent.det_eq_one`;
  `isBlockUnipotent_fromBlocks_upper`, `isBlockUnipotent_fromBlocks_lower` (`[[1, X], [0, 1]]`,
  `[[1, 0], [Y, 1]]` for a decomposition `A ⊕ B`); `kmCoord_fourRebase_of_isBlockUnipotent` (all
  four degrees at once) and the explicit two-block version `kmCoord_unipotentChange`.
* **Chain isomorphisms.** `kmCoord_chainIso`: if `C'` and `C` are related by a chain isomorphism
  `P` (`d' P = P d` in each degree) carrying `z` to `z'` and `λ'` to `λ` (`z' = P₁ z`,
  `λ' P₂ = λ`), then `u' = det P₁ det P₃ det Q₀ det Q₂ · u`; `kmCoord_chainIso_sign` (unit
  determinants: a sign) and **`kmCoord_chainIso_blockUnipotent`** (block unipotent matrices: the
  coordinate is unchanged); `kmCoord_reindex_fourRebase_sign`: after a further relabelling of the
  bases and in arbitrary orientations, the comparison is still a sign.

**What this gives for the order of the primes.** Two iterated cone models of one support (the
primes adjoined in two orders), related by a chain isomorphism whose matrices are block unipotent
and which carries the class and the functional of one model to those of the other, have the same
Knudsen–Mumford coordinate (`kmCoord_chainIso_blockUnipotent`); with unit determinants, or after a
relabelling of the bases and a change of orientation, the two coordinates differ by a sign
(`kmCoord_chainIso_sign`, `kmCoord_reindex_fourRebase_sign`). This is the algebraic core of
"their comparison is a sign".

**What is not done here.** The chain isomorphism between the two cone models is not constructed:
this file does not show that the iterated cone models of one support built in two orders of the
primes are related by a block unipotent (or unit determinant) chain isomorphism carrying the
classes to each other; that comparison is an input of the statements above.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion

/-! ### The torsion under a graded change of basis, over a domain -/

section Domain

variable {R : Type} [CommRing R] {κe κo : Type} [Fintype κe] [Fintype κo] [DecidableEq κe]
  [DecidableEq κo]

/-- **The inverse of a graded change of basis**, as a graded change of basis of the new complex
(tex 4185–4193). Kind: definition. -/
def gradedChangeInv {C : BasedCx R κe κo} (P : GradedBasisChange C) :
    GradedBasisChange (C.rebase P) where
  Pe := P.Qe
  Qe := P.Pe
  Po := P.Qo
  Qo := P.Po
  hPQe := mul_eq_one_comm.mp P.hPQe
  hPQo := mul_eq_one_comm.mp P.hPQo
  deg_Pe := P.deg_Qe
  deg_Qe := P.deg_Pe
  deg_Po := P.deg_Qo
  deg_Qo := P.deg_Po

/-- Changing the basis back recovers the complex (tex 4185–4193). Kind: PROVED. -/
theorem rebase_gradedChangeInv (C : BasedCx R κe κo) (P : GradedBasisChange C) :
    (C.rebase P).rebase (gradedChangeInv P) = C := by
  have hE : P.Qe * P.Pe = 1 := mul_eq_one_comm.mp P.hPQe
  have hO : P.Qo * P.Po = 1 := mul_eq_one_comm.mp P.hPQo
  apply BasedCx.ext'
  · rfl
  · rfl
  · change P.Qo * (P.Po * C.dOE * P.Qe) * P.Pe = C.dOE
    simp only [Matrix.mul_assoc]
    rw [hE, Matrix.mul_one, ← Matrix.mul_assoc, hO, Matrix.one_mul]
  · change P.Qe * (P.Pe * C.dEO * P.Qo) * P.Po = C.dEO
    simp only [Matrix.mul_assoc]
    rw [hO, Matrix.mul_one, ← Matrix.mul_assoc, hE, Matrix.one_mul]

/-- **A graded change of basis multiplies the torsion by `det P_od · det Q_ev`**, over a domain
and with no contraction hypothesis (tex 4185–4193; lane Torsion's `tau_rebase`; the complex is
contractible exactly when the rebased complex is). Kind: PROVED. -/
theorem torsion_rebase_domain [IsDomain R] (C : BasedCx R κe κo) (P : GradedBasisChange C)
    (σ : κe ≃ κo) : torsion (C.rebase P) σ = P.Po.det * torsion C σ * P.Qe.det := by
  by_cases hC : Nonempty (Contraction C)
  · obtain ⟨h⟩ := hC
    rw [← tau_eq_torsion _ (h.rebase P), ← tau_eq_torsion _ h, tau_rebase]
  · have hC' : ¬ Nonempty (Contraction (C.rebase P)) := by
      rintro ⟨h⟩
      exact hC ⟨rebase_gradedChangeInv C P ▸ h.rebase (gradedChangeInv P)⟩
    unfold torsion
    simp only [hC, hC', dite_false, mul_zero, zero_mul]

end Domain

/-! ### Graded changes of basis of a four-term complex -/

/-- **A graded change of basis of a four-term complex** (tex 4185–4193): invertible matrices
`P₀, …, P₃` on the bases of `C⁰, …, C³`, with given inverses `Q₀, …, Q₃` (`P_k Q_k = 1`).
Kind: definition. -/
structure FourBasisChange (R : Type) [CommRing R] (ι0 ι1 ι2 ι3 : Type) [Fintype ι0]
    [Fintype ι1] [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
    [DecidableEq ι3] where
  P0 : Matrix ι0 ι0 R
  Q0 : Matrix ι0 ι0 R
  P1 : Matrix ι1 ι1 R
  Q1 : Matrix ι1 ι1 R
  P2 : Matrix ι2 ι2 R
  Q2 : Matrix ι2 ι2 R
  P3 : Matrix ι3 ι3 R
  Q3 : Matrix ι3 ι3 R
  h0 : P0 * Q0 = 1
  h1 : P1 * Q1 = 1
  h2 : P2 * Q2 = 1
  h3 : P3 * Q3 = 1

section Four

variable {R : Type} [CommRing R] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

omit [Fintype ι0] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2]
  [DecidableEq ι3] in
/-- Two four-term complexes with the same differentials are equal (tex 4185–4193).
Kind: PROVED. -/
theorem fourCx_eq {C C' : FourCx R ι0 ι1 ι2 ι3} (h0 : C.d0 = C'.d0) (h1 : C.d1 = C'.d1)
    (h2 : C.d2 = C'.d2) : C = C' := by
  cases C
  cases C'
  simp only at h0 h1 h2
  subst h0 h1 h2
  rfl

/-- **The four-term complex in the new bases** (tex 4185–4193): `d⁰' = P₁ d⁰ Q₀`,
`d¹' = P₂ d¹ Q₁`, `d²' = P₃ d² Q₂`. Kind: definition. -/
def fourRebase (C : FourCx R ι0 ι1 ι2 ι3) (P : FourBasisChange R ι0 ι1 ι2 ι3) :
    FourCx R ι0 ι1 ι2 ι3 where
  d0 := P.P1 * C.d0 * P.Q0
  d1 := P.P2 * C.d1 * P.Q1
  d2 := P.P3 * C.d2 * P.Q2
  d10 := by
    have e : P.Q1 * P.P1 = 1 := mul_eq_one_comm.mp P.h1
    calc P.P2 * C.d1 * P.Q1 * (P.P1 * C.d0 * P.Q0)
        = P.P2 * (C.d1 * (P.Q1 * P.P1) * C.d0) * P.Q0 := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [e, Matrix.mul_one, C.d10, Matrix.mul_zero, Matrix.zero_mul]
  d21 := by
    have e : P.Q2 * P.P2 = 1 := mul_eq_one_comm.mp P.h2
    calc P.P3 * C.d2 * P.Q2 * (P.P2 * C.d1 * P.Q1)
        = P.P3 * (C.d2 * (P.Q2 * P.P2) * C.d1) * P.Q1 := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [e, Matrix.mul_one, C.d21, Matrix.mul_zero, Matrix.zero_mul]

/-- The transported cycle `P₁ z` is a cycle of the new complex (tex 4185–4193). Kind: PROVED. -/
theorem fourRebase_cycle (C : FourCx R ι0 ι1 ι2 ι3) (P : FourBasisChange R ι0 ι1 ι2 ι3)
    {z : ι1 → R} (hz : C.d1 *ᵥ z = 0) : (fourRebase C P).d1 *ᵥ (P.P1 *ᵥ z) = 0 := by
  have e : P.Q1 * P.P1 = 1 := mul_eq_one_comm.mp P.h1
  change (P.P2 * C.d1 * P.Q1) *ᵥ (P.P1 *ᵥ z) = 0
  rw [mulVec_mulVec]
  simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_one, ← mulVec_mulVec, hz, mulVec_zero]

/-- The transported functional `λ Q₂` is closed for the new complex (tex 4185–4193).
Kind: PROVED. -/
theorem fourRebase_closed (C : FourCx R ι0 ι1 ι2 ι3) (P : FourBasisChange R ι0 ι1 ι2 ι3)
    {lam : ι2 → R} (hlam : lam ᵥ* C.d1 = 0) : (lam ᵥ* P.Q2) ᵥ* (fourRebase C P).d1 = 0 := by
  have e : P.Q2 * P.P2 = 1 := mul_eq_one_comm.mp P.h2
  change (lam ᵥ* P.Q2) ᵥ* (P.P2 * C.d1 * P.Q1) = 0
  rw [vecMul_vecMul]
  simp only [← Matrix.mul_assoc]
  rw [e, Matrix.one_mul, ← vecMul_vecMul, hlam, zero_vecMul]

/-- **The change of basis of the augmented complex** (tex 4185–4193): `diag(P₀, 1)` in degree
zero, `diag(P₃, 1)` in degree three, `P₁` and `P₂` unchanged; the augmentation lines are not
moved. Kind: definition. -/
def FourBasisChange.aug (P : FourBasisChange R ι0 ι1 ι2 ι3) :
    FourBasisChange R (ι0 ⊕ Unit) ι1 ι2 (ι3 ⊕ Unit) where
  P0 := fromBlocks P.P0 0 0 1
  Q0 := fromBlocks P.Q0 0 0 1
  P1 := P.P1
  Q1 := P.Q1
  P2 := P.P2
  Q2 := P.Q2
  P3 := fromBlocks P.P3 0 0 1
  Q3 := fromBlocks P.Q3 0 0 1
  h0 := by rw [fromBlocks_multiply]; simp [P.h0, fromBlocks_one]
  h1 := P.h1
  h2 := P.h2
  h3 := by rw [fromBlocks_multiply]; simp [P.h3, fromBlocks_one]

omit [Fintype ι0] [DecidableEq ι0] in
/-- Every square matrix is homogeneous of degree zero for a constant grading (tex 4185–4193).
Kind: PROVED. -/
theorem hasDeg_const (X : Matrix ι0 ι0 R) (a : ℤ) : HasDeg X (fun _ => a) (fun _ => a) 0 :=
  fun _ _ _ => (add_zero a).symm

/-- **The graded change of basis of the based complex** of a four-term complex
(tex 4185–4193): `diag(P₀, P₂)` on the even part `C⁰ ⊕ C²`, `diag(P₁, P₃)` on the odd part
`C¹ ⊕ C³`. Kind: definition. -/
def FourBasisChange.toGraded (P : FourBasisChange R ι0 ι1 ι2 ι3) (C : FourCx R ι0 ι1 ι2 ι3) :
    GradedBasisChange C.toBased where
  Pe := fromBlocks P.P0 0 0 P.P2
  Qe := fromBlocks P.Q0 0 0 P.Q2
  Po := fromBlocks P.P1 0 0 P.P3
  Qo := fromBlocks P.Q1 0 0 P.Q3
  hPQe := by rw [fromBlocks_multiply]; simp [P.h0, P.h2, fromBlocks_one]
  hPQo := by rw [fromBlocks_multiply]; simp [P.h1, P.h3, fromBlocks_one]
  deg_Pe := hasDeg_fromBlocks (hasDeg_const P.P0 0) (hasDeg_const P.P2 2)
  deg_Qe := hasDeg_fromBlocks (hasDeg_const P.Q0 0) (hasDeg_const P.Q2 2)
  deg_Po := hasDeg_fromBlocks (hasDeg_const P.P1 1) (hasDeg_const P.P3 3)
  deg_Qo := hasDeg_fromBlocks (hasDeg_const P.Q1 1) (hasDeg_const P.Q3 3)

/-- **The based complex of the new four-term complex is the rebased based complex**
(tex 4185–4193). Kind: PROVED. -/
theorem toBased_fourRebase (C : FourCx R ι0 ι1 ι2 ι3) (P : FourBasisChange R ι0 ι1 ι2 ι3) :
    (fourRebase C P).toBased = C.toBased.rebase (P.toGraded C) := by
  refine BasedCx.ext' rfl rfl ?_ ?_
  · change fromBlocks (P.P1 * C.d0 * P.Q0) 0 0 (P.P3 * C.d2 * P.Q2) =
      fromBlocks P.P1 0 0 P.P3 * fromBlocks C.d0 0 0 C.d2 * fromBlocks P.Q0 0 0 P.Q2
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp
  · change fromBlocks 0 0 (P.P2 * C.d1 * P.Q1) 0 =
      fromBlocks P.P0 0 0 P.P2 * fromBlocks 0 0 C.d1 0 * fromBlocks P.Q1 0 0 P.Q3
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp

/-- **The augmented complex of the new complex is the new augmented complex** (tex 4185–4193):
with the cycle `P₁ z` and the functional `λ Q₂` it is the original augmented complex in the bases
`diag(P₀, 1), P₁, P₂, diag(P₃, 1)`. Kind: PROVED. -/
theorem aug_fourRebase (C : FourCx R ι0 ι1 ι2 ι3) (P : FourBasisChange R ι0 ι1 ι2 ι3)
    {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) :
    (fourRebase C P).aug (P.P1 *ᵥ z) (lam ᵥ* P.Q2) (fourRebase_cycle C P hz)
        (fourRebase_closed C P hlam) = fourRebase (C.aug z lam hz hlam) P.aug := by
  apply fourCx_eq
  · change fromCols (P.P1 * C.d0 * P.Q0) (replicateCol Unit (P.P1 *ᵥ z)) =
      P.P1 * fromCols C.d0 (replicateCol Unit z) * fromBlocks P.Q0 0 0 1
    rw [mul_fromCols, fromCols_mul_fromBlocks, replicateCol_mulVec]
    simp
  · rfl
  · change fromRows (P.P3 * C.d2 * P.Q2) (replicateRow Unit (lam ᵥ* P.Q2)) =
      fromBlocks P.P3 0 0 1 * fromRows C.d2 (replicateRow Unit lam) * P.Q2
    rw [fromBlocks_mul_fromRows, fromRows_mul, replicateRow_vecMul]
    simp

/-- **The torsion of a four-term complex under a graded change of basis** (tex 4185–4193): it is
multiplied by `det P₁ det P₃ · det Q₀ det Q₂` (lane Torsion's `tau_rebase_graded`: odd degrees in
the numerator, even degrees in the denominator). Kind: PROVED. -/
theorem torsion_toBased_fourRebase [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) (σ : ι0 ⊕ ι2 ≃ ι1 ⊕ ι3) :
    torsion (fourRebase C P).toBased σ =
      P.P1.det * P.P3.det * torsion C.toBased σ * (P.Q0.det * P.Q2.det) := by
  rw [toBased_fourRebase, torsion_rebase_domain]
  change (fromBlocks P.P1 0 0 P.P3).det * torsion C.toBased σ *
    (fromBlocks P.Q0 0 0 P.Q2).det = _
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]

/-! ### (a) The coordinate under a graded change of basis -/

/-- **(a) Graded change of basis of the Knudsen–Mumford coordinate** (tex 4185–4193): for the
conjugated complex `(P₁ d⁰ Q₀, P₂ d¹ Q₁, P₃ d² Q₂)`, the cycle `P₁ z` and the functional `λ Q₂`,
`u' = det P₁ · det P₃ · det Q₀ · det Q₂ · u`, in the same orientation `σ`. The augmented complex
is rebased by `diag(P₀, 1) ⊕ P₂` (even part) and `P₁ ⊕ diag(P₃, 1)` (odd part), so the
augmentation lines contribute nothing. Kind: PROVED. -/
theorem kmCoord_fourRebase [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord (fourRebase C P) (P.P1 *ᵥ z) (lam ᵥ* P.Q2) (fourRebase_cycle C P hz)
        (fourRebase_closed C P hlam) σ =
      P.P1.det * P.P3.det * P.Q0.det * P.Q2.det * kmCoord C z lam hz hlam σ := by
  unfold kmCoord
  rw [aug_fourRebase C P hz hlam, torsion_toBased_fourRebase]
  change -(P.P1.det * (fromBlocks P.P3 0 0 1 : Matrix (ι3 ⊕ Unit) (ι3 ⊕ Unit) R).det *
      torsion (C.aug z lam hz hlam).toBased σ *
      ((fromBlocks P.Q0 0 0 1 : Matrix (ι0 ⊕ Unit) (ι0 ⊕ Unit) R).det * P.Q2.det)) = _
  simp only [det_fromBlocks_zero₂₁, det_one, mul_one]
  ring

/-- **(a), cleared form** (tex 4185–4193): `det P₀ det P₂ · u' = det P₁ det P₃ · u`, the sign
pattern `∏_k (det P_k)^{(−1)^{k+1}}` of lane Torsion's `tau_rebase_graded`. Kind: PROVED. -/
theorem kmCoord_fourRebase_mul [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    P.P0.det * P.P2.det * kmCoord (fourRebase C P) (P.P1 *ᵥ z) (lam ᵥ* P.Q2)
        (fourRebase_cycle C P hz) (fourRebase_closed C P hlam) σ =
      P.P1.det * P.P3.det * kmCoord C z lam hz hlam σ := by
  have e0 : P.P0.det * P.Q0.det = 1 := by rw [← det_mul, P.h0, det_one]
  have e2 : P.P2.det * P.Q2.det = 1 := by rw [← det_mul, P.h2, det_one]
  rw [kmCoord_fourRebase C P hz hlam σ]
  linear_combination (P.P1.det * P.P3.det * kmCoord C z lam hz hlam σ * P.P2.det * P.Q2.det) *
    e0 + (P.P1.det * P.P3.det * kmCoord C z lam hz hlam σ) * e2

/-- **(a), field form** (tex 4185–4193): over a field,
`u' = det P₁ det P₃ / (det P₀ det P₂) · u`. Kind: PROVED. -/
theorem kmCoord_fourRebase_div {K : Type} [Field K] (C : FourCx K ι0 ι1 ι2 ι3)
    (P : FourBasisChange K ι0 ι1 ι2 ι3) {z : ι1 → K} {lam : ι2 → K} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord (fourRebase C P) (P.P1 *ᵥ z) (lam ᵥ* P.Q2) (fourRebase_cycle C P hz)
        (fourRebase_closed C P hlam) σ =
      P.P1.det * P.P3.det / (P.P0.det * P.P2.det) * kmCoord C z lam hz hlam σ := by
  have e0 : P.P0.det * P.Q0.det = 1 := by rw [← det_mul, P.h0, det_one]
  have e2 : P.P2.det * P.Q2.det = 1 := by rw [← det_mul, P.h2, det_one]
  rw [kmCoord_fourRebase C P hz hlam σ, ← inv_eq_of_mul_eq_one_right e0,
    ← inv_eq_of_mul_eq_one_right e2, div_eq_mul_inv, mul_inv]
  ring

/-! ### (b) Unit determinants -/

/-- **(b) Determinant one** (tex 4185–4193): if `det P_k = 1` in every degree, the coordinate is
unchanged. Kind: PROVED. -/
theorem kmCoord_fourRebase_of_det_eq_one [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) (h0 : P.P0.det = 1) (h1 : P.P1.det = 1)
    (h2 : P.P2.det = 1) (h3 : P.P3.det = 1) {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord (fourRebase C P) (P.P1 *ᵥ z) (lam ᵥ* P.Q2) (fourRebase_cycle C P hz)
        (fourRebase_closed C P hlam) σ = kmCoord C z lam hz hlam σ := by
  have e0 : P.Q0.det = 1 := by
    have e := congrArg det P.h0
    rwa [det_mul, det_one, h0, one_mul] at e
  have e2 : P.Q2.det = 1 := by
    have e := congrArg det P.h2
    rwa [det_mul, det_one, h2, one_mul] at e
  rw [kmCoord_fourRebase C P hz hlam σ, h1, h3, e0, e2]
  ring

omit [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1]
  [DecidableEq ι2] [DecidableEq ι3] in
/-- A scalar `±1` is the image of a unit of `ℤ` (tex 4185–4193). Kind: PROVED. -/
theorem exists_intUnit_of_pm_one {a : R} (h : a = 1 ∨ a = -1) : ∃ ε : ℤˣ, a = (ε : R) := by
  rcases h with h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

omit [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1]
  [DecidableEq ι2] [DecidableEq ι3] in
/-- The inverse of `±1` is itself (tex 4185–4193). Kind: PROVED. -/
theorem eq_of_mul_eq_one_of_pm_one {a b : R} (hab : a * b = 1) (h : a = 1 ∨ a = -1) : b = a := by
  rcases h with h | h
  · subst h
    rw [one_mul] at hab
    exact hab
  · subst h
    linear_combination -hab

/-- **(b) Unit determinants: a sign** (tex 4185–4193: "their comparison is a sign"): if
`det P_k = ±1` in every degree, the coordinate changes by a sign. Kind: PROVED. -/
theorem kmCoord_fourRebase_sign [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) (h0 : P.P0.det = 1 ∨ P.P0.det = -1)
    (h1 : P.P1.det = 1 ∨ P.P1.det = -1) (h2 : P.P2.det = 1 ∨ P.P2.det = -1)
    (h3 : P.P3.det = 1 ∨ P.P3.det = -1) {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    ∃ ε : ℤˣ, kmCoord (fourRebase C P) (P.P1 *ᵥ z) (lam ᵥ* P.Q2) (fourRebase_cycle C P hz)
        (fourRebase_closed C P hlam) σ = (ε : R) * kmCoord C z lam hz hlam σ := by
  have e0 : P.Q0.det = P.P0.det :=
    eq_of_mul_eq_one_of_pm_one (by rw [← det_mul, P.h0, det_one]) h0
  have e2 : P.Q2.det = P.P2.det :=
    eq_of_mul_eq_one_of_pm_one (by rw [← det_mul, P.h2, det_one]) h2
  obtain ⟨ε0, f0⟩ := exists_intUnit_of_pm_one h0
  obtain ⟨ε1, f1⟩ := exists_intUnit_of_pm_one h1
  obtain ⟨ε2, f2⟩ := exists_intUnit_of_pm_one h2
  obtain ⟨ε3, f3⟩ := exists_intUnit_of_pm_one h3
  refine ⟨ε1 * ε3 * ε0 * ε2, ?_⟩
  rw [kmCoord_fourRebase C P hz hlam σ, e0, e2, f0, f1, f2, f3]
  push_cast
  ring

end Four

/-! ### (c) Block unipotent changes of basis -/

section Unipotent

variable {R : Type} [CommRing R]

/-- **Block unipotent matrices** (tex 4185–4193): `P` is block triangular for some labelling `b`
of the basis by integers (the entries from a later block to an earlier block vanish), with
identity diagonal blocks. A lower block triangular matrix is the case of the labelling `−b`.
Kind: definition. -/
def IsBlockUnipotent {ι : Type} [DecidableEq ι] (P : Matrix ι ι R) : Prop :=
  ∃ b : ι → ℤ, P.BlockTriangular b ∧ ∀ i j, b i = b j → P i j = (1 : Matrix ι ι R) i j

/-- **A block unipotent matrix has determinant one** (tex 4185–4193; Mathlib's
`Matrix.BlockTriangular.det`). Kind: PROVED. -/
theorem IsBlockUnipotent.det_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι R}
    (hP : IsBlockUnipotent P) : P.det = 1 := by
  obtain ⟨b, hb, hd⟩ := hP
  rw [hb.det]
  refine Finset.prod_eq_one fun k _ => ?_
  have hk : P.toSquareBlock b k = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have e := hd i j (hi.trans hj.symm)
    simp only [toSquareBlock_def, of_apply, e]
    by_cases h : i = j
    · subst h
      simp
    · rw [one_apply_ne h, one_apply_ne (fun e' => h (congrArg Subtype.val e'))]
  rw [hk, det_one]

/-- **Upper block unipotent matrices** `[[1, X], [0, 1]]` for a decomposition `A ⊕ B`
(tex 4185–4193). Kind: PROVED. -/
theorem isBlockUnipotent_fromBlocks_upper {A B : Type} [DecidableEq A] [DecidableEq B]
    (X : Matrix A B R) : IsBlockUnipotent (fromBlocks 1 X 0 1 : Matrix (A ⊕ B) (A ⊕ B) R) := by
  refine ⟨Sum.elim (fun _ => 0) (fun _ => 1), upper_two_blockTriangular _ _ _ zero_lt_one, ?_⟩
  rintro (i | i) (j | j) h
  · rw [← fromBlocks_one]
    rfl
  · simp at h
  · simp at h
  · rw [← fromBlocks_one]
    rfl

/-- **Lower block unipotent matrices** `[[1, 0], [Y, 1]]` for a decomposition `A ⊕ B`
(tex 4185–4193). Kind: PROVED. -/
theorem isBlockUnipotent_fromBlocks_lower {A B : Type} [DecidableEq A] [DecidableEq B]
    (Y : Matrix B A R) : IsBlockUnipotent (fromBlocks 1 0 Y 1 : Matrix (A ⊕ B) (A ⊕ B) R) := by
  refine ⟨Sum.elim (fun _ => 1) (fun _ => 0), ?_, ?_⟩
  · rintro (i | i) (j | j) h
    · simp at h
    · rfl
    · simp at h
    · simp at h
  · rintro (i | i) (j | j) h
    · rw [← fromBlocks_one]
      rfl
    · simp at h
    · simp at h
    · rw [← fromBlocks_one]
      rfl

/-- **Relabelling a block unipotent matrix** keeps it block unipotent (tex 4185–4193).
Kind: PROVED. -/
theorem IsBlockUnipotent.submatrix_equiv {ι ι' : Type} [DecidableEq ι] [DecidableEq ι']
    {P : Matrix ι ι R} (hP : IsBlockUnipotent P) (e : ι' ≃ ι) :
    IsBlockUnipotent (P.submatrix e e) := by
  obtain ⟨b, hb, hd⟩ := hP
  refine ⟨b ∘ e, hb.submatrix, fun i j h => ?_⟩
  rw [submatrix_apply, hd (e i) (e j) h, ← submatrix_apply (1 : Matrix ι ι R) e e i j,
    submatrix_one_equiv]

/-- The inverse of `[[1, X], [0, 1]]` is `[[1, −X], [0, 1]]` (tex 4185–4193). Kind: PROVED. -/
theorem fromBlocks_upper_mul_neg {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (X : Matrix A B R) :
    (fromBlocks 1 X 0 1 : Matrix (A ⊕ B) (A ⊕ B) R) * fromBlocks 1 (-X) 0 1 = 1 := by
  rw [fromBlocks_multiply]
  simp [fromBlocks_one]

end Unipotent

section FourUnipotent

variable {R : Type} [CommRing R] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- **(c) Block unipotent changes of basis in all four degrees** (tex 4185–4193): if every
`P_k` is block unipotent, the coordinate is unchanged. Kind: PROVED. -/
theorem kmCoord_fourRebase_of_isBlockUnipotent [IsDomain R] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) (u0 : IsBlockUnipotent P.P0)
    (u1 : IsBlockUnipotent P.P1) (u2 : IsBlockUnipotent P.P2) (u3 : IsBlockUnipotent P.P3)
    {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord (fourRebase C P) (P.P1 *ᵥ z) (lam ᵥ* P.Q2) (fourRebase_cycle C P hz)
        (fourRebase_closed C P hlam) σ = kmCoord C z lam hz hlam σ :=
  kmCoord_fourRebase_of_det_eq_one C P u0.det_eq_one u1.det_eq_one u2.det_eq_one u3.det_eq_one
    hz hlam σ

/-- **A graded change of basis from matrices of unit determinant** (tex 4185–4193): the inverses
are the inverse matrices. Kind: definition. -/
def FourBasisChange.ofIsUnit (P0 : Matrix ι0 ι0 R) (P1 : Matrix ι1 ι1 R) (P2 : Matrix ι2 ι2 R)
    (P3 : Matrix ι3 ι3 R) (u0 : IsUnit P0.det) (u1 : IsUnit P1.det) (u2 : IsUnit P2.det)
    (u3 : IsUnit P3.det) : FourBasisChange R ι0 ι1 ι2 ι3 where
  P0 := P0
  Q0 := P0⁻¹
  P1 := P1
  Q1 := P1⁻¹
  P2 := P2
  Q2 := P2⁻¹
  P3 := P3
  Q3 := P3⁻¹
  h0 := mul_nonsing_inv P0 u0
  h1 := mul_nonsing_inv P1 u1
  h2 := mul_nonsing_inv P2 u2
  h3 := mul_nonsing_inv P3 u3

end FourUnipotent

section TwoBlock

variable {R : Type} [CommRing R] {A0 B0 A1 B1 A2 B2 A3 B3 : Type} [Fintype A0] [Fintype B0]
  [Fintype A1] [Fintype B1] [Fintype A2] [Fintype B2] [Fintype A3] [Fintype B3] [DecidableEq A0]
  [DecidableEq B0] [DecidableEq A1] [DecidableEq B1] [DecidableEq A2] [DecidableEq B2]
  [DecidableEq A3] [DecidableEq B3]

/-- **The upper unipotent change of basis** `P_k = [[1, X_k], [0, 1]]` in all four degrees, for
decompositions `C^k = A_k ⊕ B_k` (tex 4185–4193). Kind: definition. -/
def unipotentChange (X0 : Matrix A0 B0 R) (X1 : Matrix A1 B1 R) (X2 : Matrix A2 B2 R)
    (X3 : Matrix A3 B3 R) : FourBasisChange R (A0 ⊕ B0) (A1 ⊕ B1) (A2 ⊕ B2) (A3 ⊕ B3) where
  P0 := fromBlocks 1 X0 0 1
  Q0 := fromBlocks 1 (-X0) 0 1
  P1 := fromBlocks 1 X1 0 1
  Q1 := fromBlocks 1 (-X1) 0 1
  P2 := fromBlocks 1 X2 0 1
  Q2 := fromBlocks 1 (-X2) 0 1
  P3 := fromBlocks 1 X3 0 1
  Q3 := fromBlocks 1 (-X3) 0 1
  h0 := fromBlocks_upper_mul_neg X0
  h1 := fromBlocks_upper_mul_neg X1
  h2 := fromBlocks_upper_mul_neg X2
  h3 := fromBlocks_upper_mul_neg X3

/-- **(c) Explicit two-block form** (tex 4185–4193): with `P_k = [[1, X_k], [0, 1]]` in every
degree (`det P_k = 1` by Mathlib's `det_fromBlocks_zero₂₁`), the cycle `P₁ z` and the functional
`λ [[1, −X₂], [0, 1]]`, the coordinate is unchanged. Kind: PROVED. -/
theorem kmCoord_unipotentChange [IsDomain R]
    (C : FourCx R (A0 ⊕ B0) (A1 ⊕ B1) (A2 ⊕ B2) (A3 ⊕ B3)) (X0 : Matrix A0 B0 R)
    (X1 : Matrix A1 B1 R) (X2 : Matrix A2 B2 R) (X3 : Matrix A3 B3 R) {z : A1 ⊕ B1 → R}
    {lam : A2 ⊕ B2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : ((A0 ⊕ B0) ⊕ Unit) ⊕ (A2 ⊕ B2) ≃ (A1 ⊕ B1) ⊕ ((A3 ⊕ B3) ⊕ Unit)) :
    kmCoord (fourRebase C (unipotentChange X0 X1 X2 X3)) (fromBlocks 1 X1 0 1 *ᵥ z)
        (lam ᵥ* fromBlocks 1 (-X2) 0 1)
        (fourRebase_cycle C (unipotentChange X0 X1 X2 X3) hz)
        (fourRebase_closed C (unipotentChange X0 X1 X2 X3) hlam) σ =
      kmCoord C z lam hz hlam σ :=
  kmCoord_fourRebase_of_isBlockUnipotent C (unipotentChange X0 X1 X2 X3)
    (isBlockUnipotent_fromBlocks_upper X0) (isBlockUnipotent_fromBlocks_upper X1)
    (isBlockUnipotent_fromBlocks_upper X2) (isBlockUnipotent_fromBlocks_upper X3) hz hlam σ

end TwoBlock

/-! ### Chain isomorphisms -/

section ChainIso

variable {R : Type} [CommRing R] {ι0 ι1 ι2 ι3 : Type} [Fintype ι0] [Fintype ι1] [Fintype ι2]
  [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]

/-- **A chain isomorphism is a graded change of basis** (tex 4185–4193): if `d' P = P d` in each
degree, then `C' = fourRebase C P`. Kind: PROVED. -/
theorem eq_fourRebase_of_comm {C C' : FourCx R ι0 ι1 ι2 ι3} (P : FourBasisChange R ι0 ι1 ι2 ι3)
    (c0 : C'.d0 * P.P0 = P.P1 * C.d0) (c1 : C'.d1 * P.P1 = P.P2 * C.d1)
    (c2 : C'.d2 * P.P2 = P.P3 * C.d2) : C' = fourRebase C P := by
  apply fourCx_eq
  · change C'.d0 = P.P1 * C.d0 * P.Q0
    rw [← c0, Matrix.mul_assoc, P.h0, Matrix.mul_one]
  · change C'.d1 = P.P2 * C.d1 * P.Q1
    rw [← c1, Matrix.mul_assoc, P.h1, Matrix.mul_one]
  · change C'.d2 = P.P3 * C.d2 * P.Q2
    rw [← c2, Matrix.mul_assoc, P.h2, Matrix.mul_one]

/-- **The coordinate under a chain isomorphism** (tex 4185–4193): if `d' P = P d` in each degree,
`z' = P₁ z` and `λ' P₂ = λ`, then `u' = det P₁ det P₃ det Q₀ det Q₂ · u`. Kind: PROVED. -/
theorem kmCoord_chainIso [IsDomain R] {C C' : FourCx R ι0 ι1 ι2 ι3}
    (P : FourBasisChange R ι0 ι1 ι2 ι3) (c0 : C'.d0 * P.P0 = P.P1 * C.d0)
    (c1 : C'.d1 * P.P1 = P.P2 * C.d1) (c2 : C'.d2 * P.P2 = P.P3 * C.d2) {z z' : ι1 → R}
    {lam lam' : ι2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (hz' : C'.d1 *ᵥ z' = 0) (hlam' : lam' ᵥ* C'.d1 = 0) (ez : z' = P.P1 *ᵥ z)
    (elam : lam' ᵥ* P.P2 = lam) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C' z' lam' hz' hlam' σ =
      P.P1.det * P.P3.det * P.Q0.det * P.Q2.det * kmCoord C z lam hz hlam σ := by
  have elam' : lam' = lam ᵥ* P.Q2 := by
    rw [← elam, vecMul_vecMul, P.h2, vecMul_one]
  have hC := eq_fourRebase_of_comm P c0 c1 c2
  subst hC ez elam'
  exact kmCoord_fourRebase C P hz hlam σ

/-- **Under a chain isomorphism with unit determinants the coordinate changes by a sign**
(tex 4185–4193: "their comparison is a sign"). Kind: PROVED. -/
theorem kmCoord_chainIso_sign [IsDomain R] {C C' : FourCx R ι0 ι1 ι2 ι3}
    {P0 : Matrix ι0 ι0 R} {P1 : Matrix ι1 ι1 R} {P2 : Matrix ι2 ι2 R} {P3 : Matrix ι3 ι3 R}
    (h0 : P0.det = 1 ∨ P0.det = -1) (h1 : P1.det = 1 ∨ P1.det = -1)
    (h2 : P2.det = 1 ∨ P2.det = -1) (h3 : P3.det = 1 ∨ P3.det = -1)
    (c0 : C'.d0 * P0 = P1 * C.d0) (c1 : C'.d1 * P1 = P2 * C.d1) (c2 : C'.d2 * P2 = P3 * C.d2)
    {z z' : ι1 → R} {lam lam' : ι2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (hz' : C'.d1 *ᵥ z' = 0) (hlam' : lam' ᵥ* C'.d1 = 0) (ez : z' = P1 *ᵥ z)
    (elam : lam' ᵥ* P2 = lam) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    ∃ ε : ℤˣ, kmCoord C' z' lam' hz' hlam' σ = (ε : R) * kmCoord C z lam hz hlam σ := by
  have hu : ∀ {a : R}, a = 1 ∨ a = -1 → IsUnit a := by
    rintro a (h | h) <;> simp [h]
  set P := FourBasisChange.ofIsUnit P0 P1 P2 P3 (hu h0) (hu h1) (hu h2) (hu h3)
  have elam' : lam' = lam ᵥ* P.Q2 := by
    rw [← elam, vecMul_vecMul]
    change lam' = lam' ᵥ* (P2 * P2⁻¹)
    rw [mul_nonsing_inv P2 (hu h2), vecMul_one]
  have hC : C' = fourRebase C P := eq_fourRebase_of_comm P c0 c1 c2
  subst hC ez elam'
  exact kmCoord_fourRebase_sign C P h0 h1 h2 h3 hz hlam σ

/-- **Two models related by a block unipotent chain isomorphism have the same coordinate**
(tex 4185–4193): if `d' P = P d` in each degree with every `P_k` block unipotent, `z' = P₁ z`
and `λ' P₂ = λ`, then `u' = u`. Kind: PROVED. -/
theorem kmCoord_chainIso_blockUnipotent [IsDomain R] {C C' : FourCx R ι0 ι1 ι2 ι3}
    {P0 : Matrix ι0 ι0 R} {P1 : Matrix ι1 ι1 R} {P2 : Matrix ι2 ι2 R} {P3 : Matrix ι3 ι3 R}
    (u0 : IsBlockUnipotent P0) (u1 : IsBlockUnipotent P1) (u2 : IsBlockUnipotent P2)
    (u3 : IsBlockUnipotent P3) (c0 : C'.d0 * P0 = P1 * C.d0) (c1 : C'.d1 * P1 = P2 * C.d1)
    (c2 : C'.d2 * P2 = P3 * C.d2) {z z' : ι1 → R} {lam lam' : ι2 → R} (hz : C.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* C.d1 = 0) (hz' : C'.d1 *ᵥ z' = 0) (hlam' : lam' ᵥ* C'.d1 = 0)
    (ez : z' = P1 *ᵥ z) (elam : lam' ᵥ* P2 = lam) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C' z' lam' hz' hlam' σ = kmCoord C z lam hz hlam σ := by
  have hu : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι R},
      IsBlockUnipotent Q → IsUnit Q.det := fun hQ => by rw [hQ.det_eq_one]; exact isUnit_one
  set P := FourBasisChange.ofIsUnit P0 P1 P2 P3 (hu u0) (hu u1) (hu u2) (hu u3)
  rw [kmCoord_chainIso P c0 c1 c2 hz hlam hz' hlam' ez elam σ]
  change P1.det * P3.det * P0⁻¹.det * P2⁻¹.det * kmCoord C z lam hz hlam σ = _
  rw [det_nonsing_inv, det_nonsing_inv, u0.det_eq_one, u1.det_eq_one, u2.det_eq_one,
    u3.det_eq_one]
  simp

/-- **After a relabelling of the bases the comparison is still a sign** (tex 4185–4193: "their
comparison is a sign"): for a graded change of basis with unit determinants followed by a
relabelling `e₀, …, e₃` of the bases, the coordinate in any orientation `σ'` is `±` the
original coordinate in any orientation `σ`. Kind: PROVED. -/
theorem kmCoord_reindex_fourRebase_sign [IsDomain R] {ι0' ι1' ι2' ι3' : Type} [Fintype ι0']
    [Fintype ι1'] [Fintype ι2'] [Fintype ι3'] [DecidableEq ι0'] [DecidableEq ι1']
    [DecidableEq ι2'] [DecidableEq ι3'] (C : FourCx R ι0 ι1 ι2 ι3)
    (P : FourBasisChange R ι0 ι1 ι2 ι3) (h0 : P.P0.det = 1 ∨ P.P0.det = -1)
    (h1 : P.P1.det = 1 ∨ P.P1.det = -1) (h2 : P.P2.det = 1 ∨ P.P2.det = -1)
    (h3 : P.P3.det = 1 ∨ P.P3.det = -1) (e0 : ι0 ≃ ι0') (e1 : ι1 ≃ ι1') (e2 : ι2 ≃ ι2')
    (e3 : ι3 ≃ ι3') {z : ι1 → R} {lam : ι2 → R} (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit))
    (σ' : (ι0' ⊕ Unit) ⊕ ι2' ≃ ι1' ⊕ (ι3' ⊕ Unit)) :
    ∃ ε : ℤˣ, kmCoord (fourReindex (fourRebase C P) e0 e1 e2 e3) ((P.P1 *ᵥ z) ∘ e1.symm)
        ((lam ᵥ* P.Q2) ∘ e2.symm)
        (reindexF_cycle (fourRebase C P) e0 e1 e2 e3 (fourRebase_cycle C P hz))
        (reindexF_closed (fourRebase C P) e0 e1 e2 e3 (fourRebase_closed C P hlam)) σ' =
      (ε : R) * kmCoord C z lam hz hlam σ := by
  obtain ⟨ε, hε⟩ := kmCoord_fourRebase_sign C P h0 h1 h2 h3 hz hlam σ
  set τ := (Equiv.sumCongr (Equiv.sumCongr e0 (Equiv.refl Unit)) e2).symm.trans
    (σ.trans (Equiv.sumCongr e1 (Equiv.sumCongr e3 (Equiv.refl Unit))))
  have hr := kmCoord_reindexF (fourRebase C P) e0 e1 e2 e3 (fourRebase_cycle C P hz)
    (fourRebase_closed C P hlam) σ
  have ho := kmCoord_orient (fourReindex (fourRebase C P) e0 e1 e2 e3)
    (reindexF_cycle (fourRebase C P) e0 e1 e2 e3 (fourRebase_cycle C P hz))
    (reindexF_closed (fourRebase C P) e0 e1 e2 e3 (fourRebase_closed C P hlam)) τ σ'
  refine ⟨Equiv.Perm.sign (σ'.trans τ.symm) * ε, ?_⟩
  rw [ho, hr, hε]
  push_cast
  ring

end ChainIso

end ZInQ.Manuscript.RC.Wiring
