import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionE1a
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionOld
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalConsistency

/-!
# Non-vacuity of the full-condition cancellation core, including `Q = ∅`

* `preFullEx b Qn`: for every finite type `Qn` of new places (possibly empty), the full-condition
  family model over `Λ[G]` with old part `H₁ --0--> H₂` and one singular summand per new place in
  degrees one and two, with local block `t` (`det = X¹·1 + 2·0`);
* `fullCoreEx b Qn : FullCore Qn b 0 0 0 0`: the cancellation core is inhabited for every `Qn`;
  `fullCore_nonempty_empty`: in particular for `Qn = Empty` (`Q = ∅`, the case excluded by the
  `nQ` field of `Identification2G`); `identificationEx`: the derived `Identification`;
* `singularEx`: over any nontrivial ring, a full-condition complex with `B = 0`: the model sequence
  `0 → C_old → C → (N --B--> N) → 0` is short exact although `B` is not invertible (the situation
  of the mod-two representation at an odd good prime, where the singular differential vanishes).

The Selmer-side fields of `Identification3` (genuine continuous-cochain comparisons) are not
witnessed here; the genuine sequence of (5.6) is itself non-vacuous for `S' = S`
(`FullConditionSelmer.lean`).

All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup aug)

variable (b : ℕ) (Qn : Type) [Fintype Qn] [DecidableEq Qn]

/-- The full-condition family model of the example: old part `H₁ --0--> H₂`, one singular summand
`t` per new place, in degrees one and two. -/
def preFullEx : FullPreComplex (MonoidAlgebra Lam (SignGroup b)) where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Unit × Qn
  c0 := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := Matrix.diagonal fun _ => tG b
  U := 0
  V := 0
  c1_c0 := by simp
  c2_c1 := by simp

/-- The local blocks `(t)`. -/
def AFullEx : Qn → Matrix Unit Unit Lam := fun _ => of fun _ _ => PowerSeries.X

theorem hdetFullEx : ∀ q : Qn, (AFullEx Qn q).det =
    (PowerSeries.X : Lam) ^ (fun _ : Qn => 1) q * ((fun _ : Qn => (1 : Lamˣ)) q : Lam) +
      2 * (fun _ : Qn => (0 : Lam)) q := by
  intro q
  simp [AFullEx, Matrix.det_unique]

theorem hB0FullEx : ((preFullEx b Qn).B.submatrix (Equiv.refl _).symm (Equiv.refl _).symm).map aug =
    Matrix.blockDiagonal (AFullEx Qn) := by
  refine Matrix.ext fun x y => ?_
  obtain ⟨i, q⟩ := x
  obtain ⟨j, q'⟩ := y
  by_cases h : q = q'
  · subst h
    simp [preFullEx, tG, AFullEx, Matrix.blockDiagonal_apply,
      ZInQ.Manuscript.RC.Determinant.aug]
  · have h' : ((i, q) : Unit × Qn) ≠ (j, q') := fun e => h (congrArg Prod.snd e)
    change aug (Matrix.diagonal (fun _ => tG b) (i, q) (j, q')) =
      Matrix.blockDiagonal (AFullEx Qn) (i, q) (j, q')
    rw [Matrix.diagonal_apply_ne _ h', Matrix.blockDiagonal_apply_ne _ _ _ h, map_zero]

theorem hYFullEx : (preFullEx b Qn).Y.map (augR b) = 0 := Matrix.map_zero _ (map_zero _)
theorem hTFullEx : (preFullEx b Qn).T.map (augR b) = 0 := Matrix.map_zero _ (map_zero _)

theorem central_fullFullEx :
    let D := ((preFullEx b Qn).map (augR b)).old (hYFullEx b Qn) (hTFullEx b Qn)
    D.d0.map PowerSeries.constantCoeff =
        (smithForm (preFullEx b Qn).m0 (preFullEx b Qn).m1 (preFullEx b Qn).m2 (fun _ => 1)
          (fun _ => 1) (fun _ => 1)).d0 ∧
      D.d1.map PowerSeries.constantCoeff =
        (smithForm (preFullEx b Qn).m0 (preFullEx b Qn).m1 (preFullEx b Qn).m2 (fun _ => 1)
          (fun _ => 1) (fun _ => 1)).d1 ∧
      D.d2.map PowerSeries.constantCoeff =
        (smithForm (preFullEx b Qn).m0 (preFullEx b Qn).m1 (preFullEx b Qn).m2 (fun _ => 1)
          (fun _ => 1) (fun _ => 1)).d2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; exact j.elim0
  · ext (i | i | i) (j | j | j)
    all_goals first | exact i.elim0 | exact j.elim0 | rfl
  · ext i j; exact i.elim0

/-- **The full-condition cancellation core is inhabited for every finite set of new places**
(possibly empty). -/
def fullCoreEx : FullCore Qn b 0 0 0 0 where
  ιn := Unit
  A := AFullEx Qn
  dq := fun _ => 1
  hd := fun _ => by norm_num
  v := fun _ => 1
  w := fun _ => 0
  hdet := hdetFullEx Qn
  C := preFullEx b Qn
  eN := Equiv.refl _
  hB0 := hB0FullEx b Qn
  hT0 := hTFullEx b Qn
  hY0 := hYFullEx b Qn
  s := fun _ _ => 1
  s_ne := fun _ _ => one_ne_zero
  central_full := central_fullFullEx b Qn
  budget := budgetInputs_of_empty _ rfl fun i => by rcases i with _ | _ | _ | i <;> rfl

/-- The derived identification of the example. -/
def identificationEx : Identification b 0 0 0 0 := (fullCoreEx b Qn).toIdentification

/-- **`Q = ∅` is admitted**: the cancellation core with no new places. -/
theorem fullCore_nonempty_empty : Nonempty (FullCore Empty b 0 0 0 0) :=
  ⟨fullCoreEx b Empty⟩

/-- The cancellation core with one new place. -/
theorem fullCore_nonempty_unit : Nonempty (FullCore Unit b 0 0 0 0) :=
  ⟨fullCoreEx b Unit⟩

/-! ### A singular block: the model of (5.6) without invertibility -/

section Singular

variable (R : Type) [CommRing R]

/-- Old part `H₁ --0--> H₂` and one singular summand with `B = 0`. -/
def singularEx : FullPreComplex R where
  m0 := 0
  m1 := 0
  m2 := 0
  N := Unit
  c0 := 0
  Y := 0
  P := 0
  Q := 0
  T := 0
  B := 0
  U := 0
  V := 0
  c1_c0 := by simp
  c2_c1 := by simp

theorem singularEx_not_isUnit [Nontrivial R] : ¬ IsUnit (singularEx R).B.det := by
  change ¬ IsUnit (0 : Matrix Unit Unit R).det
  rw [Matrix.det_unique]
  exact not_isUnit_zero

/-- **The model sequence of (5.6) is short exact for a singular block.** -/
theorem singularEx_shortExact :
    (FullPreComplex.oldSES (C := singularEx R) rfl rfl).ShortExact :=
  FullPreComplex.oldSES_shortExact rfl rfl

end Singular

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
