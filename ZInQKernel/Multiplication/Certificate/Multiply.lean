import ZInQKernel.Multiplication.Certificate.HeightCertificate
import ZInQKernel.Multiplication.Certificate.Guard

/-!
# Unfolding the multiplication template

Blueprint: `multiplication/certificate/multiply-unfolding.md`.

For three inputs `P, Q, R ∈ ℚ⁵`, `Rel_multiply(P, Q, R)` holds iff there are `n₁, n₂, n₃ ∈ ℤ`
with `P = ι(n₁)`, `Q = ι(n₂)`, `R = ι(n₃)`, the height certificate holds at
`(P, Q, R, ℓ, ι(c_*), ι(c_* n₁), ι(c_* n₂), ι(c_* n₃))` and the guard holds at `(P, Q, R)`
(`multiply_rel_iff_unguarded`; with the height certificate unfolded, `multiply_rel_iff`).

The templates take the constructor meaning `I` and the integer values `c_* = val(cstar)`,
`ℓ = val(ell)`, `T = val(T)` as parameters. The semantics of the fixed-scalar template
`S_{c_*}` (blueprint `syntax/fixed-scalar-semantics.md`: on codes of `2E(K₀)`,
`Rel_{S_e}(ι(m), r) ⟺ r = ι(val(e) m)` for `val(e) ≥ 1`) enters as the hypothesis `hS` on `I` and
`c_*`; for the constructors of the specification it is `spec_scalar_cstar_rel_iff`
(`Certificate/Spec.lean`, from `Syntax.scalarTemplate_rel_iff_iota`).

The generator constants force `G = (0, 1641/8, -145, -15465/4, 87483/32) = ι(1)`; the membership
calls inside the height certificate force `P, Q, R` to be codes `ι(n_i)`
(`heightTemplate_rel_members`), and only then does the scalar semantics give the shift points
`ι(c_*)`, `ι(c_* n_i)`.
-/

namespace ZInQ.Mult

open MvPolynomial Syntax

variable {E : Type}

/-- The parameter vector `(P, Q, R, ℓ, S₀, S₁, S₂, S₃)` of the height-certificate call. -/
noncomputable def heightVec (P Q R : Fin 5 → ℚ) (ℓ : ℚ) (S : Fin 4 → Fin 5 → ℚ) : Fin 36 → ℚ :=
  Fin.append (Fin.append (Fin.append (Fin.append (Fin.append P Q) R) ![ℓ])
    (Fin.append (Fin.append (S 0) (S 1)) (S 2))) (S 3)

theorem heightVec_ell (P Q R : Fin 5 → ℚ) (ℓ : ℚ) (S : Fin 4 → Fin 5 → ℚ) :
    heightVec P Q R ℓ S 15 = ℓ := rfl

theorem heightVec_input (P Q R : Fin 5 → ℚ) (ℓ : ℚ) (S : Fin 4 → Fin 5 → ℚ) (i : Fin 3)
    (k : Fin 5) : heightVec P Q R ℓ S ⟨5 * i + k, by omega⟩ = ![P, Q, R] i k := by
  fin_cases i <;> fin_cases k <;> rfl

theorem heightVec_shift (P Q R : Fin 5 → ℚ) (ℓ : ℚ) (S : Fin 4 → Fin 5 → ℚ) (i : Fin 4)
    (k : Fin 5) : heightVec P Q R ℓ S ⟨16 + (5 * i + k), by omega⟩ = S i k := by
  fin_cases i <;> fin_cases k <;> rfl

/-- The values of the height-certificate call. -/
theorem ev_mulHeightArgs (y : ℕ → ℚ) (ℓ : ℤ) :
    (fun k => ev y (Fin.append (Fin.append (Fin.append (Fin.append
      (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10)) ![C ℓ])
      (Fin.append (Fin.append (varPoint 18) (varPoint 24)) (varPoint 30))) (varPoint 36) k)) =
      heightVec (pt y 0) (pt y 5) (pt y 10) ℓ ![pt y 18, pt y 24, pt y 30, pt y 36] := by
  funext k
  fin_cases k <;> simp [heightVec, Fin.append, Fin.addCases, pt]

/-- The values of the guard call. -/
theorem ev_mulGuardArgs (y : ℕ → ℚ) :
    (fun k => ev y (Fin.append (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10) k)) =
      codes3 (pt y 0) (pt y 5) (pt y 10) := by
  funext k
  fin_cases k <;> simp [codes3, Fin.append, Fin.addCases, pt]

/-- The values of a scalar call. -/
theorem ev_mulScalarArgs (y : ℕ → ℚ) (p : Code) (k : ℕ) :
    (fun i => ev y (Fin.append p (varPoint k) i)) =
      Fin.append (fun i => ev y (p i)) (pt y k) := by
  rw [ev_comp_append y p (varPoint k), ev_comp_varPoint]

/-- The generator point has the code `ι(1)` once its constants take their values. -/
theorem ev_genPoint (y : ℕ → ℚ) (h15 : y 15 = 1641 / 8) (h16 : y 16 = -15465 / 4)
    (h17 : y 17 = 87483 / 32) : (fun i => ev y (genPoint 15 i)) = iota 1 := by
  rw [iota_one]
  funext i
  fin_cases i <;> simp [genPoint, h15, h16, h17]

/-- An assignment of the variables of `multiply`: the parameters `P, Q, R`, the generator
constants and the shift points `S_i` at `18 + 6i`. Block variables are `0`. -/
noncomputable def mulY (P Q R : Fin 5 → ℚ) (S : Fin 4 → Fin 5 → ℚ) (i : ℕ) : ℚ :=
  if h : i < 15 then codes3 P Q R ⟨i, h⟩
  else if i = 15 then 1641 / 8
  else if i = 16 then -15465 / 4
  else if i = 17 then 87483 / 32
  else if h : i < 42 then
    (if h' : (i - 18) % 6 < 5 then S ⟨(i - 18) / 6, by omega⟩ ⟨(i - 18) % 6, h'⟩ else 0)
  else 0

section mulY

variable (P Q R : Fin 5 → ℚ) (S : Fin 4 → Fin 5 → ℚ)

theorem mulY_lt (i : Fin 15) : mulY P Q R S i = codes3 P Q R i := by
  rw [mulY, dite_eq_left i.isLt]

theorem mulY_15 : mulY P Q R S 15 = 1641 / 8 := by
  rw [mulY, dite_eq_right (by omega), ite_eq_left rfl]

theorem mulY_16 : mulY P Q R S 16 = -15465 / 4 := by
  rw [mulY, dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem mulY_17 : mulY P Q R S 17 = 87483 / 32 := by
  rw [mulY, dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left rfl]

theorem pt_mulY (j : Fin 4) {n : ℕ} (hn : n = 18 + 6 * j) : pt (mulY P Q R S) n = S j := by
  funext k
  subst hn
  have hj := j.isLt
  have hk := k.isLt
  show mulY P Q R S (18 + 6 * j + k) = _
  rw [mulY, dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), dite_eq_left (by omega), dite_eq_left (by omega)]
  have h1 : (⟨(18 + 6 * (j : ℕ) + k - 18) / 6, by omega⟩ : Fin 4) = j :=
    Fin.ext (by simp only; omega)
  have h2 : (⟨(18 + 6 * (j : ℕ) + k - 18) % 6, by omega⟩ : Fin 5) = k :=
    Fin.ext (by simp only; omega)
  rw [h1, h2]

end mulY

/-- **Unfolding the multiplication template.** -/
theorem multiply_rel_iff_unguarded (I : Constructors E) (cs ℓ T : ℤ)
    (hS : ∀ (m : ℤ) (r : Fin 5 → ℚ),
      (scalarTemplate I cs).Rel (Fin.append (iota m) r) ↔ r = iota (cs * m))
    (P Q R : Fin 5 → ℚ) :
    (multiplyTemplate I cs ℓ T).Rel (codes3 P Q R) ↔
      ∃ n : Fin 3 → ℤ, P = iota (n 0) ∧ Q = iota (n 1) ∧ R = iota (n 2) ∧
        heightTemplate.Rel (heightVec P Q R ℓ
          ![iota cs, iota (cs * n 0), iota (cs * n 1), iota (cs * n 2)]) ∧
        (guardTemplate I T).Rel (codes3 P Q R) := by
  rw [multiplyTemplate_rel_iff]
  have hpts : ∀ y : ℕ → ℚ, (∀ i : Fin 15, y i = codes3 P Q R i) →
      pt y 0 = P ∧ pt y 5 = Q ∧ pt y 10 = R := by
    intro y hya
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩
    · rw [show pt y 0 k = y (0 + k) from rfl, hya ⟨0 + k, by omega⟩]
      fin_cases k <;> rfl
    · rw [show pt y 5 k = y (5 + k) from rfl, hya ⟨5 + k, by omega⟩]
      fin_cases k <;> rfl
    · rw [show pt y 10 k = y (10 + k) from rfl, hya ⟨10 + k, by omega⟩]
      fin_cases k <;> rfl
  constructor
  · rintro ⟨y, hya, ⟨h15, h16, h17⟩, hL⟩
    obtain ⟨hP, hQ, hR⟩ := hpts y hya
    simp only [multiplyFormula, lift_and_cons, lift_and_nil, and_true] at hL
    obtain ⟨c0, c1, c2, c3, ch, cg⟩ := hL
    rw [Formula.lift_call y heightTemplate (Fin.append (Fin.append (Fin.append (Fin.append
      (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10)) ![C ℓ])
      (Fin.append (Fin.append (varPoint 18) (varPoint 24)) (varPoint 30))) (varPoint 36)) 42] at ch
    replace ch := (iff_of_eq (congrArg heightTemplate.Rel (ev_mulHeightArgs y ℓ))).1 ch
    rw [hP, hQ, hR] at ch
    rw [Formula.lift_call y (guardTemplate I T)
      (Fin.append (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10)) 35148] at cg
    replace cg := (iff_of_eq (congrArg (guardTemplate I T).Rel (ev_mulGuardArgs y))).1 cg
    rw [hP, hQ, hR] at cg
    obtain ⟨n, hn⟩ := heightTemplate_rel_members _ ch
    have hn' : ∀ i : Fin 3, ![P, Q, R] i = iota (n i) := fun i =>
      funext fun k => (heightVec_input P Q R ℓ _ i k).symm.trans (hn i k)
    have hP' : P = iota (n 0) := hn' 0
    have hQ' : Q = iota (n 1) := hn' 1
    have hR' : R = iota (n 2) := hn' 2
    rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (genPoint 15) (varPoint 18)) 23] at c0
    replace c0 := (iff_of_eq (congrArg (scalarTemplate I cs).Rel
      (ev_mulScalarArgs y (genPoint 15) 18))).1 c0
    rw [ev_genPoint y h15 h16 h17, hS, mul_one] at c0
    rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (varPoint 0) (varPoint 24)) 29] at c1
    replace c1 := (iff_of_eq (congrArg (scalarTemplate I cs).Rel
      (ev_mulScalarArgs y (varPoint 0) 24))).1 c1
    rw [ev_comp_varPoint, hP, hP', hS] at c1
    rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (varPoint 5) (varPoint 30)) 35] at c2
    replace c2 := (iff_of_eq (congrArg (scalarTemplate I cs).Rel
      (ev_mulScalarArgs y (varPoint 5) 30))).1 c2
    rw [ev_comp_varPoint, hQ, hQ', hS] at c2
    rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (varPoint 10) (varPoint 36)) 41] at c3
    replace c3 := (iff_of_eq (congrArg (scalarTemplate I cs).Rel
      (ev_mulScalarArgs y (varPoint 10) 36))).1 c3
    rw [ev_comp_varPoint, hR, hR', hS] at c3
    refine ⟨n, hP', hQ', hR', ?_, cg⟩
    rw [c0, c1, c2, c3] at ch
    exact ch
  · rintro ⟨n, hP, hQ, hR, hH, hG⟩
    obtain ⟨y, hy⟩ : ∃ y, y = mulY P Q R
        ![iota cs, iota (cs * n 0), iota (cs * n 1), iota (cs * n 2)] := ⟨_, rfl⟩
    have hya : ∀ i : Fin 15, y i = codes3 P Q R i := hy ▸ mulY_lt P Q R _
    obtain ⟨hP0, hQ0, hR0⟩ := hpts y hya
    have hS0 : pt y 18 = iota cs := hy ▸ pt_mulY P Q R _ 0 rfl
    have hS1 : pt y 24 = iota (cs * n 0) := hy ▸ pt_mulY P Q R _ 1 rfl
    have hS2 : pt y 30 = iota (cs * n 1) := hy ▸ pt_mulY P Q R _ 2 rfl
    have hS3 : pt y 36 = iota (cs * n 2) := hy ▸ pt_mulY P Q R _ 3 rfl
    refine ⟨y, hya, ⟨hy ▸ mulY_15 P Q R _, hy ▸ mulY_16 P Q R _, hy ▸ mulY_17 P Q R _⟩, ?_⟩
    simp only [multiplyFormula, lift_and_cons, lift_and_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (genPoint 15) (varPoint 18)) 23]
      refine (iff_of_eq (congrArg (scalarTemplate I cs).Rel
        (ev_mulScalarArgs y (genPoint 15) 18))).2 ?_
      rw [ev_genPoint y (hy ▸ mulY_15 P Q R _) (hy ▸ mulY_16 P Q R _) (hy ▸ mulY_17 P Q R _), hS,
        mul_one, hS0]
    · rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (varPoint 0) (varPoint 24)) 29]
      refine (iff_of_eq (congrArg (scalarTemplate I cs).Rel
        (ev_mulScalarArgs y (varPoint 0) 24))).2 ?_
      rw [ev_comp_varPoint, hP0, hP, hS, hS1]
    · rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (varPoint 5) (varPoint 30)) 35]
      refine (iff_of_eq (congrArg (scalarTemplate I cs).Rel
        (ev_mulScalarArgs y (varPoint 5) 30))).2 ?_
      rw [ev_comp_varPoint, hQ0, hQ, hS, hS2]
    · rw [Formula.lift_call y (scalarTemplate I cs) (Fin.append (varPoint 10) (varPoint 36)) 41]
      refine (iff_of_eq (congrArg (scalarTemplate I cs).Rel
        (ev_mulScalarArgs y (varPoint 10) 36))).2 ?_
      rw [ev_comp_varPoint, hR0, hR, hS, hS3]
    · rw [Formula.lift_call y heightTemplate (Fin.append (Fin.append (Fin.append (Fin.append
        (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10)) ![C ℓ])
        (Fin.append (Fin.append (varPoint 18) (varPoint 24)) (varPoint 30))) (varPoint 36)) 42]
      refine (iff_of_eq (congrArg heightTemplate.Rel (ev_mulHeightArgs y ℓ))).2 ?_
      rw [hP0, hQ0, hR0, hS0, hS1, hS2, hS3]
      exact hH
    · rw [Formula.lift_call y (guardTemplate I T)
        (Fin.append (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10)) 35148]
      refine (iff_of_eq (congrArg (guardTemplate I T).Rel (ev_mulGuardArgs y))).2 ?_
      rw [hP0, hQ0, hR0]
      exact hG

/-- **Unfolding the multiplication template**, with the height certificate unfolded. -/
theorem multiply_rel_iff (I : Constructors E) (cs ℓ T : ℤ)
    (hS : ∀ (m : ℤ) (r : Fin 5 → ℚ),
      (scalarTemplate I cs).Rel (Fin.append (iota m) r) ↔ r = iota (cs * m))
    (P Q R : Fin 5 → ℚ) :
    (multiplyTemplate I cs ℓ T).Rel (codes3 P Q R) ↔
      ∃ n : Fin 3 → ℤ, P = iota (n 0) ∧ Q = iota (n 1) ∧ R = iota (n 2) ∧
        HeightCert ![P, Q, R] ℓ ![cs, cs * n 0, cs * n 1, cs * n 2] ∧
        (guardTemplate I T).Rel (codes3 P Q R) := by
  rw [multiply_rel_iff_unguarded I cs ℓ T hS]
  refine exists_congr fun n => ?_
  have hY : (fun (i : Fin 3) (k : Fin 5) => heightVec P Q R ℓ
      ![iota cs, iota (cs * n 0), iota (cs * n 1), iota (cs * n 2)] ⟨5 * i + k, by omega⟩) =
      ![P, Q, R] := funext fun i => funext fun k => heightVec_input P Q R ℓ _ i k
  constructor
  · rintro ⟨hP, hQ, hR, hH, hG⟩
    rw [heightCertificate_rel_iff (ℓ : ℚ) ![cs, cs * n 0, cs * n 1, cs * n 2] _
      (heightVec_ell P Q R ℓ _) fun i k => by rw [heightVec_shift]; fin_cases i <;> rfl, hY] at hH
    exact ⟨hP, hQ, hR, hH.2, hG⟩
  · rintro ⟨hP, hQ, hR, hH, hG⟩
    refine ⟨hP, hQ, hR, ?_, hG⟩
    rw [heightCertificate_rel_iff (ℓ : ℚ) ![cs, cs * n 0, cs * n 1, cs * n 2] _
      (heightVec_ell P Q R ℓ _) fun i k => by rw [heightVec_shift]; fin_cases i <;> rfl, hY]
    refine ⟨⟨n, fun i k => ?_⟩, hH⟩
    rw [heightVec_input]
    fin_cases i
    · exact congrFun hP k
    · exact congrFun hQ k
    · exact congrFun hR k

end ZInQ.Mult

namespace ZInQ.Mult

open Syntax

variable {E : Type}

/-- The unfolding at the constants of the certificate: `c_* = val(cstar)`, `ℓ₀ = val(ell)`, with
shift indices `certShifts n = (c_*, c_* n₁, c_* n₂, c_* n₃)`. -/
theorem multiply_rel_iff_cert (I : Constructors E) (T : ℤ)
    (hS : ∀ (m : ℤ) (r : Fin 5 → ℚ),
      (scalarTemplate I (Syntax.cstar : ℤ)).Rel (Fin.append (iota m) r) ↔
        r = iota ((Syntax.cstar : ℤ) * m))
    (P Q R : Fin 5 → ℚ) :
    (multiplyTemplate I (Syntax.cstar : ℤ) (Syntax.ell : ℤ) T).Rel (codes3 P Q R) ↔
      ∃ n : Fin 3 → ℤ, P = iota (n 0) ∧ Q = iota (n 1) ∧ R = iota (n 2) ∧
        HeightCert ![P, Q, R] (Syntax.ell : ℚ) (certShifts n) ∧
        (guardTemplate I T).Rel (codes3 P Q R) := by
  rw [multiply_rel_iff I _ _ T hS, Int.cast_natCast]
  rfl

end ZInQ.Mult
