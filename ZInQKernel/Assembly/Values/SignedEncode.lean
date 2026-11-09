import ZInQKernel.Assembly.Values.Lift
import ZInQKernel.Compiler.Translation.NaturalCode
import ZInQKernel.Compiler.Translation.Points
import ZInQKernel.Compiler.Precision.Encoding

/-!
# Semantics of the signed encoding

Blueprint: `assembly/value-templates/signed-encoding-semantics.md`.

Under the multiplication statement M (`Translation.MultiplicationExact`, from which the
natural-code predicate follows), `Rel_{value.signed_encode}(N, C)` holds exactly when
`N = ι(m)` and `C = ι(enc m)` for some integer `m`.
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial Translation Compiler.Precision

variable {E : Type}

/-- The parameter point `X_k, …, X_{k+4}` of an assignment extending `a`. -/
theorem evCode_varPoint_of_params {p : ℕ} {a : Fin p → ℚ} {y : ℕ → ℚ}
    (hy : ∀ i : Fin p, y i = a i) (k : ℕ) (hk : k + 5 ≤ p) :
    evCode y (varPoint k) = fun i : Fin 5 => a ⟨k + i, by have := i.isLt; omega⟩ := by
  rw [evCode_varPoint]
  funext i
  exact hy ⟨k + i, _⟩

/-- The call atom of `natural` on a code. -/
theorem lift_natural_call (I : Constructors E) (cstar ell T : ℤ) (y : ℕ → ℚ) (p : Code)
    (w : ℕ) : (Formula.call (naturalTemplate I cstar ell T) p w).Lift y ↔
      (naturalTemplate I cstar ell T).Rel (evCode y p) :=
  Formula.lift_call _ _ _ _

theorem append_left_point (N C : Fin 5 → ℚ) :
    (fun i : Fin 5 => Fin.append N C ⟨0 + i, by omega⟩) = N := by
  funext i; fin_cases i <;> rfl

theorem append_right_point (N C : Fin 5 → ℚ) :
    (fun i : Fin 5 => Fin.append N C ⟨5 + i, by omega⟩) = C := by
  funext i; fin_cases i <;> rfl

/-- Two parameter points determine the ten parameters. -/
theorem params_of_points₂ {y : ℕ → ℚ} {N C : Fin 5 → ℚ} (h0 : evCode y (varPoint 0) = N)
    (h5 : evCode y (varPoint 5) = C) : ∀ i : Fin 10, y i = Fin.append N C i := by
  intro i
  refine Fin.addCases (m := 5) (n := 5) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, ← h0, evCode_varPoint]; simp
  · rw [Fin.append_right, ← h5, evCode_varPoint]; simp [Nat.add_comm]

/-- Reading back a point written by `writePoints`. -/
theorem evCode_writePoints {y : ℕ → ℚ} {l : List (ℕ × (Fin 5 → ℚ))}
    (hl : (l.map Prod.fst).Pairwise Separated) {r : ℕ} {P : Fin 5 → ℚ} (h : (r, P) ∈ l) :
    evCode (writePoints y l) (varPoint r) = P := by
  rw [evCode_varPoint]
  exact writePoints_point y hl h

/-- `enc(-(q+1)) = 2q + 1`. -/
theorem enc_neg_succ (q : ℕ) : (enc (-((q : ℤ) + 1)) : ℤ) = 2 * q + 1 := by
  rw [enc_of_neg (by omega)]; ring

/-- `enc(q) = 2q` for `q ∈ ℕ`. -/
theorem enc_natCast (q : ℕ) : (enc (q : ℤ) : ℤ) = 2 * q := enc_of_nonneg (by omega)

/-- **Semantics of the signed encoding.** Under M, for all `N, C ∈ ℚ⁵`,
`Rel_{value.signed_encode}(N, C) ⟺ ∃ m ∈ ℤ, N = ι(m) ∧ C = ι(enc m)`. -/
theorem signedEncode_rel_iff {I : Constructors E} {cstar ell T : ℤ}
    (hM : MultiplicationExact I cstar ell T) (N C : Fin 5 → ℚ) :
    (signedEncodeTemplate I cstar ell T).Rel (Fin.append N C) ↔
      ∃ m : ℤ, N = iota m ∧ C = iota (enc m) := by
  rw [signedEncodeTemplate_rel_iff]
  simp only [signedEncodeFormula, Formula.lift_and, Formula.lift_or, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    lift_member_call, lift_natural_call, lift_rawAdd_code, lift_peq]
  constructor
  · rintro ⟨y, hya, ⟨g0, g1, g2⟩, -, -, hQ, hQ2, hbr⟩
    have hN := evCode_varPoint_of_params hya 0 (by omega)
    have hC := evCode_varPoint_of_params hya 5 (by omega)
    rw [append_left_point] at hN
    rw [append_right_point] at hC
    obtain ⟨q, hq⟩ := (natural_rel_iff hM _).1 hQ
    rw [hq, rel_rawAdd_iota] at hQ2
    rcases hbr with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨q, ?_, ?_⟩
      · rw [← hN, h1, hq]
      · rw [← hC, h2, hQ2, enc_natCast]; congr 1; ring
    · have hG : evCode y (genPoint 140649) = iota 1 := evCode_genPoint g0 g1 g2
      rw [hq, hG, rel_rawAdd_iota] at h1
      rw [hQ2, hG, rel_rawAdd_iota, hC] at h3
      refine ⟨-((q : ℤ) + 1), ?_, ?_⟩
      · rw [← hN, h2, evCode_neg_iota h1]
      · rw [h3, enc_neg_succ]; congr 1; ring
  · rintro ⟨m, rfl, rfl⟩
    let y0 : ℕ → ℚ := fun i => if i = 140649 then 1641 / 8 else if i = 140650 then -15465 / 4
      else if i = 140651 then 87483 / 32 else 0
    have hgl : ∀ (l : List (ℕ × (Fin 5 → ℚ))), (∀ e ∈ l, e.1 ≤ 20) →
        writePoints y0 l 140649 = 1641 / 8 ∧ writePoints y0 l 140650 = -15465 / 4 ∧
          writePoints y0 l 140651 = 87483 / 32 := by
      intro l hl
      have hn : ∀ j, 140649 ≤ j → writePoints y0 l j = y0 j := fun j hj =>
        writePoints_of_not_mem y0 l fun e he h => by have := hl e he; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hn _ le_rfl]; simp [y0]
      · rw [hn _ (by omega)]; simp [y0]
      · rw [hn _ (by omega)]; simp [y0]
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm
      let l : List (ℕ × (Fin 5 → ℚ)) :=
        [(0, iota m), (5, iota (enc m)), (10, iota m), (15, iota ((m : ℤ) + m))]
      have hl : (l.map Prod.fst).Pairwise Separated := by simp [l, Separated]
      have hp : ∀ r P, (r, P) ∈ l → evCode (writePoints y0 l) (varPoint r) = P :=
        fun r P h => evCode_writePoints hl h
      refine ⟨writePoints y0 l, params_of_points₂ (hp 0 (iota m) (by simp [l])) (hp 5 (iota (enc m)) (by simp [l])),
        hgl l (by simp [l]), ?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
      · rw [hp 0 (iota m) (by simp [l]), rel_member_iff_iota]; exact ⟨_, rfl⟩
      · rw [hp 5 (iota (enc m)) (by simp [l]), rel_member_iff_iota]; exact ⟨_, rfl⟩
      · rw [hp 10 (iota m) (by simp [l]), natural_rel_iff hM]; exact ⟨m, rfl⟩
      · rw [hp 10 (iota m) (by simp [l]), hp 15 (iota ((m : ℤ) + m)) (by simp [l]), rel_rawAdd_iota]
      · rw [hp 0 (iota m) (by simp [l]), hp 10 (iota m) (by simp [l])]
      · rw [hp 5 (iota (enc m)) (by simp [l]), hp 15 (iota ((m : ℤ) + m)) (by simp [l]), enc_natCast]; congr 1; ring
    · obtain ⟨q, hq⟩ : ∃ q : ℕ, m = -((q : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
      subst hq
      let l : List (ℕ × (Fin 5 → ℚ)) :=
        [(0, iota (-((q : ℤ) + 1))), (5, iota (enc (-((q : ℤ) + 1)))), (10, iota q),
          (15, iota ((q : ℤ) + q)), (20, iota ((q : ℤ) + 1))]
      have hl : (l.map Prod.fst).Pairwise Separated := by simp [l, Separated]
      have hp : ∀ r P, (r, P) ∈ l → evCode (writePoints y0 l) (varPoint r) = P :=
        fun r P h => evCode_writePoints hl h
      obtain ⟨g0, g1, g2⟩ := hgl l (by simp [l])
      have hG : evCode (writePoints y0 l) (genPoint 140649) = iota 1 := evCode_genPoint g0 g1 g2
      refine ⟨writePoints y0 l, params_of_points₂ (hp 0 (iota (-((q : ℤ) + 1))) (by simp [l])) (hp 5 (iota (enc (-((q : ℤ) + 1)))) (by simp [l])),
        ⟨g0, g1, g2⟩, ?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
      · rw [hp 0 (iota (-((q : ℤ) + 1))) (by simp [l]), rel_member_iff_iota]; exact ⟨_, rfl⟩
      · rw [hp 5 (iota (enc (-((q : ℤ) + 1)))) (by simp [l]), rel_member_iff_iota]; exact ⟨_, rfl⟩
      · rw [hp 10 (iota q) (by simp [l]), natural_rel_iff hM]; exact ⟨q, rfl⟩
      · rw [hp 10 (iota q) (by simp [l]), hp 15 (iota ((q : ℤ) + q)) (by simp [l]), rel_rawAdd_iota]
      · rw [hp 10 (iota q) (by simp [l]), hp 20 (iota ((q : ℤ) + 1)) (by simp [l]), hG, rel_rawAdd_iota]
      · rw [hp 0 (iota (-((q : ℤ) + 1))) (by simp [l]), evCode_neg_iota (hp 20 (iota ((q : ℤ) + 1)) (by simp [l]))]
      · rw [hp 15 (iota ((q : ℤ) + q)) (by simp [l]), hp 5 (iota (enc (-((q : ℤ) + 1)))) (by simp [l]), hG, rel_rawAdd_iota, enc_neg_succ]
        congr 1; ring

end ZInQ.Assembly
