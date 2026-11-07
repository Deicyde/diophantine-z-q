import ZInQKernel.Assembly.Values.Close
import ZInQKernel.Assembly.Values.Tests

/-!
# Semantics of the value-test template

Blueprint: `assembly/value-templates/value-test-semantics.md`.

Under the multiplication statement M, `Rel_{value.test}(N, K, t)` holds exactly when `N = ι(n)`,
`K = ι(κ)` and `Test(n, κ, t)` for some integers `n, κ`.
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial Translation Compiler.Precision WeierstrassCurve WeierstrassCurve.Affine

variable {E : Type}

theorem ev_valueContact (y : ℕ → ℚ) : ev y (valueContact (X 10)) = Mult.contactPoly (y 10) := by
  simp [valueContact, Mult.contactPoly]

theorem val_pair_zero (y : ℕ → ℚ) (p : Poly) :
    Pair.val y (p, 0) = algebraMap ℚ K0 (ev y p) := by
  ext <;> simp [QuadraticAlgebra.algebraMap_eq]

theorem val_smul' (y : ℕ → ℚ) (k : Poly) (u : Pair) :
    Pair.val y (Pair.smul k u) = algebraMap ℚ K0 (ev y k) * Pair.val y u := by
  rw [Pair.val_smul, QuadraticAlgebra.algebraMap_eq]

theorem val_slopeW_foldl (y : ℕ → ℚ) (R : Poly) (l : List Pair) (W : Pair) :
    Pair.val y (l.foldl (fun W n => W.mul (Pair.one.add (Pair.smul R n.sq))) W) =
      Pair.val y W * (l.map fun n => 1 + algebraMap ℚ K0 (ev y R) * Pair.val y n ^ 2).prod := by
  induction l generalizing W with
  | nil => simp
  | cons n l ih =>
    rw [List.foldl_cons, ih, Pair.val_mul, Pair.val_add, Pair.val_one, val_smul', Pair.val_sq,
      List.map_cons, List.prod_cons, mul_assoc]

/-- The product `W` of `value.test` in field terms. -/
theorem val_slopeW (y : ℕ → ℚ) (R : Poly) {m : ℕ} (C : Fin m → Pair) :
    Pair.val y (slopeW R (List.ofFn C)) =
      ∏ j, (1 + algebraMap ℚ K0 (ev y R) * Pair.val y (C j) ^ 2) := by
  rw [slopeW, val_slopeW_foldl, Pair.val_one, one_mul, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The call atom of `pole`. -/
theorem lift_pole_call (y : ℕ → ℚ) (x : Poly) (w : ℕ) :
    (Formula.call poleTemplate ![x] w).Lift y ↔ PoleSoluble (ev y x) := by
  refine (Formula.lift_call _ _ _ _).trans ?_
  show poleTemplate.Rel (fun k : Fin 1 => ev y (![x] k)) ↔ _
  rw [poleTemplate_rel_iff]
  rfl

/-- The call atom of `multiply` on three codes. -/
theorem lift_multiply_code (I : Constructors E) (cstar ell T : ℤ) (y : ℕ → ℚ) (A B D : Code)
    (w : ℕ) :
    (Formula.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append A B) D) w).Lift y ↔
      (multiplyTemplate I cstar ell T).Rel
        (Fin.append (Fin.append (evCode y A) (evCode y B)) (evCode y D)) :=
  Translation.lift_multiply_call I cstar ell T y A B D w

/-- Two parameter points and a scalar determine the eleven parameters. -/
theorem params_iff₂ (y : ℕ → ℚ) (N K : Fin 5 → ℚ) (t : ℚ) :
    (∀ i : Fin 11, y i = Fin.append (Fin.append N K) ![t] i) ↔
      evCode y (varPoint 0) = N ∧ evCode y (varPoint 5) = K ∧ y 10 = t := by
  constructor
  · intro hy
    refine ⟨?_, ?_, (hy 10).trans rfl⟩
    · rw [evCode_varPoint]; funext i; rw [hy ⟨0 + i, by omega⟩]; fin_cases i <;> rfl
    · rw [evCode_varPoint]; funext i; rw [hy ⟨5 + i, by omega⟩]; fin_cases i <;> rfl
  · rintro ⟨h0, h5, ht⟩ i
    refine Fin.addCases (m := 10) (n := 1) (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      refine Fin.addCases (m := 5) (n := 5) (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left, ← h0, evCode_varPoint]; simp
      · rw [Fin.append_right, ← h5, evCode_varPoint]; simp [Nat.add_comm]
    · rw [Fin.append_right]
      fin_cases i
      simpa using ht

theorem algebraMap_ne_zero {r : ℚ} (h : r ≠ 0) : algebraMap ℚ K0 r ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap ℚ K0).injective).2 h

set_option maxHeartbeats 4000000 in
/-- **Semantics of the value-test template.** Under M, for all `N, K ∈ ℚ⁵` and `t ∈ ℚ`,
`Rel_{value.test}(N, K, t) ⟺ ∃ n κ ∈ ℤ, N = ι(n) ∧ K = ι(κ) ∧ Test(n, κ, t)`. -/
theorem valueTest_rel_iff {I : Constructors E} {cstar ell T : ℤ}
    (hM : MultiplicationExact I cstar ell T) (N K : Fin 5 → ℚ) (t : ℚ) :
    (valueTestTemplate I cstar ell T).Rel (Fin.append (Fin.append N K) ![t]) ↔
      ∃ n κ : ℤ, N = iota n ∧ K = iota κ ∧ Test n κ t := by
  simp only [test_iff]
  rw [valueTestTemplate_rel_iff]
  simp only [params_iff₂, valueTestFormula, valueLocalFormula, List.cons_append, List.nil_append,
    Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    lift_member_call, lift_fin, lift_multiply_code, lift_rawAdd_code, lift_ixFormula,
    lift_zFormula, lift_divFormula, lift_nzFormula, Formula.lift_eq, lift_feq, lift_pole_call]
  constructor
  · rintro ⟨y, ⟨hN, hK, ht⟩, hmN, hmK, hmC, hmH, hmU, hmV0, hmV1, hfK, hmul, hs0, hs1, hfH, hfV0,
      hixH, hzH, hixU, hzU, hixV0, hzV0, hixV1, hzV1, hd0, hd1, hnF, heta, hR0, ha0, hna, hR,
      hf0, hf1, hf2, hf3, hf4, hf5, hdW, hΘ, hnΘ, hB, hpole⟩
    obtain ⟨n, en⟩ := (rel_member_iff_iota _).1 hmN
    obtain ⟨κ, ek⟩ := (rel_member_iff_iota _).1 hmK
    obtain ⟨h, eh⟩ := (rel_member_iff_iota _).1 hmH
    obtain ⟨s₀, eu⟩ := (rel_member_iff_iota _).1 hmU
    have hκ : κ ≠ 0 := (iota_apply_zero_eq_zero_iff κ).1 (by rw [← ek]; exact hfK)
    rw [ek, en, hM.rel_iota_iff] at hmul
    rw [eh, evCode_neg_iota ek, rel_rawAdd_iota, ← sub_eq_add_neg] at hs0
    rw [eu, evCode_neg_iota hmul, rel_rawAdd_iota, ← sub_eq_add_neg] at hs1
    have hh : h ≠ 0 := (iota_apply_zero_eq_zero_iff h).1 (by rw [← eh]; exact hfH)
    have hhk : h - κ ≠ 0 := (iota_apply_zero_eq_zero_iff _).1 (by rw [← hs0]; exact hfV0)
    have wH : Pair.val y (varPair 35231) = wPt (h • genP0) := (holds_ixFormula_iota eh).1 hixH
    have wU : Pair.val y (varPair 35236) = wPt (s₀ • genP0) := (holds_ixFormula_iota eu).1 hixU
    have wV0 : Pair.val y (varPair 35241) = wPt ((h - κ) • genP0) :=
      (holds_ixFormula_iota hs0).1 hixV0
    have wV1 : Pair.val y (varPair 35246) = wPt ((s₀ - κ * n) • genP0) :=
      (holds_ixFormula_iota hs1).1 hixV1
    have zH : Pair.val y (varPair 35233) = zIdx h := ((holds_zFormula_iota eh).1 hzH).1
    have zU : Pair.val y (varPair 35238) = zIdx s₀ := ((holds_zFormula_iota eu).1 hzU).1
    have zV0 : Pair.val y (varPair 35243) = zIdx (h - κ) := ((holds_zFormula_iota hs0).1 hzV0).1
    have zV1 : Pair.val y (varPair 35248) = zIdx (s₀ - κ * n) :=
      ((holds_zFormula_iota hs1).1 hzV1).1
    have ρ0 := ((holds_divFormula_iff _ _ _ _ _).1 hd0).2
    have ρ1 := ((holds_divFormula_iff _ _ _ _ _).1 hd1).2
    rw [zU, zH] at ρ0
    rw [zV1, zV0] at ρ1
    rw [ev_valueContact, ht] at hnF
    have hF : Mult.contactPoly t ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hnF; exact zero_ne_one hnF
    have hF' := algebraMap_ne_zero hF
    have heta' : y 35257 ^ 2 = 1 := by simpa using heta
    have e0 : y 35259 = vtR0 t (y 35257) := by
      unfold vtR0; rw [pow_six_2730_rat]; simpa [ev_valueContact, ht] using hR0
    have ea : y 35260 = vtA0 t (y 35257) (y 35258) := by
      unfold vtA0; rw [← e0]; simpa using ha0
    have ha : vtA0 t (y 35257) (y 35258) ≠ 0 := by
      rw [← ea]; intro h0; simp [h0] at hna
    have eR : y 35261 = vtR t (y 35257) (y 35258) := by
      unfold vtR; rw [← e0, ← ea]; simpa using hR
    rw [val_smul', ev_valueContact, ht] at hf0 hf1 hf2 hf3 hf4 hf5
    have hC : ∀ j : Fin 6, Pair.val y (varPair (35264 + 2 * ↑j)) =
        vtD n κ t h s₀ j / algebraMap ℚ K0 (Mult.contactPoly t) := by
      intro j
      rw [eq_div_iff hF', mul_comm]
      fin_cases j
      · refine hf0.trans ?_
        rw [wH]; rfl
      · refine hf1.trans ?_
        rw [wU]; rfl
      · refine hf2.trans ?_
        rw [Pair.val_conj, wV0]; rfl
      · refine hf3.trans ?_
        rw [Pair.val_conj, wV1]; rfl
      · refine hf4.trans ?_
        rw [Pair.val_sub, val_pair_zero, ρ0, ev_X, ht]; rfl
      · refine hf5.trans ?_
        rw [Pair.val_sub, val_pair_zero, Pair.val_conj, ρ1, ev_X, ht]; rfl
    obtain ⟨hWn, hω⟩ := (holds_divFormula_iff _ _ _ _ _).1 hdW
    have hWne : Pair.val y (slopeW (X 35261) (List.ofFn fun j : Fin 6 =>
        varPair (35264 + 2 * ↑j))) ≠ 0 := by
      rw [← ev_norm_ne_zero_iff]; intro h0; rw [h0, zero_mul] at hWn; exact zero_ne_one hWn
    have hWv : Pair.val y (slopeW (X 35261) (List.ofFn fun j : Fin 6 =>
        varPair (35264 + 2 * ↑j))) = vtW n κ t h s₀ (y 35257) (y 35258) := by
      rw [val_slopeW, vtW, ev_X, eR]
      exact Finset.prod_congr rfl fun j _ => by rw [hC j]
    rw [hWv, Pair.val_one, one_div] at hω
    rw [hWv] at hWne
    have eΘ : y 35279 = vtTheta n κ t h s₀ (y 35257) (y 35258) := by
      rw [vtTheta, K0.trace_eq, ← hω]; simpa using hΘ
    have hΘ0 : vtTheta n κ t h s₀ (y 35257) (y 35258) ≠ 0 := by
      rw [← eΘ]; intro h0; simp [h0] at hnΘ
    have eB : y 35280 = vtR t (y 35257) (y 35258) /
        vtTheta n κ t h s₀ (y 35257) (y 35258) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hΘ0), ← eR, ← eΘ]; simpa using hB
    refine ⟨n, κ, by rw [← hN, en], by rw [← hK, ek], hκ, contactPoly_ne_zero_iff.1 hF, h, s₀,
      y 35257, y 35258, hh, sub_ne_zero.1 hhk, heta', ha, hWne, hΘ0, ?_⟩
    rw [← eB]; simpa using hpole
  · rintro ⟨n, κ, rfl, rfl, hκ, htC, h, s₀, η, q, hh, hhk, heta, ha, hW, hΘ, hpole⟩
    have hF : Mult.contactPoly t ≠ 0 := contactPoly_ne_zero_iff.2 htC
    have hF' := algebraMap_ne_zero hF
    have hhk' : h - κ ≠ 0 := sub_ne_zero.2 hhk
    set W := vtW n κ t h s₀ η q with hWdef
    set Θ := vtTheta n κ t h s₀ η q with hΘdef
    set Cv : Fin 6 → K0 := fun j => vtD n κ t h s₀ j / algebraMap ℚ K0 (Mult.contactPoly t) with hCv
    have hzh : zIdx h ≠ 0 := zIdx_ne_zero (admissible_of_ne_zero hh)
    have hzv : zIdx (h - κ) ≠ 0 := zIdx_ne_zero (admissible_of_ne_zero hhk')
    let pts : List (ℕ × (Fin 5 → ℚ)) := [(0, iota n), (5, iota κ), (11, iota (κ * n)), (16, iota h),
      (21, iota s₀), (26, iota (h - κ)), (31, iota (s₀ - κ * n))]
    let vals : List (ℕ × ℚ) := [(10, t),
        (35231, (wPt (h • genP0)).re),
        (35232, (wPt (h • genP0)).im),
        (35233, (zIdx h).re),
        (35234, (zIdx h).im),
        (35235, (codeNormY (iota h))⁻¹),
        (35236, (wPt (s₀ • genP0)).re),
        (35237, (wPt (s₀ • genP0)).im),
        (35238, (zIdx s₀).re),
        (35239, (zIdx s₀).im),
        (35240, (codeNormY (iota s₀))⁻¹),
        (35241, (wPt ((h - κ) • genP0)).re),
        (35242, (wPt ((h - κ) • genP0)).im),
        (35243, (zIdx (h - κ)).re),
        (35244, (zIdx (h - κ)).im),
        (35245, (codeNormY (iota (h - κ)))⁻¹),
        (35246, (wPt ((s₀ - κ * n) • genP0)).re),
        (35247, (wPt ((s₀ - κ * n) • genP0)).im),
        (35248, (zIdx (s₀ - κ * n)).re),
        (35249, (zIdx (s₀ - κ * n)).im),
        (35250, (codeNormY (iota (s₀ - κ * n)))⁻¹),
        (35251, (zIdx s₀ / zIdx h).re),
        (35252, (zIdx s₀ / zIdx h).im),
        (35253, ((zIdx h).re ^ 2 - 2 * (zIdx h).im ^ 2)⁻¹),
        (35254, (zIdx (s₀ - κ * n) / zIdx (h - κ)).re),
        (35255, (zIdx (s₀ - κ * n) / zIdx (h - κ)).im),
        (35256, ((zIdx (h - κ)).re ^ 2 - 2 * (zIdx (h - κ)).im ^ 2)⁻¹),
        (35257, η),
        (35258, q),
        (35259, vtR0 t η),
        (35260, vtA0 t η q),
        (35261, vtR t η q),
        (35262, (Mult.contactPoly t)⁻¹),
        (35263, (vtA0 t η q)⁻¹),
        (35264, (Cv 0).re),
        (35265, (Cv 0).im),
        (35266, (Cv 1).re),
        (35267, (Cv 1).im),
        (35268, (Cv 2).re),
        (35269, (Cv 2).im),
        (35270, (Cv 3).re),
        (35271, (Cv 3).im),
        (35272, (Cv 4).re),
        (35273, (Cv 4).im),
        (35274, (Cv 5).re),
        (35275, (Cv 5).im),
        (35276, (W⁻¹).re),
        (35277, (W⁻¹).im),
        (35278, (W.re ^ 2 - 2 * W.im ^ 2)⁻¹),
        (35279, Θ),
        (35280, vtR t η q / Θ ^ 2),
        (35281, Θ⁻¹)]
    have hnd : (vals.map Prod.fst).Nodup := by
      rw [show vals.map Prod.fst = [10, 35231, 35232, 35233, 35234, 35235, 35236, 35237, 35238, 35239, 35240, 35241, 35242, 35243, 35244, 35245, 35246, 35247, 35248, 35249, 35250, 35251, 35252, 35253, 35254, 35255, 35256, 35257, 35258, 35259, 35260, 35261, 35262, 35263, 35264, 35265, 35266, 35267, 35268, 35269, 35270, 35271, 35272, 35273, 35274, 35275, 35276, 35277, 35278, 35279, 35280, 35281] from rfl]
      decide
    have hfst : ∀ x ∈ vals.map Prod.fst, x = 10 ∨ 35231 ≤ x := by
      rw [show vals.map Prod.fst = [10, 35231, 35232, 35233, 35234, 35235, 35236, 35237, 35238, 35239, 35240, 35241, 35242, 35243, 35244, 35245, 35246, 35247, 35248, 35249, 35250, 35251, 35252, 35253, 35254, 35255, 35256, 35257, 35258, 35259, 35260, 35261, 35262, 35263, 35264, 35265, 35266, 35267, 35268, 35269, 35270, 35271, 35272, 35273, 35274, 35275, 35276, 35277, 35278, 35279, 35280, 35281] from rfl]
      decide
    have hsep : (pts.map Prod.fst).Pairwise Separated := by
      rw [show pts.map Prod.fst = [0, 5, 11, 16, 21, 26, 31] from rfl]; decide
    let y := writeVals (writePoints (fun _ => 0) pts) vals
    have hv : ∀ r v, (r, v) ∈ vals → y r = v := fun r v h => writeVals_of_mem _ hnd h
    have hp : ∀ r P, (r, P) ∈ pts → evCode y (varPoint r) = P := fun r P h' =>
      evCode_writeVals_writePoints _ hsep h' (by
        intro e he
        have h1 := hfst e.1 (List.mem_map_of_mem he)
        simp only [pts, List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h' | h' | h' | h' | h' | h' | h' <;> obtain ⟨rfl, -⟩ := Prod.mk.inj h' <;>
          omega)
    have pN : evCode y (varPoint 0) = iota n := hp _ _ (by simp [pts])
    have pK : evCode y (varPoint 5) = iota κ := hp _ _ (by simp [pts])
    have pC : evCode y (varPoint 11) = iota (κ * n) := hp _ _ (by simp [pts])
    have pH : evCode y (varPoint 16) = iota h := hp _ _ (by simp [pts])
    have pU : evCode y (varPoint 21) = iota s₀ := hp _ _ (by simp [pts])
    have pV0 : evCode y (varPoint 26) = iota (h - κ) := hp _ _ (by simp [pts])
    have pV1 : evCode y (varPoint 31) = iota (s₀ - κ * n) := hp _ _ (by simp [pts])
    have vz : ∀ k (w : K0), (k, w.re) ∈ vals → (k + 1, w.im) ∈ vals →
        Pair.val y (varPair k) = w := fun k w h1 h2 => by rw [val_varPair, hv _ _ h1, hv _ _ h2]
    have zinv : ∀ m : ℤ, ∀ k, (k, (codeNormY (iota m))⁻¹) ∈ vals →
        m ≠ 0 → codeNormY (iota m) * y k = 1 := fun m k h hm => by
      rw [hv _ _ h, mul_inv_cancel₀ (codeNormY_iota_ne_zero hm)]
    have fin0 : ∀ (k : ℕ) (m : ℤ), evCode y (varPoint k) = iota m → m ≠ 0 →
        ev y (varPoint k 0) = 0 := fun k m hk hm => by
      have := congrFun hk 0; simp only [evCode] at this
      rw [this]; exact (iota_apply_zero_eq_zero_iff m).2 hm
    have v10 : y 10 = t := hv _ _ (by simp [vals])
    have v57 : y 35257 = η := hv _ _ (by simp [vals])
    have v58 : y 35258 = q := hv _ _ (by simp [vals])
    have v59 : y 35259 = vtR0 t η := hv _ _ (by simp [vals])
    have v60 : y 35260 = vtA0 t η q := hv _ _ (by simp [vals])
    have v61 : y 35261 = vtR t η q := hv _ _ (by simp [vals])
    have v62 : y 35262 = (Mult.contactPoly t)⁻¹ := hv _ _ (by simp [vals])
    have v63 : y 35263 = (vtA0 t η q)⁻¹ := hv _ _ (by simp [vals])
    have v78 : y 35278 = (W.re ^ 2 - 2 * W.im ^ 2)⁻¹ := hv _ _ (by simp [vals])
    have v79 : y 35279 = Θ := hv _ _ (by simp [vals])
    have v80 : y 35280 = vtR t η q / Θ ^ 2 := hv _ _ (by simp [vals])
    have v81 : y 35281 = Θ⁻¹ := hv _ _ (by simp [vals])
    have zH : Pair.val y (varPair 35233) = zIdx h := vz _ _ (by simp [vals]) (by simp [vals])
    have zU : Pair.val y (varPair 35238) = zIdx s₀ := vz _ _ (by simp [vals]) (by simp [vals])
    have zV0 : Pair.val y (varPair 35243) = zIdx (h - κ) :=
      vz _ _ (by simp [vals]) (by simp [vals])
    have zV1 : Pair.val y (varPair 35248) = zIdx (s₀ - κ * n) :=
      vz _ _ (by simp [vals]) (by simp [vals])
    have wH : Pair.val y (varPair 35231) = wPt (h • genP0) := vz _ _ (by simp [vals]) (by simp [vals])
    have wU : Pair.val y (varPair 35236) = wPt (s₀ • genP0) :=
      vz _ _ (by simp [vals]) (by simp [vals])
    have wV0 : Pair.val y (varPair 35241) = wPt ((h - κ) • genP0) :=
      vz _ _ (by simp [vals]) (by simp [vals])
    have wV1 : Pair.val y (varPair 35246) = wPt ((s₀ - κ * n) • genP0) :=
      vz _ _ (by simp [vals]) (by simp [vals])
    have ρ0 : Pair.val y (varPair 35251) = zIdx s₀ / zIdx h := vz _ _ (by simp [vals]) (by simp [vals])
    have ρ1 : Pair.val y (varPair 35254) = zIdx (s₀ - κ * n) / zIdx (h - κ) :=
      vz _ _ (by simp [vals]) (by simp [vals])
    have ω : Pair.val y (varPair 35276) = W⁻¹ := vz _ _ (by simp [vals]) (by simp [vals])
    have hC : ∀ j : Fin 6, Pair.val y (varPair (35264 + 2 * ↑j)) = Cv j := by
      intro j
      fin_cases j
      all_goals exact vz _ _ (by simp [vals]) (by simp [vals])
    have hWv : Pair.val y (slopeW (X 35261) (List.ofFn fun j : Fin 6 =>
        varPair (35264 + 2 * ↑j))) = W := by
      rw [val_slopeW, hWdef, vtW, ev_X, v61]
      exact Finset.prod_congr rfl fun j _ => by rw [hC j]
    have hfeq : ∀ j : Fin 6, Pair.val y (Pair.smul (valueContact (X 10)) (varPair (35264 + 2 * ↑j))) =
        vtD n κ t h s₀ j := fun j => by
      rw [val_smul', ev_valueContact, v10, hC j, hCv, mul_div_cancel₀ _ hF']
    refine ⟨y, ⟨pN, pK, v10⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fin0 5 κ pK hκ, ?_, ?_, ?_,
      fin0 16 h pH hh, fin0 26 _ pV0 hhk', (holds_ixFormula_iota pH).2 wH,
      (holds_zFormula_iota pH).2 ⟨zH, zinv h 35235 (by simp [vals])⟩,
      (holds_ixFormula_iota pU).2 wU,
      (holds_zFormula_iota pU).2 ⟨zU, zinv s₀ 35240 (by simp [vals])⟩,
      (holds_ixFormula_iota pV0).2 wV0,
      (holds_zFormula_iota pV0).2 ⟨zV0, zinv _ 35245 (by simp [vals])⟩,
      (holds_ixFormula_iota pV1).2 wV1,
      (holds_zFormula_iota pV1).2 ⟨zV1, zinv _ 35250 (by simp [vals])⟩, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pN, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pK, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pC, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pH, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pU, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pV0, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pV1, rel_member_iff_iota]; exact ⟨_, rfl⟩
    · rw [pK, pN, pC, hM.rel_iota_iff]
    · rw [pH, evCode_neg_iota pK, pV0, rel_rawAdd_iota, sub_eq_add_neg]
    · rw [pU, evCode_neg_iota pC, pV1, rel_rawAdd_iota, sub_eq_add_neg]
    · refine (holds_divFormula_iff _ _ _ _ _).2 ⟨?_, by rw [ρ0, zU, zH]⟩
      rw [ev_norm_eq, zH, hv 35253 ((zIdx h).re ^ 2 - 2 * (zIdx h).im ^ 2)⁻¹ (by simp [vals])]
      exact mul_inv_cancel₀ (pairNorm_ne_zero_of_ne_zero hzh)
    · refine (holds_divFormula_iff _ _ _ _ _).2 ⟨?_, by rw [ρ1, zV1, zV0]⟩
      rw [ev_norm_eq, zV0, hv 35256 ((zIdx (h - κ)).re ^ 2 - 2 * (zIdx (h - κ)).im ^ 2)⁻¹ (by simp [vals])]
      exact mul_inv_cancel₀ (pairNorm_ne_zero_of_ne_zero hzv)
    · rw [ev_valueContact, v10, v62, mul_inv_cancel₀ hF]
    · simp [v57, heta]
    · simp only [map_mul, ev_X, ev_C, ev_valueContact, v59, v57, v10, vtR0]
      push_cast; ring
    · simp only [map_sub, map_mul, map_pow, map_one, ev_X, v60, v59, v58, vtA0]
    · simp only [ev_X, v60, v63]; exact mul_inv_cancel₀ ha
    · simp only [map_mul, map_pow, ev_X, v61, v59, v60, vtR]
    · exact (hfeq 0).trans (by rw [wH]; rfl)
    · exact (hfeq 1).trans (by rw [wU]; rfl)
    · exact (hfeq 2).trans (by rw [Pair.val_conj, wV0]; rfl)
    · exact (hfeq 3).trans (by rw [Pair.val_conj, wV1]; rfl)
    · exact (hfeq 4).trans (by rw [Pair.val_sub, val_pair_zero, ρ0, ev_X, v10]; rfl)
    · exact (hfeq 5).trans (by rw [Pair.val_sub, val_pair_zero, Pair.val_conj, ρ1, ev_X, v10]; rfl)
    · refine (holds_divFormula_iff _ _ _ _ _).2 ⟨?_, by rw [ω, hWv, Pair.val_one, one_div]⟩
      rw [ev_norm_eq, hWv, v78]
      exact mul_inv_cancel₀ (pairNorm_ne_zero_of_ne_zero hW)
    · have : y 35276 = (W⁻¹).re := by simpa [val_varPair] using congrArg QuadraticAlgebra.re ω
      simp only [map_mul, ev_X, map_ofNat, v79, this, hΘdef, vtTheta, K0.trace_eq]
      rfl
    · simp only [ev_X, v79, v81]; exact mul_inv_cancel₀ hΘ
    · simp only [map_mul, map_pow, ev_X, v80, v79, v61]
      exact div_mul_cancel₀ _ (pow_ne_zero 2 hΘ)
    · rw [ev_X, v80]; exact hpole

end ZInQ.Assembly
