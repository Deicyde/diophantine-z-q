import ZInQKernel.Multiplication.Certificate.TestGroup
import ZInQKernel.Multiplication.Certificate.SlopePredicate

/-!
# Semantics of the slope template

Blueprint: `multiplication/certificate/slope-semantics.md`.

For a parameter vector `a ∈ ℚ²²` with `a₀ = t`, `a₁ = ℓ` and the canonical codes
`ι(c₀), …, ι(c₃)` in the coordinates `2, …, 21`:
`Rel_slope(a) ⟺ Slope(t, ℓ; c)` (`slope_rel_iff`).

Each of the six groups is read by `lift_slopeGroup`: the test-group call gives `(h_g, z_g)` with
`[D_{g,j}] = τ_j(h_g, z_g; c)` (`testGroup_rel_iff`), the pair equations
`den_j C'_{g,j} ≐ D_{g,j}` give `[C'_{g,j}] = C_{gj}` once `R₀ ≠ 0` and `t ≠ 1`, and the division
gadget gives `W_g ≠ 0` and `[ω_g] = W_g⁻¹`; then `θ = Θ`, `θ u_θ ≐ 1` says `Θ ≠ 0`, `Bθ² ≐ R`
says `B = R/Θ²`, and the pole call is `Φ(B)` (`poleTemplate_rel_iff`).
-/

namespace ZInQ.Mult

open MvPolynomial Syntax

/-! ### Values -/

theorem C_eq_ratCast (q : ℚ) : (QuadraticAlgebra.C q : K0) = (q : K0) := by
  rw [QuadraticAlgebra.C_eq_algebraMap]; exact eq_ratCast _ q

theorem val_slopeW_foldl (y : ℕ → ℚ) (R : Poly) (l : List Pair) (W : Pair) :
    Pair.val y (l.foldl (fun W n => W.mul (Pair.one.add (Pair.smul R n.sq))) W) =
      Pair.val y W * (l.map fun n => 1 + (ev y R : K0) * Pair.val y n ^ 2).prod := by
  induction l generalizing W with
  | nil => simp
  | cons n l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, Pair.val_mul, Pair.val_add,
      Pair.val_one, Pair.val_smul, Pair.val_sq, C_eq_ratCast, mul_assoc]

/-- `[W] = ∏_j (1 + R [C'_j]²)`. -/
theorem val_slopeW (y : ℕ → ℚ) (R : Poly) (N : Fin 12 → Pair) :
    Pair.val y (slopeW R (List.ofFn N)) = groupW (ev y R) fun j => Pair.val y (N j) := by
  rw [slopeW, val_slopeW_foldl, Pair.val_one, one_mul, groupW, List.map_ofFn, List.prod_ofFn]
  rfl

/-- The coordinates of the test-group call of a slope group. -/
theorem ev_slopeArgs_left (y : ℕ → ℚ) (β : ℕ) (i : ℕ) (hi : i < 20) :
    ev y (Fin.append (varArgs 2 20) (pairsArgs fun j : Fin 12 => varPair (β + 2 * j))
      ⟨i, by omega⟩) = y (2 + i) := by
  show ev y (Fin.append (varArgs 2 20) (pairsArgs fun j : Fin 12 => varPair (β + 2 * j))
    (Fin.castAdd (12 * 2) ⟨i, hi⟩)) = _
  rw [Fin.append_left, ev_varArgs]

theorem ev_slopeArgs_right (y : ℕ → ℚ) (β : ℕ) (j : ℕ) (hj : j < 12) :
    ev y (Fin.append (varArgs 2 20) (pairsArgs fun j : Fin 12 => varPair (β + 2 * j))
      ⟨20 + 2 * j, by omega⟩) = y (β + 2 * j) ∧
    ev y (Fin.append (varArgs 2 20) (pairsArgs fun j : Fin 12 => varPair (β + 2 * j))
      ⟨21 + 2 * j, by omega⟩) = y (β + 2 * j + 1) := by
  constructor
  · show ev y (Fin.append (varArgs 2 20) (pairsArgs fun j : Fin 12 => varPair (β + 2 * j))
      (Fin.natAdd 20 ⟨2 * j, by omega⟩)) = _
    rw [Fin.append_right]
    simp only [pairsArgs, varPair]
    split_ifs with hpar
    · simp only [ev_X]
      congr 2
      omega
    · exact absurd (by omega) hpar
  · rw [show (⟨21 + 2 * j, by omega⟩ : Fin (20 + 12 * 2)) = Fin.natAdd 20 ⟨2 * j + 1, by omega⟩
      from Fin.ext (by simp only [Fin.natAdd_mk]; omega)]
    rw [Fin.append_right]
    simp only [pairsArgs, varPair]
    split_ifs with hpar
    · exact absurd hpar (by omega)
    · simp only [ev_X]
      congr 2
      omega

/-- The test-group call of a slope group, on canonical shift codes. -/
theorem slope_testGroup_call (y : ℕ → ℚ) (c : Fin 4 → ℤ)
    (hC : ∀ (i : Fin 4) (k : Fin 5), y (2 + (5 * i + k)) = iota (c i) k) (β : ℕ) :
    testGroupTemplate.Rel (fun k => ev y (Fin.append (varArgs 2 20)
      (pairsArgs fun j : Fin 12 => varPair (β + 2 * j)) k)) ↔
      ∃ (h : ℤ) (z : Fin 3 → ℤ), h ≠ 0 ∧ h ≠ c 0 ∧
        ∀ j : Fin 12, pr y (β + 2 * j) = testValues h z c j := by
  refine (testGroup_rel_iff c _ fun i k => by
    rw [← hC i k]; exact ev_slopeArgs_left y β _ (by omega)).trans ?_
  refine exists_congr fun h => exists_congr fun z => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun j => ?_
  obtain ⟨e1, e2⟩ := ev_slopeArgs_right y β j j.isLt
  rw [e1, e2]
  rfl

/-- One slope group: the test-group call, the twelve pair equations and the division gadget. -/
theorem lift_slopeGroup (y : ℕ → ℚ) (c : Fin 4 → ℤ)
    (hC : ∀ (i : Fin 4) (k : Fin 5), y (2 + (5 * i + k)) = iota (c i) k) (den1 den2 R : Poly)
    (β : ℕ) :
    (Formula.and (slopeGroupFormula (varArgs 2 20) den1 den2 R β)).Lift y ↔
      (∃ (h : ℤ) (z : Fin 3 → ℤ), h ≠ 0 ∧ h ≠ c 0 ∧
        ∀ j : Fin 12, pr y (β + 2 * j) = testValues h z c j) ∧
      (∀ j : Fin 12, QuadraticAlgebra.C (ev y (if j.val < 8 then den1 else den2)) *
        pr y (β + 186 + 2 * j) = pr y (β + 2 * j)) ∧
      ev y (slopeW R (List.ofFn fun j : Fin 12 => varPair (β + 186 + 2 * j))).norm *
        y (β + 212) = 1 ∧
      groupW (ev y R) (fun j => pr y (β + 186 + 2 * j)) * pr y (β + 210) = 1 := by
  simp only [slopeGroupFormula, divFormula, lift_and_cons, lift_and_nil, and_true, lift_feq,
    Pair.val_smul, val_varPair, Pair.val_mul, Pair.val_one, lift_nzFormula, val_slopeW]
  rw [Formula.lift_call y testGroupTemplate
    (Fin.append (varArgs 2 20) (pairsArgs fun j : Fin 12 => varPair (β + 2 * j))) (β + 24),
    slope_testGroup_call y c hC β]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, hn, hw⟩ := h
    refine ⟨fun j => ?_, hn, hw⟩
    fin_cases j
    exacts [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  · obtain ⟨hN, hn, hw⟩ := h
    exact ⟨hN 0, hN 1, hN 2, hN 3, hN 4, hN 5, hN 6, hN 7, hN 8, hN 9, hN 10, hN 11, hn, hw⟩

/-- `ev(F(t)) = F(t)`. -/
theorem ev_slopeContact (y : ℕ → ℚ) (t : Poly) : ev y (slopeContact t) = contactPoly (ev y t) := by
  simp only [slopeContact, contactPoly, map_mul, map_add, map_zero, ev_ofNat, add_zero]

/-- With `[den₁] = R₀(t - 1)²`, `[den₂] = R₀²⁵(t - 1)²⁶`, the normalized pairs are the
normalized tests. -/
theorem normPairs_eq (y : ℕ → ℚ) (den1 den2 : Poly) (β : ℕ) (R0 t : ℚ) (D : Fin 12 → K0)
    (hd1 : ev y den1 = R0 * (t - 1) ^ 2) (hd2 : ev y den2 = R0 ^ 25 * (t - 1) ^ 26)
    (hR0 : R0 ≠ 0) (ht1 : t ≠ 1)
    (hN : ∀ j : Fin 12, QuadraticAlgebra.C (ev y (if j.val < 8 then den1 else den2)) *
        pr y (β + 186 + 2 * j) = pr y (β + 2 * j))
    (hD : ∀ j : Fin 12, pr y (β + 2 * j) = D j) :
    (fun j : Fin 12 => pr y (β + 186 + 2 * j)) = normTests R0 t D := by
  funext j
  have ht : (t - 1 : ℚ) ≠ 0 := sub_ne_zero.2 ht1
  have hden : ((R0 : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Rat.cast_ne_zero.2 hR0)) (pow_ne_zero _ (Rat.cast_ne_zero.2 ht))
  rw [normTests, eq_div_iff hden, ← hD j, ← hN j, mul_comm, C_eq_ratCast]
  congr 1
  by_cases hj : j.val < 8
  · rw [ite_eq_left hj, hd1, prec_of_lt hj]; push_cast; ring
  · rw [ite_eq_right hj, hd2, prec_of_ge (by omega)]; push_cast; ring

/-! ### The witnesses of a slope -/

/-- Component `e` (`0` for the rational part) of an element of `K₀`. -/
def comp (x : K0) (e : ℕ) : ℚ := if e = 0 then x.re else x.im

/-- The variables of one slope group, by position in its block of `213`: the twelve pairs
`D_{g,j}`, the test-group block, the twelve pairs `C'_{g,j}`, `ω_g` and the inverse witness. -/
noncomputable def slGroupVal (D N : Fin 12 → K0) (ω : K0) (u : ℚ) (r : ℕ) : ℚ :=
  if h : r < 24 then comp (D ⟨r / 2, by omega⟩) (r % 2)
  else if r < 186 then 0
  else if h : r < 210 then comp (N ⟨(r - 186) / 2, by omega⟩) ((r - 186) % 2)
  else if r = 210 then ω.re
  else if r = 211 then ω.im
  else if r = 212 then u
  else 0

/-- An assignment of the variables of `slope`: the parameters, `η, q, R₀` and the four inverse
witnesses (`v`), the six groups at `29 + 213g`, `B = X₁₃₀₇` and `u_θ = X₁₃₀₈`. -/
noncomputable def slY (a : Fin 22 → ℚ) (v : Fin 7 → ℚ) (D N : Fin 6 → Fin 12 → K0)
    (ω : Fin 6 → K0) (u : Fin 6 → ℚ) (B iθ : ℚ) (i : ℕ) : ℚ :=
  if h : i < 22 then a ⟨i, h⟩
  else if h : i < 29 then v ⟨i - 22, by omega⟩
  else if h : i < 1307 then
    slGroupVal (D ⟨(i - 29) / 213, by omega⟩) (N ⟨(i - 29) / 213, by omega⟩)
      (ω ⟨(i - 29) / 213, by omega⟩) (u ⟨(i - 29) / 213, by omega⟩) ((i - 29) % 213)
  else if i = 1307 then B
  else if i = 1308 then iθ
  else 0

section slY

variable (a : Fin 22 → ℚ) (v : Fin 7 → ℚ) (D N : Fin 6 → Fin 12 → K0) (ω : Fin 6 → K0)
  (u : Fin 6 → ℚ) (B iθ : ℚ)

theorem slY_lt (i : Fin 22) : slY a v D N ω u B iθ i = a i := by
  rw [slY, dite_eq_left i.isLt]

theorem slY_v {i : ℕ} (k : Fin 7) (hi : i = 22 + k) : slY a v D N ω u B iθ i = v k := by
  subst hi
  rw [slY, dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg v (Fin.ext (by simp))

theorem slY_group {i : ℕ} (g : Fin 6) {r : ℕ} (hr : r < 213) (hi : i = 29 + 213 * g + r) :
    slY a v D N ω u B iθ i = slGroupVal (D g) (N g) (ω g) (u g) r := by
  subst hi
  have hg := g.isLt
  rw [slY, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  have h1 : (29 + 213 * (g : ℕ) + r - 29) / 213 = g := by omega
  have h2 : (29 + 213 * (g : ℕ) + r - 29) % 213 = r := by omega
  rw [h2]
  have e : (⟨(29 + 213 * (g : ℕ) + r - 29) / 213, by omega⟩ : Fin 6) = g := Fin.ext h1
  rw [e]

theorem slY_1307 : slY a v D N ω u B iθ 1307 = B := by
  rw [slY, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_left rfl]

theorem slY_1308 : slY a v D N ω u B iθ 1308 = iθ := by
  rw [slY, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left rfl]

theorem slY_D (g : Fin 6) (j : Fin 12) {n : ℕ} (hn : n = 29 + 213 * g + 2 * j) :
    pr (slY a v D N ω u B iθ) n = D g j := by
  subst hn
  ext
  · show slY a v D N ω u B iθ (29 + 213 * g + 2 * j) = _
    rw [slY_group a v D N ω u B iθ g (r := 2 * j) (by omega) rfl, slGroupVal,
      dite_eq_left (by omega)]
    have e : (⟨2 * (j : ℕ) / 2, by omega⟩ : Fin 12) = j := Fin.ext (by simp)
    rw [e, comp, ite_eq_left (by omega)]
  · show slY a v D N ω u B iθ (29 + 213 * g + 2 * j + 1) = _
    rw [slY_group a v D N ω u B iθ g (r := 2 * j + 1) (by omega) (by omega), slGroupVal,
      dite_eq_left (by omega)]
    have e : (⟨(2 * (j : ℕ) + 1) / 2, by omega⟩ : Fin 12) = j := Fin.ext (by simp; omega)
    rw [e, comp, ite_eq_right (by omega)]

theorem slY_N (g : Fin 6) (j : Fin 12) {n : ℕ} (hn : n = 29 + 213 * g + 186 + 2 * j) :
    pr (slY a v D N ω u B iθ) n = N g j := by
  subst hn
  ext
  · show slY a v D N ω u B iθ (29 + 213 * g + 186 + 2 * j) = _
    rw [slY_group a v D N ω u B iθ g (r := 186 + 2 * j) (by omega) (by omega), slGroupVal,
      dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega)]
    have e : (⟨(186 + 2 * (j : ℕ) - 186) / 2, by omega⟩ : Fin 12) = j := Fin.ext (by simp)
    rw [e, comp, ite_eq_left (by omega)]
  · show slY a v D N ω u B iθ (29 + 213 * g + 186 + 2 * j + 1) = _
    rw [slY_group a v D N ω u B iθ g (r := 186 + 2 * j + 1) (by omega) (by omega), slGroupVal,
      dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega)]
    have e : (⟨(186 + 2 * (j : ℕ) + 1 - 186) / 2, by omega⟩ : Fin 12) = j :=
      Fin.ext (by simp; omega)
    rw [e, comp, ite_eq_right (by omega)]

theorem slY_ω (g : Fin 6) {n : ℕ} (hn : n = 29 + 213 * g + 210) :
    pr (slY a v D N ω u B iθ) n = ω g := by
  subst hn
  ext
  · show slY a v D N ω u B iθ (29 + 213 * g + 210) = _
    rw [slY_group a v D N ω u B iθ g (r := 210) (by omega) rfl, slGroupVal,
      dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      ite_eq_left rfl]
  · show slY a v D N ω u B iθ (29 + 213 * g + 210 + 1) = _
    rw [slY_group a v D N ω u B iθ g (r := 211) (by omega) (by omega), slGroupVal,
      dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left rfl]

theorem slY_u (g : Fin 6) {n : ℕ} (hn : n = 29 + 213 * g + 212) :
    slY a v D N ω u B iθ n = u g := by
  rw [slY_group a v D N ω u B iθ g (r := 212) (by omega) hn, slGroupVal,
    dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

end slY

/-- The denominators clear the normalized tests. -/
theorem normTests_spec (R0 t : ℚ) (D : Fin 12 → K0) (j : Fin 12) (hR0 : R0 ≠ 0) (ht1 : t ≠ 1) :
    QuadraticAlgebra.C (if j.val < 8 then R0 * (t - 1) ^ 2 else R0 ^ 25 * (t - 1) ^ 26) *
      normTests R0 t D j = D j := by
  have ht : (t - 1 : ℚ) ≠ 0 := sub_ne_zero.2 ht1
  have hden : ((R0 : K0) ^ prec j * ((t - 1 : ℚ) : K0) ^ (prec j + 1)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Rat.cast_ne_zero.2 hR0)) (pow_ne_zero _ (Rat.cast_ne_zero.2 ht))
  rw [normTests, C_eq_ratCast, mul_comm, div_mul_eq_mul_div, div_eq_iff hden]
  congr 1
  by_cases hj : j.val < 8
  · rw [ite_eq_left hj, prec_of_lt hj]; push_cast; ring
  · rw [ite_eq_right hj, prec_of_ge (by omega)]; push_cast; ring

/-- **Semantics of the slope template.** -/
theorem slope_rel_iff (t ℓ : ℚ) (c : Fin 4 → ℤ) (a : Fin 22 → ℚ) (ht : a 0 = t) (hℓ : a 1 = ℓ)
    (hc : ∀ (i : Fin 4) (k : Fin 5), a ⟨2 + (5 * i + k), by omega⟩ = iota (c i) k) :
    slopeTemplate.Rel a ↔ SlopePred t ℓ c := by
  rw [slopeTemplate_rel_iff]
  have common : ∀ y : ℕ → ℚ, (∀ i : Fin 22, y i = a i) →
      y 0 = t ∧ y 1 = ℓ ∧ ∀ (i : Fin 4) (k : Fin 5), y (2 + (5 * i + k)) = iota (c i) k := by
    intro y hya
    refine ⟨(hya 0).trans ht, (hya 1).trans hℓ, fun i k => ?_⟩
    rw [← hc i k]; exact hya ⟨2 + (5 * i + k), by omega⟩
  constructor
  · rintro ⟨y, hya, hL⟩
    obtain ⟨hy0, hy1, hC⟩ := common y hya
    simp only [slopeFormula, lift_and_append, lift_and_cons, lift_and_nil, and_true,
      lift_nzFormula, Formula.lift_eq, and_assoc] at hL
    obtain ⟨heta, ht1, hF, hl, hR0, ha, g0, g1, g2, g3, g4, g5, hθ, hB, hpole⟩ := hL
    simp only [map_pow, map_sub, map_mul, map_add, map_one, ev_X, ev_ofNat, ev_slopeContact, hy0,
      hy1] at heta ht1 hF hl hR0 ha hθ hB
    have ht1' : t ≠ 1 := fun h => by
      rw [h, sub_self, zero_mul] at ht1; exact zero_ne_one ht1
    have htC : t ∉ contactSet := fun h => by
      rw [(contactPoly_eq_zero_iff t).2 h, zero_mul] at hF; exact zero_ne_one hF
    have hℓ0 : ℓ ≠ 0 := left_ne_zero_of_mul_eq_one hl
    have hη : y 22 = 1 ∨ y 22 = -1 := by
      have : (y 22 - 1) * (y 22 + 1) = 0 := by linear_combination heta
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hR0eq : y 24 = slopeR0 (y 22) t := by
      rw [slopeR0, eq_div_iff (pow_ne_zero _ (sub_ne_zero.2 ht1'))]; exact hR0
    have hR0ne : slopeR0 (y 22) t ≠ 0 := slopeR0_ne_zero hη htC ht1'
    rw [hR0eq] at ha hB
    have ha' : slopeA (slopeR0 (y 22) t) (y 23) ≠ 0 := left_ne_zero_of_mul_eq_one ha
    have hd1 : ev y (X 24 * (X 0 - 1) ^ 2) = slopeR0 (y 22) t * (t - 1) ^ 2 := by
      simp only [map_mul, map_pow, map_sub, map_one, ev_X, hy0, hR0eq]
    have hd2 : ev y (X 24 ^ 25 * (X 0 - 1) ^ 26) = slopeR0 (y 22) t ^ 25 * (t - 1) ^ 26 := by
      simp only [map_mul, map_pow, map_sub, map_one, ev_X, hy0, hR0eq]
    have hRv : ev y (X 1 ^ 2 * (1 - X 24 * X 23 ^ 2) ^ 2 * X 24) =
        slopeR ℓ (slopeA (slopeR0 (y 22) t) (y 23)) (slopeR0 (y 22) t) := by
      simp only [map_mul, map_pow, map_sub, map_one, ev_X, hy1, hR0eq]; rfl
    have hext : ∀ β : ℕ,
        (Formula.and (slopeGroupFormula (varArgs 2 20) (X 24 * (X 0 - 1) ^ 2)
          (X 24 ^ 25 * (X 0 - 1) ^ 26) (X 1 ^ 2 * (1 - X 24 * X 23 ^ 2) ^ 2 * X 24) β)).Lift y →
        ∃ (h : ℤ) (z : Fin 3 → ℤ), (h ≠ 0 ∧ h ≠ c 0) ∧
          groupW (slopeR ℓ (slopeA (slopeR0 (y 22) t) (y 23)) (slopeR0 (y 22) t))
            (normTests (slopeR0 (y 22) t) t (testValues h z c)) * pr y (β + 210) = 1 := by
      intro β hg
      rw [lift_slopeGroup y c hC] at hg
      obtain ⟨⟨h, z, hh, hc0, hD⟩, hN, -, hw⟩ := hg
      rw [hRv, normPairs_eq y _ _ β _ t _ hd1 hd2 hR0ne ht1' hN hD] at hw
      exact ⟨h, z, ⟨hh, hc0⟩, hw⟩
    obtain ⟨h0, z0, hz0, w0⟩ := hext 29 g0
    obtain ⟨h1, z1, hz1, w1⟩ := hext 242 g1
    obtain ⟨h2, z2, hz2, w2⟩ := hext 455 g2
    obtain ⟨h3, z3, hz3, w3⟩ := hext 668 g3
    obtain ⟨h4, z4, hz4, w4⟩ := hext 881 g4
    obtain ⟨h5, z5, hz5, w5⟩ := hext 1094 g5
    have hω : ∀ g : Fin 6,
        (groupW (slopeR ℓ (slopeA (slopeR0 (y 22) t) (y 23)) (slopeR0 (y 22) t))
          (normTests (slopeR0 (y 22) t) t
            (testValues (![h0, h1, h2, h3, h4, h5] g) (![z0, z1, z2, z3, z4, z5] g) c))) *
          pr y (29 + 213 * g + 210) = 1 := by
      intro g; fin_cases g
      exacts [w0, w1, w2, w3, w4, w5]
    have hΘ : traceTheta (fun g => groupW (slopeR ℓ (slopeA (slopeR0 (y 22) t) (y 23))
        (slopeR0 (y 22) t)) (normTests (slopeR0 (y 22) t) t
          (testValues (![h0, h1, h2, h3, h4, h5] g) (![z0, z1, z2, z3, z4, z5] g) c))) =
        2 * (y 239 + y 452 + y 665 + y 878 + y 1091 + y 1304) := by
      rw [traceTheta_eq, Fin.sum_univ_six, ← eq_inv_of_mul_eq_one_right (hω 0),
        ← eq_inv_of_mul_eq_one_right (hω 1), ← eq_inv_of_mul_eq_one_right (hω 2),
        ← eq_inv_of_mul_eq_one_right (hω 3), ← eq_inv_of_mul_eq_one_right (hω 4),
        ← eq_inv_of_mul_eq_one_right (hω 5)]
      rfl
    rw [← hΘ] at hθ hB
    have hΘne := left_ne_zero_of_mul_eq_one hθ
    rw [Formula.lift_call y poleTemplate ![X 1307] 1309] at hpole
    replace hpole : PoleSoluble (y 1307) := by
      have := (poleTemplate_rel_iff _).1 hpole
      simpa using this
    rw [eq_div_of_mul_eq (pow_ne_zero 2 hΘne) hB] at hpole
    refine ⟨htC, ht1', hℓ0, y 22, y 23, ![h0, h1, h2, h3, h4, h5], ![z0, z1, z2, z3, z4, z5], hη,
      ha', fun g => ?_, fun g => left_ne_zero_of_mul_eq_one (hω g), hΘne, hpole⟩
    fin_cases g
    exacts [hz0, hz1, hz2, hz3, hz4, hz5]
  · rintro ⟨htC, ht1, hℓ0, η, q, hs, zs, hη, ha, hhz, hW, hΘ, hΦ⟩
    have hR0ne : slopeR0 η t ≠ 0 := slopeR0_ne_zero hη htC ht1
    obtain ⟨R0, hR0d⟩ : ∃ R0, R0 = slopeR0 η t := ⟨_, rfl⟩
    rw [← hR0d] at ha hW hΘ hΦ hR0ne
    obtain ⟨RR, hRRd⟩ : ∃ RR, RR = slopeR ℓ (slopeA R0 q) R0 := ⟨_, rfl⟩
    rw [← hRRd] at hW hΘ hΦ
    obtain ⟨W, hWd⟩ : ∃ W : Fin 6 → K0,
        W = fun g => groupW RR (normTests R0 t (testValues (hs g) (zs g) c)) := ⟨_, rfl⟩
    rw [← hWd] at hΘ hΦ
    have hW' : ∀ g, W g ≠ 0 := by subst hWd; exact hW
    obtain ⟨y, hy⟩ : ∃ y, y = slY a ![η, q, R0, (t - 1)⁻¹, (contactPoly t)⁻¹, ℓ⁻¹,
        (slopeA R0 q)⁻¹] (fun g => testValues (hs g) (zs g) c)
        (fun g => normTests R0 t (testValues (hs g) (zs g) c)) (fun g => (W g)⁻¹)
        (fun g => normInv (W g)) (RR / traceTheta W ^ 2) (traceTheta W)⁻¹ := ⟨_, rfl⟩
    have hya : ∀ i : Fin 22, y i = a i := hy ▸ slY_lt _ _ _ _ _ _ _ _
    obtain ⟨hy0, hy1, hC⟩ := common y hya
    have hv : ∀ (k : Fin 7) (i : ℕ), i = 22 + k → y i = ![η, q, R0, (t - 1)⁻¹,
        (contactPoly t)⁻¹, ℓ⁻¹, (slopeA R0 q)⁻¹] k :=
      fun k i hi => hy ▸ slY_v _ _ _ _ _ _ _ _ k hi
    have y22 : y 22 = η := hv 0 22 rfl
    have y23 : y 23 = q := hv 1 23 rfl
    have y24 : y 24 = R0 := hv 2 24 rfl
    have y25 : y 25 = (t - 1)⁻¹ := hv 3 25 rfl
    have y26 : y 26 = (contactPoly t)⁻¹ := hv 4 26 rfl
    have y27 : y 27 = ℓ⁻¹ := hv 5 27 rfl
    have y28 : y 28 = (slopeA R0 q)⁻¹ := hv 6 28 rfl
    have hDv : ∀ (g : Fin 6) (j : Fin 12) (n : ℕ), n = 29 + 213 * g + 2 * j →
        pr y n = testValues (hs g) (zs g) c j :=
      fun g j n hn => hy ▸ slY_D _ _ _ _ _ _ _ _ g j hn
    have hNv : ∀ (g : Fin 6) (j : Fin 12) (n : ℕ), n = 29 + 213 * g + 186 + 2 * j →
        pr y n = normTests R0 t (testValues (hs g) (zs g) c) j :=
      fun g j n hn => hy ▸ slY_N _ _ _ _ _ _ _ _ g j hn
    have hωv : ∀ (g : Fin 6) (n : ℕ), n = 29 + 213 * g + 210 → pr y n = (W g)⁻¹ :=
      fun g n hn => hy ▸ slY_ω _ _ _ _ _ _ _ _ g hn
    have huv : ∀ (g : Fin 6) (n : ℕ), n = 29 + 213 * g + 212 → y n = normInv (W g) :=
      fun g n hn => hy ▸ slY_u _ _ _ _ _ _ _ _ g hn
    have y1307 : y 1307 = RR / traceTheta W ^ 2 := hy ▸ slY_1307 _ _ _ _ _ _ _ _
    have y1308 : y 1308 = (traceTheta W)⁻¹ := hy ▸ slY_1308 _ _ _ _ _ _ _ _
    have hθv : 2 * (y 239 + y 452 + y 665 + y 878 + y 1091 + y 1304) = traceTheta W := by
      rw [traceTheta_eq, Fin.sum_univ_six, ← hωv 0 239 rfl, ← hωv 1 452 rfl, ← hωv 2 665 rfl,
        ← hωv 3 878 rfl, ← hωv 4 1091 rfl, ← hωv 5 1304 rfl]
      rfl
    have hevR : ev y (X 1 ^ 2 * (1 - X 24 * X 23 ^ 2) ^ 2 * X 24) = RR := by
      simp only [map_mul, map_pow, map_sub, map_one, ev_X, hy1, y23, y24, hRRd]; rfl
    have hgrp : ∀ (β : ℕ) (g : Fin 6), β = 29 + 213 * g →
        (Formula.and (slopeGroupFormula (varArgs 2 20) (X 24 * (X 0 - 1) ^ 2)
          (X 24 ^ 25 * (X 0 - 1) ^ 26) (X 1 ^ 2 * (1 - X 24 * X 23 ^ 2) ^ 2 * X 24) β)).Lift y := by
      intro β g hβ
      have eW : W g = groupW RR (normTests R0 t (testValues (hs g) (zs g) c)) := by rw [hWd]
      have hNf : (fun j : Fin 12 => pr y (β + 186 + 2 * j)) =
          normTests R0 t (testValues (hs g) (zs g) c) :=
        funext fun j => hNv g j _ (by omega)
      rw [lift_slopeGroup y c hC]
      refine ⟨⟨hs g, zs g, (hhz g).1, (hhz g).2, fun j => hDv g j _ (by omega)⟩, fun j => ?_,
        ?_, ?_⟩
      · rw [hNv g j _ (by omega), hDv g j _ (by omega)]
        have e : ev y (if j.val < 8 then X 24 * (X 0 - 1) ^ 2 else X 24 ^ 25 * (X 0 - 1) ^ 26) =
            if j.val < 8 then R0 * (t - 1) ^ 2 else R0 ^ 25 * (t - 1) ^ 26 := by
          split_ifs <;> simp only [map_mul, map_pow, map_sub, map_one, ev_X, hy0, y24]
        rw [e]
        exact normTests_spec R0 t _ j hR0ne ht1
      · rw [Pair.ev_norm, ← Pair.re_val, ← Pair.im_val, val_slopeW]
        simp only [val_varPair]
        rw [hevR, hNf, huv g _ (by omega), ← eW]
        exact normInv_spec (hW' g)
      · rw [hevR, hNf, hωv g _ (by omega), ← eW]
        exact mul_inv_cancel₀ (hW' g)
    refine ⟨y, hya, ?_⟩
    simp only [slopeFormula, lift_and_append, lift_and_cons, lift_and_nil, and_true,
      lift_nzFormula, Formula.lift_eq, and_assoc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hgrp 29 0 rfl, hgrp 242 1 rfl, hgrp 455 2 rfl,
      hgrp 668 3 rfl, hgrp 881 4 rfl, hgrp 1094 5 rfl, ?_, ?_, ?_⟩
    · simp only [map_pow, ev_X, map_one, y22]
      rcases hη with rfl | rfl <;> norm_num
    · simp only [map_sub, map_one, ev_X, hy0, y25]
      exact mul_inv_cancel₀ (sub_ne_zero.2 ht1)
    · rw [ev_slopeContact, ev_X, hy0, y26]
      exact mul_inv_cancel₀ (contactPoly_ne_zero htC)
    · rw [ev_X, hy1, y27]
      exact mul_inv_cancel₀ hℓ0
    · simp only [map_mul, map_pow, map_sub, map_one, ev_X, ev_slopeContact, hy0, y22, y24]
      rw [hR0d, slopeR0, div_mul_cancel₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht1))]
    · simp only [map_mul, map_pow, map_sub, map_one, ev_X, y23, y24, y28]
      exact mul_inv_cancel₀ ha
    · simp only [map_mul, map_add, ev_ofNat, ev_X, y1308]
      rw [hθv]
      exact mul_inv_cancel₀ hΘ
    · simp only [map_mul, map_pow, map_add, ev_ofNat, ev_X, y1307]
      rw [hθv, div_mul_cancel₀ _ (pow_ne_zero 2 hΘ), ← hevR]
      simp only [map_mul, map_pow, map_sub, map_one, ev_X]
    · rw [Formula.lift_call y poleTemplate ![X 1307] 1309]
      exact (poleTemplate_rel_iff _).2 (by simpa [y1307] using hΦ)

end ZInQ.Mult
