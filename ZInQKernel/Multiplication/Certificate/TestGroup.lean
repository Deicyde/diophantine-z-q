import ZInQKernel.Multiplication.Certificate.LiftLemmas

/-!
# Semantics of the test-group template

Blueprint: `multiplication/certificate/test-group-semantics.md`.

For `c₀, …, c₃ ∈ ℤ` and a parameter vector `a ∈ ℚ⁴⁴` whose first twenty coordinates are the
canonical codes `ι(c₀), …, ι(c₃)`, with output pairs `D_j = (a_{20+2j}, a_{21+2j})`:
`Rel_test_group(a) ⟺ ∃ h, z₁, z₂, z₃ ∈ ℤ, h ≠ 0, h ≠ c₀, [D_j] = τ_j(h, z; c)` for all `j`
(`testGroup_rel_iff`; indices of the twelve outputs from `0`).

The proof reads the lifted formula of the template atom by atom (`lift_root`, `lift_local`): the
membership and raw-addition calls make `F_i = ι(f_i)` and `V_i = ι(f_i - c_i)`; the `fin` atoms
give `f₀ ≠ 0` and `f₀ ≠ c₀`; the local templates give `ζ, λ, ρ` at the eight points; the inverse
atoms make `λ₀, λ₄ ≠ 0`, so the ratio pairs are the quotients `A_i`, `B_i`. Conversely the
witnesses are written down explicitly (`tgY`), using `L(z([n]P₀)) ≠ 0` for `n ≠ 0`
(`ZInQ.Mult.log25_z_ne_zero`).
-/

namespace ZInQ.Mult

open MvPolynomial Syntax WeierstrassCurve WeierstrassCurve.Affine

/-! ### Reading the lifted formula -/

/-- The calls `member[F]` and `raw_add[F, neg(C), V]` of a root. -/
theorem lift_root (y : ℕ → ℚ) (F C V : Code) (w : ℕ) :
    (Formula.and (testGroupRootFormula F C V w)).Lift y ↔
      memberTemplate.Rel (fun k : Fin 5 => ev y (F k)) ∧
        rawAddTemplate.Rel (Fin.append (Fin.append (fun k => ev y (F k))
          (negCode fun k => ev y (C k))) fun k => ev y (V k)) := by
  simp only [testGroupRootFormula, lift_and_cons, lift_and_nil, and_true]
  rw [Formula.lift_call y memberTemplate F w,
    Formula.lift_call y rawAddTemplate (Fin.append (Fin.append F C.neg) V) (w + 7)]
  have e : (fun k => ev y (Fin.append (Fin.append F C.neg) V k)) =
      Fin.append (Fin.append (fun k => ev y (F k)) (negCode fun k => ev y (C k)))
        fun k => ev y (V k) :=
    (ev_comp_append y (Fin.append F C.neg) V).trans
      (by rw [ev_comp_append y F C.neg, ev_comp_neg y C])
  exact and_congr Iff.rfl (iff_of_eq (congrArg rawAddTemplate.Rel e))

/-- The calls `raw_z[P, ζ]`, `log25[ζ, λ]`, `raw_inverse_x[P, ρ]` of a local test. -/
theorem lift_local (y : ℕ → ℚ) (P : Code) (b : ℕ) :
    (Formula.and (testGroupLocalFormula P b)).Lift y ↔
      rawZTemplate.Rel (Fin.append (fun k => ev y (P k)) (prv y b)) ∧
        log25Template.Rel (Fin.append (prv y b) (prv y (b + 2))) ∧
        rawInverseXTemplate.Rel (Fin.append (fun k => ev y (P k)) (prv y (b + 4))) := by
  simp only [testGroupLocalFormula, lift_and_cons, lift_and_nil, and_true]
  rw [Formula.lift_call y rawZTemplate (Fin.append P (varPair b).args) (b + 6),
    Formula.lift_call y log25Template (Fin.append (varPair b).args (varPair (b + 2)).args) (b + 7),
    Formula.lift_call y rawInverseXTemplate (Fin.append P (varPair (b + 4)).args) (b + 7)]
  have e1 : (fun k => ev y (Fin.append P (varPair b).args k)) =
      Fin.append (fun k => ev y (P k)) (prv y b) :=
    (ev_comp_append y P (varPair b).args).trans (by rw [ev_comp_pairArgs y b])
  have e2 : (fun k => ev y (Fin.append (varPair b).args (varPair (b + 2)).args k)) =
      Fin.append (prv y b) (prv y (b + 2)) :=
    (ev_comp_append y (varPair b).args (varPair (b + 2)).args).trans
      (by rw [ev_comp_pairArgs y b, ev_comp_pairArgs y (b + 2)])
  have e3 : (fun k => ev y (Fin.append P (varPair (b + 4)).args k)) =
      Fin.append (fun k => ev y (P k)) (prv y (b + 4)) :=
    (ev_comp_append y P (varPair (b + 4)).args).trans (by rw [ev_comp_pairArgs y (b + 4)])
  exact and_congr (iff_of_eq (congrArg rawZTemplate.Rel e1))
    (and_congr (iff_of_eq (congrArg log25Template.Rel e2))
      (iff_of_eq (congrArg rawInverseXTemplate.Rel e3)))

/-- A root whose shift is the canonical code `ι(c)`: `F = ι(f)` and `V = ι(f - c)`. -/
theorem lift_root_iota (y : ℕ → ℚ) (k k' : ℕ) (C : Code) (w : ℕ) (c : ℤ)
    (hC : (fun i => ev y (C i)) = iota c) :
    (Formula.and (testGroupRootFormula (varPoint k) C (varPoint k') w)).Lift y ↔
      ∃ f : ℤ, pt y k = iota f ∧ pt y k' = iota (f - c) := by
  rw [lift_root, ev_comp_varPoint, ev_comp_varPoint, hC, member_rawAdd_iff]

/-- A local test at a point with code `ι(n)`: `ζ = z([n]P₀)`, `λ = L(ζ)`, `ρ = ρ([n]P₀)`. -/
theorem lift_local_iota (y : ℕ → ℚ) (k b : ℕ) (n : ℤ) (h : pt y k = iota n) :
    (Formula.and (testGroupLocalFormula (varPoint k) b)).Lift y ↔
      pr y b = zOf (n • genP0) ∧ pr y (b + 2) = Lam (n • genP0) ∧
        pr y (b + 4) = invX (n • genP0) := by
  rw [lift_local, ev_comp_varPoint, h, rawZ_rel_iota, log25_rel_iff, rawInverseX_rel_iota]
  simp only [pairK_prv]
  constructor
  · rintro ⟨hz, hl, hr⟩; exact ⟨hz, by rw [hl, hz]; rfl, hr⟩
  · rintro ⟨hz, hl, hr⟩; exact ⟨hz, by rw [hl, hz]; rfl, hr⟩

/-- A local test at a point `Q` that is `O` or has `x, y ≠ 0`. -/
theorem lift_local_pt (y : ℕ → ℚ) (k b : ℕ) (Q : genCurve.toAffine.Point)
    (hQ : ∀ x y h, Q = Point.some x y h → x ≠ 0 ∧ y ≠ 0) (h : pt y k = pointCode Q) :
    (Formula.and (testGroupLocalFormula (varPoint k) b)).Lift y ↔
      pr y b = zOf Q ∧ pr y (b + 2) = Lam Q ∧ pr y (b + 4) = invX Q := by
  rw [lift_local, ev_comp_varPoint, h, rawZ_rel_iff_of Q (fun x y h he => (hQ x y h he).2),
    log25_rel_iff, rawInverseX_rel_iff_of Q (fun x y h he => (hQ x y h he).1)]
  simp only [pairK_prv]
  constructor
  · rintro ⟨hz, hl, hr⟩; exact ⟨hz, by rw [hl, hz]; rfl, hr⟩
  · rintro ⟨hz, hl, hr⟩; exact ⟨hz, by rw [hl, hz]; rfl, hr⟩

/-- The parameter points of `test_group` carry the codes `ι(c_i)`. -/
theorem ev_testGroupC (y : ℕ → ℚ) (a : Fin 44 → ℚ) (c : Fin 4 → ℤ)
    (hya : ∀ i : Fin 44, y i = a i)
    (ha : ∀ (i : Fin 4) (k : Fin 5), a ⟨5 * i + k, by omega⟩ = iota (c i) k) (i : Fin 4) :
    (fun k => ev y (testGroupC i k)) = iota (c i) := by
  funext k
  simp only [testGroupC, ev_varPoint]
  rw [← ha i k]
  exact hya ⟨5 * i + k, by omega⟩

/-- The output pairs of `test_group`. -/
theorem val_testGroupD (y : ℕ → ℚ) (a : Fin 44 → ℚ) (hya : ∀ i : Fin 44, y i = a i)
    (j : Fin 12) :
    Pair.val y (testGroupD j) = ⟨a ⟨20 + 2 * j, by omega⟩, a ⟨21 + 2 * j, by omega⟩⟩ := by
  rw [testGroupD, val_varPair]
  ext
  · exact hya ⟨20 + 2 * j, by omega⟩
  · show y (20 + 2 * j + 1) = _
    rw [show 20 + 2 * (j : ℕ) + 1 = 21 + 2 * j by omega]
    exact hya ⟨21 + 2 * j, by omega⟩

/-- `L(z([n]P₀)) ≠ 0` for `n ≠ 0`. -/
theorem Lam_ne_zero {n : ℤ} (hn : n ≠ 0) : Lam (n • genP0) ≠ 0 := by
  obtain ⟨x, y, h, he, -, -, hL⟩ := log25_z_ne_zero hn
  rw [Lam, he, zOf_some]
  exact hL

/-! ### The witnesses of a test group -/

/-- The six local values at a point, by position in its block of seven variables. -/
noncomputable def tgLocal (Q : genCurve.toAffine.Point) : ℕ → ℚ
  | 0 => (zOf Q).re
  | 1 => (zOf Q).im
  | 2 => (Lam Q).re
  | 3 => (Lam Q).im
  | 4 => (invX Q).re
  | 5 => (invX Q).im
  | _ => 0

/-- An assignment of the variables of `test_group`: the parameters `a`, the eight points `P`
at `X₄₄, …, X₈₃`, the local values at the bases `136 + 7j`, the inverse witnesses `w₀, w₁` at
`X₁₉₂, X₁₉₃` and the six ratio pairs `q` at `X₁₉₄, …, X₂₀₅`. Block variables are `0`. -/
noncomputable def tgY (a : Fin 44 → ℚ) (P : Fin 8 → genCurve.toAffine.Point) (w0 w1 : ℚ)
    (q : Fin 6 → K0) (i : ℕ) : ℚ :=
  if h : i < 44 then a ⟨i, h⟩
  else if h : i < 84 then pointCode (P ⟨(i - 44) / 5, by omega⟩) ⟨(i - 44) % 5, by omega⟩
  else if i < 136 then 0
  else if h : i < 192 then tgLocal (P ⟨(i - 136) / 7, by omega⟩) ((i - 136) % 7)
  else if i = 192 then w0
  else if i = 193 then w1
  else if h : i < 206 then
    (if (i - 194) % 2 = 0 then (q ⟨(i - 194) / 2, by omega⟩).re
      else (q ⟨(i - 194) / 2, by omega⟩).im)
  else 0

section tgY

variable (a : Fin 44 → ℚ) (P : Fin 8 → genCurve.toAffine.Point) (w0 w1 : ℚ) (q : Fin 6 → K0)

theorem tgY_lt (i : Fin 44) : tgY a P w0 w1 q i = a i := by
  rw [tgY, dite_eq_left i.isLt]

theorem tgY_point_coord {i j r : ℕ} (hj : j < 8) (hr : r < 5) (hi : i = 44 + 5 * j + r) :
    tgY a P w0 w1 q i = pointCode (P ⟨j, hj⟩) ⟨r, hr⟩ := by
  subst hi
  rw [tgY, dite_eq_right (by omega), dite_eq_left (by omega)]
  have h1 : (44 + 5 * j + r - 44) / 5 = j := by omega
  have h2 : (44 + 5 * j + r - 44) % 5 = r := by omega
  exact congrArg₂ (fun k l => pointCode (P k) l)
    (Fin.ext h1 : (⟨(44 + 5 * j + r - 44) / 5, by omega⟩ : Fin 8) = ⟨j, hj⟩)
    (Fin.ext h2 : (⟨(44 + 5 * j + r - 44) % 5, by omega⟩ : Fin 5) = ⟨r, hr⟩)

theorem tgY_pt {n j : ℕ} (hj : j < 8) (hn : n = 44 + 5 * j) :
    pt (tgY a P w0 w1 q) n = pointCode (P ⟨j, hj⟩) := by
  funext r
  exact tgY_point_coord a P w0 w1 q hj r.isLt (by rw [hn])

theorem tgY_local {i j r : ℕ} (hj : j < 8) (hr : r < 7) (hi : i = 136 + 7 * j + r) :
    tgY a P w0 w1 q i = tgLocal (P ⟨j, hj⟩) r := by
  subst hi
  rw [tgY, dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_left (by omega)]
  have h1 : (136 + 7 * j + r - 136) / 7 = j := by omega
  have h2 : (136 + 7 * j + r - 136) % 7 = r := by omega
  rw [h2]
  exact congrArg (fun k => tgLocal (P k) r)
    (Fin.ext h1 : (⟨(136 + 7 * j + r - 136) / 7, by omega⟩ : Fin 8) = ⟨j, hj⟩)

theorem tgY_z {n j : ℕ} (hj : j < 8) (hn : n = 136 + 7 * j) :
    pr (tgY a P w0 w1 q) n = zOf (P ⟨j, hj⟩) := by
  ext
  · exact tgY_local a P w0 w1 q hj (r := 0) (by norm_num) (by omega)
  · exact tgY_local a P w0 w1 q hj (r := 1) (by norm_num) (by omega)

theorem tgY_L {n j : ℕ} (hj : j < 8) (hn : n = 138 + 7 * j) :
    pr (tgY a P w0 w1 q) n = Lam (P ⟨j, hj⟩) := by
  ext
  · exact tgY_local a P w0 w1 q hj (r := 2) (by norm_num) (by omega)
  · exact tgY_local a P w0 w1 q hj (r := 3) (by norm_num) (by omega)

theorem tgY_rho {n j : ℕ} (hj : j < 8) (hn : n = 140 + 7 * j) :
    pr (tgY a P w0 w1 q) n = invX (P ⟨j, hj⟩) := by
  ext
  · exact tgY_local a P w0 w1 q hj (r := 4) (by norm_num) (by omega)
  · exact tgY_local a P w0 w1 q hj (r := 5) (by norm_num) (by omega)

theorem tgY_192 : tgY a P w0 w1 q 192 = w0 := by
  rw [tgY, dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_right (by omega),
    ite_eq_left rfl]

theorem tgY_193 : tgY a P w0 w1 q 193 = w1 := by
  rw [tgY, dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left rfl]

theorem tgY_q {n k : ℕ} (hk : k < 6) (hn : n = 194 + 2 * k) :
    pr (tgY a P w0 w1 q) n = q ⟨k, hk⟩ := by
  subst hn
  have h1 : (194 + 2 * k - 194) / 2 = k := by omega
  have h1' : (194 + 2 * k + 1 - 194) / 2 = k := by omega
  ext
  · show tgY a P w0 w1 q (194 + 2 * k) = _
    rw [tgY, dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega),
        dite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega),
          ite_eq_left (by omega)]
    exact congrArg (fun l => (q l).re)
      (Fin.ext h1 : (⟨(194 + 2 * k - 194) / 2, by omega⟩ : Fin 6) = ⟨k, hk⟩)
  · show tgY a P w0 w1 q (194 + 2 * k + 1) = _
    rw [tgY, dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega),
        dite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega),
          ite_eq_right (by omega)]
    exact congrArg (fun l => (q l).im)
      (Fin.ext h1' : (⟨(194 + 2 * k + 1 - 194) / 2, by omega⟩ : Fin 6) = ⟨k, hk⟩)

end tgY

/-- The eight points `H, U₁, U₂, U₃, V₀, V₁, V₂, V₃` of a test group. -/
noncomputable def tgPts (h : ℤ) (z : Fin 3 → ℤ) (c : Fin 4 → ℤ) :
    Fin 8 → genCurve.toAffine.Point :=
  ![h • genP0, z 0 • genP0, z 1 • genP0, z 2 • genP0, (h - c 0) • genP0, (z 0 - c 1) • genP0,
    (z 1 - c 2) • genP0, (z 2 - c 3) • genP0]

/-- The six ratios `A₁, A₂, A₃, B₁, B₂, B₃` of a test group. -/
noncomputable def tgQ (h : ℤ) (z : Fin 3 → ℤ) (c : Fin 4 → ℤ) : Fin 6 → K0 :=
  ![Lam (z 0 • genP0) / Lam (h • genP0), Lam (z 1 • genP0) / Lam (h • genP0),
    Lam (z 2 • genP0) / Lam (h • genP0),
    Lam ((z 0 - c 1) • genP0) / Lam ((h - c 0) • genP0),
    Lam ((z 1 - c 2) • genP0) / Lam ((h - c 0) • genP0),
    Lam ((z 2 - c 3) • genP0) / Lam ((h - c 0) • genP0)]

/-- The inverse of the pair norm of `u ≠ 0`. -/
noncomputable def normInv (u : K0) : ℚ := (u.re ^ 2 - 2 * u.im ^ 2)⁻¹

theorem normInv_spec {u : K0} (hu : u ≠ 0) : (u.re ^ 2 - 2 * u.im ^ 2) * normInv u = 1 :=
  mul_inv_cancel₀ ((K0_ne_zero_iff_pairNorm u.re u.im).1 hu)

theorem tgPts_iota (h : ℤ) (z : Fin 3 → ℤ) (c : Fin 4 → ℤ) :
    pointCode (tgPts h z c 0) = iota h ∧ pointCode (tgPts h z c 4) = iota (h - c 0) := ⟨rfl, rfl⟩

/-! ### The theorem -/

/-- **Semantics of the test-group template.** -/
theorem testGroup_rel_iff (c : Fin 4 → ℤ) (a : Fin 44 → ℚ)
    (ha : ∀ (i : Fin 4) (k : Fin 5), a ⟨5 * i + k, by omega⟩ = iota (c i) k) :
    testGroupTemplate.Rel a ↔ ∃ (h : ℤ) (z : Fin 3 → ℤ), h ≠ 0 ∧ h ≠ c 0 ∧
      ∀ j : Fin 12, (⟨a ⟨20 + 2 * j, by omega⟩, a ⟨21 + 2 * j, by omega⟩⟩ : K0) =
        testValues h z c j := by
  rw [testGroupTemplate_rel_iff]
  constructor
  · rintro ⟨y, hya, hL⟩
    have hC := ev_testGroupC y a c hya ha
    simp only [testGroupFormula, lift_and_append, lift_and_cons, lift_and_nil, and_true, lift_feq,
      lift_fin, Pair.val_mul, Pair.val_sub, Pair.val_conj, val_varPair, Nat.reduceMul,
      Nat.reduceAdd, and_assoc] at hL
    obtain ⟨hr0, hr1, hr2, hr3, hfin0, hfin1, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hnz0, hnz1,
      hq0, hq1, hq2, hq3, hq4, hq5, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
      hd11⟩ := hL
    obtain ⟨f0, hF0, hV0⟩ := (lift_root_iota y 44 64 _ 84 (c 0) (hC 0)).1 hr0
    obtain ⟨f1, hF1, hV1⟩ := (lift_root_iota y 49 69 _ 97 (c 1) (hC 1)).1 hr1
    obtain ⟨f2, hF2, hV2⟩ := (lift_root_iota y 54 74 _ 110 (c 2) (hC 2)).1 hr2
    obtain ⟨f3, hF3, hV3⟩ := (lift_root_iota y 59 79 _ 123 (c 3) (hC 3)).1 hr3
    have hf0 : f0 ≠ 0 := by
      rw [← iota_zero_coord_eq_zero_iff, ← hF0]; simpa [pt] using hfin0
    have hfc : f0 - c 0 ≠ 0 := by
      rw [← iota_zero_coord_eq_zero_iff, ← hV0]; simpa [pt] using hfin1
    obtain ⟨-, hL0, hR0⟩ := (lift_local_iota y 44 136 f0 hF0).1 hl0
    obtain ⟨-, hL1, hR1⟩ := (lift_local_iota y 49 143 f1 hF1).1 hl1
    obtain ⟨-, hL2, hR2⟩ := (lift_local_iota y 54 150 f2 hF2).1 hl2
    obtain ⟨-, hL3, hR3⟩ := (lift_local_iota y 59 157 f3 hF3).1 hl3
    obtain ⟨-, hL4, hR4⟩ := (lift_local_iota y 64 164 _ hV0).1 hl4
    obtain ⟨-, hL5, hR5⟩ := (lift_local_iota y 69 171 _ hV1).1 hl5
    obtain ⟨-, hL6, hR6⟩ := (lift_local_iota y 74 178 _ hV2).1 hl6
    obtain ⟨-, hL7, hR7⟩ := (lift_local_iota y 79 185 _ hV3).1 hl7
    have hlam0 : pr y 138 ≠ 0 := lift_nz_norm_imp y 138 192 hnz0
    have hlam4 : pr y 166 ≠ 0 := lift_nz_norm_imp y 166 193 hnz1
    have e0 : pr y 194 = pr y 145 / pr y 138 := eq_div_of_mul_eq hlam0 (by rw [mul_comm]; exact hq0)
    have e1 : pr y 196 = pr y 152 / pr y 138 := eq_div_of_mul_eq hlam0 (by rw [mul_comm]; exact hq1)
    have e2 : pr y 198 = pr y 159 / pr y 138 := eq_div_of_mul_eq hlam0 (by rw [mul_comm]; exact hq2)
    have e3 : pr y 200 = pr y 173 / pr y 166 := eq_div_of_mul_eq hlam4 (by rw [mul_comm]; exact hq3)
    have e4 : pr y 202 = pr y 180 / pr y 166 := eq_div_of_mul_eq hlam4 (by rw [mul_comm]; exact hq4)
    have e5 : pr y 204 = pr y 187 / pr y 166 := eq_div_of_mul_eq hlam4 (by rw [mul_comm]; exact hq5)
    have l0 : pr y 138 = Lam (f0 • genP0) := hL0
    have l1 : pr y 145 = Lam (f1 • genP0) := hL1
    have l2 : pr y 152 = Lam (f2 • genP0) := hL2
    have l3 : pr y 159 = Lam (f3 • genP0) := hL3
    have l4 : pr y 166 = Lam ((f0 - c 0) • genP0) := hL4
    have l5 : pr y 173 = Lam ((f1 - c 1) • genP0) := hL5
    have l6 : pr y 180 = Lam ((f2 - c 2) • genP0) := hL6
    have l7 : pr y 187 = Lam ((f3 - c 3) • genP0) := hL7
    refine ⟨f0, ![f1, f2, f3], hf0, fun h => hfc (sub_eq_zero.2 h), fun j => ?_⟩
    rw [← val_testGroupD y a hya j]
    fin_cases j
    · exact hd0.trans hR0
    · exact hd1.trans hR1
    · exact hd2.trans hR2
    · exact hd3.trans hR3
    · exact hd4.trans (congrArg star hR4)
    · exact hd5.trans (congrArg star hR5)
    · exact hd6.trans (congrArg star hR6)
    · exact hd7.trans (congrArg star hR7)
    · exact hd8.trans (by rw [e0, e3, l0, l1, l4, l5] <;> rfl)
    · exact hd9.trans (by rw [e1, e4, l0, l2, l4, l6] <;> rfl)
    · exact hd10.trans (by rw [e2, e5, l0, l3, l4, l7] <;> rfl)
    · exact hd11.trans (by rw [e0, e1, e2, l0, l1, l2, l3] <;> rfl)
  · rintro ⟨h, z, hh, hc, hτ⟩
    have hhc : h - c 0 ≠ 0 := sub_ne_zero.2 hc
    obtain ⟨P, hP⟩ : ∃ P, P = tgPts h z c := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = tgY a P (normInv (Lam (h • genP0)))
        (normInv (Lam ((h - c 0) • genP0))) (tgQ h z c) := ⟨_, rfl⟩
    have hya : ∀ i : Fin 44, y i = a i := hy ▸ tgY_lt a P _ _ _
    have hC := ev_testGroupC y a c hya ha
    refine ⟨y, hya, ?_⟩
    simp only [testGroupFormula, lift_and_append, lift_and_cons, lift_and_nil, and_true, lift_feq,
      lift_fin, Pair.val_mul, Pair.val_sub, Pair.val_conj, val_varPair, Nat.reduceMul,
      Nat.reduceAdd, and_assoc]
    have hpt : ∀ (n : ℕ) (j : Fin 8), n = 44 + 5 * j.val → pt y n = pointCode (P j) :=
      fun n j hn => hy ▸ tgY_pt a P _ _ _ j.isLt hn
    have hL : ∀ (n : ℕ) (j : Fin 8), n = 138 + 7 * j.val → pr y n = Lam (P j) :=
      fun n j hn => hy ▸ tgY_L a P _ _ _ j.isLt hn
    have hR : ∀ (n : ℕ) (j : Fin 8), n = 140 + 7 * j.val → pr y n = invX (P j) :=
      fun n j hn => hy ▸ tgY_rho a P _ _ _ j.isLt hn
    have hZ : ∀ (n : ℕ) (j : Fin 8), n = 136 + 7 * j.val → pr y n = zOf (P j) :=
      fun n j hn => hy ▸ tgY_z a P _ _ _ j.isLt hn
    have hQ : ∀ (n : ℕ) (k : Fin 6), n = 194 + 2 * k.val → pr y n = tgQ h z c k :=
      fun n k hn => hy ▸ tgY_q a P _ _ _ k.isLt hn
    have hD : ∀ j : Fin 12, Pair.val y (testGroupD j) = testValues h z c j := fun j =>
      (val_testGroupD y a hya j).trans (hτ j)
    subst hP
    have hPm : ∀ j : Fin 8, ∃ n : ℤ, tgPts h z c j = n • genP0 := by
      intro j; fin_cases j
      exacts [⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩]
    have hloc : ∀ (k b : ℕ) (j : Fin 8), k = 44 + 5 * j.val → b = 136 + 7 * j.val →
        (Formula.and (testGroupLocalFormula (varPoint k) b)).Lift y := by
      intro k b j hk hb
      obtain ⟨n, hn⟩ := hPm j
      rw [lift_local_pt y k b (tgPts h z c j) (hn ▸ zsmul_genP0_coords n) (hpt k j hk)]
      exact ⟨hZ b j hb, hL (b + 2) j (by omega), hR (b + 4) j (by omega)⟩
    have hy192 : y 192 = normInv (Lam (h • genP0)) := hy ▸ tgY_192 a _ _ _ _
    have hy193 : y 193 = normInv (Lam ((h - c 0) • genP0)) := hy ▸ tgY_193 a _ _ _ _
    have hnz : ∀ (n m : ℕ) (j : Fin 8), n = 138 + 7 * j.val →
        y m = normInv (Lam (tgPts h z c j)) →
        Lam (tgPts h z c j) ≠ 0 → (nzFormula (varPair n).norm m).Lift y := by
      intro n m j hn hm hne
      rw [lift_nzFormula, Pair.ev_norm, ev_varPair_fst, ev_varPair_snd, hm]
      have e := hL n j hn
      have e1 : y n = (Lam (tgPts h z c j)).re := congrArg QuadraticAlgebra.re e
      have e2 : y (n + 1) = (Lam (tgPts h z c j)).im := congrArg QuadraticAlgebra.im e
      rw [e1, e2]
      exact normInv_spec hne
    have hfin : ∀ (k : ℕ) (j : Fin 8) (n : ℤ), k = 44 + 5 * j.val →
        tgPts h z c j = n • genP0 → n ≠ 0 → ev y (varPoint k 0) = 0 := by
      intro k j n hk hn hn0
      rw [ev_varPoint]
      have := congrFun (hpt k j hk) 0
      rw [hn, ← iota_def] at this
      exact this.trans ((iota_zero_coord_eq_zero_iff n).2 hn0)
    refine ⟨(lift_root_iota y 44 64 _ 84 (c 0) (hC 0)).2 ⟨h, hpt 44 0 rfl,
        hpt 64 4 rfl⟩,
      (lift_root_iota y 49 69 _ 97 (c 1) (hC 1)).2 ⟨z 0, hpt 49 1 rfl,
        hpt 69 5 rfl⟩,
      (lift_root_iota y 54 74 _ 110 (c 2) (hC 2)).2 ⟨z 1, hpt 54 2 rfl,
        hpt 74 6 rfl⟩,
      (lift_root_iota y 59 79 _ 123 (c 3) (hC 3)).2 ⟨z 2, hpt 59 3 rfl,
        hpt 79 7 rfl⟩,
      hfin 44 0 h rfl rfl hh, hfin 64 4 (h - c 0) rfl rfl hhc,
      hloc 44 136 0 rfl rfl, hloc 49 143 1 rfl rfl,
      hloc 54 150 2 rfl rfl, hloc 59 157 3 rfl rfl,
      hloc 64 164 4 rfl rfl, hloc 69 171 5 rfl rfl,
      hloc 74 178 6 rfl rfl, hloc 79 185 7 rfl rfl,
      hnz 138 192 0 rfl hy192 (Lam_ne_zero hh),
      hnz 166 193 4 rfl hy193 (Lam_ne_zero hhc), ?_, ?_, ?_, ?_, ?_, ?_,
      (hD 0).trans (hR 140 0 rfl).symm,
      (hD 1).trans (hR 147 1 rfl).symm,
      (hD 2).trans (hR 154 2 rfl).symm,
      (hD 3).trans (hR 161 3 rfl).symm,
      (hD 4).trans (congrArg star (hR 168 4 rfl)).symm,
      (hD 5).trans (congrArg star (hR 175 5 rfl)).symm,
      (hD 6).trans (congrArg star (hR 182 6 rfl)).symm,
      (hD 7).trans (congrArg star (hR 189 7 rfl)).symm,
      (hD 8).trans (by rw [hQ 194 0 rfl, hQ 200 3 rfl]; rfl),
      (hD 9).trans (by rw [hQ 196 1 rfl, hQ 202 4 rfl]; rfl),
      (hD 10).trans (by rw [hQ 198 2 rfl, hQ 204 5 rfl]; rfl),
      (hD 11).trans (by rw [hQ 194 0 rfl, hQ 196 1 rfl, hQ 198 2 rfl]; rfl)⟩
    · rw [hL 138 0 rfl, hQ 194 0 rfl, hL 145 1 rfl]
      exact mul_div_cancel₀ _ (Lam_ne_zero hh)
    · rw [hL 138 0 rfl, hQ 196 1 rfl, hL 152 2 rfl]
      exact mul_div_cancel₀ _ (Lam_ne_zero hh)
    · rw [hL 138 0 rfl, hQ 198 2 rfl, hL 159 3 rfl]
      exact mul_div_cancel₀ _ (Lam_ne_zero hh)
    · rw [hL 166 4 rfl, hQ 200 3 rfl, hL 173 5 rfl]
      exact mul_div_cancel₀ _ (Lam_ne_zero hhc)
    · rw [hL 166 4 rfl, hQ 202 4 rfl, hL 180 6 rfl]
      exact mul_div_cancel₀ _ (Lam_ne_zero hhc)
    · rw [hL 166 4 rfl, hQ 204 5 rfl, hL 187 7 rfl]
      exact mul_div_cancel₀ _ (Lam_ne_zero hhc)

end ZInQ.Mult

namespace ZInQ.Mult

open Syntax

/-- The parameter vector `(ι(c₀), ι(c₁), ι(c₂), ι(c₃), D₁, …, D₁₂)` of a test group. -/
noncomputable def testGroupVec (c : Fin 4 → ℤ) (D : Fin 12 → Fin 2 → ℚ) : Fin 44 → ℚ := fun k =>
  if h : k.val < 20 then iota (c ⟨k / 5, by omega⟩) ⟨k % 5, by omega⟩
  else D ⟨(k - 20) / 2, by omega⟩ ⟨(k - 20) % 2, by omega⟩

/-- **Semantics of the test-group template**, in the form of the article: for all
`c₀, …, c₃ ∈ ℤ` and rational pairs `D₁, …, D₁₂`,
`Rel(ι(c₀), …, ι(c₃), D₁, …, D₁₂) ⟺ ∃ h, z, h ≠ 0, h ≠ c₀, [D_j] = τ_j(h, z; c)`. -/
theorem testGroup_rel_iff_codes (c : Fin 4 → ℤ) (D : Fin 12 → Fin 2 → ℚ) :
    testGroupTemplate.Rel (testGroupVec c D) ↔
      ∃ (h : ℤ) (z : Fin 3 → ℤ), h ≠ 0 ∧ h ≠ c 0 ∧
        ∀ j : Fin 12, pairK (D j) = testValues h z c j := by
  refine (testGroup_rel_iff c _ fun i k => ?_).trans ?_
  · have hi := i.isLt
    have hk := k.isLt
    simp only [testGroupVec]
    rw [dite_eq_left (by omega)]
    have e1 : (⟨(5 * (i : ℕ) + k) / 5, by omega⟩ : Fin 4) = i := Fin.ext (by simp only; omega)
    have e2 : (⟨(5 * (i : ℕ) + k) % 5, by omega⟩ : Fin 5) = k := Fin.ext (by simp only; omega)
    simp only [e1, e2]
  · refine exists_congr fun h => exists_congr fun z => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    refine forall_congr' fun j => ?_
    have hj := j.isLt
    have e : (⟨testGroupVec c D ⟨20 + 2 * j, by omega⟩, testGroupVec c D ⟨21 + 2 * j, by omega⟩⟩ :
        K0) = pairK (D j) := by
      simp only [testGroupVec, pairK]
      rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      have e1 : (⟨(20 + 2 * (j : ℕ) - 20) / 2, by omega⟩ : Fin 12) = j :=
        Fin.ext (by simp only; omega)
      have e2 : (⟨(21 + 2 * (j : ℕ) - 20) / 2, by omega⟩ : Fin 12) = j :=
        Fin.ext (by simp only; omega)
      have e3 : (⟨(20 + 2 * (j : ℕ) - 20) % 2, by omega⟩ : Fin 2) = 0 :=
        Fin.ext (by simp only [Fin.val_zero]; omega)
      have e4 : (⟨(21 + 2 * (j : ℕ) - 20) % 2, by omega⟩ : Fin 2) = 1 :=
        Fin.ext (by simp only [Fin.val_one]; omega)
      simp only [e1, e2, e3, e4]
    rw [e]

end ZInQ.Mult
