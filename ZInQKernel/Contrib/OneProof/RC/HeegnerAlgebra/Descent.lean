import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 3: descend once, before twisting; the multiplier `L`

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 4 "Descend once, before twisting" (tex 3004–3032), paragraph 5 "Integral local descent
at the old places" (tex 3034–3086), and the corestriction compatibility of `d_a`
(tex 3281–3288).

* (H8)–(H9): the inflation–restriction sequence (Nekovář, (4.1.4.1); `PRINT`, see
  `Interfaces.lean`) enters as abstract exactness data `FiveTerm`.  When the outer terms are
  killed by `2^e` (by (H2)), `d_a(c) = 2^e b` for any `b` with `res b = 2^e c` is well defined,
  additive, natural (coefficient reduction, transport of the field diagram, corestriction in
  Cartesian squares), restricts to `2^{2e} c`, and equals `2^{2e} c` when the relative group is
  trivial (`I = ∅`).  All `PROVED`.
* (H10) and the Kummer descent: from `c_B H¹(Gal(F'/F), B(F')) = 0` (Lang's theorem and the
  formal-group filtration: `PRINT`/`GLUE`, see `Interfaces.lean`), a class that becomes Kummer
  over the unramified `F'` becomes Kummer over `F` after multiplication by `c_B`: `PROVED`
  diagram chase.
* (H11): `L = m₀ C_π C_bad 2^{2e}` and `b_{I,a} = m₀ C_bad d_a(c_{I,a})` restricts to
  `δ_a(L D_I y_{f n_I})`: `PROVED`.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

/-! ## (H8)–(H9): the descent map `d_a` -/

/-- The five-term inflation–restriction sequence (H8) as exactness data:
`0 → H¹(Γ, V^{G_M}) → H¹(B, V) → H¹(M, V)^Γ → H²(Γ, V^{G_M})`. -/
structure FiveTerm (A B C D : Type*) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] where
  /-- inflation `H¹(Γ, V^{G_M}) → H¹(B, V)` -/
  inf : A →+ B
  /-- restriction `H¹(B, V) → H¹(M, V)^Γ` -/
  res : B →+ C
  /-- transgression `H¹(M, V)^Γ → H²(Γ, V^{G_M})` -/
  tg : C →+ D
  inf_injective : Function.Injective inf
  exact_B : ∀ b, res b = 0 ↔ ∃ x, inf x = b
  exact_C : ∀ c, tg c = 0 ↔ ∃ b, res b = c

section Descent

variable {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable (S : FiveTerm A B C D) (e : ℕ)

/-- tex 3017: since `2^e` kills `H²(Γ, V^{G_M})` (by (H2)), `2^e c` lifts. -/
theorem FiveTerm.lift_exists (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) :
    ∃ b, S.res b = ((2 : ℤ) ^ e) • c := by
  rw [← S.exact_C, map_zsmul]; exact hD _

/-- (H9), tex 3017–3019: `d_a(c) = 2^e b` for a chosen `b` with `res b = 2^e c`. -/
noncomputable def FiveTerm.descend (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) : B :=
  ((2 : ℤ) ^ e) • Classical.choose (S.lift_exists e hD c)

/-- (H9) is independent of the choice, tex 3021–3022, `PROVED`: any two lifts differ by an
inflated class, which `2^e` kills (by (H2)). -/
theorem FiveTerm.descend_eq (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) (b : B) (hb : S.res b = ((2 : ℤ) ^ e) • c) :
    S.descend e hD c = ((2 : ℤ) ^ e) • b := by
  have h0 := Classical.choose_spec (S.lift_exists e hD c)
  have hdiff : S.res (Classical.choose (S.lift_exists e hD c) - b) = 0 := by
    rw [map_sub, h0, hb, sub_self]
  obtain ⟨x, hx⟩ := (S.exact_B _).mp hdiff
  have : ((2 : ℤ) ^ e) • (Classical.choose (S.lift_exists e hD c) - b) = 0 := by
    rw [← hx, ← map_zsmul, hA, map_zero]
  rw [FiveTerm.descend, ← sub_eq_zero, ← smul_sub, this]

/-- (H9), tex 3024, `PROVED`: the restriction of `d_a(c)` is exactly `2^{2e} c`. -/
theorem FiveTerm.res_descend (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : C) :
    S.res (S.descend e hD c) = ((2 : ℤ) ^ (2 * e)) • c := by
  rw [FiveTerm.descend, map_zsmul, Classical.choose_spec (S.lift_exists e hD c), smul_smul,
    ← pow_add, two_mul]

/-- (H9) is additive, tex 3022–3023, `PROVED`. -/
theorem FiveTerm.descend_add (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c c' : C) :
    S.descend e hD (c + c') = S.descend e hD c + S.descend e hD c' := by
  have h := Classical.choose_spec (S.lift_exists e hD c)
  have h' := Classical.choose_spec (S.lift_exists e hD c')
  rw [S.descend_eq e hA hD (c + c') (Classical.choose (S.lift_exists e hD c) +
      Classical.choose (S.lift_exists e hD c')) (by rw [map_add, h, h', smul_add]),
    smul_add]
  rfl

/-- (H9) as an additive map. -/
noncomputable def FiveTerm.descendHom (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) : C →+ B where
  toFun := S.descend e hD
  map_zero' := by
    rw [S.descend_eq e hA hD 0 0 (by simp), smul_zero]
  map_add' := S.descend_add e hA hD

/-- (H9) is natural, tex 3022–3024 and 3281–3288, `PROVED`: for any map of the data commuting with
restriction (coefficient reduction, transport of the whole field diagram, or corestriction in the
Cartesian class-field squares, where `res ∘ cor = cor ∘ res`), `d_a` commutes with it. -/
theorem FiveTerm.descend_natural {A' B' C' D' : Type*} [AddCommGroup A'] [AddCommGroup B']
    [AddCommGroup C'] [AddCommGroup D'] (S' : FiveTerm A' B' C' D')
    (hA' : ∀ x : A', ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (hD' : ∀ x : D', ((2 : ℤ) ^ e) • x = 0)
    (α : B →+ B') (γ : C →+ C') (hcomm : ∀ b, S'.res (α b) = γ (S.res b)) (c : C) :
    S'.descend e hD' (γ c) = α (S.descend e hD c) := by
  have h := Classical.choose_spec (S.lift_exists e hD c)
  rw [S'.descend_eq e hA' hD' (γ c) (α (Classical.choose (S.lift_exists e hD c)))
      (by rw [hcomm, h, map_zsmul]), FiveTerm.descend, map_zsmul]

/-- tex 3281–3288, `PROVED`: compatibility of `d_a` with corestriction in a Cartesian square
(`res ∘ cor = cor ∘ res`): "if `b` lifts `2^e c`, its corestriction lifts `2^e` times the
corestricted class; uniqueness after the second multiplication by `2^e` proves the required
compatibility". -/
theorem FiveTerm.descend_cor {A' B' C' D' : Type*} [AddCommGroup A'] [AddCommGroup B']
    [AddCommGroup C'] [AddCommGroup D'] (S' : FiveTerm A' B' C' D')
    (hA' : ∀ x : A', ((2 : ℤ) ^ e) • x = 0)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (hD' : ∀ x : D', ((2 : ℤ) ^ e) • x = 0)
    (cor : B →+ B') (corM : C →+ C') (hsq : ∀ b, S'.res (cor b) = corM (S.res b)) (c : C) :
    S'.descend e hD' (corM c) = cor (S.descend e hD c) :=
  S.descend_natural e S' hA' hD hD' cor corM hsq c

/-- tex 3030–3032, `PROVED`: for `I = ∅` the relative group is trivial, restriction is the
identity, and the same definition gives `d_a(c) = 2^{2e} c` (the same normalizing multiplier for
the primitive class and its derivatives). -/
theorem FiveTerm.descend_trivial (S : FiveTerm A B B D) (hres : ∀ b, S.res b = b)
    (hA : ∀ x : A, ((2 : ℤ) ^ e) • x = 0) (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (c : B) :
    S.descend e hD c = ((2 : ℤ) ^ (2 * e)) • c := by
  rw [S.descend_eq e hA hD c (((2 : ℤ) ^ e) • c) (hres _), smul_smul, ← pow_add, two_mul]

end Descent

/-! ## (H10): integral local descent at the old places -/

/-- tex 3058–3062, `PROVED` (diagram chase).  `κ : B(F) → H¹(F, B[2^a])` and
`j : H¹(F, B[2^a]) → H¹(F, B)` form the Kummer sequence over `F` (exact at the middle); likewise
over `F'`; `res` commutes with `j`; the kernel of `res : H¹(F, B) → H¹(F', B)` is the image of
inflation from `H¹(Gal(F'/F), B(F'))`, which `c_B` kills by (H10).  If `v` becomes Kummer over
`F'`, then `c_B v` is Kummer over `F`. -/
theorem kummer_descent {Pt Pt' HV HV' HB HB' Hinf : Type*} [AddCommGroup Pt] [AddCommGroup Pt']
    [AddCommGroup HV] [AddCommGroup HV'] [AddCommGroup HB] [AddCommGroup HB'] [AddCommGroup Hinf]
    (κ : Pt →+ HV) (j : HV →+ HB) (exK : ∀ v, j v = 0 → ∃ x, κ x = v)
    (κ' : Pt' →+ HV') (j' : HV' →+ HB') (hκ' : ∀ x', j' (κ' x') = 0)
    (res : HV →+ HV') (resB : HB →+ HB') (hcomm : ∀ v, j' (res v) = resB (j v))
    (infl : Hinf →+ HB) (exInf : ∀ w, resB w = 0 → ∃ z, infl z = w)
    (cB : ℤ) (hH10 : ∀ z : Hinf, cB • z = 0)
    (v : HV) (hv : ∃ x', res v = κ' x') : ∃ x, κ x = cB • v := by
  obtain ⟨x', hx'⟩ := hv
  have h1 : resB (j v) = 0 := by rw [← hcomm, hx', hκ']
  obtain ⟨z, hz⟩ := exInf _ h1
  apply exK
  rw [map_zsmul, ← hz, ← map_zsmul, hH10, map_zero]

/-! ## (H11): the single multiplier -/

/-- The multiplier `L = m₀ C_π C_bad 2^{2e}` of (H11), tex 3074; it depends only on the fixed
integers `m₀, C_π, C_bad, e`, not on `K, f, I, m, b, G`. -/
def Lmult (m0 Cπ Cbad e : ℕ) : ℤ := m0 * Cπ * Cbad * 2 ^ (2 * e)

/-- (H11), tex 3074–3081, `PROVED`: `b_{I,a} = m₀ C_bad d_a(c_{I,a})`, with
`c_{I,a} = δ_a(C_π D_I y_{f n_I})`, restricts to `δ_a(L D_I y_{f n_I})`. -/
theorem H11_restriction {A B C D P : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup P] (S : FiveTerm A B C D) (e : ℕ)
    (hD : ∀ x : D, ((2 : ℤ) ^ e) • x = 0) (δa : P →+ C) (m0 Cπ Cbad : ℕ) (x : P) :
    S.res (((m0 * Cbad : ℕ) : ℤ) • S.descend e hD (δa ((Cπ : ℤ) • x))) =
      δa (Lmult m0 Cπ Cbad e • x) := by
  rw [map_zsmul, S.res_descend, ← map_zsmul, ← map_zsmul, smul_smul, smul_smul, Lmult]
  congr 2
  push_cast; ring

/-- (H11), tex 3080, `PROVED`: `b_{I,a}` is Kummer at an old place `v | 2N`.  Its restriction to
the unramified local field `F' = (M_I)_w` is the Kummer class `δ_a(L D_I y)`, so by
`kummer_descent` the class `C_bad · d_a(c)` (and then `m₀ C_bad d_a(c)`) is Kummer over
`F = (H_f)_v`.  Here the local images are abstracted: `locB` and `locM` are the localizations,
compatible with restriction, and `δ_a(L D_I y)` localizes to a Kummer class over `F'`. -/
theorem H11_kummer_at_old {Pt Pt' HV HV' HB HB' Hinf : Type*} [AddCommGroup Pt] [AddCommGroup Pt']
    [AddCommGroup HV] [AddCommGroup HV'] [AddCommGroup HB] [AddCommGroup HB'] [AddCommGroup Hinf]
    (κ : Pt →+ HV) (j : HV →+ HB) (exK : ∀ v, j v = 0 → ∃ x, κ x = v)
    (κ' : Pt' →+ HV') (j' : HV' →+ HB') (hκ' : ∀ x', j' (κ' x') = 0)
    (res : HV →+ HV') (resB : HB →+ HB') (hcomm : ∀ v, j' (res v) = resB (j v))
    (infl : Hinf →+ HB) (exInf : ∀ w, resB w = 0 → ∃ z, infl z = w)
    (Cbad : ℤ) (hH10 : ∀ z : Hinf, Cbad • z = 0) (m0 : ℤ)
    (v : HV) (hv : ∃ x', res v = κ' x') : ∃ x, κ x = (m0 * Cbad) • v := by
  obtain ⟨x, hx⟩ := kummer_descent κ j exK κ' j' hκ' res resB hcomm infl exInf Cbad hH10 v hv
  exact ⟨m0 • x, by rw [map_zsmul, hx, smul_smul]⟩

end ZInQ.Manuscript.RC.HeegnerAlgebra
