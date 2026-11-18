import ZInQKernel.Contrib.OneProof.RC.Wiring.ConstituentModelRel
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.NonVacuity

/-!
# A corrected constituent model with a NONZERO reading (dihedral constituents)

Consistency check, not part of the manuscript (LESSON 2). RC0's only witness of
`ConstituentModelRel` has the zero reading, and `AdditiveObstruction.lean` shows that additive
reduced traces (for example abelian images) can only give the zero reading. Here (all `PROVED`)
`dihModel T ap B` is a `ConstituentModelRel` whose reduced traces are quadratic in `g`; with even
`a_p` and `B ≤ 2` its inputs hold (`dihModel_inputs`); and its reading is one at `{3}` for the sign
type data (`constituentModelRel_nonzero`). RC0's `rulesUpTo_of_constituentsRel` then applies
(`rulesUpTo_dihModel`).

Construction:
* group: the generalized dihedral group `G = (ℕ → ℤ/4) ⋊ ℤ/2` (the type inverts the rotation
  coordinates). The type character is the `ℤ/2` part and the Legendre characters are the
  rotation parities. `N_U` is the kernel of the type and the `U`-characters, so
  `chi_surj` holds at every `U` and Chebotarev in `G/N_U` follows from batch 3's `realizeNat`;
  `frob q` carries the type of `q` and its bits `(q/s)`;
* constituents over `K = ℚ`, `O = ℤ`, `𝔪 = (2)`, in blocks `none` (for `U = ∅`) and `some p` (for
  `U = {p}`):
  * the trivial representation;
  * the sign of the type, `g ↦ diag(1, (−1)^{type})`;
  * the sign of the bit at `p`;
  * the dihedral representation `g ↦ rot(k_p(g)π/2) · diag(1, (−1)^{type})` with image `D₄`.
  All traces lie in `{0, ±2}` and all determinants are `±1`;
* lattice `Λ`: integer vectors whose entries are congruent modulo `2` inside each block. `F_U` is
  the indicator of the block of `U`. `read_U` takes the sum of `c_k·(v_k − v_0)/2 mod 2` over the
  block. On `F_U` this reads `tr_k(g)/2 − 1` modulo `2`: the second `2`-adic digit of the traces,
  which the congruence lattice makes additive;
* fields:
  * `two_fresh` and `det_orbit`: products of two even traces, and `(det − 1)·tr`, lie in `4ℤ`;
  * `level_red`: for `n ∈ N_U` each trace in the block changes by a multiple of `4`. The rotation
    coordinate of `n` at `p ∈ U` is even, so `ρ_p(n) = ±1`;
* value functions (`readFun_value`): `f_∅(g) = type(g)` and `f_{p}(g) = bit_p(g)(type(g) + typ p)`.
  The second is quadratic in `g`, from the dihedral constituent (the indicator that `ρ_p(g)` is
  central);
* reading `Rd`: `R({q}) = typ q` and `R({p, q}) = (q/p)(typ p + typ q)`. These are the Rédei
  determinants on one and two vertices, and they are symmetric by reciprocity (`Rd_pair`);
* `o12` at `U = {p}`: `f_{p}(gτ) + f_{p}(g) = type(g) + typ p = f_∅(gφ_p)`, with RC12's
  `cp_sum_odd` on the left.

Why `B ≤ 2` (remark, not formalized): (O.12) makes the derivative of `f_U` in the bit at `p` equal
to a shift of `f_{U∖p}`. So a nonzero reading needs `f_U` of degree at least `|U| + 1` in `g`, for
`|U| ≤ B − 1`, i.e. degree up to `B`. `D₄` constituents give degree two. Larger budgets need
constituents with deeper `2`-adic structure (for example dihedral images `D_{2^k}` over real
cyclotomic fields), as the genuine `GL₂` images have.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.TraceWitness.Dih

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.Wiring
  ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset Matrix

/-- The rotation coordinates `ℕ → ℤ/4`. -/
abbrev Nw : Type := Multiplicative (ℕ → ZMod 4)

/-- The reflection coordinate `ℤ/2` (the type). -/
abbrev Ew : Type := Multiplicative (ZMod 2)

/-- Inversion, an automorphism of the abelian group `Nw`. -/
def invAut : MulAut Nw where
  toFun n := n⁻¹
  invFun n := n⁻¹
  left_inv n := inv_inv n
  right_inv n := inv_inv n
  map_mul' a b := by rw [mul_inv, mul_comm]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- The type acts by inversion. -/
def flipAut : Ew →* MulAut Nw where
  toFun x := if Multiplicative.toAdd x = 0 then 1 else invAut
  map_one' := by simp
  map_mul' x y := by
    have hinv : invAut * invAut = 1 := by ext n; simp [invAut]
    rcases zmod2_cases (Multiplicative.toAdd x) with hx | hx <;>
      rcases zmod2_cases (Multiplicative.toAdd y) with hy | hy <;>
      simp only [toAdd_mul, hx, hy] <;> simp (config := {decide := true}) [hinv]

/-- The witness group: the generalized dihedral group of `ℕ → ℤ/4`. -/
abbrev Gd : Type := Nw ⋊[flipAut] Ew

/-- The type of `g`. -/
def tyOf (g : Gd) : ZMod 2 := Multiplicative.toAdd g.right

/-- The rotation coordinate of `g` at `s`. -/
def rotOf (g : Gd) (s : ℕ) : ZMod 4 := Multiplicative.toAdd g.left s

theorem flipAut_apply (x : Ew) (n : Nw) (s : ℕ) :
    Multiplicative.toAdd (flipAut x n) s =
      if Multiplicative.toAdd x = 0 then Multiplicative.toAdd n s else -Multiplicative.toAdd n s := by
  simp only [flipAut, MonoidHom.coe_mk, OneHom.coe_mk]
  rcases zmod2_cases (Multiplicative.toAdd x) with hx | hx
  · rw [if_pos hx, if_pos hx]; rfl
  · have h1 : ¬ Multiplicative.toAdd x = 0 := by rw [hx]; decide
    rw [if_neg h1, if_neg h1]; rfl

@[simp] theorem tyOf_mul (g h : Gd) : tyOf (g * h) = tyOf g + tyOf h := rfl

theorem rotOf_mul (g h : Gd) (s : ℕ) :
    rotOf (g * h) s = rotOf g s + (if tyOf g = 0 then rotOf h s else -rotOf h s) := by
  show Multiplicative.toAdd (g.left * flipAut g.right h.left) s = _
  rw [toAdd_mul, Pi.add_apply, flipAut_apply]
  rfl

/-- The reduction `ℤ/4 → ℤ/2`. -/
def red (a : ZMod 4) : ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) a

theorem red_add (a b : ZMod 4) : red (a + b) = red a + red b := map_add _ a b
theorem red_neg (a : ZMod 4) : red (-a) = red a := by
  unfold red; revert a; decide

/-- The bit of `g` at `s`: the parity of its rotation coordinate. -/
def bitOf (g : Gd) (s : ℕ) : ZMod 2 := red (rotOf g s)

theorem bitOf_mul (g h : Gd) (s : ℕ) : bitOf (g * h) s = bitOf g s + bitOf h s := by
  unfold bitOf
  rw [rotOf_mul, red_add]
  split_ifs
  · rfl
  · rw [red_neg]

/-- The type character. -/
def chiT : Gd →* Multiplicative (ZMod 2) := SemidirectProduct.rightHom

/-- The Legendre characters. -/
def chiB (s : ℕ) : Gd →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (bitOf g s)
  map_one' := rfl
  map_mul' g h := by rw [bitOf_mul]; rfl

theorem chiT_apply (g : Gd) : chiT g = Multiplicative.ofAdd (tyOf g) := rfl
theorem chiB_apply (s : ℕ) (g : Gd) : chiB s g = Multiplicative.ofAdd (bitOf g s) := rfl

/-! ### Matrices -/

/-- The rotation by `π/2`. -/
def Rm : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

theorem Rm_pow_four : Rm ^ 4 = 1 := by
  simp [Rm, pow_succ, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem Rm_pow_mod (m : ℕ) : Rm ^ m = Rm ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, Rm_pow_four, one_pow, one_mul]

/-- Rotation by `kπ/2`. -/
def rotM (k : ZMod 4) : Matrix (Fin 2) (Fin 2) ℚ := Rm ^ k.val

/-- The reflection `diag(1, ±1)`. -/
def refM (e : ZMod 2) : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, if e = 0 then 1 else -1]

theorem rotM_mul (a b : ZMod 4) : rotM a * rotM b = rotM (a + b) := by
  unfold rotM
  rw [← pow_add, ZMod.val_add, Rm_pow_mod (a.val + b.val)]

theorem refM_mul (a b : ZMod 2) : refM a * refM b = refM (a + b) := by
  fin_cases a <;> fin_cases b <;> simp (config := {decide := true}) [refM, Matrix.mul_fin_two]

theorem refM_rotM (e : ZMod 2) (k : ZMod 4) :
    refM e * rotM k = rotM (if e = 0 then k else -k) * refM e := by
  have hk : ∀ k : ZMod 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  have h0 : refM 0 = 1 := by simp [refM, Matrix.one_fin_two]
  rcases zmod2_cases e with rfl | rfl
  · simp [h0]
  · simp only [show ¬ ((1 : ZMod 2) = 0) by decide, ↓reduceIte]
    rcases hk k with rfl | rfl | rfl | rfl <;>
      simp [rotM, refM, Rm, pow_succ, Matrix.one_fin_two,
        show (-1 : ZMod 4).val = 3 by decide, show (-2 : ZMod 4).val = 2 by decide,
        show (-3 : ZMod 4).val = 1 by decide, show (1 : ZMod 4).val = 1 by decide,
        show (2 : ZMod 4).val = 2 by decide, show (3 : ZMod 4).val = 3 by decide]

/-- The dihedral matrices `rot(k) · ref(e)`. -/
def dihMat (k : ZMod 4) (e : ZMod 2) : Matrix (Fin 2) (Fin 2) ℚ := rotM k * refM e

theorem dihMat_mul (k₁ k₂ : ZMod 4) (e₁ e₂ : ZMod 2) :
    dihMat k₁ e₁ * dihMat k₂ e₂ = dihMat (k₁ + if e₁ = 0 then k₂ else -k₂) (e₁ + e₂) := by
  unfold dihMat
  rw [mul_assoc, ← mul_assoc (refM e₁), refM_rotM, mul_assoc, refM_mul, ← mul_assoc, rotM_mul]

theorem refM_zero : refM 0 = 1 := by simp [refM, Matrix.one_fin_two]
theorem rotM_zero : rotM 0 = 1 := by simp [rotM]

theorem det_rotM (k : ZMod 4) : (rotM k).det = 1 := by
  rw [rotM, det_pow]; simp [Rm, Matrix.det_fin_two]

theorem det_refM (e : ZMod 2) : (refM e).det = if e = 0 then 1 else -1 := by
  simp [refM, Matrix.det_fin_two]

theorem det_dihMat (k : ZMod 4) (e : ZMod 2) : (dihMat k e).det = if e = 0 then 1 else -1 := by
  rw [dihMat, det_mul, det_rotM, det_refM, one_mul]

theorem det_ne (e : ZMod 2) : (if e = 0 then (1 : ℚ) else -1) ≠ 0 := by split_ifs <;> norm_num

/-- The integer trace of a dihedral matrix. -/
def trD (k : ZMod 4) (e : ZMod 2) : ℤ := if e = 0 then (if k = 0 then 2 else if k = 2 then -2 else 0) else 0

theorem trace_dihMat (k : ZMod 4) (e : ZMod 2) : (dihMat k e).trace = (trD k e : ℚ) := by
  have hk : ∀ k : ZMod 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases zmod2_cases e with rfl | rfl <;> rcases hk k with rfl | rfl | rfl | rfl <;>
    simp [dihMat, trD, rotM, refM, Rm, pow_succ, Matrix.trace_fin_two, Matrix.one_fin_two,
      show (1 : ZMod 4).val = 1 by decide, show (2 : ZMod 4).val = 2 by decide,
      show (3 : ZMod 4).val = 3 by decide] <;> norm_num <;> decide

theorem trace_refM (e : ZMod 2) : (refM e).trace = if e = 0 then 2 else 0 := by
  rcases zmod2_cases e with rfl | rfl <;> simp [refM, Matrix.trace_fin_two]; norm_num

/-- A matrix with nonzero determinant as an element of `GL₂(ℚ)`. -/
abbrev toGL (M : Matrix (Fin 2) (Fin 2) ℚ) (h : M.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero M h

theorem coe_toGL (M : Matrix (Fin 2) (Fin 2) ℚ) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = M := rfl

/-- **The dihedral constituent at `p`**: `g ↦ rot(k_p(g)) ref(type g)`. -/
def dihRep (p : ℕ) : Gd →* GL (Fin 2) ℚ where
  toFun g := toGL (dihMat (rotOf g p) (tyOf g)) (by rw [det_dihMat]; exact det_ne _)
  map_one' := Units.ext (by
    show dihMat (rotOf 1 p) (tyOf 1) = 1
    simp [dihMat, rotOf, tyOf, rotM_zero, refM_zero])
  map_mul' g h := Units.ext (by
    show dihMat (rotOf (g * h) p) (tyOf (g * h)) = dihMat (rotOf g p) (tyOf g) * dihMat (rotOf h p) (tyOf h)
    rw [dihMat_mul, rotOf_mul, tyOf_mul])

/-- **A sign constituent**: `g ↦ ref(χ g)` for a character `χ`. -/
def sigRep (χ : Gd →* Multiplicative (ZMod 2)) : Gd →* GL (Fin 2) ℚ where
  toFun g := toGL (refM (Multiplicative.toAdd (χ g))) (by rw [det_refM]; exact det_ne _)
  map_one' := Units.ext (by
    show refM (Multiplicative.toAdd (χ 1)) = 1
    rw [map_one, toAdd_one, refM_zero])
  map_mul' g h := Units.ext (by
    show refM (Multiplicative.toAdd (χ (g * h))) = refM _ * refM _
    rw [map_mul, toAdd_mul, refM_mul])


/-! ### The constituents -/

/-- The constituent index: a block (`none` for `U = ∅`, `some p` for `U = {p}`) and a kind. -/
abbrev Iw : Type := Option ℕ × Fin 4

/-- The constituents: kind `0` trivial, `1` the type sign, `2` the sign of the bit at `p`, `3` the
dihedral representation at `p` (kinds `2, 3` are trivial in the block `none`). -/
def rhoI (i : Iw) : Gd →* GL (Fin 2) ℚ :=
  if i.2 = 1 then sigRep chiT
  else if i.2 = 2 then (match i.1 with | none => 1 | some p => sigRep (chiB p))
  else if i.2 = 3 then (match i.1 with | none => 1 | some p => dihRep p)
  else 1

/-- The trace of a sign. -/
def trR (e : ZMod 2) : ℤ := if e = 0 then 2 else 0

/-- The integer traces of the constituents. -/
def trI (i : Iw) (g : Gd) : ℤ :=
  if i.2 = 1 then trR (tyOf g)
  else if i.2 = 2 then (match i.1 with | none => 2 | some p => trR (bitOf g p))
  else if i.2 = 3 then (match i.1 with | none => 2 | some p => trD (rotOf g p) (tyOf g))
  else 2

/-- The integer determinants of the constituents. -/
def detI (i : Iw) (g : Gd) : ℤ :=
  if i.2 = 1 then (if tyOf g = 0 then 1 else -1)
  else if i.2 = 2 then (match i.1 with | none => 1 | some p => if bitOf g p = 0 then 1 else -1)
  else if i.2 = 3 then (match i.1 with | none => 1 | some p => if tyOf g = 0 then 1 else -1)
  else 1

theorem trace_one_GL : ((1 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).trace = 2 := by
  simp

theorem det_one_GL : ((1 : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  simp

theorem trace_sigRep (χ : Gd →* Multiplicative (ZMod 2)) (g : Gd) :
    ((sigRep χ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).trace =
      (trR (Multiplicative.toAdd (χ g)) : ℚ) := by
  show (refM (Multiplicative.toAdd (χ g))).trace = _
  rw [trace_refM, trR]; split_ifs <;> simp

theorem det_sigRep (χ : Gd →* Multiplicative (ZMod 2)) (g : Gd) :
    ((sigRep χ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ((if Multiplicative.toAdd (χ g) = 0 then 1 else -1 : ℤ) : ℚ) := by
  show (refM (Multiplicative.toAdd (χ g))).det = _
  rw [det_refM]; split_ifs <;> simp

theorem trace_dihRep (p : ℕ) (g : Gd) :
    ((dihRep p g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).trace = (trD (rotOf g p) (tyOf g) : ℚ) :=
  trace_dihMat _ _

theorem det_dihRep (p : ℕ) (g : Gd) :
    ((dihRep p g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ((if tyOf g = 0 then 1 else -1 : ℤ) : ℚ) := by
  show (dihMat (rotOf g p) (tyOf g)).det = _
  rw [det_dihMat]; split_ifs <;> simp

theorem fin4_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by revert k; decide

theorem trace_rhoI (i : Iw) (g : Gd) :
    ((rhoI i g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).trace = (trI i g : ℚ) := by
  obtain ⟨b, k⟩ := i
  rcases fin4_cases k with rfl | rfl | rfl | rfl <;> cases b <;>
    simp (config := {decide := true}) only [rhoI, trI, ↓reduceIte, trace_one_GL,
      trace_sigRep, trace_dihRep, chiT_apply, chiB_apply, toAdd_ofAdd] <;> norm_num

theorem det_rhoI (i : Iw) (g : Gd) :
    ((rhoI i g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = (detI i g : ℚ) := by
  obtain ⟨b, k⟩ := i
  rcases fin4_cases k with rfl | rfl | rfl | rfl <;> cases b <;>
    simp (config := {decide := true}) only [rhoI, detI, ↓reduceIte, det_one_GL,
      det_sigRep, det_dihRep, chiT_apply, chiB_apply, toAdd_ofAdd] <;>
    first | (split_ifs <;> simp_all) | simp

theorem trI_even (i : Iw) (g : Gd) : ∃ z : ℤ, trI i g = 2 * z := by
  obtain ⟨b, k⟩ := i
  rcases fin4_cases k with rfl | rfl | rfl | rfl <;> cases b <;>
    simp (config := {decide := true}) only [trI, trR, trD, ↓reduceIte] <;> (try split_ifs) <;>
    first | exact ⟨1, rfl⟩ | exact ⟨0, rfl⟩ | exact ⟨-1, rfl⟩

theorem sign_sub_one_even (c : Prop) [Decidable c] :
    ∃ z : ℤ, (if c then (1 : ℤ) else -1) - 1 = 2 * z := by
  by_cases hc : c
  · exact ⟨0, by simp [hc]⟩
  · exact ⟨-1, by simp [hc]⟩

theorem detI_sub_one_even (i : Iw) (g : Gd) : ∃ z : ℤ, detI i g - 1 = 2 * z := by
  obtain ⟨b, k⟩ := i
  rcases fin4_cases k with rfl | rfl | rfl | rfl <;> cases b <;>
    simp (config := {decide := true}) only [detI, ↓reduceIte] <;>
    first | exact sign_sub_one_even _ | exact ⟨0, rfl⟩

/-! ### The lattice, the forms and the readings -/

/-- The lattice: integer vectors whose entries are congruent modulo `2` inside each block. -/
def Lam : Submodule ℤ (Iw → ℚ) where
  carrier := {v | (∀ i, ∃ z : ℤ, v i = z) ∧ ∀ b k k', ∃ z : ℤ, v (b, k) - v (b, k') = 2 * z}
  add_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    refine ⟨fun i => ?_, fun b k k' => ?_⟩
    · obtain ⟨a, ha⟩ := hv1 i; obtain ⟨c, hc⟩ := hw1 i
      exact ⟨a + c, by simp [ha, hc]⟩
    · obtain ⟨a, ha⟩ := hv2 b k k'; obtain ⟨c, hc⟩ := hw2 b k k'
      exact ⟨a + c, by simp only [Pi.add_apply]; push_cast; linarith⟩
  zero_mem' := ⟨fun _ => ⟨0, by simp⟩, fun _ _ _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c v ⟨hv1, hv2⟩
    refine ⟨fun i => ?_, fun b k k' => ?_⟩
    · obtain ⟨a, ha⟩ := hv1 i
      exact ⟨c * a, by simp [ha]⟩
    · obtain ⟨a, ha⟩ := hv2 b k k'
      refine ⟨c * a, ?_⟩
      simp only [Pi.smul_apply, zsmul_eq_mul]
      rw [← mul_sub, ha]; push_cast; ring

/-- The block of a set of at most one prime. -/
def blockOf (U : Finset ℕ) : Option (Option ℕ) :=
  if U = ∅ then some none else
    if h : U.card = 1 then some (some (U.min' (Finset.card_pos.1 (by omega)))) else none

theorem blockOf_empty : blockOf ∅ = some none := by simp [blockOf]

theorem blockOf_singleton (p : ℕ) : blockOf {p} = some (some p) := by
  simp [blockOf]

/-- The forms: the indicator of the block of `U`. -/
def Fv (U : Finset ℕ) : Iw → ℚ := fun i => if blockOf U = some i.1 then 1 else 0

theorem Fv_mem (U : Finset ℕ) : Fv U ∈ Lam := by
  refine ⟨fun i => ?_, fun b k k' => ⟨0, ?_⟩⟩
  · unfold Fv; split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  · simp [Fv]

/-- Half of an even number, modulo `2`. -/
def half (x : ℚ) : ZMod 2 := ((⌊x / 2⌋ : ℤ) : ZMod 2)

theorem half_intCast (z : ℤ) : half (z : ℚ) = ((z / 2 : ℤ) : ZMod 2) := by
  unfold half
  rw [show ((2 : ℚ)) = ((2 : ℕ) : ℚ) by norm_num, Rat.floor_intCast_div_natCast]
  rfl

theorem half_add {a b : ℚ} (ha : ∃ z : ℤ, a = 2 * z) (hb : ∃ z : ℤ, b = 2 * z) :
    half (a + b) = half a + half b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [show (2 * (x : ℚ) + 2 * y) = ((2 * (x + y) : ℤ) : ℚ) by push_cast; ring,
    show (2 * (x : ℚ)) = ((2 * x : ℤ) : ℚ) by push_cast; ring,
    show (2 * (y : ℚ)) = ((2 * y : ℤ) : ℚ) by push_cast; ring, half_intCast, half_intCast,
    half_intCast]
  simp

variable {ε : ZMod 2 →+ ZMod 2}

/-- The reading coefficients of a block. -/
def coefB (T : TypeData (ZMod 2) ε) : Option ℕ → Fin 4 → ZMod 2
  | none, k => if k = 1 then 1 else 0
  | some p, k => if k = 1 then 1 else if k = 2 then 1 + T.typ p else if k = 3 then 1 else 0

/-- The reading of `U` on the lattice. -/
def readFun (T : TypeData (ZMod 2) ε) (U : Finset ℕ) : Lam →+ ZMod 2 where
  toFun v := match blockOf U with
    | none => 0
    | some b => ∑ k : Fin 4, coefB T b k * half ((v : Iw → ℚ) (b, k) - (v : Iw → ℚ) (b, 0))
  map_zero' := by cases blockOf U <;> simp [half]
  map_add' v w := by
    cases blockOf U with
    | none => simp
    | some b =>
      simp only [← Finset.sum_add_distrib, ← mul_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have e : ((v + w : Lam) : Iw → ℚ) (b, k) - ((v + w : Lam) : Iw → ℚ) (b, 0) =
          ((v : Iw → ℚ) (b, k) - (v : Iw → ℚ) (b, 0)) + ((w : Iw → ℚ) (b, k) - (w : Iw → ℚ) (b, 0)) := by
        simp only [Submodule.coe_add, Pi.add_apply]; ring
      rw [e]
      exact half_add (v.2.2 b k 0) (w.2.2 b k 0)

theorem half_trR (e : ZMod 2) : half ((trR e : ℚ) - 2) = e := by
  rw [show ((trR e : ℚ) - 2) = ((trR e - 2 : ℤ) : ℚ) by push_cast; ring, half_intCast]
  revert e; decide

theorem half_trD (k : ZMod 4) (e : ZMod 2) :
    half ((trD k e : ℚ) - 2) = red k + e + red k * e := by
  rw [show ((trD k e : ℚ) - 2) = ((trD k e - 2 : ℤ) : ℚ) by push_cast; ring, half_intCast]
  revert k e; decide


/-! ### Membership in `2Λ` -/

theorem mem_two_of_four {u : Iw → ℚ} (hu : ∀ i, ∃ z : ℤ, u i = 4 * z) :
    u ∈ ((Ideal.span {(2 : ℤ)}) • (⊤ : Submodule ℤ Lam)).map Lam.subtype := by
  choose z hz using hu
  have hw : (fun i => (2 * z i : ℚ)) ∈ Lam :=
    ⟨fun i => ⟨2 * z i, by push_cast; ring⟩, fun b k k' => ⟨z (b, k) - z (b, k'), by push_cast; ring⟩⟩
  refine ⟨(2 : ℤ) • ⟨_, hw⟩, Submodule.smul_mem_smul (Ideal.subset_span rfl) trivial, ?_⟩
  funext i
  simp only [Submodule.coe_subtype, Submodule.coe_smul_of_tower, Pi.smul_apply, zsmul_eq_mul, hz i]
  push_cast; ring

theorem tV_apply (g : Gd) (v : Iw → ℚ) (i : Iw) : tV rhoI g v i = (trI i g : ℚ) * v i := by
  simp [tV, trace_rhoI]

theorem dV_apply (g : Gd) (v : Iw → ℚ) (i : Iw) : dV rhoI g v i = (detI i g : ℚ) * v i := by
  simp [dV, det_rhoI]

theorem Fv_int (U : Finset ℕ) (i : Iw) : ∃ z : ℤ, Fv U i = z := (Fv_mem U).1 i

/-! ### The subgroups `N_U` and the Frobenius elements -/

/-- `N_U`: trivial type and trivial bits at `U`. -/
def Nd (U : Finset ℕ) : Subgroup Gd := chiT.ker ⊓ ⨅ s ∈ U, (chiB s).ker

theorem mem_Nd {U : Finset ℕ} {n : Gd} : n ∈ Nd U ↔ chiT n = 1 ∧ ∀ s ∈ U, chiB s n = 1 := by
  simp only [Nd, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem tyOf_of_mem {U : Finset ℕ} {n : Gd} (hn : n ∈ Nd U) : tyOf n = 0 := by
  have := (mem_Nd.1 hn).1
  rwa [chiT_apply, ofAdd_eq_one] at this

theorem bitOf_of_mem {U : Finset ℕ} {n : Gd} (hn : n ∈ Nd U) {s : ℕ} (hs : s ∈ U) :
    bitOf n s = 0 := by
  have := (mem_Nd.1 hn).2 s hs
  rwa [chiB_apply, ofAdd_eq_one] at this

theorem red_val (b : ZMod 2) : red ((b.val : ℕ) : ZMod 4) = b := by revert b; decide

/-- The Frobenius element of `q`: its type and its Legendre bits. -/
def frobD (T : TypeData (ZMod 2) ε) (q : ℕ) : Gd :=
  ⟨Multiplicative.ofAdd (fun s => ((legBit q s).val : ZMod 4)), Multiplicative.ofAdd (T.typ q)⟩

theorem tyOf_frobD (T : TypeData (ZMod 2) ε) (q : ℕ) : tyOf (frobD T q) = T.typ q := rfl
theorem bitOf_frobD (T : TypeData (ZMod 2) ε) (q s : ℕ) : bitOf (frobD T q) s = legBit q s :=
  red_val _

/-! ### The level -/

theorem trD_shift (k c : ZMod 4) (e : ZMod 2) (hc : red c = 0) :
    (4 : ℤ) ∣ trD (k + c) e - trD k e := by
  revert k c e; decide

theorem blockOf_some {U : Finset ℕ} {p : ℕ} (h : blockOf U = some (some p)) : p ∈ U := by
  unfold blockOf at h
  split_ifs at h with h0 h1
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]; exact Finset.min'_mem _ _

theorem trI_level {U : Finset ℕ} {g n : Gd} (hn : n ∈ Nd U) {i : Iw}
    (hi : blockOf U = some i.1) : ∃ z : ℤ, (trI i (g * n) : ℚ) - trI i g = 4 * z := by
  obtain ⟨b, k⟩ := i
  have hty : tyOf (g * n) = tyOf g := by rw [tyOf_mul, tyOf_of_mem hn, add_zero]
  suffices h : (4 : ℤ) ∣ trI (b, k) (g * n) - trI (b, k) g by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by exact_mod_cast hz⟩
  rcases fin4_cases k with rfl | rfl | rfl | rfl <;> cases b with
  | none => simp (config := {decide := true}) [trI, hty]
  | some p =>
    have hp : p ∈ U := blockOf_some hi
    have hbit : bitOf (g * n) p = bitOf g p := by rw [bitOf_mul, bitOf_of_mem hn hp, add_zero]
    have hn0 : red (rotOf n p) = 0 := bitOf_of_mem hn hp
    simp (config := {decide := true}) only [trI, ↓reduceIte, hty, hbit, sub_self, dvd_zero]
    all_goals rw [rotOf_mul]
    all_goals split_ifs
    all_goals first
      | exact trD_shift _ _ _ hn0
      | exact trD_shift _ _ _ (by rw [red_neg]; exact hn0)


/-! ### The reading and the model -/

/-- The reading on sets of at most two primes: `R({q}) = typ q` and
`R({p, q}) = (q/p)(typ p + typ q)` (the Rédei symbol on one and two vertices). -/
def Rd (T : TypeData (ZMod 2) ε) (W : Finset ℕ) : ZMod 2 :=
  if h : W.card = 1 then T.typ (W.min' (Finset.card_pos.1 (by omega)))
  else if h2 : W.card = 2 then
    legBit (W.max' (Finset.card_pos.1 (by omega))) (W.min' (Finset.card_pos.1 (by omega))) *
      (T.typ (W.min' (Finset.card_pos.1 (by omega))) + T.typ (W.max' (Finset.card_pos.1 (by omega))))
  else 0

theorem Rd_singleton (T : TypeData (ZMod 2) ε) (q : ℕ) : Rd T {q} = T.typ q := by
  simp [Rd]

theorem legBit_sym (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) {p q : ℕ} (hp : T.Good p)
    (hq : T.Good q) (hpq : p ≠ q) :
    legBit p q * (T.typ p + T.typ q) = legBit q p * (T.typ p + T.typ q) := by
  rw [T.legBit_rev hp hq hpq]
  simp only [AddMonoidHom.id_apply]
  generalize legBit q p = a
  generalize T.typ p = x
  generalize T.typ q = y
  revert a x y; decide

theorem Rd_pair (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) {p q : ℕ} (hp : T.Good p)
    (hq : T.Good q) (hpq : q ≠ p) :
    Rd T (insert q {p}) = legBit q p * (T.typ q + T.typ p) := by
  have hc : (insert q {p} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
  unfold Rd
  rw [dif_neg (by omega), dif_pos hc]
  have hmin : (insert q {p} : Finset ℕ).min' (Finset.insert_nonempty _ _) = min p q := by
    rw [Finset.min'_insert _ _ (Finset.singleton_nonempty p), Finset.min'_singleton, min_comm]
  have hmax : (insert q {p} : Finset ℕ).max' (Finset.insert_nonempty _ _) = max p q := by
    rw [Finset.max'_insert _ _ (Finset.singleton_nonempty p), Finset.max'_singleton, max_comm]
  rw [hmin, hmax]
  rcases lt_or_gt_of_ne hpq with h | h
  · rw [min_eq_right h.le, max_eq_left h.le]
    rw [legBit_sym T hq hp hpq]
    try ring
  · rw [min_eq_left h.le, max_eq_right h.le]
    try ring

theorem Rd_three : Rd signTypeData {3} = 1 := by rw [Rd_singleton]; rfl

/-- The reading functionals on the reduced module. -/
def readQ (T : TypeData (ZMod 2) ε) (U : Finset ℕ) :
    (Lam ⧸ ((Ideal.span {(2 : ℤ)}) • (⊤ : Submodule ℤ Lam))) →+ ZMod 2 :=
  (((Ideal.span {(2 : ℤ)}) • (⊤ : Submodule ℤ Lam)).liftQ (readFun T U).toIntLinearMap (by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hr
    rw [LinearMap.mem_ker, map_zsmul, AddMonoidHom.coe_toIntLinearMap, zsmul_eq_mul]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul])).toAddMonoidHom

/-- **A corrected constituent model with a nonzero reading** (see `dihModel_inputs`, `Rd_three`). -/
def dihModel (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) (ap : ℕ → ℤ) (B : ℕ) :
    ConstituentModelRel T (Rd T) ap B where
  G := Gd
  I := Iw
  K := ℚ
  O := ℤ
  m := Ideal.span {2}
  two_mem := Ideal.subset_span rfl
  ρ := rhoI
  Λ := Lam
  stable_t g v hv := by
    refine ⟨fun i => ?_, fun b k k' => ?_⟩
    · obtain ⟨a, ha⟩ := hv.1 i
      exact ⟨trI i g * a, by rw [tV_apply, ha]; push_cast; ring⟩
    · obtain ⟨a, ha⟩ := hv.1 (b, k)
      obtain ⟨c, hc⟩ := hv.1 (b, k')
      obtain ⟨x, hx⟩ := trI_even (b, k) g
      obtain ⟨y, hy⟩ := trI_even (b, k') g
      refine ⟨x * a - y * c, ?_⟩
      rw [tV_apply, tV_apply, ha, hc, hx, hy]; push_cast; ring
  stable_d g v hv := by
    refine ⟨fun i => ?_, fun b k k' => ?_⟩
    · obtain ⟨a, ha⟩ := hv.1 i
      exact ⟨detI i g * a, by rw [dV_apply, ha]; push_cast; ring⟩
    · obtain ⟨a, ha⟩ := hv.1 (b, k)
      obtain ⟨c, hc⟩ := hv.1 (b, k')
      obtain ⟨z, hz⟩ := hv.2 b k k'
      obtain ⟨x, hx⟩ := detI_sub_one_even (b, k) g
      obtain ⟨y, hy⟩ := detI_sub_one_even (b, k') g
      refine ⟨z + x * a - y * c, ?_⟩
      have hx' : (detI (b, k) g : ℚ) = 2 * x + 1 := by exact_mod_cast (by linarith : detI (b, k) g = 2 * x + 1)
      have hy' : (detI (b, k') g : ℚ) = 2 * y + 1 := by exact_mod_cast (by linarith : detI (b, k') g = 2 * y + 1)
      rw [dV_apply, dV_apply, hx', hy']
      rw [ha, hc] at hz ⊢
      push_cast; linarith
  F U := ⟨Fv U, Fv_mem U⟩
  read := readQ T
  frob := frobD T
  N := Nd
  chiType := chiT
  chiBit := chiB
  det_orbit U u v := by
    refine mem_two_of_four fun i => ?_
    obtain ⟨a, ha⟩ := Fv_int U i
    obtain ⟨x, hx⟩ := trI_even i v
    obtain ⟨y, hy⟩ := detI_sub_one_even i u
    refine ⟨x * y * a, ?_⟩
    show dV rhoI u (tV rhoI v (Fv U)) i - tV rhoI v (Fv U) i = _
    rw [dV_apply, tV_apply, ha, hx]
    have hy' : (detI i u : ℚ) = 2 * y + 1 := by exact_mod_cast (by linarith : detI i u = 2 * y + 1)
    rw [hy']; push_cast; ring
  two_fresh U g h := by
    refine mem_two_of_four fun i => ?_
    obtain ⟨a, ha⟩ := Fv_int U i
    obtain ⟨x, hx⟩ := trI_even i g
    obtain ⟨y, hy⟩ := trI_even i h
    refine ⟨x * y * a, ?_⟩
    show tV rhoI g (tV rhoI h (Fv U)) i = _
    rw [tV_apply, tV_apply, ha, hx, hy]; push_cast; ring
  level_red U g n hn := by
    refine mem_two_of_four fun i => ?_
    show ∃ z : ℤ, tV rhoI (g * n) (Fv U) i - tV rhoI g (Fv U) i = 4 * z
    rw [tV_apply, tV_apply, ← sub_mul]
    by_cases hi : blockOf U = some i.1
    · obtain ⟨z, hz⟩ := trI_level hn hi
      refine ⟨z, ?_⟩
      rw [hz]; simp [Fv, hi]
    · exact ⟨0, by simp [Fv, hi]⟩
  N_anti U U' hU' n hn := by
    rw [mem_Nd] at hn ⊢
    exact ⟨hn.1, fun s hs => hn.2 s (hU' hs)⟩
  N_chi U n hn := mem_Nd.mp hn
  kummer U g h1 h2 := Subgroup.mem_sup_right (mem_Nd.mpr ⟨h1, h2⟩)
  chi_surj U _ ℓ b := ⟨⟨Multiplicative.ofAdd (fun s => ((b s).val : ZMod 4)), Multiplicative.ofAdd ℓ⟩,
    rfl, fun s _ => by rw [chiB_apply]; exact congrArg Multiplicative.ofAdd (red_val (b s))⟩
  chebotarev U hU g avoid := by
    obtain ⟨x, -, hx, hold, -⟩ := realizeNat T U avoid hU (fun _ => tyOf g)
      (fun _ s => bitOf g s) (fun _ _ => 0) 1
    obtain ⟨hq, hqU, hqa, htq⟩ := hx 0 (by norm_num)
    refine ⟨x 0, 1, g⁻¹ * frobD T (x 0), mem_Nd.mpr ⟨?_, fun s hs => ?_⟩, hq, hqa, by group⟩
    · rw [map_mul, map_inv, chiT_apply, chiT_apply, tyOf_frobD, htq, inv_mul_cancel]
    · rw [map_mul, map_inv, chiB_apply, chiB_apply, bitOf_frobD, hold 0 (by norm_num) s hs,
        inv_mul_cancel]
  typ_frob _ _ := rfl
  bit_frob q s _ _ _ := by rw [chiB_apply, bitOf_frobD]


/-- The value functions of the model. -/
def valF (T : TypeData (ZMod 2) ε) (U : Finset ℕ) (g : Gd) : ZMod 2 :=
  match blockOf U with
  | some none => tyOf g
  | some (some p) => bitOf g p * (tyOf g + T.typ p)
  | none => 0

/-- **The value functions** (`PROVED`): `read_U(t(g)F_U)` is `type(g)` for `U = ∅` and
`bit_p(g)(type(g) + typ p)` for `U = {p}`. The second is quadratic in `g`, from the dihedral
constituent. -/
theorem readFun_value (T : TypeData (ZMod 2) ε) (U : Finset ℕ) (g : Gd) (v : Lam)
    (hv : (v : Iw → ℚ) = tV rhoI g (Fv U)) : readFun T U v = valF T U g := by
  obtain ⟨v, hvm⟩ := v
  simp only at hv
  subst hv
  unfold readFun valF
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rcases h : blockOf U with _ | _ | p
  · rfl
  · simp only [Fin.sum_univ_four, coefB, tV_apply, Fv, h]
    simp (config := {decide := true}) only [↓reduceIte, trI, mul_one, one_mul, zero_mul,
      add_zero, zero_add]
    rw [show ((2 : ℤ) : ℚ) = 2 by norm_num, half_trR]
  · simp only [Fin.sum_univ_four, coefB, tV_apply, Fv, h]
    simp (config := {decide := true}) only [↓reduceIte, trI, mul_one, one_mul, zero_mul,
      add_zero, zero_add]
    rw [show ((2 : ℤ) : ℚ) = 2 by norm_num, half_trR, half_trR, half_trD]
    unfold bitOf
    generalize tyOf g = e
    generalize red (rotOf g p) = x
    generalize T.typ p = t
    revert e x t; decide

theorem card_le_one_cases {U : Finset ℕ} (h : U.card ≤ 1) : U = ∅ ∨ ∃ a, U = {a} := by
  rcases Nat.lt_or_ge U.card 1 with h0 | h1
  · left; exact Finset.card_eq_zero.1 (by omega)
  · right; exact Finset.card_eq_one.1 (by omega)

/-- **The two inputs of the model at budget at most two** (`PROVED`; even `a_p`). -/
theorem dihModel_inputs (T : TypeData (ZMod 2) (AddMonoidHom.id (ZMod 2))) (ap : ℕ → ℤ)
    (hap : ∀ p, Even (ap p)) (B : ℕ) (hB : B ≤ 2) : (dihModel T ap B).Inputs := by
  have hval : ∀ (U : Finset ℕ) (g : (dihModel T ap B).G),
      (dihModel T ap B).readM U ((dihModel T ap B).tM g ((dihModel T ap B).FM U)) = valF T U g :=
    fun U g => readFun_value T U g ((dihModel T ap B).tΛ g ((dihModel T ap B).F U)) rfl
  refine ⟨fun U q hU hq hqU hcard => ?_, fun U p hp hU hcard g => ?_⟩
  · rw [hval]
    have hc : U.card ≤ 1 := by rw [Finset.card_insert_of_notMem hqU] at hcard; omega
    rcases card_le_one_cases hc with rfl | ⟨a, rfl⟩
    · rw [show (insert q ∅ : Finset ℕ) = {q} by simp, Rd_singleton]
      simp only [valF, blockOf_empty]
      exact (tyOf_frobD T q).symm
    · have hqa : q ≠ a := fun h => hqU (by simp [h])
      rw [Rd_pair T (hU a (by simp)) hq hqa]
      simp only [valF, blockOf_singleton]
      show legBit q a * (T.typ q + T.typ a) = bitOf (frobD T q) a * (tyOf (frobD T q) + T.typ a)
      rw [bitOf_frobD, tyOf_frobD]
  · have hc : U.card ≤ 1 := by omega
    have hUp : U = {p} := by
      rcases card_le_one_cases hc with rfl | ⟨a, rfl⟩
      · simp at hp
      · rw [Finset.mem_singleton.1 hp]
    subst hUp
    let τ : (dihModel T ap B).G := (⟨Multiplicative.ofAdd (Pi.single p 1), 1⟩ : Gd)
    have hτt : tyOf τ = 0 := rfl
    have hτb : bitOf τ p = 1 := by
      show red ((Pi.single p (1 : ZMod 4) : ℕ → ZMod 4) p) = 1
      rw [Pi.single_eq_same]; rfl
    refine ⟨τ, (dihModel T ap B).frob p, 1, Or.inl rfl, rfl, fun s hs hsp => absurd (Finset.mem_singleton.1 hs) hsp,
      by show chiB p τ = _; rw [chiB_apply, hτb], rfl, fun s hs hsp => absurd (Finset.mem_singleton.1 hs) hsp, ?_⟩
    rw [hval, hval, hval, hval, Finset.erase_singleton]
    simp only [valF, blockOf_empty, blockOf_singleton]
    have e1 : tyOf (g * τ * (dihModel T ap B).frob p) = tyOf g + T.typ p := by
      show tyOf g + tyOf τ + T.typ p = _; rw [hτt, add_zero]
    have e2 : tyOf (g * (dihModel T ap B).frob p) = tyOf g + T.typ p := rfl
    have e3 : tyOf (g * τ) = tyOf g := by
      show tyOf g + tyOf τ = _; rw [hτt, add_zero]
    have e4 : bitOf (g * τ) p = bitOf g p + 1 := by
      rw [← hτb]; exact bitOf_mul g τ p
    rw [e1, e2, e3, e4]
    obtain ⟨-, k, hk⟩ := cp_sum_odd (hap p) (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
    have hc' : ((Cp (ap p) (-1) : ℤ) : ZMod 2) = ((Cp (ap p) 1 : ℤ) : ZMod 2) + 1 := by
      have : (Cp (ap p) (-1) : ℤ) = 2 * k + 1 - Cp (ap p) 1 := by linarith
      rw [this]; push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
      generalize ((Cp (ap p) 1 : ℤ) : ZMod 2) = c
      revert c; decide
    rw [hc']
    generalize ((Cp (ap p) 1 : ℤ) : ZMod 2) = c
    generalize tyOf g = e
    generalize bitOf g p = x
    generalize T.typ p = t
    revert c e x t; decide

/-- **Non-vacuity of `ConstituentModelRel` with a nonzero reading** (`PROVED`): for the sign type
data, `a_p = 0` and every budget `B ≤ 2`, a corrected constituent model with its inputs whose
reading is one at `{3}`. -/
theorem constituentModelRel_nonzero (B : ℕ) (hB : B ≤ 2) :
    ∃ R : Finset ℕ → ZMod 2, (∃ X : ConstituentModelRel signTypeData R (fun _ => 0) B, X.Inputs) ∧
      R {3} = 1 :=
  ⟨Rd signTypeData, ⟨dihModel signTypeData _ B, dihModel_inputs signTypeData _ (fun _ => ⟨0, rfl⟩) B hB⟩,
    Rd_three⟩


/-- RC0's rules within the budget follow: `RulesUpTo` at size one for the symbol of the reading
(`PROVED`, `rulesUpTo_of_constituentsRel`). -/
theorem rulesUpTo_dihModel :
    RulesUpTo (AddMonoidHom.id (ZMod 2)) (symb signTypeData (Rd signTypeData)) 1 :=
  rulesUpTo_of_constituentsRel (dihModel signTypeData (fun _ => 0) 2)
    (dihModel_inputs signTypeData _ (fun _ => ⟨0, rfl⟩) 2 le_rfl) (fun _ _ => ⟨0, rfl⟩)


end ZInQ.Contrib.CloudB3RC53.TraceWitness.Dih
