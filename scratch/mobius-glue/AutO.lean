import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.HDecomp.Textbook.SkolemNoether

/-! Development file for §7 of `MobiusGlue.lean`: `AutOInnerFinite` from Skolem–Noether (proved
in the kernel, `TSkolemKW.leafSkolemNoether`) and the finiteness of `N(𝒪)/ℚ^×𝒪^×`. -/

noncomputable section

namespace LeafQM

namespace AutODev

/-- Copy of `AutOInnerFinite` (§4 of `MobiusGlue.lean`). -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-! ### `AutOInnerFinite` from Skolem–Noether and the normalizer -/

/-- **Normalizer fact (N(𝒪)/ℚ^×𝒪^× finite).** Every `u ∈ B^×` normalizing `𝒪` is
`q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t` in a fixed finite set. -/
def NormalizerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ, (∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) →
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B)

/-- Skolem–Noether (proved in the kernel, `TSkolemKW.leafSkolemNoether`) applied to `α̃`. -/
theorem conj_of_skolem : ∃ u : Bˣ, ∀ b : B, extFun α b = u * b * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner TSkolemKW.leafSkolemNoether (extAlgEquiv α)
  exact ⟨u, fun b => hu b⟩

/-- Conjugation by a unit of `𝒪`, `a ↦ v⁻¹ a v`. -/
def conjUnit (v : Oˣ) : O ≃+* O where
  toFun a := ((v⁻¹ : Oˣ) : O) * a * v
  invFun a := (v : O) * a * ((v⁻¹ : Oˣ) : O)
  left_inv a := by
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  right_inv a := by
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  map_mul' a b := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' a b := by
    simp only [mul_add, add_mul]

theorem key_conj {R : Type*} [Ring R] (x y w w' c c' t : R) (hvv : w' * w = 1) (hcc : c' * c = 1)
    (hc : c * x = x * c) (h : x * (c * w * t) = c * w * t * y) : w' * x * w * t = t * y := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc w' * x * w * t = w' * (x * w * t) := by simp only [mul_assoc]
    _ = w' * (w * t * y) := by rw [h1]
    _ = t * y := by simp only [← mul_assoc]; rw [hvv, one_mul]

/-- **`AutOInnerFinite` from the normalizer fact** (with Skolem–Noether from the kernel). -/
theorem autOInnerFinite_of_normalizer (hN : NormalizerFinite) : AutOInnerFinite := by
  classical
  obtain ⟨T, hT, hTu⟩ := hN
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, dif_pos hβ']
    exact Classical.choose_spec hβ'
  have hT' : T'.Finite := by
    refine Set.Finite.of_finite_image (f := f) (hT.subset (t := f '' T') ?_) ?_
    · rintro _ ⟨β, hβ, rfl⟩; exact (hf β hβ).1
    · intro β₁ h₁ β₂ h₂ heq
      apply RingEquiv.ext; intro a
      apply Subtype.ext
      have e1 := (hf β₁ h₁).2 a
      have e2 := (hf β₂ h₂).2 a
      rw [heq] at e1
      exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  refine ⟨T', hT', fun α => ?_⟩
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := hTu u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end AutODev

end LeafQM

#print axioms LeafQM.AutODev.extAlgEquiv
#print axioms LeafQM.AutODev.autOInnerFinite_of_normalizer
