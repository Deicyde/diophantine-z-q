import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.HDecomp.Repo.PRArith
import ZInQKernel.HDecomp.Textbook.SkolemNoether

/-!
# inner-twist: `FibreCoverExists` without `InnerTwistCount` and `UnramifiedConjugates`

Task inner-twist (2026-11-13). Assembly file:
* §0 `scratch/aut-o-finite/AutOFinite.lean` (body, unchanged): `Aut(𝒪)/Inn(𝒪^×)` has four classes.
* §1 `scratch/fibre-cover/FibreCover.lean` (body, unchanged; it states `InnerTwistCount` and
  `UnramifiedConjugates` and proves `fibreCoverExists_of_propTS`, `fibreCoverExists_of_propTSAll`).
* §2 the proofs `innerTwistCount` (`InnerTwist.lean`) and `unramifiedConjugates`
  (`UnramConj.lean`), and the composites with both hypotheses discharged.
Placed before §1's `open … MonObj`, §0 is unaffected by it.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

/-! ## §A The target (verbatim) -/

/-- **Algebra fact (finiteness of `Aut(𝒪)` modulo inner automorphisms by units).** Every ring
automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many. (Every
automorphism of `𝒪` extends to `B = 𝒪 ⊗ ℚ`, hence is conjugation by some `x ∈ N(𝒪)`
(Skolem–Noether), and `N(𝒪)/ℚ^×𝒪^×` is finite: for the maximal order of the quaternion algebra
of discriminant 6 it is the Atkin–Lehner group `W ≅ (ℤ/2)²`. STANDARD (Vignéras, *Arithmétique
des algèbres de quaternions*; locator UNVERIFIED); not in Mathlib.) A statement about the concrete
order `O` of the kernel only. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

end Pin

end AV

end LeafQM

/-! ## §7 `AutOInnerFinite` from Skolem–Noether (proved in the kernel) and `NormalizerFinite`

(Outside the `open MonObj` scope of §0-§6.) -/

namespace LeafQM

namespace AV

namespace Pin

namespace AutOExt

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
    simp only [f, hβ', dite_true]
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

end AutOExt

end Pin

end AV

end LeafQM

/-! ## §8 `NormalizerFinite`, proved: `N(𝒪)/ℚ^×𝒪^×` is represented by `{1, i, j, ij}`

Descent on `|nrd|`. A prime `p ∤ 6` dividing `nrd(u)` of a normalizing `u ∈ 𝒪` divides `u`: an
explicit identity `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`,
`scratch/mobius-glue/py/normalizer_identity.py`). If `2 | nrd(u)` then `u i⁻¹ ∈ 𝒪`, and if
`3 | nrd(u)` then `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by `decide`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace NormO

/-! ### Integer coordinates -/

/-- The reduced norm in the coordinates of `ofInt`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2

/-- The conjugate in the coordinates of `ofInt`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [mulCoord, nrdZ]; ring

theorem ofInt_scalar (z : ℤ) : ofInt ![z, 0, 0, 0] = algebraMap ℚ B (z : ℚ) := by
  ext <;> simp [ofInt]

theorem smul_ofInt (z : ℤ) (n : Fin 4 → ℤ) : (z : ℚ) • ofInt n = ofInt (fun l => z * n l) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O_iff (x : B) : x ∈ O ↔ ∃ n, x = ofInt n := Iff.rfl

/-- `(1/z) • ofInt m ∈ 𝒪` forces `z ∣ m`. -/
theorem dvd_of_smul_mem {z : ℤ} (hz : z ≠ 0) {m : Fin 4 → ℤ}
    (h : ((z : ℚ)⁻¹) • ofInt m ∈ O) : ∀ l, z ∣ m l := by
  obtain ⟨w, hw⟩ := h
  have : ofInt m = ofInt (fun l => z * w l) := by
    rw [← smul_ofInt, ← hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hz), one_smul]
  have e := AV.ofInt_injective this
  intro l
  exact ⟨w l, congrFun e l⟩

/-! ### The units `i`, `j` of `B` -/

def ei : Fin 4 → ℤ := ![0, 1, 0, 0]
def ej : Fin 4 → ℤ := ![-1, 0, 2, 0]

theorem nrdZ_ei : nrdZ ei = -2 := by simp [nrdZ, ei]
theorem nrdZ_ej : nrdZ ej = 3 := by simp [nrdZ, ej]

def ui : Bˣ where
  val := ofInt ei
  inv := ((2 : ℚ)⁻¹) • ofInt ei
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]

def uj : Bˣ where
  val := ofInt ej
  inv := ((-3 : ℚ)⁻¹) • ofInt ej
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]

/-- The representatives `{1, i, j, ij}` of `N(𝒪)/ℚ^×𝒪^×`. -/
def T : Set Bˣ := {1, ui, uj, ui * uj}

theorem T_finite : T.Finite := by
  simp only [T]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-! ### Normalizing units -/

/-- `u` normalizes `𝒪`. -/
def IsNorm (u : Bˣ) : Prop :=
  ∀ a ∈ O, (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O ∧ ((u⁻¹ : Bˣ) : B) * a * u ∈ O

theorem IsNorm.mul {u w : Bˣ} (hu : IsNorm u) (hw : IsNorm w) : IsNorm (u * w) := by
  intro a ha
  refine ⟨?_, ?_⟩
  · have := (hu _ (hw a ha).1).1
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this
  · have := (hw _ (hu a ha).2).2
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this

theorem IsNorm.inv {u : Bˣ} (hu : IsNorm u) : IsNorm u⁻¹ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hu a ha
  exact ⟨h2, by simpa using h1⟩

/-- The unit `c ∈ ℚ^×` of `B`. -/
def sc (c : ℚ) (hc : c ≠ 0) : Bˣ where
  val := algebraMap ℚ B c
  inv := algebraMap ℚ B c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem isNorm_sc (c : ℚ) (hc : c ≠ 0) : IsNorm (sc c hc) := by
  intro a ha
  have e1 : ((sc c hc : Bˣ) : B) * a * (((sc c hc)⁻¹ : Bˣ) : B) = a := by
    change algebraMap ℚ B c * a * algebraMap ℚ B c⁻¹ = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
  have e2 : (((sc c hc)⁻¹ : Bˣ) : B) * a * ((sc c hc : Bˣ) : B) = a := by
    change algebraMap ℚ B c⁻¹ * a * algebraMap ℚ B c = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  exact ⟨by rw [e1]; exact ha, by rw [e2]; exact ha⟩

theorem isNorm_ui : IsNorm ui := by
  rintro a ⟨n, rfl⟩
  have e : ((ui : Bˣ) : B) * ofInt n * ((ui⁻¹ : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change ofInt ei * ofInt n * (((2 : ℚ)⁻¹) • ofInt ei) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  have e' : ((ui⁻¹ : Bˣ) : B) * ofInt n * ((ui : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change (((2 : ℚ)⁻¹) • ofInt ei) * ofInt n * ofInt ei = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

theorem isNorm_uj : IsNorm uj := by
  rintro a ⟨n, rfl⟩
  have e : ((uj : Bˣ) : B) * ofInt n * ((uj⁻¹ : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change ofInt ej * ofInt n * (((-3 : ℚ)⁻¹) • ofInt ej) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  have e' : ((uj⁻¹ : Bˣ) : B) * ofInt n * ((uj : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change (((-3 : ℚ)⁻¹) • ofInt ej) * ofInt n * ofInt ej = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

/-! ### The norm of a unit in `𝒪` and its inverse -/

theorem nrdZ_ne_zero (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) : nrdZ n ≠ 0 := by
  intro h0
  have h1 : (u : B) * ofInt (conjC n) = 0 := by
    rw [hu, ofInt_mul, mulCoord_conjC, h0, ofInt_scalar]; simp
  have h2 : ofInt (conjC n) = 0 := by
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) * x) h1
    simpa [← mul_assoc] using this
  have h3 : conjC n = 0 := AV.ofInt_injective (h2.trans ofInt_zero.symm)
  have h4 : n = 0 := by
    funext l
    have e0 := congrFun h3 0; have e1 := congrFun h3 1
    have e2 := congrFun h3 2; have e3 := congrFun h3 3
    simp [conjC] at e0 e1 e2 e3
    fin_cases l <;> simp <;> omega
  have : (u : B) = 0 := by rw [hu, h4, ofInt_zero]
  exact u.ne_zero this

theorem inv_eq (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) :
    ((u⁻¹ : Bˣ) : B) = ((nrdZ n : ℚ)⁻¹) • ofInt (conjC n) := by
  have hN : (nrdZ n : ℚ) ≠ 0 := by exact_mod_cast nrdZ_ne_zero u n hu
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_smul_comm, hu, ofInt_mul, mulCoord_conjC, ofInt_scalar, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ hN, map_one]

def bas : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- For a normalizing `u = ofInt n`, `nrd(u)` divides every coordinate of `u e_k ū`. -/
theorem nrd_dvd_coords (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (k l : Fin 4) : nrdZ n ∣ mulCoord (mulCoord n (bas k)) (conjC n) l := by
  have h := (hN (ofInt (bas k)) ⟨_, rfl⟩).1
  rw [inv_eq u n hu, mul_smul_comm, hu, ofInt_mul, ofInt_mul] at h
  exact dvd_of_smul_mem (nrdZ_ne_zero u n hu) h l

/-- The identities `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`). -/
theorem six_sq_identities (n : Fin 4 → ℤ) :
    let F := fun k l => mulCoord (mulCoord n (bas k)) (conjC n) l
    6 * n 0 ^ 2 = 2 * F 0 0 + 2 * F 1 1 + 2 * F 1 3 + 2 * F 2 2 - 2 * F 3 1 ∧
    6 * n 1 ^ 2 = -F 1 1 - 2 * F 2 0 + F 3 1 + F 3 3 ∧
    6 * n 2 ^ 2 = 2 * F 0 0 - 2 * F 1 1 + 2 * F 2 2 - 2 * F 3 3 ∧
    6 * n 3 ^ 2 = F 1 1 + F 1 3 - 2 * F 2 0 - F 3 3 := by
  intro F
  simp only [F, mulCoord, bas, conjC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- A prime `p ≠ 2, 3` dividing `nrd(u)` of a normalizing `u = ofInt n` divides `n`. -/
theorem dvd_of_prime_dvd_nrd (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hpd : (p : ℤ) ∣ nrdZ n) :
    ∀ l, (p : ℤ) ∣ n l := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hF : ∀ k l, (p : ℤ) ∣ mulCoord (mulCoord n (bas k)) (conjC n) l :=
    fun k l => hpd.trans (nrd_dvd_coords u n hu hN k l)
  have h6 : ¬ (p : ℤ) ∣ 6 := by
    intro h
    have h' : p ∣ 6 := by exact_mod_cast h
    have : p ∣ 2 * 3 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  obtain ⟨i0, i1, i2, i3⟩ := six_sq_identities n
  have k0 : (p : ℤ) ∣ 6 * n 0 ^ 2 := by
    rw [i0]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 1 3) _))
      (dvd_mul_of_dvd_right (hF 2 2) _)) (dvd_mul_of_dvd_right (hF 3 1) _)
  have k1 : (p : ℤ) ∣ 6 * n 1 ^ 2 := by
    rw [i1]
    exact dvd_add (dvd_add (dvd_sub (dvd_neg.mpr (hF 1 1)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 1)) (hF 3 3)
  have k2 : (p : ℤ) ∣ 6 * n 2 ^ 2 := by
    rw [i2]
    exact dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 2 2) _))
      (dvd_mul_of_dvd_right (hF 3 3) _)
  have k3 : (p : ℤ) ∣ 6 * n 3 ^ 2 := by
    rw [i3]
    exact dvd_sub (dvd_sub (dvd_add (hF 1 1) (hF 1 3)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 3)
  have key : ∀ l, (p : ℤ) ∣ 6 * n l ^ 2 := by
    intro l; fin_cases l
    exacts [k0, k1, k2, k3]
  intro l
  rcases hpZ.dvd_or_dvd (key l) with h | h
  · exact absurd h h6
  · exact hpZ.dvd_of_dvd_pow h

/-! ### The primes 2 and 3 -/

theorem two_dvd_mulCoord_ei (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) :
    ∀ l, (2 : ℤ) ∣ mulCoord n ei l := by
  have hz : ((nrdZ n : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 2,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a = 0 ∧ c = 0 := by
    decide
  obtain ⟨h0, h2⟩ := key _ _ _ _ hz
  have d0 : (2 : ℤ) ∣ n 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
  have d2 : (2 : ℤ) ∣ n 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
  intro l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem three_dvd_mulCoord_ej (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) :
    ∀ l, (3 : ℤ) ∣ mulCoord n ej l := by
  have hz : ((nrdZ n : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 3,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a - c = 0 ∧ b - d = 0 := by
    decide
  obtain ⟨h0, h1⟩ := key _ _ _ _ hz
  have d0 : (3 : ℤ) ∣ n 0 - n 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h0)
  have d1 : (3 : ℤ) ∣ n 1 - n 3 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h1)
  intro l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

/-! ### Closure of `T` under right multiplication by `i` and `j` -/

theorem T_mem_iff (t : Bˣ) : t ∈ T ↔ t = 1 ∨ t = ui ∨ t = uj ∨ t = ui * uj := Iff.rfl

theorem T_mul_ui : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (ui : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, ui, by simp [T], by simp⟩
  · refine ⟨2, two_ne_zero, 1, by simp [T], ?_⟩
    change ofInt ei * ofInt ei = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ei, QuaternionAlgebra.algebraMap_eq]
  · refine ⟨-1, by norm_num, ui * uj, by simp [T], ?_⟩
    change ofInt ej * ofInt ei = _ * (ofInt ei * ofInt ej)
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-2, by norm_num, uj, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ei = _ * ofInt ej
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

theorem T_mul_uj : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (uj : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, uj, by simp [T], by simp⟩
  · exact ⟨1, one_ne_zero, ui * uj, by simp [T], by simp⟩
  · refine ⟨-3, by norm_num, 1, by simp [T], ?_⟩
    change ofInt ej * ofInt ej = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-3, by norm_num, ui, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ej = _ * ofInt ei
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

/-- Rearranging `q v t i = (q c) v t'` for central `c`. -/
theorem rearrange (q c : ℚ) (V Tt I T' : B) (h : Tt * I = algebraMap ℚ B c * T') :
    algebraMap ℚ B q * V * Tt * I = algebraMap ℚ B (q * c) * V * T' := by
  rw [mul_assoc (algebraMap ℚ B q * V), h, ← mul_assoc, mul_assoc (algebraMap ℚ B q),
    ← Algebra.commutes c V, ← mul_assoc, ← map_mul]

theorem mulCoord_smul_right (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord n (fun l => z * m l) = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem mulCoord_smul_left (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord (fun l => z * n l) m = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem nrdZ_smul (n : Fin 4 → ℤ) (z : ℤ) : nrdZ (fun l => z * n l) = z ^ 2 * nrdZ n := by
  simp [nrdZ]; ring

/-! ### The descent -/

theorem descent (m : ℕ) : ∀ (u : Bˣ) (n : Fin 4 → ℤ), (u : B) = ofInt n →
    (nrdZ n).natAbs = m → IsNorm u →
    ∃ q : ℚ, q ≠ 0 ∧ ∃ v : Oˣ, ∃ t ∈ T, (u : B) = algebraMap ℚ B q * ((v : O) : B) * t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u n hu hm hN
  have hN0 := nrdZ_ne_zero u n hu
  by_cases h1 : m = 1
  · have hsq : nrdZ n * nrdZ n = 1 := by
      have : (nrdZ n).natAbs = 1 := hm.trans h1
      rcases Int.natAbs_eq_iff.mp this with h | h <;> rw [h] <;> norm_num
    set w : Fin 4 → ℤ := fun l => nrdZ n * conjC n l with hw_def
    have hw1 : mulCoord n w = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_right, mulCoord_conjC]
      funext l; fin_cases l <;> simp [hsq]
    have hw2 : mulCoord w n = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_left, mulCoord_conjC']
      funext l; fin_cases l <;> simp [hsq]
    let v : Oˣ :=
      ⟨⟨ofInt n, n, rfl⟩, ⟨ofInt w, w, rfl⟩,
        Subtype.ext (by
          change ofInt n * ofInt w = 1
          rw [ofInt_mul, hw1, ofInt_one]),
        Subtype.ext (by
          change ofInt w * ofInt n = 1
          rw [ofInt_mul, hw2, ofInt_one])⟩
    refine ⟨1, one_ne_zero, v, 1, by simp [T], ?_⟩
    rw [map_one, one_mul, Units.val_one, mul_one]
    exact hu
  · have hm0 : m ≠ 0 := by
      rintro rfl; exact hN0 (Int.natAbs_eq_zero.mp hm)
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : (p : ℤ) ∣ nrdZ n := by
      rw [Int.natCast_dvd, hm]; exact Nat.minFac_dvd m
    have hp1 : 2 ≤ p := hp.two_le
    by_cases hp2 : p = 2
    · have h2 : (2 : ℤ) ∣ nrdZ n := by rw [hp2] at hpd; exact_mod_cast hpd
      have hc := two_dvd_mulCoord_ei n h2
      set n' : Fin 4 → ℤ := fun l => mulCoord n ei l / 2 with hn'_def
      have hn' : mulCoord n ei = fun l => 2 * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hc l)).symm
      have hu' : ((u * ui⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((2 : ℚ)⁻¹) • ofInt ei) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ei = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * ui⁻¹ : Bˣ) : B) * ((ui : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ei
        rw [hmul, nrdZ_ei] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h2' : (-2 : ℤ).natAbs = 2 := rfl
        rw [← hm, e, Int.natAbs_mul, h2']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * ui⁻¹) n' hu' rfl (hN.mul isNorm_ui.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_ui t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * ui⁻¹ : Bˣ) : B) * ui := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    by_cases hp3 : p = 3
    · have h3 : (3 : ℤ) ∣ nrdZ n := by rw [hp3] at hpd; exact_mod_cast hpd
      have hc := three_dvd_mulCoord_ej n h3
      set n' : Fin 4 → ℤ := fun l => -(mulCoord n ej l / 3) with hn'_def
      have hn' : mulCoord n ej = fun l => (-3) * n' l := by
        funext l
        simp only [hn'_def]
        rw [mul_neg, neg_mul, neg_neg, Int.mul_ediv_cancel' (hc l)]
      have hu' : ((u * uj⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((-3 : ℚ)⁻¹) • ofInt ej) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ej = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * uj⁻¹ : Bˣ) : B) * ((uj : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ej
        rw [hmul, nrdZ_ej] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [← hm, e, Int.natAbs_mul, h3']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * uj⁻¹) n' hu' rfl (hN.mul isNorm_uj.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_uj t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * uj⁻¹ : Bˣ) : B) * uj := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    · have hdiv := dvd_of_prime_dvd_nrd u n hu hN p hp hp2 hp3 hpd
      set n' : Fin 4 → ℤ := fun l => n l / p with hn'_def
      have hn' : n = fun l => (p : ℤ) * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hdiv l)).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpi : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero hp0
      have hu' : ((sc _ hpi * u : Bˣ) : B) = ofInt n' := by
        change algebraMap ℚ B ((p : ℚ)⁻¹) * u = _
        rw [← Algebra.smul_def, hu, hn', ← smul_ofInt, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hp0, one_smul]
      have hlt : (nrdZ n').natAbs < m := by
        have e : nrdZ n = (p : ℤ) ^ 2 * nrdZ n' := by rw [hn', nrdZ_smul]
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        rw [← hm, e, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have : 4 ≤ p ^ 2 := by nlinarith
        have : (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs := by
          have : 1 * (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa using this
        exact this
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (sc _ hpi * u) n' hu' rfl ((isNorm_sc _ hpi).mul hN)
      refine ⟨p * q, mul_ne_zero hp0 hq, v, t, ht, ?_⟩
      have : (u : B) = algebraMap ℚ B (p : ℚ) * ((sc _ hpi * u : Bˣ) : B) := by
        change _ = _ * (algebraMap ℚ B ((p : ℚ)⁻¹) * u)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
      rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

/-! ### `NormalizerFinite` -/

/-- **`N(𝒪)/ℚ^×𝒪^×` is finite** (represented by `{1, i, j, ij}`). -/
theorem normalizerFinite : AutOExt.NormalizerFinite := by
  refine ⟨T, T_finite, fun u hu => ?_⟩
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

end NormO

open CategoryTheory AlgebraicGeometry

/-- **`AutOInnerFinite`, proved** (Skolem–Noether from the kernel, the normalizer from §8). -/
theorem autOInnerFinite : AutOInnerFinite :=
  AutOExt.autOInnerFinite_of_normalizer NormO.normalizerFinite

end Pin

end AV

end LeafQM


/-! ## §9 The explicit computation: `Aut(𝒪)/Inn(𝒪^×)` has exactly four classes

Representatives: conjugation by `1, i, j, ij` (`rep 0, …, rep 3`). Every ring automorphism of `𝒪`
is `v · rep k · v⁻¹` for some `k` and `v ∈ 𝒪^×` (`rep_cover`), and `rep k`, `rep l` are conjugate
by a unit of `𝒪` only if `k = l` (`rep_distinct`: a conjugating unit would give
`nrd(t_k) = ± r² nrd(t_l)` with `r ∈ ℚ`, impossible as `nrd(1, i, j, ij) = 1, -2, 3, -6`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace Exact

open NormO AutOExt

/-- The reduced norm of `B = (2, -3)_ℚ`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem nrd_algebraMap (q : ℚ) : nrd (algebraMap ℚ B q) = q ^ 2 := by
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

theorem nrd_ofInt (n : Fin 4 → ℤ) : nrd (ofInt n) =
    ((n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2 : ℤ) : ℚ) := by
  simp [nrd, ofInt]; ring

theorem not_sq (s : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : s ^ 2 = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨s, by rw [← h]; ring⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

/-- An element of `B` commuting with `i` and `j` is a scalar. -/
theorem comm_scalar (w : B) (hi : w * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * w)
    (hj : w * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * w) : w = algebraMap ℚ B w.re := by
  have h1 := congrArg QuaternionAlgebra.imJ hi
  have h2 := congrArg QuaternionAlgebra.imK hi
  have h3 := congrArg QuaternionAlgebra.imI hj
  have h4 := congrArg QuaternionAlgebra.imK hj
  simp at h1 h2 h3 h4
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> linarith

/-- The norm of a unit of `𝒪` is `±1`. -/
theorem nrd_unit (v : Oˣ) : nrd ((v : O) : B) = 1 ∨ nrd ((v : O) : B) = -1 := by
  obtain ⟨n, hn⟩ := (v : O).2
  obtain ⟨m, hm⟩ := ((v⁻¹ : Oˣ) : O).2
  have h1 : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h2 := congrArg nrd h1
  rw [nrd_mul, hn, hm, nrd_ofInt, nrd_ofInt] at h2
  have h3 : nrd 1 = 1 := by simp [nrd]
  rw [h3] at h2
  have h4 := Int.eq_one_or_neg_one_of_mul_eq_one (by exact_mod_cast h2)
  rw [hn, nrd_ofInt]
  rcases h4 with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem isNorm_one : IsNorm 1 := by
  intro a ha
  exact ⟨by simpa using ha, by simpa using ha⟩

/-- Conjugation `a ↦ u a u⁻¹` by a unit `u ∈ B^×` normalizing `𝒪`, as a ring automorphism. -/
def conjO (u : Bˣ) (hu : IsNorm u) : O ≃+* O where
  toFun a := ⟨(u : B) * a * ((u⁻¹ : Bˣ) : B), (hu a a.2).1⟩
  invFun a := ⟨((u⁻¹ : Bˣ) : B) * a * u, (hu a a.2).2⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]
  map_add' a b := by apply Subtype.ext; simp [mul_add, add_mul]

theorem conjO_apply (u : Bˣ) (hu : IsNorm u) (a : O) :
    ((conjO u hu a : O) : B) = (u : B) * a * ((u⁻¹ : Bˣ) : B) := rfl

/-- The representatives `1, i, j, ij` of `N(𝒪)/ℚ^×𝒪^×`. -/
def tt : Fin 4 → Bˣ := ![1, ui, uj, ui * uj]

theorem tt_isNorm (k : Fin 4) : IsNorm (tt k) := by
  fin_cases k
  exacts [isNorm_one, isNorm_ui, isNorm_uj, isNorm_ui.mul isNorm_uj]

/-- The four representatives of `Aut(𝒪)/Inn(𝒪^×)`: conjugation by `1, i, j, ij`. -/
def rep (k : Fin 4) : O ≃+* O := conjO (tt k) (tt_isNorm k)

/-- The reduced norms `1, -2, 3, -6` of `1, i, j, ij`. -/
def N : Fin 4 → ℤ := ![1, -2, 3, -6]

theorem nrd_tt (k : Fin 4) : nrd (tt k : B) = (N k : ℚ) := by
  fin_cases k
  · simp [tt, N, nrd]
  · change nrd (ofInt ei) = _
    simp [nrd_ofInt, ei, N]
  · change nrd (ofInt ej) = _
    simp [nrd_ofInt, ej, N]
  · change nrd (ofInt ei * ofInt ej) = _
    rw [nrd_mul]
    simp [nrd_ofInt, ei, ej, N]; norm_num

theorem tt_of_T (t : Bˣ) (ht : t ∈ T) : ∃ k, tt k = t := by
  rcases (T_mem_iff t).1 ht with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The concrete normalizer statement (the body of `NormO.normalizerFinite`, with `T` named). -/
theorem normalizer_rep (u : Bˣ) (hu : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) :
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B) := by
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

theorem key2 {R : Type*} [Ring R] (x y w w' c c' t t' : R) (hww : w * w' = 1)
    (hcc : c' * c = 1) (htt : t * t' = 1) (hc : c * x = x * c)
    (h : x * (c * w * t) = c * w * t * y) : x = w * (t * y * t') * w' := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc x = x * (w * (t * t') * w') := by rw [htt, mul_one, hww, mul_one]
    _ = x * w * t * t' * w' := by simp only [mul_assoc]
    _ = w * t * y * t' * w' := by rw [h1]
    _ = w * (t * y * t') * w' := by simp only [mul_assoc]

/-- **Every automorphism of `𝒪` is `v · rep k · v⁻¹`** for some `k` and some `v ∈ 𝒪^×`. -/
theorem rep_cover (α : O ≃+* O) : ∃ k : Fin 4, ∃ v : Oˣ, ∀ a : O,
    α a = (v : O) * rep k a * ((v⁻¹ : Oˣ) : O) := by
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
  obtain ⟨t, ht, v, q, hq, huq⟩ := normalizer_rep u hnorm
  obtain ⟨k, rfl⟩ := tt_of_T t ht
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  refine ⟨k, v, fun a => Subtype.ext ?_⟩
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul]
  change _ = ((v : O) : B) * ((tt k : B) * a * (((tt k)⁻¹ : Bˣ) : B)) * (((v⁻¹ : Oˣ) : O) : B)
  have hvv : ((v : O) : B) * (((v⁻¹ : Oˣ) : O) : B) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hq, map_one]
  have h := hrel a
  rw [huq] at h
  exact key2 _ _ _ _ _ _ _ _ hvv hcc (Units.mul_inv _) (Algebra.commutes q _) h

/-- **The four representatives are pairwise non-conjugate by units of `𝒪`.** -/
theorem rep_distinct (k l : Fin 4) (v : Oˣ)
    (h : ∀ a : O, rep k a = (v : O) * rep l a * ((v⁻¹ : Oˣ) : O)) : k = l := by
  set V : B := ((v : O) : B) with hVdef
  set V' : B := (((v⁻¹ : Oˣ) : O) : B) with hV'def
  have hVV' : V * V' = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have hV'V : V' * V = 1 := by
    rw [hVdef, hV'def, ← MulMemClass.coe_mul, Units.inv_mul]; rfl
  have hV'Vx : ∀ X : B, V' * (V * X) = X := fun X => by rw [← mul_assoc, hV'V, one_mul]
  set P : B := (tt k : B) with hP
  set P' : B := (((tt k)⁻¹ : Bˣ) : B) with hP'
  set Q : B := (tt l : B) with hQ
  set Q' : B := (((tt l)⁻¹ : Bˣ) : B) with hQ'
  have hP'P : P' * P = 1 := Units.inv_mul _
  have hQ'Qx : ∀ X : B, Q' * (Q * X) = X := fun X => by
    rw [← mul_assoc, show Q' * Q = 1 from Units.inv_mul _, one_mul]
  have hQQ'x : ∀ X : B, Q * (Q' * X) = X := fun X => by
    rw [← mul_assoc, show Q * Q' = 1 from Units.mul_inv _, one_mul]
  have hVV'x : ∀ X : B, V * (V' * X) = X := fun X => by rw [← mul_assoc, hVV', one_mul]
  have hcomm : ∀ a ∈ O, (Q' * V' * P) * a = a * (Q' * V' * P) := by
    intro a ha
    have e : P * a * P' = V * (Q * a * Q') * V' := by
      have := congrArg Subtype.val (h ⟨a, ha⟩)
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul] at this
      exact this
    calc Q' * V' * P * a = Q' * V' * (P * a * P') * P := by
          simp only [mul_assoc, hP'P, mul_one]
      _ = Q' * V' * (V * (Q * a * Q') * V') * P := by rw [e]
      _ = a * (Q' * V' * P) := by simp only [mul_assoc, hV'Vx, hQ'Qx]
  set W := Q' * V' * P with hW
  have hWs : W = algebraMap ℚ B W.re :=
    comm_scalar W (hcomm _ (mem_O_of_int 0 1 0 0)) (hcomm _ (mem_O_of_int 0 0 1 0))
  have hPW : P = V * Q * W := by
    rw [hW]; simp only [mul_assoc, hQQ'x, hVV'x]
  have e1 : (N k : ℚ) = nrd V * N l * W.re ^ 2 := by
    rw [← nrd_tt, ← nrd_tt, ← nrd_algebraMap, ← hWs, ← nrd_mul, ← nrd_mul]
    exact congrArg nrd hPW
  have hmain : ∀ ε : ℤ, nrd V = ε → ε ^ 2 = 1 →
      (W.re * N l) ^ 2 = ((ε * N k * N l : ℤ) : ℚ) := by
    intro ε hε hε2
    have hε2' : (ε : ℚ) ^ 2 = 1 := by exact_mod_cast hε2
    push_cast
    rw [e1, hε]
    linear_combination (-(W.re ^ 2 * (N l : ℚ) ^ 2)) * hε2'
  rcases nrd_unit v with h1 | h1
  · have hm := hmain 1 (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim
  · have hm := hmain (-1) (by rw [← hVdef] at h1; simpa using h1) (by norm_num)
    fin_cases k <;> fin_cases l <;>
      first | rfl | exact (not_sq _ _ (by decide +kernel) hm).elim

/-- **Explicit computation of `Aut(𝒪)/Inn(𝒪^×)`: exactly four classes**, represented by
conjugation by `1, i, j, ij`. -/
theorem autO_mod_inner_exact : ∃ t : Fin 4 → (O ≃+* O),
    (∀ α : O ≃+* O, ∃ k, ∃ v : Oˣ, ∀ a : O, α a = (v : O) * t k a * ((v⁻¹ : Oˣ) : O)) ∧
    ∀ k l, (∃ v : Oˣ, ∀ a : O, t k a = (v : O) * t l a * ((v⁻¹ : Oˣ) : O)) → k = l :=
  ⟨rep, rep_cover, fun k l ⟨v, hv⟩ => rep_distinct k l v hv⟩

/-- `AutOInnerFinite` again, from the explicit computation. -/
theorem autOInnerFinite' : AutOInnerFinite := by
  refine ⟨Set.range rep, Set.finite_range rep, fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := rep_cover α
  exact ⟨rep k, ⟨k, rfl⟩, v, hv⟩

end Exact

end Pin

end AV

end LeafQM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK



/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P


/-! ## Part 1 (proved): `FibreCoverOut` is a statement about the residue field of `y` alone -/

/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree (copied from `scratch/rv-g0pieces/Exotic.lean`). -/
theorem spec_to_specQ_eq {K : Type} [Field K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- **A `ℚ̄`-point factors through every subfield `K ⊆ ℚ̄` containing its residue field.** -/
theorem exists_factor_of_residueImage_le (Y : Over (Spec (CommRingCat.of ℚ)))
    (y : fieldPt Qbar ⟶ Y) (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ yK : fieldPt K ⟶ Y, fieldMap K.val ≫ yK = y := by
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  unfold residueImage at hK
  rw [hp] at hK
  have hmem : ∀ a, emb a ∈ K := fun a => hK (IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩)
  let emb' : Y.left.residueField x ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (emb.hom.codRestrict K hmem)
  have aux : Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
      (Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩ = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply, hp]
    rfl
  exact ⟨Over.homMk ((Scheme.SpecToEquivOfField K Y.left).symm ⟨x, emb'⟩)
    (spec_to_specQ_eq _ _), Over.OverMorphism.ext aux⟩

/-- The residue field of `z ∘ Spec(K ⊆ ℚ̄)` lies in `K` (scheme form). -/
theorem residueImage_le_aux {X : Scheme.{0}} (K : IF) (z : Spec (CommRingCat.of K) ⟶ X) :
    residueImage (X := X)
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ z) ≤ K := by
  unfold residueImage
  rw [IntermediateField.adjoin_le_iff, specToEquivOfField_comp]
  rintro _ ⟨a, rfl⟩
  exact ((Scheme.SpecToEquivOfField K X z).2 a).2

/-- The residue field of `y ∘ Spec(K ⊆ ℚ̄)` lies in `K`. -/
theorem residueImage_comp_le (Y : Over (Spec (CommRingCat.of ℚ))) (K : IF)
    (yK : fieldPt K ⟶ Y) : residueImage (X := Y.left) (fieldMap K.val ≫ yK).left ≤ K :=
  residueImage_le_aux K yK.left

/-- A base change along `K ⊆ ℚ̄` of `PK`, isomorphic to `P`, makes `PK.A` a model of `P.A`. -/
theorem isModelOver_of_baseChange {K : IF} {PK : QML3 K} {Q P : QML3 Qbar}
    (hb : IsBaseChangeOf ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) PK Q) (e : Q.Iso P) :
    IsModelOver K PK.A P := by
  obtain ⟨g, hpb, -, -⟩ := hb
  refine ⟨Iso.trans ?_ ⟨e.φ.hom, e.ψ.hom, e.left, e.right⟩⟩
  exact Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd

/-- **The rational fibre (proved from R1fp alone)**: if `K ⊆ ℚ̄` contains the residue field of
the point `y` of `P`, there is a rational fibre `PK/K` over `P`. -/
theorem rationalFibre_of_le {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) {y : fieldPt Qbar ⟶ Y} {P : QML3 Qbar} (hy : Φ Qbar y = M3.mk P)
    (K : IF) (hK : residueImage (X := Y.left) y.left ≤ K) :
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK := by
  obtain ⟨yK, hyK⟩ := exists_factor_of_residueImage_le Y y K hK
  -- adapted (inner-twist): R1fpProps has two more conjuncts after pin-apply
  obtain ⟨-, -, -, hnat, -⟩ := h1
  have hPK : Φ K yK = M3.mk (Quotient.out (Φ K yK)) := (Quotient.out_eq _).symm
  obtain ⟨Q, hQ, hb⟩ := hnat K Qbar K.val yK _ hPK
  rw [hyK, hy] at hQ
  have e : Nonempty (P.Iso Q) := Quotient.exact hQ
  exact ⟨_, ⟨yK, hPK, hyK ▸ hy⟩, isModelOver_of_baseChange hb e.some.symm⟩

/-- **The field part of G2's output** for a subfield `F ⊆ ℚ̄`: `F` lies in the splitting field
of a separable `f ∈ ℚ[X]` of degree `≤ 324` unramified outside `T(u)`. -/
def FibreFieldOut (F : IF) (u : ℚ) : Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    F ≤ IntermediateField.adjoin ℚ (f.rootSet Qbar)

/-- **`FibreCoverOut` is exactly the field part for the residue field of `y`** (both
directions, from R1fp alone). -/
theorem fibreCoverOut_iff {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) {y : fieldPt Qbar ⟶ Y} {P : QML3 Qbar} (hy : Φ Qbar y = M3.mk P)
    (u : ℚ) : FibreCoverOut Y Φ u P ↔ FibreFieldOut (residueImage (X := Y.left) y.left) u := by
  constructor
  · rintro ⟨f, hs, hd, hram, PK, ⟨yK, -, hyK⟩, -⟩
    refine ⟨f, hs, hd, hram, ?_⟩
    have : fieldMap (IntermediateField.adjoin ℚ (f.rootSet Qbar)).val ≫ yK = y :=
      (Φ Qbar).injective (hyK.trans hy.symm)
    rw [← this]
    exact residueImage_comp_le Y _ yK
  · rintro ⟨f, hs, hd, hram, hle⟩
    obtain ⟨PK, hPK⟩ := rationalFibre_of_le h1 hy _ hle
    exact ⟨f, hs, hd, hram, PK, hPK⟩

/-- **Independence of the moduli bijection (the relabeling of rv-g0pieces keeps G2).** For two
bijections `Φ, Φ'` on the same `Y`, both with R1fp, and the same point `y`, `FibreCoverOut`
holds for `(Φ, P)` iff it holds for `(Φ', P')`, where `P`, `P'` are the objects of `y`.
In particular a relabeled triple `(Y, Φ ∘ τ, π)` (rv-g0pieces `relabel`, R1fp by
`r1fp_relabel`) satisfies G2 at `y` iff `(Y, Φ, π)` does. -/
theorem fibreCoverOut_indep {Y : Over (Spec (CommRingCat.of ℚ))} {Φ Φ' : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (h1' : R1fpProps Y Φ') {y : fieldPt Qbar ⟶ Y} {P P' : QML3 Qbar}
    (hy : Φ Qbar y = M3.mk P) (hy' : Φ' Qbar y = M3.mk P') (u : ℚ) :
    FibreCoverOut Y Φ u P ↔ FibreCoverOut Y Φ' u P' :=
  (fibreCoverOut_iff h1 hy u).trans (fibreCoverOut_iff h1' hy' u).symm

/-! ## Part 2 (proved): the field part from a degree bound and unramifiedness of `ℚ(y)` -/

/-- **Textbook (STANDARD): the Galois closure of an unramified field is unramified.** If
`ℚ(α) ⊆ ℚ̄` is unramified at `p`, so is the splitting field `ℚ(roots of minpoly α)`, which is
the compositum of the conjugates `σℚ(α) ≅ ℚ(α)`; a compositum of number fields unramified at `p`
is unramified at `p` (Neukirch, *Algebraic Number Theory*, Ch. I §9 or Ch. III §2, the
compositum of unramified extensions; UNVERIFIED locator). Not in Mathlib v4.35 for
`UnramifiedAt` (cf. g0-mod-field's `UnramifiedSup`, the Galois case). -/
def UnramifiedConjugates : Prop :=
  ∀ (α : Qbar) (p : ℕ), UnramifiedAt (IntermediateField.adjoin ℚ {α}) p →
    UnramifiedAt (IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar)) p

/-- **The field part from `[F:ℚ] ≤ 324` and `F` unramified outside `T(u)`**: take `f` the
minimal polynomial of a primitive element of `F` (separable in characteristic 0, of degree
`[F:ℚ]`); its splitting field contains `F` and is unramified outside `T(u)` by
`UnramifiedConjugates`. -/
theorem fibreFieldOut_of (hU : UnramifiedConjugates) (F : IF) [FiniteDimensional ℚ F]
    (hd : Module.finrank ℚ F ≤ 324) (u : ℚ)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt F p) : FibreFieldOut F u := by
  obtain ⟨β, hF⟩ : ∃ β : Qbar, IntermediateField.adjoin ℚ {β} = F := by
    obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
    refine ⟨α, le_antisymm ?_ ?_⟩
    · rw [IntermediateField.adjoin_simple_le_iff]; exact α.2
    · intro x hx
      have h1 : (⟨x, hx⟩ : F) ∈ IntermediateField.adjoin ℚ {α} := by
        rw [hα]; exact IntermediateField.mem_top
      have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map F.val := ⟨⟨x, hx⟩, h1, rfl⟩
      rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
      exact h2
  subst hF
  have hint : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly ℚ β, (minpoly.irreducible hint).separable, ?_, fun p hp => hU _ p (hram p hp), ?_⟩
  · rw [← IntermediateField.adjoin.finrank hint]; exact hd
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ _
      ((Polynomial.mem_rootSet).2 ⟨minpoly.ne_zero hint, minpoly.aeval ℚ _⟩)

/-! ## Part 3: the remaining glue as named Props, and `FibreCoverExists` from them -/

/-- **Glue (G2, degree; Glazer N5 L436-441 and L524-526): the residue field of a point over
`J(u)` has degree `≤ 324`.** For moduli data with R1fp, R2fp, `u ∉ 𝒞`, and a `ℚ̄`-point `y`
with object `P` over `J(u)`, the residue field `ℚ(y) ⊆ ℚ̄` is finite over `ℚ` of degree `≤ 324`.
Argument (glue): the `ℚ`-embeddings of `ℚ(y)` give distinct points `σy` of the fibre over the
rational value `J(u)` (`ToP1.val_comp`), which `Φ` maps injectively into the `Aut 𝒪`-twist class
of `P` (R2fp); that class has at most `4·|(𝒪/3𝒪)^×| ≤ 324` elements (`TwistClassCard`). This
step does not depend on which triple `(Y, Φ, π)` is used. -/
def FibreDegree : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (y : fieldPt Qbar ⟶ Y), R1fpProps Y Φ → R2fpProps Y Φ π →
    u ∉ contactSet → Φ Qbar y = M3.mk P →
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ _ : FiniteDimensional ℚ (residueImage (X := Y.left) y.left),
      Module.finrank ℚ (residueImage (X := Y.left) y.left) ≤ 324

/-- **Glue (G2, ramification: Prop. TS + Lemma NV, Glazer N5 L484-529; h-decomposition G2 with
inputs R1(d), R2, T1, T2): the residue field of a point over `J(u)` is unramified outside
`T(u) = S_mul ∪ supp M_{S_mul}(u)`.** For the genuine `(Y₃, π)` this is the manuscript's local
calculation: `Y₃ → P¹` has a proper smooth model over `ℤ[1/30]` branched only over `0, ∞, −16/27`
with tame indices; the pullback by `J` has indices `2, 6, 2`, normalized to `2, 1, 1`; the fibre
over `u` is unramified at `p ∉ T(u)` (the valuation case analysis is proved,
`GlueRepo.PR.inertia_orders_eq_one_iff`; Lemma NV step 2 is proved,
`LeafQM.AV.residue_unramified_over_branch`). **Pinning caveat** (fibre-cover §3): as stated it
quantifies over every `(Y, π)` satisfying R1fp, R2fp for some `Φ`; these clauses constrain
`(Y, π)` only through field points, so the genuine proof applies only once `(Y, π)` is pinned
(task qm-pin). Relabelings of `Φ` alone do not matter (`fibreCoverOut_indep`). -/
def FibreUnramified : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (y : fieldPt Qbar ⟶ Y), R1fpProps Y Φ → R2fpProps Y Φ π →
    u ∉ contactSet → Φ Qbar y = M3.mk P →
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt (residueImage (X := Y.left) y.left) p

/-- **`FibreCoverExists` from the degree bound, Prop. TS + Lemma NV on `ℚ(y)`, and the textbook
fact on Galois closures** (the rational fibre itself is proved from R1fp, `rationalFibre_of_le`). -/
theorem fibreCoverExists_of (hD : FibreDegree) (hR : FibreUnramified)
    (hU : UnramifiedConjugates) : FibreCoverExists := by
  intro Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩
  rw [fibreCoverOut_iff h1 hy u]
  obtain ⟨hfd, hd⟩ := hD Y Φ π u P y h1 h2 hu hy hπ
  exact fibreFieldOut_of hU _ hd u (hR Y Φ π u P y h1 h2 hu hy hπ)

/-! ## Part 4: `FibreDegree` from the intrinsic count `TwistClassCard` -/

/-- **Glue (Glazer N5 L425-441, the degree bound `≤ 4·|(𝒪/3𝒪)^×| ≤ 324`): the `Aut 𝒪`-twist
class of a level-3 object over `ℚ̄` has at most `324` isomorphism classes.** For `P = (A, ι, η)`
over `ℚ̄`, the classes `[Q]` whose QM pair is an `Aut 𝒪`-twist of `(A, ι)` number at most
`4·|(𝒪/3𝒪)^×|`: `Aut 𝒪` modulo inner automorphisms (which give isomorphic pairs) has order 4
(the Atkin–Lehner group `W`), and on a fixed pair the level structures `η : 𝒪 → A[3]` are
determined by `η(1)`, a free generator of the `𝒪/3𝒪`-module `A[3] ≅ 𝒪/3𝒪` (`|A[3]| = 3⁴`,
Mumford §4, UNVERIFIED locator), so there are `|(𝒪/3𝒪)^×| = |GL₂(𝔽₃)| = 48 ≤ 81` of them.
Intrinsic: it mentions no moduli scheme. -/
def TwistClassCard : Prop :=
  ∀ P : QML3 Qbar, ∃ s : Finset (M3 Qbar), s.card ≤ 324 ∧
    ∀ Q : QML3 Qbar, (∃ α : LeafQM.O ≃+* LeafQM.O, Nonempty (QMIso (P.q.twist α) Q.q)) → M3.mk Q ∈ s

/-- Every finite subextension `K ⊆ F` has degree at most the number of embeddings `F → ℚ̄`. -/
theorem finrank_le_of_card_algHom_le (F : IF) (n : ℕ)
    (h : ∀ t : Finset (F →ₐ[ℚ] Qbar), t.card ≤ n) (K : IntermediateField ℚ F)
    [FiniteDimensional ℚ K] : Module.finrank ℚ K ≤ n := by
  classical
  have hext : ∀ e : K →ₐ[ℚ] Qbar, ∃ e' : F →ₐ[ℚ] Qbar, e'.domRestrict K = e := fun e =>
    IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := K) (M := Qbar) (E := F) e
  choose ext hext using hext
  have hinj : Function.Injective ext := fun e₁ e₂ h12 => by
    rw [← hext e₁, ← hext e₂, h12]
  calc Module.finrank ℚ K = Fintype.card (K →ₐ[ℚ] Qbar) := (AlgHom.card ℚ K Qbar).symm
    _ = (Finset.univ.image ext).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ ≤ n := h _

/-- **A subfield of `ℚ̄` with at most `n` embeddings into `ℚ̄` is finite of degree `≤ n`.** -/
theorem finiteDimensional_of_card_algHom_le (F : IF) (n : ℕ)
    (h : ∀ t : Finset (F →ₐ[ℚ] Qbar), t.card ≤ n) :
    ∃ _ : FiniteDimensional ℚ F, Module.finrank ℚ F ≤ n := by
  classical
  let Pm : ℕ → Prop := fun m => ∃ K : IntermediateField ℚ F,
    FiniteDimensional ℚ K ∧ Module.finrank ℚ K = m
  have h1 : Pm 1 := ⟨⊥, inferInstance, IntermediateField.finrank_bot⟩
  have hn : 1 ≤ n := by
    have := finrank_le_of_card_algHom_le F n h (⊥ : IntermediateField ℚ F)
    rwa [IntermediateField.finrank_bot] at this
  obtain ⟨K₀, hK₀, hK₀r⟩ := Nat.findGreatest_spec hn h1
  have htop : K₀ = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    let K₁ : IntermediateField ℚ F := K₀ ⊔ IntermediateField.adjoin ℚ {x}
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : FiniteDimensional ℚ K₁ := IntermediateField.finiteDimensional_sup _ _
    have hle : K₀ ≤ K₁ := le_sup_left
    have hr : Module.finrank ℚ K₁ ≤ Module.finrank ℚ K₀ := by
      rw [hK₀r]
      exact Nat.le_findGreatest (finrank_le_of_card_algHom_le F n h K₁) ⟨K₁, inferInstance, rfl⟩
    have heq : K₀ = K₁ := IntermediateField.eq_of_le_of_finrank_le hle hr
    rw [heq]
    exact le_sup_right (a := K₀) (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : (⊤ : IntermediateField ℚ F) ≃ₗ[ℚ] F := IntermediateField.topEquiv.toLinearEquiv
  have : FiniteDimensional ℚ (⊤ : IntermediateField ℚ F) := htop ▸ hK₀
  have : FiniteDimensional ℚ F := e.finiteDimensional
  refine ⟨inferInstance, ?_⟩
  rw [← e.finrank_eq]
  have := finrank_le_of_card_algHom_le F n h (⊤ : IntermediateField ℚ F)
  exact this

/-- **`FibreDegree` from `TwistClassCard`** (no pinning needed): the embeddings `e` of
`F = ℚ(y)` give points `e ∘ y_F` over `J(u)`, pairwise distinct (`F` is generated by the image
of the residue field), whose classes lie in the twist class of `P` (R2fp). -/
theorem fibreDegree_of (hC : TwistClassCard) : FibreDegree := by
  classical
  intro Y Φ π u P y h1 h2 hu hy hπ
  obtain ⟨⟨x, emb⟩, hp⟩ : ∃ q, Scheme.SpecToEquivOfField Qbar Y.left y.left = q := ⟨_, rfl⟩
  have hF : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range emb) := by
    unfold residueImage; rw [hp]
  rw [hF]
  set F : IF := IntermediateField.adjoin ℚ (Set.range emb) with hFdef
  have hmem : ∀ a, emb a ∈ F := fun a => IntermediateField.subset_adjoin ℚ _ ⟨a, rfl⟩
  let emb' : Y.left.residueField x ⟶ CommRingCat.of F :=
    CommRingCat.ofHom (emb.hom.codRestrict F hmem)
  let zF : Spec (CommRingCat.of F) ⟶ Y.left := (Scheme.SpecToEquivOfField F Y.left).symm ⟨x, emb'⟩
  have hz : ∀ e : F →ₐ[ℚ] Qbar, Scheme.SpecToEquivOfField Qbar Y.left
      (Spec.map (CommRingCat.ofHom (e : F →+* Qbar)) ≫ zF) = ⟨x, emb' ≫ CommRingCat.ofHom e⟩ := by
    intro e
    rw [specToEquivOfField_comp, Equiv.apply_symm_apply]
  have hzy : Spec.map (CommRingCat.ofHom ((F.val : F →ₐ[ℚ] Qbar) : F →+* Qbar)) ≫ zF = y.left := by
    apply (Scheme.SpecToEquivOfField Qbar Y.left).injective
    rw [hz, hp]
    rfl
  let yF : fieldPt F ⟶ Y := Over.homMk zF (spec_to_specQ_eq _ _)
  obtain ⟨s, hs, hsP⟩ := hC P
  apply finiteDimensional_of_card_algHom_le F 324
  intro t
  -- the value of `π` at the points `e ∘ y_F`
  have hy' : (π.val (K := F) zF).map (F.val : F →+* Qbar) =
      OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) := by
    rw [← π.val_comp (F.val : F →+* Qbar) zF, hzy]
    exact hπ
  have hval : ∀ e : F →ₐ[ℚ] Qbar, π.val (K := Qbar)
      (Spec.map (CommRingCat.ofHom (e : F →+* Qbar)) ≫ zF) =
      OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) := by
    intro e
    rw [π.val_comp]
    revert hy'
    induction π.val (K := F) zF using OnePoint.rec with
    | infty => intro h; simp at h
    | coe z =>
      intro h
      simp only [OnePoint.map_some] at h ⊢
      have hz' : z = algebraMap ℚ F (ZInQ.JHeight.Jmap u) := by
        apply (F.val : F →+* Qbar).injective
        have h' := OnePoint.coe_injective h
        rw [h']
        exact (F.val.commutes _).symm
      rw [hz']
      exact congrArg _ (e.commutes _)
  let g : (F →ₐ[ℚ] Qbar) → M3 Qbar := fun e => Φ Qbar (fieldMap e ≫ yF)
  have hmaps : ∀ e ∈ t, g e ∈ s := by
    intro e _
    have hQ : Φ Qbar (fieldMap e ≫ yF) = M3.mk (Quotient.out (Φ Qbar (fieldMap e ≫ yF))) :=
      (Quotient.out_eq _).symm
    have := ((h2 y _ P _ hy hQ).1).1 (hπ.trans (hval e).symm)
    show Φ Qbar (fieldMap e ≫ yF) ∈ s
    rw [hQ]
    exact hsP _ this
  have hinj : Set.InjOn g t := by
    intro e₁ _ e₂ _ h12
    have hpt : fieldMap e₁ ≫ yF = fieldMap e₂ ≫ yF := (Φ Qbar).injective h12
    have hl : Spec.map (CommRingCat.ofHom (e₁ : F →+* Qbar)) ≫ zF =
        Spec.map (CommRingCat.ofHom (e₂ : F →+* Qbar)) ≫ zF :=
      congrArg (fun z : fieldPt Qbar ⟶ Y => z.left) hpt
    have hl' := congrArg (Scheme.SpecToEquivOfField Qbar Y.left) hl
    rw [hz, hz] at hl'
    have hemb := eq_of_heq (Sigma.mk.inj_iff.mp hl').2
    apply IntermediateField.algHom_ext_of_eq_adjoin (hS := hFdef)
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun φ : Y.left.residueField x ⟶ CommRingCat.of Qbar => φ a) hemb
  calc t.card ≤ s.card := Finset.card_le_card_of_injOn g hmaps hinj
    _ ≤ 324 := hs

/-- **`FibreCoverExists` from the intrinsic count, Prop. TS + Lemma NV on `ℚ(y)`, and the textbook
fact on Galois closures.** -/
theorem fibreCoverExists_of_twistClassCard (hC : TwistClassCard) (hR : FibreUnramified)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of (fibreDegree_of hC) hR hU

/-! ## Part 5: what the ramification step needs from a pinning (only `(Y, π)` up to isomorphism) -/

/-- The residue field can only shrink along a morphism (scheme form). -/
theorem residueImage_comp_le_self_aux {X X' : Scheme.{0}} (h : X ⟶ X')
    (z : Spec (CommRingCat.of Qbar) ⟶ X) :
    residueImage (X := X') (z ≫ h) ≤ residueImage (X := X) z := by
  unfold residueImage
  rw [specToEquivOfField_comp_right]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _ ⟨_, rfl⟩

/-- The residue field can only shrink along a morphism: `ℚ(h ∘ y) ⊆ ℚ(y)`. -/
theorem residueImage_comp_le_self {Y Y' : Over (Spec (CommRingCat.of ℚ))} (h : Y ⟶ Y')
    (y : fieldPt Qbar ⟶ Y) :
    residueImage (X := Y'.left) (y ≫ h).left ≤ residueImage (X := Y.left) y.left :=
  residueImage_comp_le_self_aux h.left y.left

/-- Along an isomorphism the residue field is unchanged. -/
theorem residueImage_comp_iso {Y Y' : Over (Spec (CommRingCat.of ℚ))} (g : Y ≅ Y')
    (y : fieldPt Qbar ⟶ Y) :
    residueImage (X := Y'.left) (y ≫ g.hom).left = residueImage (X := Y.left) y.left := by
  apply le_antisymm (residueImage_comp_le_self g.hom y)
  have := residueImage_comp_le_self g.inv (y ≫ g.hom)
  rwa [Category.assoc, g.hom_inv_id, Category.comp_id] at this

/-- **Prop. TS + Lemma NV for one curve with one map to `P¹`** (the genuine `(Y₃, π)`): the
residue field of every `ℚ̄`-point over `J(u)`, `u ∉ 𝒞`, is unramified outside `T(u)`. This
mentions no moduli bijection. -/
def FibreUnramifiedOn (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (u : ℚ) (y : fieldPt Qbar ⟶ Y₀), u ∉ contactSet →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **The pin that `FibreUnramified` needs** (to be supplied by task qm-pin's repair): every
`(Y, π)` admitting a moduli bijection `Φ` with R1fp and R2fp is isomorphic to `(Y₀, π₀)` over
`P¹` on `ℚ̄`-points. `Φ` itself need not be pinned (`fibreCoverOut_indep`). -/
def CurvePinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∃ g : Y ≅ Y₀, ∀ y : fieldPt Qbar ⟶ Y,
      π.val (K := Qbar) y.left = π₀.val (K := Qbar) (y ≫ g.hom).left

/-- **`FibreUnramified` from Prop. TS on one curve and the pin of `(Y, π)`.** -/
theorem fibreUnramified_of_pinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀) : FibreUnramified := by
  intro Y Φ π u P y h1 h2 hu _ hπ p hp
  obtain ⟨g, hg⟩ := hpin Y Φ π h1 h2
  rw [← residueImage_comp_iso g y]
  exact h0 u (y ≫ g.hom) hu ((hg y).symm.trans hπ) p hp

/-- **The composite, corrected form**: `FibreCoverExists` from the intrinsic count, Prop. TS +
Lemma NV on the genuine `(Y₀, π₀)`, the pin of `(Y, π)`, and the textbook fact. -/
theorem fibreCoverExists_of_pinned (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hC : TwistClassCard) (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀)
    (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_twistClassCard hC (fibreUnramified_of_pinned Y₀ π₀ hpin h0) hU

/-! ## Part 6: `TwistClassCard` from 3-torsion and the Atkin–Lehner count -/

/-- **Glue + textbook leaf (`|A[3]| = 3⁴` for an abelian surface; Mumford §4, the kernel's leaf
`PkgI2.TorsionStructure`, which is stated for `A(K̄)[n]`, `K̄ = AlgebraicClosure K`): the
`3`-torsion of `A(ℚ̄)` has at most `81` points.** From `TorsionStructure` at `K = ℚ̄` and the
injection `A(ℚ̄) → A(AlgebraicClosure ℚ̄)` (glue, not compiled here). -/
def TorsionBound3 : Prop :=
  ∀ A : PkgI3.AbVar Qbar, A.dim = 2 → ∃ s : Finset (Additive (A.Pt Qbar)), s.card ≤ 81 ∧
    ∀ x : Additive (A.Pt Qbar), 3 • x = 0 → x ∈ s

/-- **Glue (computation on N5's maximal order `𝒪` of discriminant 6): `Aut 𝒪` modulo inner
automorphisms by units has at most 4 elements.** Every `α ∈ Aut 𝒪` is `w ∘ Ad u` with `w` in a
fixed set of `≤ 4` automorphisms and `u ∈ 𝒪^×`. Reason: `Aut 𝒪 = N_B(𝒪)/ℚ^×` (Skolem–Noether,
T13, proved) and `N_B(𝒪)/ℚ^×𝒪^× ≅ (ℤ/2)²`, the Atkin–Lehner group `W` of the two ramified primes
(Vignéras, *Arithmétique des algèbres de quaternions*, Ch. II §1 / Ch. III §5, UNVERIFIED
locator; N5 L425-429: "at each of the two division primes its quotient … has order two"). -/
def InnerTwistCount : Prop :=
  ∃ W : Finset (LeafQM.O ≃+* LeafQM.O), W.card ≤ 4 ∧
    ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ w ∈ W, ∃ u : (LeafQM.O)ˣ,
      ∀ a : LeafQM.O, α a = w (u * a * ↑u⁻¹)

section TwistCount

variable {K : Type} [Field K]

/-- A level structure is determined by `η(1)`: `η(a) = a·η(1)`. -/
theorem level3_eta_eq {A : PkgI3.AbVar K} {q : QMStr A} (e : Level3 q) (a : LeafQM.O) :
    e.eta a = qmAct q K a (e.eta 1) := by
  rw [← e.linear, _root_.mul_one]

theorem level3_ext {A : PkgI3.AbVar K} {q : QMStr A} (e e' : Level3 q)
    (h : e.eta 1 = e'.eta 1) : e = e' := by
  have heta : e.eta = e'.eta :=
    AddMonoidHom.ext fun a => by rw [level3_eta_eq e a, level3_eta_eq e' a, h]
  cases e; cases e'
  cases heta
  rfl

/-- `η(1)` is a `3`-torsion point. -/
theorem level3_three {A : PkgI3.AbVar K} {q : QMStr A} (e : Level3 q) : 3 • e.eta 1 = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, _root_.mul_one]
  exact (e.ker _).mpr ⟨1, by rw [_root_.mul_one]; rfl⟩

/-- The inner twist `ι ∘ w ∘ Ad u` is isomorphic to `ι ∘ w`, by `ι(w(u))^{-1}`. -/
noncomputable def innerIso {A : PkgI3.AbVar K} (q : QMStr A) (w : LeafQM.O ≃+* LeafQM.O) (u : (LeafQM.O)ˣ)
    (α : LeafQM.O ≃+* LeafQM.O) (hα : ∀ a, α a = w (u * a * ↑u⁻¹)) :
    QMIso (q.twist α) (q.twist w) where
  φ := q.iota (w ↑u⁻¹)
  ψ := q.iota (w ↑u)
  left := by
    show (q.iota (w ↑u) * q.iota (w ↑u⁻¹)).hom = (1 : PkgI3.AbVar.End A).hom
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  right := by
    show (q.iota (w ↑u⁻¹) * q.iota (w ↑u)).hom = (1 : PkgI3.AbVar.End A).hom
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  equivariant a := by
    show (q.iota (w ↑u⁻¹) * q.iota (α a)).hom = (q.iota (w a) * q.iota (w ↑u⁻¹)).hom
    rw [hα, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← _root_.mul_assoc, ← _root_.mul_assoc,
      Units.inv_mul, _root_.one_mul]

/-- Transport of a level structure along a QM isomorphism. -/
noncomputable def transportLevel {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (θ : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (PkgI3.AbVar.ptMap (L := K) θ.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ θ.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ θ.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ θ.φ.hom) = _
    rw [Category.assoc, θ.equivariant a, Category.assoc]
  ker a := by
    have hinv : Function.LeftInverse (PkgI3.AbVar.ptMap (L := K) θ.ψ).toAdditive
        (PkgI3.AbVar.ptMap (L := K) θ.φ).toAdditive := fun x => by
      change Additive.ofMul ((Additive.toMul x ≫ θ.φ.hom) ≫ θ.ψ.hom) = x
      rw [Category.assoc, θ.left, Category.comp_id]; rfl
    rw [AddMonoidHom.comp_apply, map_eq_zero_iff _ hinv.injective, e.ker]

/-- The transported object is isomorphic to the original. -/
noncomputable def transportIso (Q : QML3 K) {A' : PkgI3.AbVar K} (hs : A'.dim = 2) {q' : QMStr A'}
    (θ : QMIso Q.q q') : Q.Iso ⟨A', hs, q', transportLevel θ Q.e⟩ where
  φ := θ.φ
  ψ := θ.ψ
  left := θ.left
  right := θ.right
  equivariant := θ.equivariant
  level _ := rfl

end TwistCount

/-- **`TwistClassCard` from the 3-torsion bound and the Atkin–Lehner count** (Glazer's
`4·81 = 324`): a class in the twist class of `P` is `[(A, ι∘w, η')]` for `w ∈ W` and a level
structure `η'`, which is determined by the `3`-torsion point `η'(1)`. -/
theorem twistClassCard_of (hT : TorsionBound3) (hW : InnerTwistCount) : TwistClassCard := by
  classical
  intro P
  obtain ⟨s3, hs3, hs3P⟩ := hT P.A P.surface
  obtain ⟨W, hWc, hWα⟩ := hW
  let F : (LeafQM.O ≃+* LeafQM.O) × Additive (P.A.Pt Qbar) → M3 Qbar := fun wx =>
    if h : ∃ e : Level3 (P.q.twist wx.1), e.eta 1 = wx.2 then
      M3.mk ⟨P.A, P.surface, P.q.twist wx.1, h.choose⟩ else M3.mk P
  refine ⟨(W ×ˢ s3).image F, ?_, ?_⟩
  · calc ((W ×ˢ s3).image F).card ≤ (W ×ˢ s3).card := Finset.card_image_le
      _ = W.card * s3.card := Finset.card_product _ _
      _ ≤ 4 * 81 := Nat.mul_le_mul hWc hs3
      _ = 324 := by norm_num
  · rintro Q ⟨α, ⟨f⟩⟩
    obtain ⟨w, hw, u, hu⟩ := hWα α
    let θ : QMIso Q.q (P.q.twist w) := f.symm.trans (innerIso P.q w u α hu)
    let e' := transportLevel θ Q.e
    have hx : e'.eta 1 ∈ s3 := hs3P _ (level3_three e')
    have hex : ∃ e : Level3 (P.q.twist w), e.eta 1 = e'.eta 1 := ⟨e', rfl⟩
    have hF : F (w, e'.eta 1) = M3.mk Q := by
      dsimp only [F]
      rw [dite_eq_left hex, level3_ext _ _ hex.choose_spec]
      exact (Quotient.sound (⟨transportIso Q P.surface θ⟩ : Nonempty _)).symm
    rw [← hF]
    exact Finset.mem_image_of_mem F (Finset.mem_product.mpr ⟨hw, hx⟩)

/-- **The composite with the twist count reduced**: `FibreCoverExists` from the 3-torsion
bound, the Atkin–Lehner count, the pin, Prop. TS + Lemma NV on one curve, and the textbook fact. -/
theorem fibreCoverExists_of_pinned' (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (hT : TorsionBound3) (hW : InnerTwistCount) (hpin : CurvePinned Y₀ π₀)
    (h0 : FibreUnramifiedOn Y₀ π₀) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_pinned Y₀ π₀ (twistClassCard_of hT hW) hpin h0 hU

/-! ## Part 7: `TorsionBound3` from the kernel's leaf `TorsionStructure` -/

/-- Precomposition with `Spec L → Spec K` (a field extension) is injective on `K`-points. -/
theorem spec_comp_injective {X : Scheme.{0}} {K L : Type} [Field K] [Field L] (i : K →+* L)
    (z z' : Spec (CommRingCat.of K) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ z = Spec.map (CommRingCat.ofHom i) ≫ z') : z = z' := by
  have h' := congrArg (Scheme.SpecToEquivOfField L X) h
  rw [specToEquivOfField_comp, specToEquivOfField_comp] at h'
  obtain ⟨⟨p1, f1⟩, hp1⟩ : ∃ q, Scheme.SpecToEquivOfField K X z = q := ⟨_, rfl⟩
  obtain ⟨⟨p2, f2⟩, hp2⟩ : ∃ q, Scheme.SpecToEquivOfField K X z' = q := ⟨_, rfl⟩
  rw [hp1, hp2] at h'
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h'
  have hf : f1 = f2 := by
    ext a
    apply i.injective
    exact congrArg (fun φ : X.residueField p1 ⟶ CommRingCat.of L => φ a) (eq_of_heq hh)
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [hp1, hp2, hf]

/-- `Spec(AlgebraicClosure ℚ̄) → Spec ℚ̄` over `ℚ̄`. -/
noncomputable def specIncl :
    PkgI2.specOver Qbar (AlgebraicClosure Qbar) ⟶ PkgI3.AbVar.ptObj (K := Qbar) Qbar :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar)))) (by
    simp only [PkgI2.specOver, PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id])

/-- **`TorsionBound3` from the textbook leaf `TorsionStructure`** (`A(K̄)[3] ≅ (ℤ/3)⁴` at
`K = ℚ̄`, `K̄ = AlgebraicClosure ℚ̄`): `A(ℚ̄)[3]` injects into `A(K̄)[3]`, which has `81` points. -/
theorem torsionBound3_of (hT : ObjBridge.TorsionStructure) : TorsionBound3 := by
  classical
  intro A hA
  obtain ⟨e, -⟩ := hT Qbar (ObjBridge.toGrp A) 2 3 (by rw [Nat.cast_ofNat]; exact hA)
    (by norm_num) (by norm_num)
  set Tset := PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure Qbar) 3 with hTset
  have : Finite Tset := Finite.of_equiv _ e.symm
  have hTfin : Tset.Finite := Set.toFinite Tset
  have hcard : hTfin.toFinset.card = 81 := by
    rw [← Set.ncard_eq_toFinset_card Tset hTfin, ← Nat.card_coe_set_eq, Nat.card_congr e,
      Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  let incl : Additive (A.Pt Qbar) → PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure Qbar) :=
    fun x => specIncl ≫ Additive.toMul x
  have hinj : Function.Injective incl := by
    intro x y hxy
    have hl : Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) ≫
        (Additive.toMul x).left =
        Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) ≫
        (Additive.toMul y).left :=
      congrArg (fun f => f.left) hxy
    exact Additive.toMul.injective (Over.OverMorphism.ext (spec_comp_injective _ _ _ hl))
  have htors : ∀ x : Additive (A.Pt Qbar), 3 • x = 0 → incl x ∈ Tset := by
    intro x hx
    show (specIncl ≫ Additive.toMul x) ^ 3 = 1
    have h3 : Additive.toMul x ^ 3 = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    have hpow : ∀ n : ℕ, specIncl ≫ Additive.toMul x ^ n = (specIncl ≫ Additive.toMul x) ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
      | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
    rw [← hpow, h3, MonObj.comp_one]
  have hsfin : {x : Additive (A.Pt Qbar) | 3 • x = 0}.Finite :=
    Set.Finite.of_finite_image (hTfin.subset (by rintro _ ⟨x, hx, rfl⟩; exact htors x hx))
      hinj.injOn
  refine ⟨hsfin.toFinset, ?_, fun x hx => hsfin.mem_toFinset.mpr hx⟩
  rw [← hcard]
  exact Finset.card_le_card_of_injOn incl
    (fun x hx => hTfin.mem_toFinset.mpr (htors x (hsfin.mem_toFinset.mp hx))) hinj.injOn

/-- **The composite with the torsion count from the kernel's leaf.** -/
theorem fibreCoverExists_of_leafTorsion (Y₀ : Over (Spec (CommRingCat.of ℚ)))
    (π₀ : ToP1 Y₀.left) (hT : ObjBridge.TorsionStructure) (hW : InnerTwistCount)
    (hpin : CurvePinned Y₀ π₀) (h0 : FibreUnramifiedOn Y₀ π₀) (hU : UnramifiedConjugates) :
    FibreCoverExists :=
  fibreCoverExists_of_pinned' Y₀ π₀ (torsionBound3_of hT) hW hpin h0 hU

/-- The same with the leaf exactly as it appears in the bundle (`TextbookLeaves.t5 :
PkgI2.TorsionStructure.{0}`, scratch/h-decomposition/Leaves.lean). -/
theorem torsionBound3_of_t5 (t5 : PkgI2.TorsionStructure.{0}) : TorsionBound3 :=
  torsionBound3_of (ObjBridge.torsionStructure_iff.mpr t5)

/-! ## Part 8: Prop. TS in Beckmann's inertia form; the valuation analysis is the repository's -/

/-- **Glue from leaves: Prop. TS (specialization inertia) on one cover `π₀ : Y₀ → P¹`**
(N5 L484-525; Beckmann, *On extensions of number fields obtained by specializing branched
coverings*, J. reine angew. Math. 419 (1991), Prop. 4.2, UNVERIFIED number; or T1-T2 with the
integral model R1(d)). For a rational non-branch value `t` and a prime `p > 324` (so
`p ∤ |G|`, `p ∤ 30`: good reduction, and the branch points `0, ∞, −16/27` stay distinct mod `p`),
the residue field of a `ℚ̄`-point over `t` is unramified at `p` once the three Beckmann inertia
orders `e_b / gcd(e_b, m_b)` are `1`: `e = 4, 6, 2` at `0, ∞, −16/27` (the indices of
`Y₃ → P¹`, `RvNocm.ramification_eq_orbifold_order`), `m_b` the intersection multiplicities
`v_p(t)⁺`, `(−v_p(t))⁺`, `v_p(t + 16/27)⁺`. -/
def PropTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left) : Prop :=
  ∀ (t : ℚ) (y : fieldPt Qbar ⟶ Y₀), t ≠ 0 → t ≠ -16 / 27 →
    π₀.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar t) →
    ∀ p : Nat.Primes, 324 < (p : ℕ) →
      4 ∣ (padicValRat p t).toNat → 6 ∣ (-padicValRat p t).toNat →
      2 ∣ (padicValRat p (t + 16 / 27)).toNat →
      UnramifiedAt (residueImage (X := Y₀.left) y.left) p

/-- **`FibreUnramifiedOn` from Prop. TS**: for `p ∉ T(u)` (so `p > 324` and `p ∤ M_S(u)`), the
three inertia orders at `t = J(u)` are `1` (`GlueRepo.PR.inertia_trivial_iff_not_dvd`, the
repository's valuation case analysis), and `J(u) ≠ 0, −16/27` for `u ∉ 𝒞`. -/
theorem fibreUnramifiedOn_of_propTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (h : PropTS Y₀ π₀) : FibreUnramifiedOn Y₀ π₀ := by
  intro u y hu hπ p hp
  have hp' : (p : ℕ) ∉ Mult.S_mul ∪ (contactSupport Mult.S_mul u).primeFactors := hp
  have hS : ∀ q, q.Prime → q ≤ 324 → q ∈ Mult.S_mul := fun q hq hq' =>
    Mult.mem_S_mul.mpr (Or.inl (Mult.mem_S_ht.mpr ⟨hq, hq'⟩))
  have hpS : (p : ℕ) ∉ Mult.S_mul := fun h' => hp' (Finset.mem_union_left _ h')
  have hp324 : 324 < (p : ℕ) := by
    by_contra h'
    exact hpS (hS _ p.2 (by omega))
  have hndvd : ¬ (p : ℕ) ∣ contactSupport Mult.S_mul u := fun hd =>
    hp' (Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨p.2, hd, (GlueDescent.contactSupport_pos _ _).ne'⟩))
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨h4, h6, h2⟩ :=
    (GlueRepo.PR.inertia_trivial_iff_not_dvd (p := p) Mult.S_mul hS hpS hu).mpr hndvd
  exact h (ZInQ.JHeight.Jmap u) y (GlueRepo.PR.J_ne_zero hu) (GlueRepo.PR.J_ne_branch u) hπ p
    hp324 h4 h6 h2

/-- **The composite on the leaves of the bundle**: `FibreCoverExists` from T5
(`TorsionStructure`), `InnerTwistCount`, the pin `CurvePinned Y₀ π₀`, Prop. TS on `(Y₀, π₀)`, and
`UnramifiedConjugates`. -/
theorem fibreCoverExists_of_propTS (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (t5 : PkgI2.TorsionStructure.{0}) (hW : InnerTwistCount) (hpin : CurvePinned Y₀ π₀)
    (hTS : PropTS Y₀ π₀) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_pinned' Y₀ π₀ (torsionBound3_of_t5 t5) hW hpin
    (fibreUnramifiedOn_of_propTS Y₀ π₀ hTS) hU

/-- **Prop. TS for every admissible cover** (the pin-free alternative to `CurvePinned`): every
`(Y, π)` admitting a moduli bijection with R1fp and R2fp satisfies Prop. TS. SPECULATIVE truth
argument (fibre-cover §3.2): R2fp makes every rational fibre of `π` isomorphic, as a Galois set
with residue fields, to a fibre of the genuine `π₀`, a `G`-torsor; by Hilbert irreducibility the
arithmetic monodromy of `π` then acts regularly, so `π` is Galois of degree `|G|` with the same
branch values and indices `4, 6, 2`, and Beckmann's theorem applies with the same inertia orders. -/
def PropTSAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → PropTS Y π

theorem fibreUnramified_of_propTSAll (h : PropTSAll) : FibreUnramified :=
  fun Y Φ π u _ y h1 h2 hu _ hπ => fibreUnramifiedOn_of_propTS Y π (h Y Φ π h1 h2) u y hu hπ

/-- **The pin-free composite**: `FibreCoverExists` from T5, `InnerTwistCount`, `PropTSAll` and
`UnramifiedConjugates`. -/
theorem fibreCoverExists_of_propTSAll (t5 : PkgI2.TorsionStructure.{0}) (hW : InnerTwistCount)
    (hTS : PropTSAll) (hU : UnramifiedConjugates) : FibreCoverExists :=
  fibreCoverExists_of_twistClassCard (twistClassCard_of (torsionBound3_of_t5 t5) hW)
    (fibreUnramified_of_propTSAll hTS) hU


/-! ## §2 (task inner-twist) -/

open NumberField

/-- `Ad v ∘ t = t ∘ Ad (t⁻¹ v)`: the form `α = Ad v ∘ t` of `autO_mod_inner_exact` gives the form
`α = t ∘ Ad u` of `InnerTwistCount`, with `u = t⁻¹(v)`. -/
theorem ad_comp_eq_comp_ad (t : LeafQM.O ≃+* LeafQM.O) (v : (LeafQM.O)ˣ) (a : LeafQM.O) :
    (v : LeafQM.O) * t a * ((v⁻¹ : (LeafQM.O)ˣ) : LeafQM.O) =
      t ((Units.map t.symm.toRingHom.toMonoidHom v : (LeafQM.O)ˣ) * a *
        ↑(Units.map t.symm.toRingHom.toMonoidHom v)⁻¹) := by
  simp [Units.coe_map, Units.coe_map_inv, map_mul]

/-- **`InnerTwistCount`, proved** (no leaf, no glue Prop): `W = {Ad 1, Ad i, Ad j, Ad ij}`. -/
theorem innerTwistCount : InnerTwistCount := by
  classical
  obtain ⟨t, hcov, -⟩ := LeafQM.AV.Pin.Exact.autO_mod_inner_exact
  refine ⟨Finset.univ.image t, Finset.card_image_le.trans (by simp), fun α => ?_⟩
  obtain ⟨k, v, hv⟩ := hcov α
  exact ⟨t k, Finset.mem_image_of_mem _ (Finset.mem_univ _), _,
    fun a => (hv a).trans (ad_comp_eq_comp_ad (t k) v a)⟩

/-- **Sharpness**: the bound `4` of `InnerTwistCount` cannot be lowered. Every `W` with the
covering property has at least four elements, because `Aut(𝒪)/Inn(𝒪^×)` has exactly four
classes (`Exact.autO_mod_inner_exact`). -/
theorem innerTwistCount_sharp (W : Finset (LeafQM.O ≃+* LeafQM.O))
    (hW : ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ w ∈ W, ∃ u : (LeafQM.O)ˣ,
      ∀ a : LeafQM.O, α a = w (u * a * ↑u⁻¹)) : 4 ≤ W.card := by
  classical
  obtain ⟨t, -, hdist⟩ := LeafQM.AV.Pin.Exact.autO_mod_inner_exact
  choose w hwW u hu using fun k => hW (t k)
  -- `t k = w k ∘ Ad (u k) = Ad (w k (u k)) ∘ w k`
  have hform : ∀ k a, t k a = ((Units.map (w k).toRingHom.toMonoidHom (u k) : (LeafQM.O)ˣ) :
      LeafQM.O) * w k a * ↑(Units.map (w k).toRingHom.toMonoidHom (u k))⁻¹ := by
    intro k a
    rw [hu k a]
    simp [Units.coe_map, Units.coe_map_inv, map_mul]
  have hinj : Function.Injective w := by
    intro k l hkl
    apply hdist k l
    refine ⟨Units.map (w k).toRingHom.toMonoidHom (u k) *
      (Units.map (w l).toRingHom.toMonoidHom (u l))⁻¹, fun a => ?_⟩
    rw [hform k a, hform l a, hkl]
    simp only [Units.val_mul, mul_inv_rev, inv_inv, _root_.mul_assoc, Units.inv_mul_cancel_left]
  calc 4 = (Finset.univ : Finset (Fin 4)).card := by simp
    _ = (Finset.univ.image w).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ W.card := Finset.card_le_card (fun x hx => by
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx; exact hwW k)

/-! ## The abstract step: inertia fixes an unramified subfield -/

section Abstract

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois ℚ L]

/-- **Inertia fixes the integers of an unramified subfield.** For number fields `K → L`, `L/ℚ`
Galois, `K` unramified at `p` (every prime of `𝓞 K` containing `p` has `e = 1` over `ℤ`), a prime
`Q ∋ p` of `𝓞 L` and `g ∈ I(Q) ≤ Gal(L/ℚ)`: `g` fixes the image of `𝓞 K`. -/
theorem inertia_le_fixing (p : ℕ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → ((p : ℤ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 L) ∈ Q) (g : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) (y : 𝓞 K) :
    g • algebraMap (𝓞 K) (𝓞 L) y = algebraMap (𝓞 K) (𝓞 L) y := by
  let G := L ≃ₐ[ℚ] L
  let H : Subgroup G := fixingSubgroup G (Set.range (algebraMap (𝓞 K) (𝓞 L)))
  have : IsGaloisGroup H (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isScalarTower G ℤ (𝓞 L) (𝓞 K)
  let QK : Ideal (𝓞 K) := Q.under (𝓞 K)
  have : QK.IsPrime := Ideal.IsPrime.under (𝓞 K) Q
  have : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) QK :=
    Algebra.HasSeparableResidueFieldsAt.tower_top (Q.under ℤ) QK
  have hpQK : ((p : ℤ) : 𝓞 K) ∈ QK := by
    show algebraMap (𝓞 K) (𝓞 L) ((p : ℤ) : 𝓞 K) ∈ Q
    rw [map_intCast]; exact hpQ
  have he1 : QK.ramificationIdx ℤ = 1 := hK QK inferInstance hpQK
  have htower : Q.ramificationIdx ℤ = QK.ramificationIdx ℤ * Q.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower (R := ℤ) QK Q
  have hcardH : Nat.card (Q.inertia H) = Q.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) QK Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx QK Q H]
  have hcardG : Nat.card (Q.inertia G) = Q.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.under ℤ) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q G]
  have hcard : Nat.card ((Q.inertia G).subgroupOf H) = Nat.card (Q.inertia G) := by
    rw [hcardG, htower, he1, _root_.one_mul, ← hcardH]; rfl
  have hle : Q.inertia G ≤ H := by
    have h1 : Nat.card ((Q.inertia G) ⊓ H : Subgroup G) = Nat.card (Q.inertia G) := by
      rw [← hcard, ← Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_map_of_injective H.subtype_injective
    have h2 : (Q.inertia G) ⊓ H = Q.inertia G :=
      Subgroup.eq_of_le_of_card_ge inf_le_left h1.ge
    exact inf_eq_left.mp h2
  exact (mem_fixingSubgroup_iff G).mp (hle hg) _ ⟨y, rfl⟩


/-- **Inertia fixes an unramified subfield** (`K = Frac(𝓞 K)`). -/
theorem inertia_fixes_field (p : ℕ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → ((p : ℤ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] (hpQ : ((p : ℤ) : 𝓞 L) ∈ Q) (g : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) (x : K) : g (algebraMap K L x) = algebraMap K L x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h : ∀ y : 𝓞 K, g (algebraMap K L (algebraMap (𝓞 K) K y)) =
      algebraMap K L (algebraMap (𝓞 K) K y) := fun y =>
    congrArg (fun z : 𝓞 L => (z : L)) (inertia_le_fixing p hK Q hpQ g hg y)
  rw [map_div₀, map_div₀, h a, h b]

omit [IsGalois ℚ L] in
/-- **Conjugation of inertia**: `σ⁻¹ I(Q) σ ⊆ I(σ⁻¹ Q)`, where `σ⁻¹ Q = {x | σ x ∈ Q}`. -/
theorem conj_mem_inertia (Q : Ideal (𝓞 L)) (g σ : L ≃ₐ[ℚ] L)
    (hg : g ∈ Q.inertia (L ≃ₐ[ℚ] L)) :
    σ⁻¹ * g * σ ∈ (Q.comap (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ)).inertia
      (L ≃ₐ[ℚ] L) := by
  rw [Ideal.mem_inertia] at hg ⊢
  intro x
  show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ ((σ⁻¹ * g * σ) • x - x) ∈ Q
  rw [map_sub]
  simp only [MulSemiringAction.toRingHom_apply, mul_smul, smul_inv_smul]
  exact hg (σ • x)

end Abstract

/-- A finite intermediate field of `ℚ̄/ℚ` is a number field. -/
theorem numberField_of_fd (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] :
    NumberField F :=
  { to_charZero := inferInstance, to_finiteDimensional := inferInstance }

/-- **`UnramifiedConjugates`, proved** (no leaf, no glue Prop). -/
theorem unramifiedConjugates : UnramifiedConjugates := by
  classical
  intro α p hK
  have hαint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hf0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hαint
  set K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {α} with hKdef
  set L : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ ((minpoly ℚ α).rootSet Qbar) with hLdef
  have hroot : ∀ β ∈ (minpoly ℚ α).rootSet Qbar, β ∈ L :=
    fun β hβ => IntermediateField.subset_adjoin _ _ hβ
  have hαroot : α ∈ (minpoly ℚ α).rootSet Qbar :=
    (Polynomial.mem_rootSet).2 ⟨hf0, minpoly.aeval ℚ α⟩
  have hαL : α ∈ L := hroot α hαroot
  have hKL : K ≤ L := IntermediateField.adjoin_simple_le_iff.2 hαL
  have : Polynomial.IsSplittingField ℚ L (minpoly ℚ α) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ L := Polynomial.IsSplittingField.finiteDimensional L (minpoly ℚ α)
  have : IsGalois ℚ L :=
    IsGalois.of_separable_splitting_field (minpoly.irreducible hαint).separable
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField K := numberField_of_fd K
  have : NumberField L := numberField_of_fd L
  let : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  intro Q hQ hpQ
  -- every element of the inertia group fixes every root of `minpoly α`
  have hfix : ∀ g ∈ Q.inertia (L ≃ₐ[ℚ] L), ∀ β (hβ : β ∈ (minpoly ℚ α).rootSet Qbar),
      g ⟨β, hroot β hβ⟩ = ⟨β, hroot β hβ⟩ := by
    intro g hg β hβ
    have hβ0 : Polynomial.aeval β (minpoly ℚ α) = 0 := ((Polynomial.mem_rootSet).1 hβ).2
    have hmin : minpoly ℚ (⟨β, hroot β hβ⟩ : L) = minpoly ℚ (⟨α, hαL⟩ : L) := by
      rw [← minpoly.algHom_eq L.val Subtype.val_injective (⟨β, hroot β hβ⟩ : L),
        ← minpoly.algHom_eq L.val Subtype.val_injective (⟨α, hαL⟩ : L)]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hαint) hβ0
        (minpoly.monic hαint)).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := L)).mp hmin
    -- `σ⁻¹ g σ` lies in the inertia group of `σ⁻¹ Q`, which contains `p`
    let Q' : Ideal (𝓞 L) := Q.comap (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ)
    have : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hpQ' : ((p : ℤ) : 𝓞 L) ∈ Q' := by
      show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ ((p : ℤ) : 𝓞 L) ∈ Q
      rw [map_intCast]; exact hpQ
    have h1 := inertia_fixes_field (K := K) (L := L) p hK Q' hpQ' (σ⁻¹ * g * σ)
      (conj_mem_inertia Q g σ hg) ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩
    have h2 : algebraMap K L ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α⟩ =
        (⟨α, hαL⟩ : L) := rfl
    rw [h2] at h1
    have h3 : (⟨β, hroot β hβ⟩ : L) = σ ⟨α, hαL⟩ := hσ.symm
    rw [h3]
    have h4 := congrArg σ h1
    simpa [AlgEquiv.mul_apply] using h4
  -- hence the inertia group is trivial
  have htriv : ∀ g ∈ Q.inertia (L ≃ₐ[ℚ] L), g = 1 := by
    intro g hg
    let s : Qbar ≃ₐ[ℚ] Qbar := g.liftNormal Qbar
    have hs : ∀ y : L, s (y : Qbar) = ((g y : L) : Qbar) :=
      fun y => AlgEquiv.liftNormal_commutes g Qbar y
    have hsroot : ∀ β ∈ (minpoly ℚ α).rootSet Qbar, s β = β := by
      intro β hβ
      have := hs ⟨β, hroot β hβ⟩
      rw [hfix g hg β hβ] at this
      exact this
    have hL' : L ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
      rw [hLdef, IntermediateField.adjoin_le_iff]
      intro β hβ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hsβ : s ∈ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) β :=
        MulAction.mem_stabilizer_iff.mpr (hsroot β hβ)
      exact MulAction.mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr hsβ) hf)
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have hy := hL' y.2 ⟨s, Subgroup.mem_zpowers s⟩
    rw [← hs]
    exact hy
  have hcard : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q (L ≃ₐ[ℚ] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (Q.under ℤ) Q, hcard]


/-! ## §2 composites with `InnerTwistCount` and `UnramifiedConjugates` discharged -/

/-- **`FibreCoverExists` from T5, the pin and Prop. TS** (the two Props of task inner-twist are
proved: `innerTwistCount`, `unramifiedConjugates`). -/
theorem fibreCoverExists_of_propTS' (Y₀ : Over (Spec (CommRingCat.of ℚ))) (π₀ : ToP1 Y₀.left)
    (t5 : PkgI2.TorsionStructure.{0}) (hpin : CurvePinned Y₀ π₀) (hTS : PropTS Y₀ π₀) :
    FibreCoverExists :=
  fibreCoverExists_of_propTS Y₀ π₀ t5 innerTwistCount hpin hTS unramifiedConjugates

/-- **The pin-free composite** with the two Props of task inner-twist discharged. -/
theorem fibreCoverExists_of_propTSAll' (t5 : PkgI2.TorsionStructure.{0}) (hTS : PropTSAll) :
    FibreCoverExists :=
  fibreCoverExists_of_propTSAll t5 innerTwistCount hTS unramifiedConjugates

end G0ModField

#print axioms G0ModField.innerTwistCount
#print axioms G0ModField.unramifiedConjugates
#print axioms G0ModField.fibreCoverExists_of_propTS'
#print axioms G0ModField.fibreCoverExists_of_propTSAll'
