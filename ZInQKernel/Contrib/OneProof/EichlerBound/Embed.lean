import ZInQKernel.Contrib.OneProof.EichlerBound.Defs

/-! eichler-bound, part B1: optimal embeddings `R ↪ 𝒪`, the intertwiner lattice `J(Ψ, Φ) ∩ 𝒪`, and the unit
criterion (`J𝒪 = 𝒪`) from the absence of bad primes. No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

/-- The inverse of a nonzero quaternion, `(nrd x)⁻¹ x̄`. -/
def qinv (x : B) : B := (nrd x)⁻¹ • star x

theorem mul_qinv {x : B} (hx : x ≠ 0) : x * qinv x = 1 := mul_inv_eq x hx

theorem qinv_mul {x : B} (hx : x ≠ 0) : qinv x * x = 1 := inv_mul_eq x hx

theorem star_eq_nrd_qinv {x : B} (hx : x ≠ 0) : star x = nrd x • qinv x := by
  unfold qinv; rw [smul_smul, mul_inv_cancel₀ (nrd_ne_zero hx), one_smul]

theorem intCast_eq_coe (z : ℤ) : (z : B) = ((z : ℚ) : B) := (QuaternionAlgebra.coe_intCast z).symm

theorem coe_eq_smul_one (q : ℚ) : (q : B) = q • (1 : B) := by
  rw [← coe_mul_eq_smul, mul_one]

/-- `nrd (x + y z) = x² + x y trd z + y² nrd z`. -/
theorem nrd_add_mul (x y : ℚ) (z : B) :
    nrd ((x : B) + (y : B) * z) = x ^ 2 + x * y * trd z + y ^ 2 * nrd z := by
  simp [nrd, trd]; ring

theorem trd_add_mul (x y : ℚ) (z : B) : trd ((x : B) + (y : B) * z) = 2 * x + y * trd z := by
  simp [trd]; ring

/-- A non-rational quaternion satisfying `z² = t z − n` has `trd z = t`, `nrd z = n`. -/
theorem trd_nrd_of_quad {z : B} (hz : ∀ q : ℚ, z ≠ (q : B)) {t n : ℚ}
    (h : z * z = (t : B) * z - (n : B)) : t = trd z ∧ n = nrd z := by
  have h2 := sq_eq_trd z
  have e : ((t - trd z : ℚ) : B) * z = ((n - nrd z : ℚ) : B) := by
    rw [QuaternionAlgebra.coe_sub, QuaternionAlgebra.coe_sub, sub_mul]
    exact sub_eq_sub_iff_sub_eq_sub.mp (h.symm.trans h2)
  by_cases ht : t = trd z
  · refine ⟨ht, ?_⟩
    rw [ht, sub_self, QuaternionAlgebra.coe_zero, zero_mul] at e
    have := congrArg QuaternionAlgebra.re e
    simp at this
    linarith
  · exfalso
    apply hz ((t - trd z)⁻¹ * (n - nrd z))
    have hd : (t - trd z) ≠ 0 := sub_ne_zero.mpr ht
    rw [QuaternionAlgebra.coe_mul, ← e, ← mul_assoc, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hd,
      QuaternionAlgebra.coe_one, one_mul]

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k}

theorem optEmb_mem (Φ : OptEmb k R) (a : k) : Φ.1 a ∈ LeafQM.O ↔ a ∈ R := by
  have h := Φ.2
  constructor
  · intro ha; rw [← h]; exact ha
  · intro ha; rw [← h] at ha; exact ha

theorem emb_rat (Φ : OptEmb k R) (q : ℚ) : Φ.1 (algebraMap ℚ k q) = (q : B) := by
  rw [Φ.1.commutes]; rfl

theorem emb_ratCast (Φ : OptEmb k R) (q : ℚ) : Φ.1 (q : k) = (q : B) := by
  rw [← eq_ratCast (algebraMap ℚ k) q, emb_rat]

theorem emb_intCast (Φ : OptEmb k R) (z : ℤ) : Φ.1 (z : k) = ((z : ℚ) : B) := by
  rw [map_intCast, intCast_eq_coe]

theorem emb_injective (Φ : OptEmb k R) : Function.Injective Φ.1 := Φ.1.toRingHom.injective

theorem emb_notRat (Φ : OptEmb k R) {a : k} (ha : ∀ q : ℚ, a ≠ algebraMap ℚ k q) :
    ∀ q : ℚ, Φ.1 a ≠ (q : B) := by
  intro q hq
  apply ha q
  apply emb_injective Φ
  rw [hq, emb_rat]

/-- An order `R = ℤ + ℤω` with `ω² − tω + n = 0`. -/
structure QBasis (R : Subring k) where
  ω : k
  mem : ω ∈ R
  notRat : ∀ q : ℚ, ω ≠ algebraMap ℚ k q
  span : ∀ r ∈ R, ∃ x y : ℤ, r = (x : k) + (y : k) * ω
  t : ℤ
  n : ℤ
  quad : ω * ω - (t : k) * ω + (n : k) = 0

theorem exists_qbasis (hk : Module.finrank ℚ k = 2) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) : Nonempty (QBasis R) := by
  obtain ⟨ω, hω, hq, hs⟩ := exists_basis hk R hR hc
  obtain ⟨t, n, htn⟩ := quad_rel hk ω (hR hω)
  exact ⟨⟨ω, hω, hq, hs, t, n, htn⟩⟩

variable (Bs : QBasis R)

theorem QBasis.notRat' : ∀ q : ℚ, Bs.ω ≠ (q : k) := by
  intro q h; exact Bs.notRat q (by rw [h, eq_ratCast])

/-- Every element of `k` is `x + yω` with `x, y ∈ ℚ`. -/
theorem QBasis.decomp (hk : Module.finrank ℚ k = 2) (a : k) : ∃ x y : ℚ, a = (x : k) + (y : k) * Bs.ω := by
  obtain ⟨x, y, h⟩ := EichlerBound.decomp hk Bs.notRat a
  exact ⟨x, y, by rw [h, eq_ratCast, Rat.smul_def]⟩

theorem emb_omega_mem (Φ : OptEmb k R) : Φ.1 Bs.ω ∈ LeafQM.O := (optEmb_mem Φ _).2 Bs.mem

theorem emb_omega_notRat (Φ : OptEmb k R) : ∀ q : ℚ, Φ.1 Bs.ω ≠ (q : B) := emb_notRat Φ Bs.notRat

theorem emb_omega_sq (Φ : OptEmb k R) :
    Φ.1 Bs.ω * Φ.1 Bs.ω = ((Bs.t : ℚ) : B) * Φ.1 Bs.ω - ((Bs.n : ℚ) : B) := by
  have := congrArg Φ.1 Bs.quad
  rw [map_add, map_sub, map_mul, map_mul, emb_intCast, emb_intCast, map_zero] at this
  rw [← sub_eq_zero, ← this]; abel

theorem trd_omega (Φ : OptEmb k R) : trd (Φ.1 Bs.ω) = Bs.t :=
  ((trd_nrd_of_quad (emb_omega_notRat Bs Φ) (emb_omega_sq Bs Φ)).1).symm

theorem nrd_omega (Φ : OptEmb k R) : nrd (Φ.1 Bs.ω) = Bs.n :=
  ((trd_nrd_of_quad (emb_omega_notRat Bs Φ) (emb_omega_sq Bs Φ)).2).symm

theorem emb_lin (Φ : OptEmb k R) (x y : ℚ) :
    Φ.1 ((x : k) + (y : k) * Bs.ω) = (x : B) + (y : B) * Φ.1 Bs.ω := by
  rw [map_add, map_mul, emb_ratCast, emb_ratCast]

include Bs in
theorem trd_emb (hk : Module.finrank ℚ k = 2) (Φ Ψ : OptEmb k R) (a : k) : trd (Φ.1 a) = trd (Ψ.1 a) := by
  obtain ⟨x, y, rfl⟩ := Bs.decomp hk a
  rw [emb_lin, emb_lin, trd_add_mul, trd_add_mul, trd_omega, trd_omega]

include Bs in
theorem nrd_emb (hk : Module.finrank ℚ k = 2) (Φ Ψ : OptEmb k R) (a : k) : nrd (Φ.1 a) = nrd (Ψ.1 a) := by
  obtain ⟨x, y, rfl⟩ := Bs.decomp hk a
  rw [emb_lin, emb_lin, nrd_add_mul, nrd_add_mul, trd_omega, trd_omega, nrd_omega, nrd_omega]

/-- The conjugation of `k`, `a ↦ trd(Ψ a) − a` (independent of `Ψ`). -/
def sk (Ψ : OptEmb k R) (a : k) : k := (trd (Ψ.1 a) : k) - a

theorem emb_sk (Ψ : OptEmb k R) (a : k) : Ψ.1 (sk Ψ a) = star (Ψ.1 a) := by
  rw [sk, map_sub, emb_ratCast, star_eq_trd_sub]

include Bs in
theorem emb_sk' (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) (a : k) :
    Φ.1 (sk Ψ a) = star (Φ.1 a) := by
  rw [sk, map_sub, emb_ratCast, star_eq_trd_sub, trd_emb Bs hk Φ Ψ]

theorem sk_mem (Ψ : OptEmb k R) {a : k} (ha : a ∈ R) : sk Ψ a ∈ R := by
  obtain ⟨z, hz⟩ := trd_int ((optEmb_mem Ψ a).2 ha)
  rw [sk, hz]
  exact R.sub_mem (by exact_mod_cast _root_.intCast_mem R z) ha

theorem sk_mul (Ψ : OptEmb k R) (a b : k) : sk Ψ (a * b) = sk Ψ a * sk Ψ b := by
  apply emb_injective Ψ
  rw [emb_sk, map_mul, star_mul, ← emb_sk, ← emb_sk, ← map_mul, mul_comm]

theorem sk_sk (Ψ : OptEmb k R) (a : k) : sk Ψ (sk Ψ a) = a := by
  apply emb_injective Ψ
  rw [emb_sk, emb_sk, star_star]

theorem sk_ratCast_mul (Ψ : OptEmb k R) (q : ℚ) (a : k) : sk Ψ ((q : k) * a) = (q : k) * sk Ψ a := by
  apply emb_injective Ψ
  rw [emb_sk, map_mul, map_mul, emb_sk, emb_ratCast, star_mul, QuaternionAlgebra.star_coe, coe_comm]

/-! ### The centralizer of `Ψ(ω)` is `Ψ(k)` -/

theorem comm_components {z b : B} (h : z * b = b * z) :
    z.imI * b.imJ = z.imJ * b.imI ∧ z.imJ * b.imK = z.imK * b.imJ ∧ z.imK * b.imI = z.imI * b.imK := by
  have e1 := congrArg QuaternionAlgebra.imI h
  have e2 := congrArg QuaternionAlgebra.imJ h
  have e3 := congrArg QuaternionAlgebra.imK h
  simp at e1 e2 e3
  refine ⟨by linarith, by linarith, by linarith⟩

theorem centralizer_rat {z b : B} (hb : ∀ q : ℚ, b ≠ (q : B)) (h : z * b = b * z) :
    ∃ x y : ℚ, z = (x : B) + (y : B) * b := by
  obtain ⟨h1, h2, h3⟩ := comm_components h
  have hb' : b.imI ≠ 0 ∨ b.imJ ≠ 0 ∨ b.imK ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hb b.re
    ext <;> simp [hc.1, hc.2.1, hc.2.2]
  rcases hb' with hI | hJ | hK
  · refine ⟨z.re - z.imI / b.imI * b.re, z.imI / b.imI, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · refine ⟨z.re - z.imJ / b.imJ * b.re, z.imJ / b.imJ, ?_⟩
    ext <;> simp <;> field_simp <;> linarith
  · refine ⟨z.re - z.imK / b.imK * b.re, z.imK / b.imK, ?_⟩
    ext <;> simp <;> field_simp <;> linarith

include Bs in
theorem centralizer (Ψ : OptEmb k R) {z : B} (h : z * Ψ.1 Bs.ω = Ψ.1 Bs.ω * z) : ∃ a : k, z = Ψ.1 a := by
  obtain ⟨x, y, rfl⟩ := centralizer_rat (emb_omega_notRat Bs Ψ) h
  exact ⟨(x : k) + (y : k) * Bs.ω, (emb_lin Bs Ψ x y).symm⟩

/-! ### The intertwiner lattice -/

/-- `J(Ψ, Φ) = {c ∈ B : c Ψ(a) = Φ(a) c}`. -/
def J (Ψ Φ : OptEmb k R) : Set B := {c | ∀ a : k, c * Ψ.1 a = Φ.1 a * c}

/-- `J(Ψ, Φ) ∩ 𝒪`. -/
def Jo (Ψ Φ : OptEmb k R) : Set B := {c | c ∈ LeafQM.O ∧ c ∈ J Ψ Φ}

include Bs in
theorem J_of_gen (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {c : B}
    (h : c * Ψ.1 Bs.ω = Φ.1 Bs.ω * c) : c ∈ J Ψ Φ := by
  intro a
  obtain ⟨x, y, rfl⟩ := Bs.decomp hk a
  rw [emb_lin, emb_lin, coe_eq_smul_one x, coe_eq_smul_one y]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h]

theorem J_conj {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ J Ψ Φ) (hc0 : c ≠ 0) (a : k) :
    Φ.1 a = c * Ψ.1 a * qinv c := by
  rw [hc a, mul_assoc, mul_qinv hc0, mul_one]

theorem J_qinv {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ J Ψ Φ) (hc0 : c ≠ 0) (a : k) :
    qinv c * Φ.1 a = Ψ.1 a * qinv c := by
  rw [J_conj hc hc0 a, ← mul_assoc, ← mul_assoc, qinv_mul hc0, one_mul]

include Bs in
theorem J_param {Ψ Φ : OptEmb k R} {c0 c : B} (hc0 : c0 ∈ J Ψ Φ) (hne : c0 ≠ 0) (hc : c ∈ J Ψ Φ) :
    ∃ a : k, c = c0 * Ψ.1 a := by
  obtain ⟨a, ha⟩ := centralizer Bs Ψ (z := qinv c0 * c) (by
    rw [mul_assoc, hc, ← mul_assoc, J_qinv hc0 hne, mul_assoc])
  refine ⟨a, ?_⟩
  rw [← ha, ← mul_assoc, mul_qinv hne, one_mul]

theorem J_mul_right {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ J Ψ Φ) (b : k) : c * Ψ.1 b ∈ J Ψ Φ := by
  intro a
  rw [mul_assoc, ← map_mul, mul_comm b a, map_mul, ← mul_assoc, hc a, mul_assoc]

theorem J_add {Ψ Φ : OptEmb k R} {c d : B} (hc : c ∈ J Ψ Φ) (hd : d ∈ J Ψ Φ) : c + d ∈ J Ψ Φ := by
  intro a; rw [add_mul, mul_add, hc a, hd a]

theorem J_neg {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ J Ψ Φ) : -c ∈ J Ψ Φ := by
  intro a; rw [neg_mul, mul_neg, hc a]

theorem J_smul {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ J Ψ Φ) (q : ℚ) : q • c ∈ J Ψ Φ := by
  intro a; rw [smul_mul_assoc, mul_smul_comm, hc a]

include Bs in
theorem J_star (hk : Module.finrank ℚ k = 2) {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ J Ψ Φ) :
    star c ∈ J Φ Ψ := by
  intro b
  have := congrArg star (hc (sk Ψ b))
  rw [star_mul, star_mul, ← emb_sk Ψ (sk Ψ b), ← emb_sk' Bs hk Ψ Φ (sk Ψ b), sk_sk] at this
  exact this.symm

theorem Jo_add {Ψ Φ : OptEmb k R} {c d : B} (hc : c ∈ Jo Ψ Φ) (hd : d ∈ Jo Ψ Φ) : c + d ∈ Jo Ψ Φ :=
  ⟨LeafQM.O.add_mem hc.1 hd.1, J_add hc.2 hd.2⟩

theorem Jo_sub {Ψ Φ : OptEmb k R} {c d : B} (hc : c ∈ Jo Ψ Φ) (hd : d ∈ Jo Ψ Φ) : c - d ∈ Jo Ψ Φ := by
  rw [sub_eq_add_neg]
  exact ⟨LeafQM.O.add_mem hc.1 (LeafQM.O.neg_mem hd.1), J_add hc.2 (J_neg hd.2)⟩

theorem Jo_zsmul {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ Jo Ψ Φ) (z : ℤ) : (z : ℚ) • c ∈ Jo Ψ Φ := by
  refine ⟨?_, J_smul hc.2 _⟩
  rw [← coe_mul_eq_smul]
  exact LeafQM.O.mul_mem (intCast_mem z) hc.1

theorem Jo_mul_right {Ψ Φ : OptEmb k R} {c : B} (hc : c ∈ Jo Ψ Φ) {r : k} (hr : r ∈ R) :
    c * Ψ.1 r ∈ Jo Ψ Φ :=
  ⟨LeafQM.O.mul_mem hc.1 ((optEmb_mem Ψ r).2 hr), J_mul_right hc.2 r⟩

/-- Saturation: `J ∩ ℓ𝒪 = ℓ (J ∩ 𝒪)`. -/
theorem Jo_div {Ψ Φ : OptEmb k R} {ℓ : ℤ} (hℓ : ℓ ≠ 0) {c : B} (hc : c ∈ Jo Ψ Φ) (hl : LO ℓ c) :
    ((ℓ : ℚ)⁻¹ • c) ∈ Jo Ψ Φ :=
  ⟨LO_div hℓ hl, J_smul hc.2 _⟩

theorem central_ij {b : B} (hi : b * ⟨0, 1, 0, 0⟩ = ⟨0, 1, 0, 0⟩ * b)
    (hj : b * ⟨0, 0, 1, 0⟩ = ⟨0, 0, 1, 0⟩ * b) : b = (b.re : B) := by
  have e1 := congrArg QuaternionAlgebra.imJ hi
  have e2 := congrArg QuaternionAlgebra.imK hi
  have e3 := congrArg QuaternionAlgebra.imK hj
  have e4 := congrArg QuaternionAlgebra.imI hj
  simp at e1 e2 e3 e4
  ext <;> simp <;> linarith

include Bs in
/-- **Skolem–Noether for `R ↪ 𝒪`**: the intertwiner lattice is nonzero. -/
theorem exists_Jo (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) : ∃ c ∈ Jo Ψ Φ, c ≠ 0 := by
  set β0 := Ψ.1 Bs.ω
  set β := Φ.1 Bs.ω
  have hβ0 := emb_omega_mem Bs Ψ
  have hβ := emb_omega_mem Bs Φ
  have hsq := emb_omega_sq Bs Φ
  have hst : star β0 = ((Bs.t : ℚ) : B) - β0 := by rw [star_eq_trd_sub, trd_omega]
  have hn : star β0 * β0 = ((Bs.n : ℚ) : B) := by rw [star_mul_self', nrd_omega]
  have key : ∀ s : B, s ∈ LeafQM.O → (β * s - s * star β0) ∈ Jo Ψ Φ := by
    intro s hs
    refine ⟨LeafQM.O.sub_mem (LeafQM.O.mul_mem hβ hs) (LeafQM.O.mul_mem hs (star_mem hβ0)),
      J_of_gen Bs hk ?_⟩
    rw [sub_mul, mul_sub, mul_assoc s, hn, ← mul_assoc β β, hsq, hst]
    rw [coe_eq_smul_one, coe_eq_smul_one]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
    abel
  by_contra hall
  push Not at hall
  have h1 := hall _ (key 1 LeafQM.O.one_mem)
  have hi := hall _ (key ⟨0, 1, 0, 0⟩ (by refine ⟨![0, 1, 0, 0], ?_⟩; ext <;> simp [ofInt]))
  have hj := hall _ (key ⟨0, 0, 1, 0⟩ (by refine ⟨![-1, 0, 2, 0], ?_⟩; ext <;> simp [ofInt] <;> norm_num))
  rw [mul_one, one_mul, sub_eq_zero] at h1
  rw [← h1, sub_eq_zero] at hi hj
  apply emb_omega_notRat Bs Φ β.re
  exact central_ij hi hj

end Emb

end EichlerBound
