import ZInQKernel.Contrib.TYZGenus.ShimuraEtaInv
import ZInQKernel.Contrib.GZTheta.JacobiGauss

/-!
# tyz-cm: `x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` and the `Γ₀(32)`-invariance of `x, y` (proved)

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

**Main result**: `etaModelInvariant : X0.EtaModelInvariant` (x0-32's leaf, proved), hence
`cmFieldOfDefinition_of_cmValueRingClass : CMValueRingClass → CM.CMFieldOfDefinition ringClassFieldD`.

Proof of the eta identity `x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` (`xC_eq_even`), with `Q = e^{2πiτ}`,
`θ₀₀(τ') = θ(0; τ')`, `θ₀₁(τ') = θ(1/2; τ')` and `θ(8τ; 16τ) = Q⁻²·θ₁₀(16τ)` (Mathlib's
`jacobiTheta₂`), and gz-theta's Jacobi triple product (`jacobiTheta₂_eq_jtpP`):
* `θ₀₁(4τ) = ∏(1 − Q^{4n+4})(1 − Q^{4n+2})² = η(2τ)²/η(4τ)`;
* `θ₀₀(16τ) = A C²`, `θ(8τ; 16τ) = 2 A B²`, with `A = ∏(1 − Q^{16n+16})`, `B = ∏(1 + Q^{16n+16})`,
  `C = ∏(1 + Q^{16n+8})`; and `η(8τ) ∼ D A`, `η(32τ) ∼ A B` with `D = ∏(1 − Q^{16n+8})`;
* Euler: `B C D = 1`;
* splitting `Σ (−1)ⁿ Q^{2n²}` by the parity of `n`: `θ₀₁(4τ) = θ₀₀(16τ) − Q²θ(8τ; 16τ)`.
Then `x = η(16)⁶/(η(8)²η(32)⁴)` has only even exponents, and gz-theta's `η²` multiplier in closed
form (`ShimuraEtaInv.lean`) gives the exponent `3X₁₆ − X₈ − 2X₃₂ = −24bd ≡ 0 (mod 12)`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open Complex Filter Topology
open scoped Real
open ZInQ.GZTheta (gp gp_mul_gp gp_even_mul_odd gp_pow multipliable_geom_lin jtpA jtpA_ne_zero
  jtpA_eq_gp jtpB_eq_gp jtpP qJ eJ jacobiTheta₂_eq_jtpP jtpP_half_eq_gp zeta12 zeta12_ne_zero
  mobius_denom_ne_zero)

section Products
variable {q : ℂ}

theorem gp_mul_neg (hq : ‖q‖ < 1) (k m : ℕ) (hk : 0 < k) :
    gp q (-1) k m * gp q 1 k m = gp q (-1) (2 * k) (2 * m) := by
  rw [gp_mul_gp hq _ _ _ _ hk]
  unfold gp
  exact tprod_congr fun n => by ring

end Products

variable {τ : ℂ}

/-- `Q = e^{2πiτ}`. -/
irreducible_def Qt (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

theorem norm_Qt_lt_one (hτ : 0 < τ.im) : ‖Qt τ‖ < 1 := by
  rw [Qt_def, Complex.norm_exp]
  have : (2 * (π : ℂ) * I * τ).re = -(2 * π * τ.im) := by simp [Complex.mul_re, Complex.mul_im]
  rw [this, ← Real.exp_zero]
  exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])

theorem Qt_ne_zero (τ : ℂ) : Qt τ ≠ 0 := by rw [Qt_def]; exact Complex.exp_ne_zero _

theorem qJ_mul_nat (k : ℕ) (τ : ℂ) : qJ ((2 * k : ℕ) * τ) = Qt τ ^ k := by
  rw [qJ, Qt_def, ← Complex.exp_nat_mul]; push_cast; ring_nf

theorem eJ_mul_nat (k : ℕ) (τ : ℂ) : eJ ((k : ℕ) * τ) = Qt τ ^ k := by
  rw [eJ, Qt_def, ← Complex.exp_nat_mul]; ring_nf

/-! ## Theta series as products -/

/-- `θ₀₁(4τ) = ∏(1 − Q^{4n+4})(1 − Q^{4n+2})²`. -/
theorem theta01_four (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) (4 * τ) = gp (Qt τ) (-1) 4 4 * gp (Qt τ) (-1) 4 2 ^ 2 := by
  have h4 : 0 < (4 * τ).im := by simp; linarith
  rw [jacobiTheta₂_eq_jtpP h4, jtpP_half_eq_gp,
    show (4 : ℂ) * τ = ((2 * 2 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat, gp_pow, gp_pow]
  norm_num
  ring

/-- `θ₀₀(16τ) = A C²`. -/
theorem theta00_sixteen (hτ : 0 < τ.im) :
    jacobiTheta₂ 0 (16 * τ) = gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 8 ^ 2 := by
  have h16 : 0 < (16 * τ).im := by simp; linarith
  rw [jacobiTheta₂_eq_jtpP h16]
  unfold jtpP
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, neg_zero,
    show (16 : ℂ) * τ = ((2 * 8 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat,
    show eJ 0 = 1 by simp [eJ], gp_pow, gp_pow]
  norm_num
  ring

theorem gp_shift (_hq : q ≠ 0) (c : ℂ) (k m j : ℕ) :
    gp q (c * q ^ j) k m = gp q c k (m + j) := by
  unfold gp
  exact tprod_congr fun n => by ring

/-- `θ(8τ; 16τ) = 2 A B²`. -/
theorem theta_eight_sixteen (hτ : 0 < τ.im) :
    jacobiTheta₂ (8 * τ) (16 * τ) = 2 * gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 16 ^ 2 := by
  have h16 : 0 < (16 * τ).im := by simp; linarith
  have hq := norm_Qt_lt_one hτ
  have hQ := Qt_ne_zero τ
  rw [jacobiTheta₂_eq_jtpP h16]
  unfold jtpP
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp,
    show (16 : ℂ) * τ = ((2 * 8 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat,
    show -((8 : ℂ) * τ) = -(((8 : ℕ) : ℂ) * τ) by norm_num,
    show (8 : ℂ) * τ = ((8 : ℕ) : ℂ) * τ by norm_num, ZInQ.GZTheta.eJ_neg, eJ_mul_nat,
    gp_pow, gp_pow, gp_pow]
  -- `∏(1 + Q⁸ Q^{16n+8}) = B`
  have hB : gp (Qt τ) (Qt τ ^ 8) (8 * 2) (8 * 1) = gp (Qt τ) 1 16 16 := by
    have := gp_shift hQ 1 16 8 8
    rw [one_mul] at this
    norm_num at this ⊢
    exact this
  -- `∏(1 + Q⁻⁸ Q^{16n+8}) = ∏(1 + Q^{16n}) = 2 B`
  have hB' : gp (Qt τ) (Qt τ ^ 8)⁻¹ (8 * 2) (8 * 1) = 2 * gp (Qt τ) 1 16 16 := by
    have e1 : gp (Qt τ) (Qt τ ^ 8)⁻¹ (8 * 2) (8 * 1) = gp (Qt τ) 1 16 0 := by
      unfold gp
      refine tprod_congr fun n => ?_
      have : (Qt τ ^ 8)⁻¹ * Qt τ ^ (8 * 2 * n + 8 * 1) = Qt τ ^ (16 * n + 0) := by
        rw [show 8 * 2 * n + 8 * 1 = 8 + 16 * n by ring, pow_add, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hQ), one_mul, add_zero]
      rw [this, one_mul]
    rw [e1]
    have hm1 : Multipliable (fun n : ℕ => 1 + 1 * Qt τ ^ (16 * (n + 1) + 0)) :=
      (multipliable_geom_lin hq 1 16 16 (by norm_num)).congr fun n => by ring_nf
    have h := tprod_eq_zero_mul' (f := fun n : ℕ => 1 + 1 * Qt τ ^ (16 * n + 0)) hm1
    beta_reduce at h
    unfold gp
    rw [h]
    congr 1
    rw [mul_zero, add_zero, pow_zero, mul_one]; norm_num
  rw [hB, hB']
  norm_num
  ring

/-! ## The parity split `θ₀₁(4τ) = θ₀₀(16τ) − Q² θ(8τ; 16τ)` -/

theorem theta_parity (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) (4 * τ) =
      jacobiTheta₂ 0 (16 * τ) - Qt τ ^ 2 * jacobiTheta₂ (8 * τ) (16 * τ) := by
  have h4 : 0 < (4 * τ).im := by simp; linarith
  have h16 : 0 < (16 * τ).im := by simp; linarith
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (1 / 2) (4 * τ) with hfdef
  have hf : HasSum f (jacobiTheta₂ (1 / 2) (4 * τ)) := hasSum_jacobiTheta₂_term _ h4
  have he : HasSum (f ∘ fun m : ℤ => 2 * m) (jacobiTheta₂ 0 (16 * τ)) := by
    refine (hasSum_jacobiTheta₂_term 0 h16).congr_fun fun m => ?_
    simp only [Function.comp_apply, hfdef, jacobiTheta₂_term]
    have : 2 * (π : ℂ) * I * ((2 * m : ℤ) : ℂ) * (1 / 2) + π * I * ((2 * m : ℤ) : ℂ) ^ 2 * (4 * τ) =
        (2 * π * I * (m : ℂ) * 0 + π * I * (m : ℂ) ^ 2 * (16 * τ)) + (m : ℂ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have ho : HasSum (f ∘ fun m : ℤ => 2 * m + 1)
      (-(Qt τ ^ 2) * jacobiTheta₂ (8 * τ) (16 * τ)) := by
    refine ((hasSum_jacobiTheta₂_term (8 * τ) h16).mul_left (-(Qt τ ^ 2))).congr_fun fun m => ?_
    simp only [Function.comp_apply, hfdef, jacobiTheta₂_term, Qt_def]
    rw [← Complex.exp_nat_mul, neg_mul, ← Complex.exp_add]
    have : 2 * (π : ℂ) * I * ((2 * m + 1 : ℤ) : ℂ) * (1 / 2) +
        π * I * ((2 * m + 1 : ℤ) : ℂ) ^ 2 * (4 * τ) =
        (((2 : ℕ) : ℂ) * (2 * π * I * τ) + (2 * π * I * (m : ℂ) * (8 * τ) +
          π * I * (m : ℂ) ^ 2 * (16 * τ))) + (π * I + (m : ℂ) * (2 * π * I)) := by
      push_cast; ring
    rw [this, Complex.exp_add _ (π * I + (m : ℂ) * (2 * π * I)), Complex.exp_add (π * I),
      Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have hcompl : IsCompl (Set.range fun m : ℤ => 2 * m) (Set.range fun m : ℤ => 2 * m + 1) := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor
    · ext n
      simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_range, Set.bot_eq_empty,
        Set.mem_empty_iff_false, iff_false, not_and, forall_exists_index]
      rintro a rfl ⟨b, hb⟩
      omega
    · ext n
      simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.top_eq_univ, Set.mem_univ,
        iff_true]
      rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
      · exact Or.inl ⟨k, rfl⟩
      · exact Or.inr ⟨k, rfl⟩
  have he' := (Function.Injective.hasSum_range_iff (f := f)
    (g := fun m : ℤ => 2 * m) (fun a b h => by simpa using h)).mpr he
  have ho' := (Function.Injective.hasSum_range_iff (f := f)
    (g := fun m : ℤ => 2 * m + 1) (fun a b h => by simpa using h)).mpr ho
  have := HasSum.add_isCompl (f := f) hcompl he' ho'
  rw [hf.unique this]
  ring

/-! ## Euler's identity `B C D = 1` and the products of `η(8τ), η(32τ)` -/

theorem euler_BCD (hτ : 0 < τ.im) :
    gp (Qt τ) 1 16 16 * gp (Qt τ) 1 16 8 * gp (Qt τ) (-1) 16 8 = 1 := by
  have hq := norm_Qt_lt_one hτ
  -- `C D = G(−1, 32, 16)`
  have hCD : gp (Qt τ) 1 16 8 * gp (Qt τ) (-1) 16 8 = gp (Qt τ) (-1) 32 16 := by
    rw [mul_comm, gp_mul_neg hq 16 8 (by norm_num)]
  -- `G(−1,16,16) = G(−1,32,16) G(−1,32,32)`
  have hsplit := gp_even_mul_odd hq (-1) 16 16 (by norm_num)
  norm_num at hsplit
  -- `G(−1,16,16) B = G(−1,32,32)`
  have hAB := gp_mul_neg hq 16 16 (by norm_num)
  norm_num at hAB
  -- `G(−1,32,32) = jtpA(32τ) ≠ 0`
  have h32 : 0 < (32 * τ).im := by simp; linarith
  have hne : gp (Qt τ) (-1) 32 32 ≠ 0 := by
    have := jtpA_ne_zero h32
    rw [jtpA_eq_gp, show (32 : ℂ) * τ = ((2 * 16 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat,
      gp_pow] at this
    norm_num at this
    exact this
  have key : (gp (Qt τ) 1 16 16 * gp (Qt τ) (-1) 32 16 - 1) * gp (Qt τ) (-1) 32 32 = 0 := by
    linear_combination (gp (Qt τ) 1 16 16) * hsplit + hAB
  rw [mul_assoc, hCD]
  have := (mul_eq_zero.1 key).resolve_right hne
  linear_combination this

/-! ## The eta identity `x = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` -/

theorem eta_eq_gp (k : ℕ) (τ : ℂ) :
    ModularForm.eta ((k : ℂ) * τ) = X0.wz τ ^ k * gp (Qt τ) (-1) k k := by
  rw [← X0.etaD, X0.etaD_eq'']
  congr 1
  unfold X0.pF X0.prodF gp
  refine tprod_congr fun n => ?_
  rw [show Function.Periodic.qParam 1 ((k : ℂ) * τ) = Qt τ ^ k by
    rw [Function.Periodic.qParam, Qt_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]
  rw [← pow_mul]
  ring_nf

theorem wz_pow_48 (τ : ℂ) : X0.wz τ ^ 48 = Qt τ ^ 2 := by
  rw [show 48 = 24 * 2 by norm_num, pow_mul, X0.wz_pow_24, Qt_def]

/-- **The eta identity**: `x(τ) = η(16τ)⁶/(η(8τ)²η(32τ)⁴)` on `ℍ`. -/
theorem xC_eq_even (τ : UpperHalfPlane) :
    X0.xC τ = X0.etaD 16 τ ^ 6 / (X0.etaD 8 τ ^ 2 * X0.etaD 32 τ ^ 4) := by
  have hτ := τ.im_pos
  have hq := norm_Qt_lt_one hτ
  have hG2 : gp (Qt τ) (-1) 2 2 = gp (Qt τ) (-1) 4 2 * gp (Qt τ) (-1) 4 4 := by
    have := gp_even_mul_odd hq (-1) 2 2 (by norm_num); norm_num at this; rw [← this]
  have hG8 : gp (Qt τ) (-1) 8 8 = gp (Qt τ) (-1) 16 8 * gp (Qt τ) (-1) 16 16 := by
    have := gp_even_mul_odd hq (-1) 8 8 (by norm_num); norm_num at this; rw [← this]
  have hG32 : gp (Qt τ) (-1) 32 32 = gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 16 := by
    have := gp_mul_neg hq 16 16 (by norm_num); norm_num at this; rw [← this]
  have hpar : gp (Qt τ) (-1) 4 2 ^ 2 * gp (Qt τ) (-1) 4 4 =
      gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 8 ^ 2 -
        2 * Qt τ ^ 2 * gp (Qt τ) (-1) 16 16 * gp (Qt τ) 1 16 16 ^ 2 := by
    have := theta_parity hτ
    rw [theta01_four hτ, theta00_sixteen hτ, theta_eight_sixteen hτ] at this
    linear_combination this
  have heul := euler_BCD hτ
  have e2 := eta_eq_gp 2 τ
  have e4 := eta_eq_gp 4 τ
  have e8 := eta_eq_gp 8 τ
  have e16 := eta_eq_gp 16 τ
  have e32 := eta_eq_gp 32 τ
  have n8 := X0.etaD_ne_zero (d := 8) (by norm_num) τ
  have n32 := X0.etaD_ne_zero (d := 32) (by norm_num) τ
  have n4 := X0.etaD_ne_zero (d := 4) (by norm_num) τ
  have h48 := wz_pow_48 (τ : ℂ)
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ n8) (pow_ne_zero _ n32))]
  unfold X0.xC
  rw [div_add' _ _ _ (mul_ne_zero n4 (pow_ne_zero _ n32)), div_mul_eq_mul_div,
    div_eq_iff (mul_ne_zero n4 (pow_ne_zero _ n32))]
  simp only [X0.etaD]
  rw [e2, e4, e8, e16, e32, hG2, hG8, hG32]
  set w := X0.wz (τ : ℂ)
  set A := gp (Qt τ) (-1) 16 16
  set B := gp (Qt τ) 1 16 16
  set C := gp (Qt τ) 1 16 8
  set D := gp (Qt τ) (-1) 16 8
  set P := gp (Qt τ) (-1) 4 2
  set G4 := gp (Qt τ) (-1) 4 4
  linear_combination (w ^ 164 * G4 * A ^ 7 * D ^ 2 * B ^ 4) * hpar +
    (w ^ 164 * G4 * A ^ 7 * D ^ 2 * B ^ 4 * 2 * A * B ^ 2) * h48 +
    (w ^ 164 * G4 * A ^ 8 * B ^ 2 * (B * C * D + 1)) * heul

/-! ## `x` is `Γ₀(32)`-invariant; `X0.EtaModelInvariant` -/

/-- **`x` is `Γ₀(32)`-invariant** (unconditional). -/
theorem xC_gamma0' (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 32) (τ : UpperHalfPlane) :
    X0.xC ((γ • τ : UpperHalfPlane) : ℂ) = X0.xC τ := by
  rw [xC_eq_even (γ • τ), xC_eq_even τ]
  obtain ⟨k, hk, hd⟩ := gamma0_32_data hγ
  set a := γ 0 0
  set b := γ 0 1
  set d := γ 1 1
  set L : ℂ := (γ 1 0 : ℂ) * τ + d
  have hL : L ≠ 0 := by
    have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
    exact mobius_denom_ne_zero hdet0 τ.im_pos
  have h8 := etaD_sq_smul (δ := 8) (by norm_num) γ (k := 4 * k) (by rw [hk]; push_cast; ring) hd τ
  have h16 := etaD_sq_smul (δ := 16) (by norm_num) γ (k := 2 * k) (by rw [hk]; push_cast; ring) hd τ
  have h32 := etaD_sq_smul (δ := 32) (by norm_num) γ (k := k) (by rw [hk]; push_cast; ring) hd τ
  set A8 := zeta12 ^ (XfR a ((8 : ℕ) * b) (4 * k) d)
  set A16 := zeta12 ^ (XfR a ((16 : ℕ) * b) (2 * k) d)
  set A32 := zeta12 ^ (XfR a ((32 : ℕ) * b) k d)
  have hA8 : A8 ≠ 0 := zpow_ne_zero _ zeta12_ne_zero
  have hA32 : A32 ≠ 0 := zpow_ne_zero _ zeta12_ne_zero
  have hratio : A16 ^ 3 / (A8 * A32 ^ 2) = 1 := by
    rw [div_eq_one_iff_eq (mul_ne_zero hA8 (pow_ne_zero _ hA32))]
    simp only [A8, A16, A32, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ zeta12_ne_zero]
    apply zeta12_zpow_congr
    exact ⟨-2 * b * d, by simp only [XfR]; push_cast; ring⟩
  set E8 := X0.etaD 8 τ ^ 2
  set E16 := X0.etaD 16 τ ^ 2
  set E32 := X0.etaD 32 τ ^ 2
  have hE8 : E8 ≠ 0 := pow_ne_zero _ (X0.etaD_ne_zero (by norm_num) τ)
  have hE32 : E32 ≠ 0 := pow_ne_zero _ (X0.etaD_ne_zero (by norm_num) τ)
  have hx : ∀ z : ℂ, X0.etaD 16 z ^ 6 / (X0.etaD 8 z ^ 2 * X0.etaD 32 z ^ 4) =
      (X0.etaD 16 z ^ 2) ^ 3 / (X0.etaD 8 z ^ 2 * (X0.etaD 32 z ^ 2) ^ 2) := fun z => by ring
  rw [hx, hx, h8, h16, h32]
  calc (A16 * L * E16) ^ 3 / ((A8 * L * E8) * (A32 * L * E32) ^ 2)
      = (A16 ^ 3 / (A8 * A32 ^ 2)) * (E16 ^ 3 / (E8 * E32 ^ 2)) := by
        field_simp
    _ = E16 ^ 3 / (E8 * E32 ^ 2) := by rw [hratio, one_mul]

/-- **x0-32's leaf `X0.EtaModelInvariant`, proved.** -/
theorem etaModelInvariant : X0.EtaModelInvariant :=
  fun γ hγ τ => ⟨xC_gamma0' γ hγ τ, yC_gamma0 γ hγ τ⟩

/-! ## The main results with `EtaModelInvariant` discharged -/

/-- **MAIN RESULT of tyz-cm: the CM leaf `CM.CMFieldOfDefinition ringClassFieldD` from the one
textbook leaf `CMValueRingClass`.** -/
theorem cmFieldOfDefinition_of_cmValueRingClass (hV : CMValueRingClass) :
    ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_cmValue hV etaModelInvariant

/-- **`Package.CMFieldOfDefinitionTYZ` from `CMValueRingClass`.** -/
theorem cmFieldTYZ_of_cmValueRingClass (hV : CMValueRingClass) :
    ZInQ.Contrib.TYZGenus.Package.CMFieldOfDefinitionTYZ :=
  cmFieldTYZ_of_cmValue hV etaModelInvariant

/-- **The CM leaf from Gross's form of the main theorem of CM** (`ShimuraReciprocityModFn`). -/
theorem cmFieldOfDefinition_of_shimuraModFn (hS : ShimuraReciprocityModFn) :
    ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition RingClass.ringClassFieldD :=
  cmFieldOfDefinition_of_cmValueRingClass (cmValueRingClass_of_modFn hS)

/-- **`ShimuraReciprocityPic` (the leaf of `ShimuraRecip.lean`, used by `ShimuraZn.lean`) from
`ShimuraReciprocityModFn` alone.** -/
theorem shimuraReciprocityPic_of_shimuraModFn (hS : ShimuraReciprocityModFn) :
    ShimuraReciprocityPic :=
  shimuraReciprocityPic_of_modFn hS etaModelInvariant

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **Reading A of TYZ Theorem 3.5 with the CM field-of-definition leaf replaced by
`CMValueRingClass`** (`TYZSigmaFixesZn` stays a hypothesis: task cm-numeric). -/
theorem tyzThm35ReadingA_of_cmValueRingClass (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hV : CMValueRingClass) (hs : TYZSigmaFixesZn)
    (h318 : Lemma318Literal RingClass.HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmValue h11 h1 h29 hV etaModelInvariant hs h318 hG

end ZInQ.Contrib.TYZGenus.Shimura
