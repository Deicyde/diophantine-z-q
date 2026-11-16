import ZInQKernel.Contrib.GZTheta.JacobiGauss
import ZInQKernel.Contrib.GZTheta.HeckeComb
import ZInQKernel.Contrib.GZTheta.Main

/-!
# gz-theta: the `q`-series identity `η(4τ)² η(8τ)² = ∑ heckeCoeff 1 n qⁿ`

With `Q = e^{2π i τ}`, Jacobi's identity at `8τ` gives
`∑_n n (−1)^n Q^{4n² + 4n} = ∏ (1 − Q^{8n+8})³` and Gauss's identity at `8τ` gives
`∑_m (−1)^m Q^{4m²} = ∏ (1 − Q^{8n+8})(1 − Q^{8n+4})²`. Their product times `Q` is
`∑_{n,m} n (−1)^{n+m} Q^{(2n+1)² + (2m)²}`; grouping by `N = (2n+1)² + (2m)²` gives
`∑_N heckeCoeff 1 N Q^N` (`HeckeComb.lean`), and the product side is `η(4τ)² η(8τ)²`.

This proves `EtaThetaIdentity`, hence `CMForm32` (Hecke's theorem for `ψ₁`).
-/

open Complex Filter ModularForm ZInQ.Contrib.HeckeFE
open UpperHalfPlane hiding I
open scoped Real Topology

noncomputable section

namespace ZInQ.GZTheta

/-- The fibre of `(n, m) ↦ (2n+1)² + (2m)²` over `N`. -/
def Fib (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(N : ℤ)) N)).filter
    (fun p => (2 * p.1 + 1) ^ 2 + (2 * p.2) ^ 2 = N)

theorem mem_Fib {N : ℕ} {p : ℤ × ℤ} : p ∈ Fib N ↔ (2 * p.1 + 1) ^ 2 + (2 * p.2) ^ 2 = N := by
  simp only [Fib, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;>
      nlinarith [sq_nonneg (2 * p.1 + 1), sq_nonneg (2 * p.2), sq_nonneg (p.1 + 1),
        sq_nonneg (p.1), sq_nonneg (p.2 - 1), sq_nonneg (p.2 + 1)]

/-- **The coefficient identity**: `∑_{(2n+1)² + (2m)² = N} n (−1)^{n+m} = heckeCoeff 1 N`. -/
theorem sum_Fib_eq_heckeCoeff (N : ℕ) :
    ∑ p ∈ Fib N, (p.1 : ℂ) * cexp (π * I * (p.1 + p.2)) = heckeCoeff 1 N := by
  rw [heckeCoeff_one_eq_sum_Soe]
  refine Finset.sum_nbij' (fun p => (2 * p.1 + 1, 2 * p.2)) (fun p => (p.1 / 2, p.2 / 2))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, mem_Fib] at hp
    simp only [Finset.mem_coe, Soe, Finset.mem_filter, mem_normFiber]
    exact ⟨hp, by omega, by omega⟩
  · intro p hp
    simp only [Finset.mem_coe, Soe, Finset.mem_filter, mem_normFiber] at hp
    simp only [Finset.mem_coe, mem_Fib]
    have h1 : 2 * (p.1 / 2) + 1 = p.1 := by omega
    have h2 : 2 * (p.2 / 2) = p.2 := by omega
    rw [h1, h2]; exact hp.1
  · intro p _
    simp only
    ext <;> simp <;> omega
  · intro p hp
    simp only [Finset.mem_coe, Soe, Finset.mem_filter] at hp
    simp only
    ext <;> simp <;> omega
  · intro p _
    simp only
    rw [uo_odd_even, mul_comm]
    congr 2
    push_cast
    omega

theorem summable_norm_of_hasSum {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasSum f a) :
    Summable (fun i => ‖f i‖) :=
  summable_norm_iff.mpr h.summable

theorem term_identity (τ : ℂ) (n m : ℤ) :
    cexp (2 * π * I * τ) * (((n : ℂ) * jacobiTheta₂_term n ((1 + 8 * τ) / 2) (8 * τ)) *
      jacobiTheta₂_term m (1 / 2) (8 * τ)) =
      (n : ℂ) * cexp (π * I * (n + m)) *
        cexp (2 * π * I * τ * (((2 * n + 1) ^ 2 + (2 * m) ^ 2 : ℤ) : ℂ)) := by
  simp only [jacobiTheta₂_term]
  have e : ∀ x y z : ℂ, cexp x * ((n : ℂ) * cexp y * cexp z) = (n : ℂ) * cexp (x + y + z) :=
    fun x y z => by rw [Complex.exp_add, Complex.exp_add]; ring
  rw [e, mul_assoc (n : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem eta_tprod_eq_gp (τ : ℂ) (k : ℕ) :
    ∏' n : ℕ, (1 - eta_q n (k * τ)) = gp (cexp (2 * π * I * τ)) (-1) k k := by
  unfold gp
  refine tprod_congr fun n => ?_
  rw [eta_q_eq_pow]
  rw [show cexp (2 * π * I * (k * τ)) = cexp (2 * π * I * τ) ^ k by
    rw [← Complex.exp_nat_mul]; ring_nf]
  rw [← pow_mul]
  ring_nf

theorem product_side {τ : ℂ} (hτ : 0 < τ.im) :
    cexp (2 * π * I * τ) * (jtpA (8 * τ) ^ 3 * (gp (qJ (8 * τ)) (-1) 2 2 *
      gp (qJ (8 * τ)) (-1) 2 1 * gp (qJ (8 * τ)) (-1) 2 1)) =
      η (4 * τ) ^ 2 * η (8 * τ) ^ 2 := by
  set Q : ℂ := cexp (2 * π * I * τ) with hQdef
  have hQq : qJ (2 * τ) = Q := by rw [qJ, hQdef]; ring_nf
  have hQ1 : ‖Q‖ < 1 := by
    have := norm_qJ_lt_one (τ := 2 * τ) (by simp; exact hτ)
    rwa [hQq] at this
  have hq8 : qJ (8 * τ) = Q ^ 4 := by
    rw [show (8 : ℂ) * τ = 4 * (2 * τ) by ring, qJ_four_mul, hQq]
  have e4 : ∏' n : ℕ, (1 - eta_q n (4 * τ)) = gp Q (-1) 4 4 := by
    have := eta_tprod_eq_gp τ 4; push_cast at this; exact this
  have e8 : ∏' n : ℕ, (1 - eta_q n (8 * τ)) = gp Q (-1) 8 8 := by
    have := eta_tprod_eq_gp τ 8; push_cast at this; exact this
  have hsplit := gp_even_mul_odd hQ1 (-1) 4 4 (by norm_num)
  norm_num only at hsplit
  have hq24 : Function.Periodic.qParam 24 (4 * τ) ^ 2 *
      Function.Periodic.qParam 24 (8 * τ) ^ 2 = Q := by
    simp only [Function.Periodic.qParam, hQdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hl : jtpA (8 * τ) ^ 3 * (gp (qJ (8 * τ)) (-1) 2 2 * gp (qJ (8 * τ)) (-1) 2 1 *
      gp (qJ (8 * τ)) (-1) 2 1) = gp Q (-1) 8 8 ^ 4 * gp Q (-1) 8 4 ^ 2 := by
    rw [jtpA_eq_gp, hq8, gp_pow, gp_pow]
    norm_num only
    ring
  have hr : η (4 * τ) ^ 2 * η (8 * τ) ^ 2 =
      (Function.Periodic.qParam 24 (4 * τ) ^ 2 * Function.Periodic.qParam 24 (8 * τ) ^ 2) *
        (gp Q (-1) 4 4 ^ 2 * gp Q (-1) 8 8 ^ 2) := by
    rw [ModularForm.eta, ModularForm.eta, e4, e8]
    ring
  rw [hl, hr, hq24, ← hsplit]
  ring

/-- **`η(4τ)² η(8τ)² = ∑ heckeCoeff 1 n qⁿ`.** -/
theorem etaThetaIdentity : EtaThetaIdentity := by
  intro τ
  have hτ : 0 < (τ : ℂ).im := τ.im_pos
  have h8 : 0 < (8 * (τ : ℂ)).im := by simp; exact hτ
  let fJ : ℤ → ℂ := fun n => (n : ℂ) * jacobiTheta₂_term n ((1 + 8 * (τ : ℂ)) / 2) (8 * τ)
  let fG : ℤ → ℂ := fun m => jacobiTheta₂_term m (1 / 2) (8 * τ)
  have hJ : HasSum fJ (jtpA (8 * τ) ^ 3) := hasSum_jacobi h8
  have hG : HasSum fG (gp (qJ (8 * τ)) (-1) 2 2 * gp (qJ (8 * τ)) (-1) 2 1 *
      gp (qJ (8 * τ)) (-1) 2 1) := hasSum_gauss h8
  have hJn : Summable (fun n => ‖fJ n‖) := summable_norm_iff.mpr hJ.summable
  have hGn : Summable (fun n => ‖fG n‖) := summable_norm_iff.mpr hG.summable
  have hfg : Summable (fun x : ℤ × ℤ => fJ x.1 * fG x.2) :=
    summable_mul_of_summable_norm (f := fJ) (g := fG) hJn hGn
  have hprod := HasSum.mul (f := fJ) (g := fG) hJ hG hfg
  have hT := hprod.mul_left (cexp (2 * π * I * τ))
  rw [product_side hτ] at hT
  have hfib := hT.tsum_fiberwise (fun p : ℤ × ℤ => ((2 * p.1 + 1) ^ 2 + (2 * p.2) ^ 2).toNat)
  refine hfib.congr_fun fun N => ?_
  symm
  have hset : (fun p : ℤ × ℤ => ((2 * p.1 + 1) ^ 2 + (2 * p.2) ^ 2).toNat) ⁻¹' {N} =
      ↑(Fib N) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_Fib]
    have : 0 ≤ (2 * p.1 + 1) ^ 2 + (2 * p.2) ^ 2 := by positivity
    omega
  rw [hset, Finset.tsum_subtype' (Fib N)
    (fun p : ℤ × ℤ => cexp (2 * π * I * τ) * (fJ p.1 * fG p.2))]
  simp only [fJ, fG, term_identity]
  have hN : ∀ p ∈ Fib N, cexp (2 * π * I * τ * (((2 * p.1 + 1) ^ 2 + (2 * p.2) ^ 2 : ℤ) : ℂ)) =
      cexp (2 * π * I * τ) ^ N := by
    intro p hp
    rw [mem_Fib.mp hp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun p hp => by rw [hN p hp], ← Finset.sum_mul, sum_Fib_eq_heckeCoeff]

/-- **Hecke's theorem for `ψ₁` (modularity of `y² = x³ − x`)**, proved. -/
theorem cmForm32 : CMForm32 := cmForm32_of_etaThetaIdentity etaThetaIdentity

end ZInQ.GZTheta
