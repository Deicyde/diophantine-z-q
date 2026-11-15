import ZInQKernel.Contrib.OneProof.LeafAudit1115H29
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice

noncomputable section

/-! ## TYZ leaves (h29-ne3) -/

namespace ZInQ.Contrib.TYZDecomp.H29Split.LeafAudit1115

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp NumberField
open IsDedekindDomain
open scoped Quaternion TensorProduct FiniteAdeleExtension

/-- A sign choice of `𝓛` from TYZ Theorem 1.1 (the open hypothesis `h11 : TYZThm11Integral`). -/
def lcalOf (h11 : TYZThm11Integral) (m : ℕ) : ℤ :=
  open Classical in
  if h : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) then (h11 m h.1 h.2).choose else 0

theorem isLcalSign_lcalOf (h11 : TYZThm11Integral) : IsLcalSign (lcalOf h11) := by
  intro m hm hc
  have h : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) := ⟨hm, hc⟩
  simp only [lcalOf, dif_pos h]
  exact (h11 m h.1 h.2).choose_spec

/-- **Non-vacuity of `TYZLemma29PrintedNe3` and `TYZThm21At31`, relative to their sibling leaves**: at every
squarefree `1 < n ≡ 1, 3 (mod 8)` (e.g. `n = 3` for `TYZThm21At31`, `n = 11` for `TYZLemma29PrintedNe3`) the
quantified objects exist: an admissible `τ` (from Legendre and Jones–Pall), a nonzero test vector
(`TYZTestVectorExists`) and a sign choice `ℓ` of `𝓛` (`TYZThm11Integral`, the open hypothesis `h11`). -/
theorem tyz_premises (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hT : TYZTestVectorExists)
    (h11 : TYZThm11Integral) (n : ℕ) [NeZero n] (hsq : Squarefree n) (h1 : 1 < n)
    (hcl : n % 8 = 1 ∨ n % 8 = 3) :
    ∃ (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (ℓ : ℕ → ℤ),
      AdmissibleTau n τ ∧ IsTestVector n τ f ∧ (∃ x : ℍ[AQ]ˣ, f x ≠ 0) ∧ IsLcalSign ℓ := by
  obtain ⟨τ, hτ⟩ := tyzTauExists_of_legendreJonesPall (legendreJonesPall_of hL hJ) n hsq hcl
  obtain ⟨f, hf, hx⟩ := hT n hsq h1 hcl τ hτ
  exact ⟨τ, f, lcalOf h11, hτ, hf, hx, isLcalSign_lcalOf h11⟩

theorem squarefree_three : Squarefree 3 := Nat.prime_three.squarefree
theorem squarefree_eleven : Squarefree 11 := (by norm_num : Nat.Prime 11).squarefree

example (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hT : TYZTestVectorExists)
    (h11 : TYZThm11Integral) :
    ∃ (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (ℓ : ℕ → ℤ),
      AdmissibleTau 3 τ ∧ IsTestVector 3 τ f ∧ (∃ x : ℍ[AQ]ˣ, f x ≠ 0) ∧ IsLcalSign ℓ :=
  tyz_premises hL hJ hT h11 3 squarefree_three (by norm_num) (Or.inr rfl)

example (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hT : TYZTestVectorExists)
    (h11 : TYZThm11Integral) :
    ∃ (τ : QNeg 11 →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (ℓ : ℕ → ℤ),
      AdmissibleTau 11 τ ∧ IsTestVector 11 τ f ∧ (∃ x : ℍ[AQ]ˣ, f x ≠ 0) ∧ IsLcalSign ℓ :=
  tyz_premises hL hJ hT h11 11 squarefree_eleven (by norm_num) (Or.inr rfl)

/-- **Not stronger (1/2):** h29-fix's `TYZLemma29Printed` (the `w_K` form it replaces) implies the new print
`TYZLemma29PrintedNe3`. -/
theorem ne3_of_printed (h : TYZLemma29Printed) : TYZLemma29PrintedNe3 := by
  intro n _ hsq h1 h3 hcl τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, he⟩ := h n hsq h1 hcl τ hτ f hf ℓ hℓ
  refine ⟨ε, hε, ?_⟩
  have hw : wK n = 1 := by simp [wK, h3]
  rw [hw, one_mul] at he
  exact he

/-- **Not stronger (2/2):** `TYZLemma29Printed` implies `TYZThm21At31`. -/
theorem thm21At31_of_printed (h : TYZLemma29Printed) : TYZThm21At31 := by
  intro τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, he⟩ := h 3 squarefree_three (by norm_num) (Or.inr rfl) τ hτ f hf ℓ hℓ
  refine ⟨ε 1, hε 1, ?_⟩
  rw [pairIdx_three_eq, Finset.sum_singleton, Nat.div_one, wK_three_eq_torsionOrder,
    genusPeriodTV_three] at he
  rw [← he]
  ring

/-- The two new leaves are equivalent to h29-fix's `TYZLemma29Printed` (with h29-ne3's
`tyzLemma29Printed_of_ne3_thm21`). -/
theorem printed_iff : TYZLemma29Printed ↔ TYZLemma29PrintedNe3 ∧ TYZThm21At31 :=
  ⟨fun h => ⟨ne3_of_printed h, thm21At31_of_printed h⟩,
    fun h => tyzLemma29Printed_of_ne3_thm21 h.1 h.2⟩

end ZInQ.Contrib.TYZDecomp.H29Split.LeafAudit1115

/-! ## X0ModuliGaloisMero (gz-heegner) -/

namespace ZInQ.GZHeegner.LeafAudit1115

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2 WeierstrassCurve
  ZInQ.Contrib.TYZDecomp.CurveA

theorem pp_I : T5Glue.pp UpperHalfPlane.I = ZInQ.GZWeil.squarePP := rfl

theorem jL_pp_I : T5Glue.jL (T5Glue.pp UpperHalfPlane.I) = 1728 := by
  rw [pp_I, T5Glue.jL, T5Glue.discL, ZInQ.GZWeil.g₃_squarePP]
  have h2 := ZInQ.GZWeil.g₂_ne_zero_of_g₃_eq_zero _ ZInQ.GZWeil.g₃_squarePP
  field_simp
  ring

theorem isRatModFnMero_one : IsRatModFnMero 1 (fun _ => (1 : ℂ)) := by
  refine ⟨fun γ _ τ => rfl, fun τ => analyticAt_const.meromorphicAt, fun γ => ⟨0, ?_⟩,
    ⟨0, fun n => if n = 0 then 1 else 0, 0, fun τ _ => ?_⟩⟩
  · simp only [CharP.cast_eq_zero, mul_zero, zero_mul, Real.exp_zero]
    exact Asymptotics.isBigO_const_const _ one_ne_zero _
  · rw [pow_zero, one_mul]
    convert hasSum_single (f := fun n : ℕ => ((if n = 0 then 1 else 0 : ℚ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) 0 (fun b hb => by simp [hb]) using 1
    simp

/-- **Non-vacuity of `X0ModuliGaloisMero`:** all its hypotheses are met at `N = 1`, `g = 1`, `σ = id`,
`τ = τ' = i`, `μ = 1` (the moduli coordinate `j(i) = 1728` is algebraic). -/
theorem x0ModuliGaloisMero_premises :
    ∃ (g : UpperHalfPlane → ℂ) (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      IsRatModFnMero 1 g ∧ RegularAt g τ ∧ RegularAt g τ' ∧
      (∀ i < 1, ∃ a : Qbar, ιC a = T5Glue.modCoord 1 τ i) ∧
      T5Glue.IsConjModel (σ : ℂ →+* ℂ) (T5Glue.pp τ) (T5Glue.pp τ') μ := by
  refine ⟨fun _ => 1, RingEquiv.refl ℂ, UpperHalfPlane.I, UpperHalfPlane.I, 1, isRatModFnMero_one,
    analyticAt_const, analyticAt_const, fun i hi => ⟨1728, ?_⟩, ⟨one_ne_zero, by simp, by simp⟩⟩
  obtain rfl : i = 0 := by omega
  rw [T5Glue.modCoord_zero, jL_pp_I, map_ofNat]

end ZInQ.GZHeegner.LeafAudit1115
