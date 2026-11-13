import ZInQKernel.Contrib.GZTheta.Final

/-!
# gz-theta: newness from level 32 and the Atkin–Li twist theorem; the headline

`NewCM` (newness of the theta series of `ψ_d` at level `32 d²`) follows from two standard facts:

* `NewAt32`: the theta series `f₁ = η(4τ)²η(8τ)²` of `ψ₁` is new at level 32 (the conductor of
  `y² = x³ − x` is 32);
* `AtkinLiTwistNew`: the twist of a newform of level `M` and trivial character by the quadratic
  character `(·/r)` (`r ≡ 1 mod 4` squarefree, prime to `M`) is new at level `M r²` (Atkin–Li,
  Invent. Math. 48 (1978), Thm 3.1; Shimura 1971, §3.6; UNVERIFIED locators).

`f_d = f₁ ⊗ (·/d)`, so `NewCM ⇐ NewAt32 ∧ AtkinLiTwistNew` (`newCM_of_newAt32_atkinLi`).
The file ends with the headline of the project with gz-decomp's leaves, L1 replaced by `NewCM`.
-/

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE

/-- **The theta series of `ψ₁` is new at level 32.** Every cusp form on `Γ₁(32)` with
coefficients `heckeCoeff 1 n` lies in Tau Ceti's new subspace. Not proved here. -/
def NewAt32 : Prop :=
  ∀ F : CuspForm ((Gamma1 32).map (mapGL ℝ)) 2,
    (∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n) → F ∈ TauCeti.cuspFormsNew 32 2

theorem dvd_twist_left (M r : ℕ) : M * r ∣ M * r ^ 2 := ⟨r, by ring⟩

theorem dvd_twist_right (M r : ℕ) : r * r ∣ M * r ^ 2 := ⟨M, by ring⟩

/-- **Atkin–Li: twisting a newform by a primitive quadratic character of coprime conductor.**
For a newform `g` of level `M`, weight 2 and trivial character, and `r ≡ 1 (mod 4)` squarefree
prime to `M`, the twist `g ⊗ (·/r)` (Tau Ceti `CuspForm.twist`) is new at level `M r²`.
Literature: A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
W-operators*, Invent. Math. 48 (1978), Theorem 3.1; G. Shimura, *Introduction to the arithmetic
theory of automorphic functions* (1971), Prop. 3.64 (UNVERIFIED locators). Not proved here. -/
def AtkinLiTwistNew : Prop :=
  ∀ (M : ℕ) [NeZero M] (g : Newform M 2), g.χ = 1 →
    ∀ (r : ℕ) [NeZero r], r % 4 = 1 → Squarefree r → Nat.Coprime r M →
      CuspForm.twist (jacobiChar r) (dvd_twist_left M r) (dvd_twist_right M r) g.toCuspForm ∈
        TauCeti.cuspFormsNew (M * r ^ 2) 2

/-- The coefficients of `etaForm32`. -/
theorem qExpansion_etaForm32_coeff (n : ℕ) : (qExpansion 1 etaForm32).coeff n = heckeCoeff 1 n := by
  have key : ∀ τ : ℍ, HasSum (fun m : ℕ => heckeCoeff 1 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (etaForm32 τ) := by
    intro τ
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * τ) := by
      simp [Function.Periodic.qParam]
    simpa [hq, smul_eq_mul, coe_etaForm32, etaQuot32] using etaThetaIdentity τ
  exact (ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma0_map 32) key n).symm

/-- `f₁` restricted to `Γ₁(32)` is an eigenform away from the level. -/
theorem exists_eigenformAway32 :
    ∃ E : EigenformAwayFromLevel 32 2, E.toCuspForm = restrict32 etaForm32 ∧ E.χ = 1 := by
  have hc : ∀ n, (qExpansion 1 (restrict32 etaForm32)).coeff n = heckeCoeff 1 n := fun n => by
    rw [qExpansion_restrict32, qExpansion_etaForm32_coeff]
  refine EigenformAwayFromLevel.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two
    (TauCeti.restrict_mem_cuspFormCharSpace_one (N := 32) (k := 2) etaForm32) ?_
    (fun u v huv => ?_) (fun p hp hpN r => ?_)
  · intro h0
    have h1 := hc 1
    rw [h0, heckeCoeff_one] at h1
    simp [qExpansion_zero] at h1
  · simp only [hc]
    exact heckeMult 1 u v huv
  · simp only [hc]
    have hp2 : ¬ p ∣ 2 * 1 := by
      intro h
      have h2 : 2 * 1 ∣ 32 := ⟨16, rfl⟩
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (hpN.coprime_dvd_right h2) h
    rw [heckePrimePow' (by norm_num) squarefree_one p hp r, ite_eq_right hp2]
    simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    norm_num

/-- **`NewCM` from newness at level 32 and Atkin–Li.** -/
theorem newCM_of_newAt32_atkinLi (h32 : NewAt32) (hAL : AtkinLiTwistNew) : NewCM := by
  intro d _ hd4 hsq F hF
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway32
  have hc : ∀ n, (qExpansion 1 (restrict32 etaForm32)).coeff n = heckeCoeff 1 n := fun n => by
    rw [qExpansion_restrict32, qExpansion_etaForm32_coeff]
  let g₁ : Newform 32 2 :=
    ⟨E, by rw [hE]; exact h32 _ hc, by rw [hE, hc 1, heckeCoeff_one]⟩
  have hcop : Nat.Coprime d 32 := by
    have hodd : Odd d := odd_of_mod_four hd4
    have : Nat.Coprime d (2 ^ 5) := Nat.Coprime.pow_right 5 (Nat.coprime_two_right.mpr hodd)
    simpa using this
  have hnew := hAL 32 g₁ hEχ d hd4 hsq hcop
  have hFeq : F = CuspForm.twist (jacobiChar d) (dvd_twist_left 32 d) (dvd_twist_right 32 d)
      g₁.toCuspForm := by
    apply CuspForm.qExpansion_injective one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)
    ext n
    show (qExpansion 1 F).coeff n = (qExpansion 1 (CuspForm.twist (jacobiChar d)
      (dvd_twist_left 32 d) (dvd_twist_right 32 d) g₁.toCuspForm)).coeff n
    rw [hF, CuspForm.qExpansion_twist_coeff]
    have : g₁.toCuspForm = restrict32 etaForm32 := hE
    rw [this, hc, jacobiChar_natCast, heckeCoeff_eq_jacobiSym_mul]
  rw [hFeq]
  exact hnew

/-- **The leaf from newness at level 32 and Atkin–Li.** -/
theorem heckeThetaNewform_of_newAt32_atkinLi (h32 : NewAt32) (hAL : AtkinLiTwistNew) :
    ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_newCM (newCM_of_newAt32_atkinLi h32 hAL)

/-- **The headline with gz-decomp's leaves, L1 reduced to newness.** -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_newCM_gzLeaves (hH : ZInQ.SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hnew : NewCM) (hL2 : ZInQ.GZDecomp.FHNonvanishing)
    (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) : ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves hH hA
    (heckeThetaNewform_of_newCM hnew) hL2 hL3

end ZInQ.GZTheta
