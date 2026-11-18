import ZInQKernel.Contrib.OneProof.RC.AppE.Ramsey

/-!
# Appendix E: the Galois comparison, `a(D)/(a(D₀) z_D) ∈ ℚ`

The 11/5 manuscript, Appendix E, tex 8086–8134. Let `g` lie in the full good-Hecke eigenspace of
`E` and `η = ψχ_{−σ}` at a level `N`, with `a_g(D₀) ≠ 0`. Elliot's argument:

1. (tex 8060–8083) the eigenspace contains an algebraic `g'` with `a_{g'}(D₀) = 1`
   (`exists_algebraic_normalized`, from Ramsey's model);
2. (tex 8086–8091) for `τ ∈ Aut(ℚ̄/ℚ)` choose an odd `e` with `τ(ζ) = ζ^e` on the values of `ψ`
   and `η` (`exists_odd_exponent`), put `ν = η^{(e−1)/2}`;
3. (tex 8090–8093) `g'^τ` has character `ψ^e` and good eigenvalues `η(p)^e a_p(E)`
   (`conj_mem_eigenspace`, from Ramsey's conjugation clause);
4. (tex 8099–8103) the twist `g' ⊗ ν` has character `ψν² = ψ^e` and the same eigenvalues
   (`twist_mem_eigenspace`, from the twisting statement `HalfIntegralTwist`, GLUE, see below);
5. (tex 8104–8113) at a common level both lie in one full eigenspace, so the full-space comparison
   gives `τ(a(D)) = ν(D/D₀) a(D)` (`galois_identity`);
6. (tex 8114–8132) `ν(D/D₀) = z_D^{e−1}` and `τ(z_D) = z_D^e`, so `a(D)/z_D` is fixed by every `τ`,
   hence rational (`rational_of_ramsey`).

**`HalfIntegralTwist` (GLUE, not proved; a hypothesis of `rational_of_ramsey`).** The manuscript:
"The twist is modular at a level still supported on `S₀`; this follows as well by writing it as the
finite additive translation sum using the Gauss sum of the primitive character inducing `ν`"
(tex 8101–8103). Proving it on lane RC8's definitions needs the transformation formula of the
theta multiplier `j(γ, z)` on `Γ₀(4)` (`j(γ, z) = ε_d^{-1} (c/d) √(cz+d)`, Shimura 1973, §1), to see
that `j(γ', z + u'/m) = j(γ, z)` for the conjugate `γ' = T^{u/m} γ T^{−u'/m}`; that formula is not in
Mathlib (it is the theta transformation law with quadratic reciprocity, a few thousand lines). The
statement is the standard twisting lemma (Shimura, Ann. of Math. 97 (1973), Lemma 3.6, for
primitive characters, locator UNVERIFIED; for an imprimitive `ν` add the sieve to indices prime to
`N`, which is the twist by the trivial character modulo each prime of `N`).

Everything else here is PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane
  CongruenceSubgroup
open scoped MatrixGroups

/-- **Twisting a weight-`3/2` form by a character** (GLUE, missing theory; tex 8099–8103; the
standard lemma is Shimura, Ann. of Math. 97 (1973), Lemma 3.6, UNVERIFIED). For a cusp form `f` of
weight `3/2`, level `N > 0` (`4 ∣ N`) and character `ψ`, and a Dirichlet character `ν` modulo `N`,
the coefficientwise twist `Σ ν(n) a_f(n) qⁿ` is a cusp form of weight `3/2` and character `ψν²` at
a level `M` with `N ∣ M` and the same prime support as `N`. -/
def HalfIntegralTwist : Prop :=
  ∀ N : ℕ, 0 < N → 4 ∣ N → ∀ ψ ν : DirichletCharacter ℂ N, ∀ f : ℍ → ℂ,
    IsHalfIntegralWeightCuspForm 3 N ψ f →
    ∃ (M : ℕ) (hNM : N ∣ M), 0 < M ∧ (∀ p : ℕ, p.Prime → p ∣ M → p ∣ N) ∧
      ∃ f' : ℍ → ℂ, IsHalfIntegralWeightCuspForm 3 M ((ψ * ν ^ 2).changeLevel hNM) f' ∧
        ∀ n : ℕ, hiwCoeff f' n = ν n * hiwCoeff f n

/-! ## Level raising -/

/-- The lower-right entry of `γ ∈ Γ₀(M)` is prime to `M` (PROVED: `ad − bc = 1`, `M ∣ c`). -/
theorem isCoprime_d_of_mem_Gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    IsCoprime (γ 1 1 : ℤ) (M : ℤ) := by
  rw [Gamma0_mem] at hγ
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨γ 0 0, -(γ 0 1 * t), ?_⟩
  rw [ht] at hdet
  linear_combination hdet

theorem Gamma0_mono {N M : ℕ} (h : N ∣ M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : γ ∈ Gamma0 N := by
  rw [Gamma0_mem] at hγ ⊢
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
  exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h) _

/-- **A form of level `N` is a form of level `M` for `N ∣ M`** (PROVED), with the character
`χ` lifted to level `M`. -/
theorem hiwForm_changeLevel {k N M : ℕ} {χ : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsHalfIntegralWeightCuspForm k N χ g) (h : N ∣ M) :
    IsHalfIntegralWeightCuspForm k M (χ.changeLevel h) g := by
  refine ⟨hg.1, fun γ hγ z => ?_, hg.2.2⟩
  rw [hg.2.1 γ (Gamma0_mono h hγ) z,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' χ h (isCoprime_d_of_mem_Gamma0 hγ)]

/-- A prime `p ∤ M` is prime to `M`, as an integer (PROVED). -/
theorem isCoprime_of_prime_not_dvd {p M : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    IsCoprime (p : ℤ) (M : ℤ) :=
  Int.isCoprime_iff_gcd_eq_one.mpr (by
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)

theorem changeLevel_apply_prime {N M : ℕ} (χ : DirichletCharacter ℂ N) (h : N ∣ M) {p : ℕ}
    (hp : p.Prime) (hpM : ¬ p ∣ M) : χ.changeLevel h p = χ p := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ h (isCoprime_of_prime_not_dvd hp hpM)
  simpa using this

theorem changeLevel_apply_coprime {N M : ℕ} (χ : DirichletCharacter ℂ N) (h : N ∣ M) {n : ℕ}
    (hn : n.Coprime M) : χ.changeLevel h n = χ n := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ h
    (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_natCast_natCast]; exact hn))
  simpa using this

/-- `T(p²)` at a good prime does not see the level (PROVED). -/
theorem heckeT3_changeLevel {N M : ℕ} (χ : DirichletCharacter ℂ N) (h : N ∣ M) {p : ℕ}
    (hp : p.Prime) (hpM : ¬ p ∣ M) (a : ℕ → ℂ) (n : ℕ) :
    heckeT3 M (χ.changeLevel h) p a n = heckeT3 N χ p a n := by
  unfold heckeT3
  rw [changeLevel_apply_prime χ h hp hpM]

/-- **The eigenspace at level `N` lies in the eigenspace at level `M`** (PROVED). -/
theorem eigen_changeLevel {E : WeierstrassCurve ℚ} {N M : ℕ} {ψ η : DirichletCharacter ℂ N}
    {g : ℍ → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) (h : N ∣ M) :
    IsInWaldspurgerEigenspace E M (ψ.changeLevel h) (η.changeLevel h) g := by
  refine ⟨hiwForm_changeLevel hg.1 h, fun p hp hpM n => ?_⟩
  have hpN : ¬ p ∣ N := fun hpN => hpM (dvd_trans hpN h)
  rw [heckeT3_changeLevel ψ h hp hpM, hg.2 p hp hpN n, changeLevel_apply_prime η h hp hpM]

/-! ## The quadratic character `χ_{−σ}` on integers prime to the level -/

/-- `χ_{−σ}(n)² = 1` for `n` prime to `N`, `4 ∣ N` (PROVED). -/
theorem kronecker_sq_of_coprime {N : ℕ} (h4 : 4 ∣ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {n : ℕ}
    (hn : n.Coprime N) : kronecker (-σ) n ^ 2 = 1 := by
  have h2N : 2 ∣ N := dvd_trans (by norm_num) h4
  have hn2 : ¬ 2 ∣ n := fun h => by
    have := Nat.Coprime.coprime_dvd_left h hn
    rw [Nat.Coprime, Nat.gcd_eq_left h2N] at this
    omega
  have hfac : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hn2
  unfold kronecker
  rw [hfac, pow_zero, pow_zero, one_mul, Nat.div_one]
  apply jacobiSym.sq_one
  rcases hσ with rfl | rfl <;> simp

theorem kronecker_cpx_sq {N : ℕ} (h4 : 4 ∣ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {n : ℕ}
    (hn : n.Coprime N) : ((kronecker (-σ) n : ℤ) : ℂ) ^ 2 = 1 := by
  exact_mod_cast kronecker_sq_of_coprime h4 hσ hn

/-- `η² = ψ²` as Dirichlet characters, since `ψ/η = χ_{−σ}` is quadratic (PROVED). -/
theorem eta_sq_eq {N : ℕ} [NeZero N] (h4 : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)) :
    η ^ 2 = ψ ^ 2 := by
  refine MulChar.ext fun u => ?_
  have hn := ZMod.val_coe_unit_coprime u
  have hu : (((u : ZMod N).val : ℕ) : ZMod N) = (u : ZMod N) := ZMod.natCast_zmod_val _
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.pow_apply' _ two_ne_zero, ← hu, hψη _ hn, mul_pow,
    kronecker_cpx_sq h4 hσ hn, mul_one]

/-- `ψ ν² = ψ^e` and `η ν² = η^e` for `ν = η^{(e−1)/2}`, `e` odd (PROVED; tex 8099–8100: "The
identities hold because `ψ/η` is quadratic"). -/
theorem twist_chars {N : ℕ} [NeZero N] (h4 : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {e : ℕ} (he : Odd e) :
    ψ * (η ^ ((e - 1) / 2)) ^ 2 = ψ ^ e ∧ η * (η ^ ((e - 1) / 2)) ^ 2 = η ^ e := by
  obtain ⟨k, rfl⟩ := he
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  rw [hk, ← pow_mul, mul_comm k 2, pow_mul, eta_sq_eq h4 ψ η hσ hψη, ← pow_mul]
  refine ⟨by rw [pow_succ'], ?_⟩
  rw [pow_mul, ← eta_sq_eq h4 ψ η hσ hψη, ← pow_mul, pow_succ']

/-! ## The Galois exponent `e` (tex 8086–8088) -/

/-- **An odd exponent describing `τ` on roots of unity** (PROVED): for `K > 0` and
`τ ∈ Aut(ℚ̄/ℚ)` there is an odd `e` with `τ(x) = x^e` for every `x ∈ ℚ̄` with `x^K = 1`. -/
theorem exists_odd_exponent (τ : Qbar ≃ₐ[ℚ] Qbar) {K : ℕ} (hK : 0 < K) :
    ∃ e : ℕ, Odd e ∧ ∀ x : Qbar, x ^ K = 1 → τ x = x ^ e := by
  set K' := 2 * K with hK'
  have hK'0 : K' ≠ 0 := by omega
  have : NeZero K' := ⟨hK'0⟩
  -- a primitive `K'`-th root of unity in `ℚ̄`
  have hζ := Complex.isPrimitiveRoot_exp K' hK'0
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / K') with hζdef
  have hζmem : ζ ∈ Qbar := mem_Qbar_of_pow_eq_one (Nat.pos_of_ne_zero hK'0) hζ.pow_eq_one
  set μ : Qbar := ⟨ζ, hζmem⟩
  have hμ : IsPrimitiveRoot μ K' := by
    have hinj : Function.Injective (algebraMap Qbar ℂ) := (algebraMap Qbar ℂ).injective
    exact (IsPrimitiveRoot.map_iff_of_injective hinj).mp hζ
  set u := hμ.autToPow ℚ τ
  refine ⟨(u : ZMod K').val, ?_, ?_⟩
  · -- `e` is prime to the even `K'`
    have hcop := ZMod.val_coe_unit_coprime u
    rw [Nat.odd_iff]
    by_contra hne
    have h2 : 2 ∣ (u : ZMod K').val := by omega
    have := Nat.Coprime.coprime_dvd_left h2 hcop
    rw [Nat.Coprime, Nat.gcd_eq_left (dvd_mul_right 2 K)] at this
    omega
  · intro x hx
    have hx' : x ^ K' = 1 := by rw [hK', pow_mul', hx, one_pow]
    obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hx'
    rw [map_pow, ← hμ.autToPow_spec ℚ τ, ← pow_mul, ← pow_mul, mul_comm]

/-- The values of a Dirichlet character modulo `N` are `φ(N)`-th roots of unity or `0`, so `τ`
acts on them by `x ↦ x^e` (PROVED). -/
theorem tau_dirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (τ : Qbar ≃ₐ[ℚ] Qbar)
    {e : ℕ} (he : Odd e)
    (hτ : ∀ x : Qbar, x ^ Fintype.card (ZMod N)ˣ = 1 → τ x = x ^ e)
    (n : ZMod N) (x : Qbar) (hx : χ n = (x : ℂ)) : ((τ x : Qbar) : ℂ) = χ n ^ e := by
  by_cases hn : IsUnit n
  · obtain ⟨v, rfl⟩ := hn
    have hpow : x ^ Fintype.card (ZMod N)ˣ = 1 := by
      apply Subtype.ext
      rw [IntermediateField.coe_pow, ← hx, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
        Units.val_one, map_one]
      rfl
    rw [hτ x hpow, IntermediateField.coe_pow, hx]
  · have hx0 : x = 0 := by
      apply Subtype.ext
      rw [← hx, χ.map_nonunit hn]
      rfl
    rw [hx0, map_zero, χ.map_nonunit hn, zero_pow (Nat.pos_of_ne_zero (by
      rintro rfl; exact absurd he (by decide))).ne']
    rfl

/-! ## The conjugate form (tex 8090–8093) -/

/-- `T(p²)` of a coefficient sequence `f ∘ A` (`f : ℚ̄ →+* ℂ`) is `f` of the same expression in
`ℚ̄` (PROVED). -/
theorem heckeT3_map {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) (f : Qbar →+* ℂ)
    (A : ℕ → Qbar) (P : Qbar) (hP : χ p = f P) (n : ℕ) :
    heckeT3 N χ p (fun m => f (A m)) n =
      f (A (p ^ 2 * n) + P * (jacobiSym (-(n : ℤ)) p : Qbar) * A n +
        P ^ 2 * (p : Qbar) * (if p ^ 2 ∣ n then A (n / p ^ 2) else 0)) := by
  unfold heckeT3
  rw [hP]
  split_ifs <;> simp [map_add, map_mul, map_pow, map_intCast, map_natCast]

/-- **The conjugate `g^τ` lies in the eigenspace of `ψ^e`, `η^e`** (tex 8090–8093; PROVED from
the PRINT `RamseyAlgebraicModel`, clause (R-conj)): coefficientwise conjugation of an algebraic `g`
in the eigenspace of `ψ, η` gives a form with character `ψ^e` and good eigenvalues
`η(p)^e a_p(E)`, whose coefficients are `τ(a_g(n))`. -/
theorem conj_mem_eigenspace (hR : RamseyAlgebraicModel) {E : WeierstrassCurve ℚ} {N : ℕ}
    [NeZero N] (hN : 4 ∣ N) {ψ η : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsInWaldspurgerEigenspace E N ψ η g) (halg : HasAlgebraicCoeffs g)
    (τ : Qbar ≃ₐ[ℚ] Qbar) {e : ℕ} (he : Odd e)
    (hτ : ∀ x : Qbar, x ^ Fintype.card (ZMod N)ˣ = 1 → τ x = x ^ e) :
    ∃ g' : ℍ → ℂ, IsInWaldspurgerEigenspace E N (ψ ^ e) (η ^ e) g' ∧
      ∀ (n : ℕ) (x : Qbar), hiwCoeff g n = (x : ℂ) → hiwCoeff g' n = ((τ x : Qbar) : ℂ) := by
  have hN0 : 0 < N := NeZero.pos N
  have he0 : e ≠ 0 := by rintro rfl; exact absurd he (by decide)
  have hψe : ∀ (n : ZMod N) (x : Qbar), ψ n = (x : ℂ) → (ψ ^ e) n = ((τ x : Qbar) : ℂ) := by
    intro n x hx
    rw [MulChar.pow_apply' _ he0, tau_dirichlet ψ τ he hτ n x hx]
  obtain ⟨g', hg'S, hg'c⟩ := (hR N hN0 hN ψ).2 τ (ψ ^ e) hψe g hg.1 halg
  refine ⟨g', ⟨hg'S, fun p hp hpN n => ?_⟩, hg'c⟩
  -- the coefficients as elements of `ℚ̄`
  let A : ℕ → Qbar := fun m => ⟨hiwCoeff g m, halg m⟩
  let ι : Qbar →+* ℂ := algebraMap Qbar ℂ
  let φ : Qbar →+* ℂ := ι.comp τ.toRingEquiv.toRingHom
  have hιA : hiwCoeff g = fun m => ι (A m) := rfl
  have hφA : hiwCoeff g' = fun m => φ (A m) := funext fun m => hg'c m (A m) rfl
  let P : Qbar := ⟨ψ p, dirichlet_mem_Qbar ψ p⟩
  let H : Qbar := ⟨η p, dirichlet_mem_Qbar η p⟩
  have hT := hg.2 p hp hpN n
  rw [hιA, heckeT3_map ψ p ι A P rfl n] at hT
  -- the Hecke equation in `ℚ̄`
  have hQ : A (p ^ 2 * n) + P * (jacobiSym (-(n : ℤ)) p : Qbar) * A n +
      P ^ 2 * (p : Qbar) * (if p ^ 2 ∣ n then A (n / p ^ 2) else 0) =
      H * ((E.LFunction p : ℤ) : Qbar) * A n := by
    apply ι.injective
    rw [hT]
    simp [ι, H, lcoeff]
  have hφP : (ψ ^ e) p = φ P := (hψe p P rfl)
  have hφH : (η ^ e) p = φ H := by
    rw [MulChar.pow_apply' _ he0, ← tau_dirichlet η τ he hτ p H rfl]
    rfl
  rw [hφA, heckeT3_map (ψ ^ e) p φ A P hφP n, hQ, hφH]
  simp [lcoeff]

/-! ## The twisted form (tex 8094–8103) -/

/-- **The twist `g ⊗ ν` lies in the eigenspace of `ψν²`, `ην²`** (tex 8099–8103; PROVED from the
GLUE `HalfIntegralTwist`): at the level `M` of the twist, the good `T(p²)` eigenvalues of
`Σ ν(n) a(n) qⁿ` are `η(p)ν(p)² a_p(E)`. -/
theorem twist_mem_eigenspace (hT : HalfIntegralTwist) {E : WeierstrassCurve ℚ} {N : ℕ}
    (hN0 : 0 < N) (hN : 4 ∣ N) {ψ η : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsInWaldspurgerEigenspace E N ψ η g) (ν : DirichletCharacter ℂ N) :
    ∃ (M : ℕ) (hNM : N ∣ M), 0 < M ∧ (∀ p : ℕ, p.Prime → p ∣ M → p ∣ N) ∧
      ∃ f' : ℍ → ℂ, IsInWaldspurgerEigenspace E M ((ψ * ν ^ 2).changeLevel hNM)
          ((η * ν ^ 2).changeLevel hNM) f' ∧
        ∀ n : ℕ, hiwCoeff f' n = ν n * hiwCoeff g n := by
  obtain ⟨M, hNM, hM0, hsupp, f', hf'S, hf'c⟩ := hT N hN0 hN ψ ν g hg.1
  refine ⟨M, hNM, hM0, hsupp, f', ⟨hf'S, fun p hp hpM n => ?_⟩, hf'c⟩
  have hpN : ¬ p ∣ N := fun h => hpM (dvd_trans h hNM)
  have hc : hiwCoeff f' = fun m : ℕ => ν m * hiwCoeff g m := funext hf'c
  rw [heckeT3_changeLevel _ hNM hp hpM, changeLevel_apply_prime _ hNM hp hpM, hc]
  have hE := hg.2 p hp hpN n
  unfold heckeT3 at hE ⊢
  simp only [MulChar.coeToFun_mul, Pi.mul_apply] at *
  split_ifs at hE ⊢ with hdiv
  · obtain ⟨m, rfl⟩ := hdiv
    have hm : p ^ 2 * m / p ^ 2 = m :=
      Nat.mul_div_cancel_left m (pow_pos hp.pos 2)
    rw [hm] at hE ⊢
    push_cast at hE ⊢
    simp only [map_mul, map_pow, MulChar.pow_apply' _ two_ne_zero]
    linear_combination (ν p ^ 2 * (ν p ^ 2 * ν m)) * hE
  · push_cast at hE ⊢
    simp only [map_mul, map_pow, MulChar.pow_apply' _ two_ne_zero]
    linear_combination (ν p ^ 2 * ν n) * hE

end ZInQ.Manuscript.RC.AppE
