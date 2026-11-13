import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula

/-!
# T25 (`PkgI4.NewformOfEigenform`): the bridge to Tau Ceti's newform theory

Task t25-newform. The leaf T25 of `docs/research/h-decomposition.md` says that every normalized
eigenform `g` of level `M` (in the coefficient form `PkgI4.IsNormalizedEigenform`) has the Hecke
eigenvalues away from `M` of a newform (`PkgI4.IsNewform`) of some level `N ∣ M`.

It follows from Tau Ceti's
`HeckeRing.GL2.Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`
(Diamond–Shurman Prop. 5.8.4, eigenvalue half; vendored under `ZInQKernel/Contrib/TauCeti/`),
together with:

* `HeckeRing.GL2.heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul` (coefficients ⇒
  `T_p g = a_p(g) g` for `p ∤ M`);
* `mem_cuspFormCharSpace_iff_nebentypus` (Tau Ceti's diamond character space versus the slash
  form `PkgI4.HasNebentypus`);
* `HeckeRing.GL2.Newform.toEigenform` (a newform is an eigenform of every `T_n`, bad primes
  included) and the divisor-sum coefficient formula
  `HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0`, which give
  the leaf's identity `a_m a_n = ∑_{d ∣ (m,n)} χ(d) d^{k-1} a_{mn/d²}` for all `m, n`;
* `TauCeti.levelRaise_mem_cuspFormsOld` and `TauCeti.disjoint_cuspFormsOld_cuspFormsNew` (the
  leaf's `oldSpace`, a span of functions `τ ↦ f(dτ)`, lies in Tau Ceti's `cuspFormsOld`, which
  meets the new subspace only in `0`).

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace T25

open PkgI4 (CF coeff HasNebentypus IsNormalizedEigenform oldSpace IsNewform scaleH)

variable {N : ℕ} {k : ℤ}

/-! ### Slash action of `SL(2, ℤ)` versus `mapGL` -/

theorem slash_SL_eq_mapGL (f : UpperHalfPlane → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] mapGL ℝ γ := by
  rw [ModularForm.SL_slash]
  rfl

/-! ### Nebentypus: `PkgI4.HasNebentypus` versus `cuspFormCharSpace` -/

/-- The leaf's slash-form nebentypus `χ` (a Dirichlet character) puts a cusp form in Tau Ceti's
diamond character space of `MulChar.toUnitHom χ`. -/
theorem mem_cuspFormCharSpace_of_hasNebentypus [NeZero N] {f : CF N k}
    {χ : DirichletCharacter ℂ N} (h : HasNebentypus f χ) :
    f ∈ cuspFormCharSpace k (MulChar.toUnitHom χ) := by
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  intro g
  rw [← slash_SL_eq_mapGL, h (g : SL(2, ℤ)) g.2, MulChar.coe_toUnitHom]
  congr 2

/-- Tau Ceti's diamond character space of `χ₀` gives the leaf's slash-form nebentypus for the
zero extension `MulChar.ofUnitHom χ₀`. -/
theorem hasNebentypus_of_mem_cuspFormCharSpace [NeZero N] {f : CF N k}
    {χ₀ : (ZMod N)ˣ →* ℂˣ} (h : f ∈ cuspFormCharSpace k χ₀) :
    HasNebentypus f (MulChar.ofUnitHom χ₀) := by
  intro γ hγ
  have h' := (mem_cuspFormCharSpace_iff_nebentypus k χ₀ f).mp h ⟨γ, hγ⟩
  rw [slash_SL_eq_mapGL]
  refine h'.trans ?_
  congr 1
  rw [← MulChar.ofUnitHom_coe]
  congr 1

/-! ### `T_p`-eigenvectors from the coefficient identities -/

theorem coeff_zero (f : CF N k) : coeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)

theorem heckeTCuspNat_eq_coeff_smul [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenform g χ) {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) g = coeff g p • g := by
  rw [heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul hp hpN
    (mem_cuspFormCharSpace_of_hasNebentypus hg.1)]
  intro m
  change coeff g (p * m) = coeff g p * coeff g m - _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 := coeff_zero g
    simp only [coeff] at h0
    simp only [coeff, h0, mul_zero, Nat.zero_div, ite_self, sub_zero]
  have key := hg.2.2 p m hp.pos hm
  rw [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
  by_cases hpm : p ∣ m
  · obtain ⟨m', rfl⟩ := hpm
    have e1 : p * (p * m') / 1 ^ 2 = p * (p * m') := by simp
    have e2 : p * (p * m') / p ^ 2 = m' := by
      rw [← mul_assoc, ← pow_two, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
    have e3 : p * m' / p = m' := Nat.mul_div_cancel_left _ hp.pos
    rw [Nat.gcd_eq_left (dvd_mul_right p m'), hp.divisors, Finset.sum_pair hp.one_lt.ne, e1,
      e2] at key
    simp only [dvd_mul_right, ↓reduceIte, e3]
    simp only [Nat.cast_one, map_one, one_zpow, one_mul] at key
    change _ = _ - _ * _ * coeff g m'
    linear_combination -key
  · have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.divisors_one, Finset.sum_singleton] at key
    simp only [Nat.cast_one, map_one, one_zpow, one_mul, one_pow, Nat.div_one] at key
    simp only [hpm, ↓reduceIte, sub_zero]
    linear_combination -key

/-! ### The old space -/

/-- The coercion of cusp forms to functions, as a `ℂ`-linear map. -/
def coeL (N : ℕ) (k : ℤ) : CF N k →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem scaleGL_smul_eq_scaleH (d : ℕ+) (τ : UpperHalfPlane) :
    (TauCeti.scaleGL (d : ℕ) • τ) = scaleH d τ := by
  ext
  rw [TauCeti.coe_scaleGL_smul]
  rfl

/-- The leaf's old space lies in (the image of) Tau Ceti's `cuspFormsOld`. -/
theorem oldSpace_le_map_cuspFormsOld [NeZero N] :
    oldSpace N k ≤ (TauCeti.cuspFormsOld N k).map (coeL N k) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨M, d, f, hM0, hMN, hMlt, hdM, rfl⟩
  have : NeZero (d : ℕ) := ⟨d.ne_zero⟩
  refine ⟨_, TauCeti.levelRaise_mem_cuspFormsOld hdM hMlt.ne k f, ?_⟩
  funext τ
  simp [coeL, scaleGL_smul_eq_scaleH]

theorem not_mem_oldSpace [NeZero N] {f : CF N k} (hnew : f ∈ TauCeti.cuspFormsNew N k)
    (h0 : f ≠ 0) : (⇑f : UpperHalfPlane → ℂ) ∉ oldSpace N k := by
  intro hf
  obtain ⟨x, hx, hxf⟩ := oldSpace_le_map_cuspFormsOld hf
  have : x = f := DFunLike.coe_injective hxf
  subst this
  exact h0 ((Submodule.disjoint_def.mp (TauCeti.disjoint_cuspFormsOld_cuspFormsNew N k)) x hx hnew)

/-! ### The newform's coefficient identities -/

/-- A Tau Ceti newform satisfies the leaf's coefficient identities for all `m, n ≥ 1`, with its
zero-extended nebentypus: `T_n f = a_n(f) f` at every `n` (`Newform.toEigenform`) and the
divisor-sum formula for the coefficients of `T_n f`. -/
theorem newform_coeff_mul [NeZero N] (f : Newform N k) (m n : ℕ) (hn : 0 < n) :
    coeff f.toCuspForm m * coeff f.toCuspForm n =
      ∑ d ∈ (Nat.gcd m n).divisors, (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) d *
        (d : ℂ) ^ (k - 1) * coeff f.toCuspForm (m * n / d ^ 2) := by
  lift n to ℕ+ using hn
  have h := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 (N := N) (k := k)
    (χ := f.toEigenform.χ) (n := n) n.ne_zero
    ⟨f.toEigenform.toCuspForm, f.toEigenform.mem_charSpace⟩ m
  rw [f.toEigenform.isEigen n, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, smul_eq_mul, Newform.toEigenform_eigenvalue_eq_qExpansion_coeff]
    at h
  simp only [Newform.toEigenform_toCuspForm, Newform.toEigenform_χ] at h
  rw [mul_comm]
  exact h

/-! ### The leaf -/

/-- **T25** (`PkgI4.NewformOfEigenform`, unfolded): every normalized eigenform `g` of level `M`
with nebentypus `χ` has the Hecke eigenvalues away from `M` of a newform of some level
`N ∣ M`. -/
theorem newformOfEigenform :
    ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
      0 < M → IsNormalizedEigenform g χ →
      ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p := by
  intro M k χ g hM hg
  have : NeZero M := ⟨hM.ne'⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 := hg.2.1
    simp only [coeff, FunLike.coe_zero, qExpansion_zero, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨N, _, hNM, f, hf⟩ :=
    Newform.exists_newform_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul hg0
      (a := fun p _ _ => coeff g p) fun p hp hpM => heckeTCuspNat_eq_coeff_smul hg hp hpM
  refine ⟨N, MulChar.ofUnitHom f.χ, f.toCuspForm, Nat.pos_of_ne_zero (NeZero.ne N), hNM,
    ⟨⟨hasNebentypus_of_mem_cuspFormCharSpace f.mem_charSpace, f.isNorm,
      fun m n _ hn => newform_coeff_mul f m n hn⟩, not_mem_oldSpace f.isNew f.ne_zero⟩, ?_⟩
  intro p hp hpM
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  have h1 := f.toEigenform_eigenvalue_eq_qExpansion_coeff ⟨p, hp.pos⟩
  have h2 := EigenformAwayFromLevel.toEigenform_eigenvalue f.toEigenformAwayFromLevel
    (fun _ hq hqN ↦ ⟨_, f.heckeUCuspNat_eq_qExpansion_coeff_smul hq hqN⟩) ⟨p, hp.pos⟩
    (hcop.coprime_dvd_right hNM)
  rw [← hf p hp hcop]
  exact (h2.symm.trans h1).symm

end T25
