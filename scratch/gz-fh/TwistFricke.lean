import ZInQKernel.Contrib.OneProof.FHNonvanishing.FE

open HeckeRing.GL2 CongruenceSubgroup ZMod

namespace ZInQ.GZFH

open ZInQ.GZDecomp

/-! ## The character `χ_D` on `ZMod |D|` and its Fourier transform -/

section Character

variable {D : ℤ}

theorem chiDMod_eq (x : ZMod D.natAbs) : chiDMod D x = (jacobiSym (x.val : ℤ) D.natAbs : ℂ) := rfl

theorem chiDMod_intCast [NeZero D.natAbs] (n : ℤ) :
    chiDMod D (n : ZMod D.natAbs) = (jacobiSym n D.natAbs : ℂ) := by
  rw [chiDMod_eq, ZMod.val_intCast, ← jacobiSym.mod_left]

theorem chiDMod_mul [NeZero D.natAbs] (x y : ZMod D.natAbs) :
    chiDMod D (x * y) = chiDMod D x * chiDMod D y := by
  have hx : x = ((x.val : ℤ) : ZMod D.natAbs) := by simp
  have hy : y = ((y.val : ℤ) : ZMod D.natAbs) := by simp
  rw [hx, hy, ← Int.cast_mul, chiDMod_intCast, chiDMod_intCast, chiDMod_intCast,
    jacobiSym.mul_left]
  push_cast; ring

theorem chiDMod_one [NeZero D.natAbs] : chiDMod D 1 = 1 := by
  rw [show (1 : ZMod D.natAbs) = ((1 : ℤ) : ZMod D.natAbs) by simp, chiDMod_intCast,
    jacobiSym.one_left]; simp

theorem chiDMod_unit [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D u = 1 ∨ chiDMod D u = -1 := by
  rw [chiDMod_eq]
  have h := ZMod.val_coe_unit_coprime u
  rcases jacobiSym.eq_one_or_neg_one (a := ((u : ZMod D.natAbs).val : ℤ)) (b := D.natAbs)
    (by rw [Int.gcd_natCast_natCast]; exact h) with h1 | h1
  · left; rw [h1]; simp
  · right; rw [h1]; simp

theorem chiDMod_unit_sq [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D u * chiDMod D u = 1 := by
  rcases chiDMod_unit u with h | h <;> rw [h] <;> norm_num

theorem chiDMod_inv [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    chiDMod D (↑u⁻¹ : ZMod D.natAbs) = chiDMod D u := by
  have h1 : chiDMod D u * chiDMod D (↑u⁻¹ : ZMod D.natAbs) = 1 := by
    rw [← chiDMod_mul, Units.mul_inv, chiDMod_one]
  rcases chiDMod_unit u with h | h <;> rw [h] at h1 ⊢
  · linear_combination h1
  · linear_combination -h1

/-- `𝓕 χ_D (u) = χ_D(u) 𝓕 χ_D (1)` at a unit `u`. -/
theorem dft_chiDMod_unit [NeZero D.natAbs] (u : (ZMod D.natAbs)ˣ) :
    𝓕 (chiDMod D) u = chiDMod D u * 𝓕 (chiDMod D) 1 := by
  rw [dft_apply, dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulRight u) _ _ (fun j => ?_)
  simp only [Units.mulRight_apply, mul_one, smul_eq_mul]
  rw [chiDMod_mul]
  linear_combination (-(stdAddChar (-(j * (u : ZMod D.natAbs))) * chiDMod D j)) * chiDMod_unit_sq u

/-- **The witness for primitivity.** For a non-unit `a` of `ZMod |D|` (`D` an odd fundamental
discriminant) there is a unit `x ≡ 1` modulo `|D| / p` (`p ∣ gcd(a, |D|)` prime), so that
`(x − 1) a = 0`, with `χ_D(x) = −1` (`x` a non-residue modulo `p`). -/
theorem exists_twist_witness (hD : IsOddFundDisc D) [NeZero D.natAbs] (a : ZMod D.natAbs)
    (ha : ¬ IsUnit a) :
    ∃ x : (ZMod D.natAbs)ˣ, ((x : ZMod D.natAbs) - 1) * a = 0 ∧ chiDMod D x = -1 := by
  have hcop : ¬ Nat.Coprime a.val D.natAbs := fun h =>
    ha (by rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_iff_coprime _ _).mpr h)
  obtain ⟨p, hp, hpa, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  obtain ⟨r', hr'⟩ := hpr
  have hsq : Squarefree D.natAbs := Int.squarefree_natAbs.mpr hD.2.2
  have hr'0 : r' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hr'; exact NeZero.ne D.natAbs hr'
  have hpr' : Nat.Coprime p r' := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    obtain ⟨t, ht⟩ := h
    have : p * p ∣ D.natAbs := ⟨t, by rw [hr', ht]; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  have hrodd : D.natAbs % 2 = 1 := by
    have h4 := hD.2.1
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ D.natAbs := ⟨r', hr'⟩
    omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r' := ⟨hr'0⟩
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hpr' g.val 1
  -- `χ_D(n) = (n/p)(n/r') = (−1)(1)`
  have hJp : jacobiSym (n : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : ((n : ℤ) : ZMod p) = g := by
      have := (ZMod.natCast_eq_natCast_iff n g.val p).mpr hn1
      push_cast; rw [this, ZMod.natCast_zmod_val]
    rw [this]; exact hg
  have hJr' : jacobiSym (n : ℤ) r' = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1)]
    · exact jacobiSym.one_left _
    · exact_mod_cast hn2
  have hJ : jacobiSym (n : ℤ) D.natAbs = -1 := by
    rw [hr', jacobiSym.mul_right, hJp, hJr']; norm_num
  have hunit : IsUnit ((n : ℕ) : ZMod D.natAbs) := by
    refine (ZMod.isUnit_iff_coprime _ _).mpr ?_
    have h0 : jacobiSym (n : ℤ) D.natAbs ≠ 0 := by rw [hJ]; norm_num
    rw [Ne, jacobiSym.eq_zero_iff_not_coprime, not_not, Int.gcd_natCast_natCast] at h0
    exact h0
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    have hdvd : (D.natAbs : ℤ) ∣ ((n : ℤ) - 1) * (a.val : ℤ) := by
      have h1 : (r' : ℤ) ∣ (n : ℤ) - 1 := by
        have := (Nat.ModEq.dvd hn2.symm)
        push_cast at this; exact this
      have h2 : (p : ℤ) ∣ (a.val : ℤ) := by exact_mod_cast hpa
      have hc : ((D.natAbs : ℕ) : ℤ) = (r' : ℤ) * p := by rw [hr']; push_cast; ring
      rw [hc]
      exact mul_dvd_mul h1 h2
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ D.natAbs).mpr hdvd
    push_cast at this
    rwa [ZMod.natCast_zmod_val] at this
  · rw [IsUnit.unit_spec, show ((n : ℕ) : ZMod D.natAbs) = ((n : ℤ) : ZMod D.natAbs) by push_cast; rfl,
      chiDMod_intCast, hJ]; push_cast; rfl

/-- `𝓕 χ_D` vanishes at the non-units (primitivity of `χ_D`). -/
theorem dft_chiDMod_nonunit (hD : IsOddFundDisc D) [NeZero D.natAbs] (a : ZMod D.natAbs)
    (ha : ¬ IsUnit a) : 𝓕 (chiDMod D) a = 0 := by
  obtain ⟨x, hxa, hx⟩ := exists_twist_witness hD a ha
  have h : 𝓕 (chiDMod D) a = chiDMod D x * 𝓕 (chiDMod D) a := by
    rw [dft_apply, Finset.mul_sum]
    refine Fintype.sum_equiv (Units.mulLeft x) _ _ (fun j => ?_)
    simp only [Units.mulLeft_apply, smul_eq_mul]
    have e : (x : ZMod D.natAbs) * j * a = j * a := by
      linear_combination j * hxa
    rw [e, chiDMod_mul]
    linear_combination (-(stdAddChar (-(j * a)) * chiDMod D j)) * chiDMod_unit_sq x
  rw [hx] at h
  linear_combination h / 2

end Character

/-! ## Slash-action lemmas for a newform of trivial nebentypus -/

section Slash

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open Matrix.GeneralLinearGroup (upperRightHom)
open scoped MatrixGroups ModularForm

variable {N : ℕ} [NeZero N]

theorem upperRightHom_intCast (m : ℤ) :
    (upperRightHom (m : ℝ) : GL (Fin 2) ℝ) = mapGL ℝ (ModularGroup.T ^ m) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

omit [NeZero N] in
/-- A cusp form of level `Γ₁(N)` is invariant under `τ ↦ τ + m`, `m ∈ ℤ`. -/
theorem slash_upperRightHom_add_intCast {k : ℤ} (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : ℝ) (m : ℤ) :
    (⇑F ∣[k] (upperRightHom (x + m) : GL (Fin 2) ℝ)) = ⇑F ∣[k] (upperRightHom x : GL (Fin 2) ℝ) := by
  rw [add_comm, AddChar.map_add_eq_mul, SlashAction.slash_mul, upperRightHom_intCast,
    SlashInvariantForm.slash_action_eqn F]
  refine ⟨ModularGroup.T ^ m, ?_, rfl⟩
  show ModularGroup.T ^ m ∈ Gamma1 N
  rw [Gamma1_mem]
  simp [ModularGroup.coe_T_zpow]

/-- The Fricke involution acts on a newform of trivial nebentypus (weight 2) by its sign. -/
theorem slash_frickeGL_newform (f : Newform N 2) (hχ : f.χ = 1) :
    (⇑f.toCuspForm ∣[(2 : ℤ)] TauCeti.frickeGL ℝ N) = f.frickeSign hχ • ⇑f.toCuspForm := by
  have h := congrArg (fun F : CuspForm _ 2 => (⇑F : ℍ → ℂ))
    (f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ)
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp] at h
  have h1 : TauCeti.atkinLehnerNormalizer N 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  rw [h1, one_smul] at h
  rw [h, FunLike.coe_smul]

/-- A newform of trivial nebentypus is invariant under `Γ₀(N)`. -/
theorem slash_gamma0_newform (f : Newform N 2) (hχ : f.χ = 1) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 N) : (⇑f.toCuspForm ∣[(2 : ℤ)] (mapGL ℝ γ : GL (Fin 2) ℝ)) = ⇑f.toCuspForm := by
  have h := (mem_cuspFormCharSpace_iff_nebentypus 2 f.χ f.toCuspForm).mp
    f.mem_charSpace ⟨γ, hγ⟩
  rw [hχ] at h
  simpa using h

/-- The matrix `[r, −b; −N a, d₀] ∈ Γ₀(N)` for `r d₀ − N a b = 1`. -/
def twistGamma (N r : ℕ) (a b d₀ : ℤ) (h : (r : ℤ) * d₀ - N * a * b = 1) : SL(2, ℤ) :=
  ⟨!![(r : ℤ), -b; -(N * a), d₀], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem coe_twistGamma (N r : ℕ) (a b d₀ : ℤ) (h : (r : ℤ) * d₀ - N * a * b = 1) :
    ((twistGamma N r a b d₀ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(r : ℤ), -b; -(N * a), d₀] := rfl

theorem twistGamma_mem (N r : ℕ) (a b d₀ : ℤ) (h : (r : ℤ) * d₀ - N * a * b = 1) :
    twistGamma N r a b d₀ h ∈ Gamma0 N := by
  rw [Gamma0_mem]
  have : (twistGamma N r a b d₀ h) 1 0 = -(N * a) := by
    rw [show (twistGamma N r a b d₀ h) 1 0 =
      ((twistGamma N r a b d₀ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl,
      coe_twistGamma]; simp
  rw [this]; simp

/-- **The matrix identity**: `[1, a/r; 0, 1] W_{N r²} = (r I) W_N γ [1, b/r; 0, 1]` with
`γ = [r, −b; −N a, d₀]`, `r d₀ − N a b = 1`. -/
theorem upperRightHom_mul_frickeGL (N r : ℕ) [NeZero N] [NeZero r] [NeZero (N * r * r)]
    (a b d₀ : ℤ) (h : (r : ℤ) * d₀ - N * a * b = 1) :
    (upperRightHom ((a : ℝ) / r) : GL (Fin 2) ℝ) * TauCeti.frickeGL ℝ (N * r * r) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (r : ℝ) (NeZero.ne _)) *
        TauCeti.frickeGL ℝ N * mapGL ℝ (twistGamma N r a b d₀ h) *
          (upperRightHom ((b : ℝ) / r) : GL (Fin 2) ℝ) := by
  have hr : (r : ℝ) ≠ 0 := NeZero.ne _
  have hR : (r : ℝ) * d₀ - N * a * b = 1 := by exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.upperRightHom_apply,
      coe_twistGamma, Matrix.GeneralLinearGroup.coe_scalar, Matrix.natCast_apply,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.map_apply] <;>
    field_simp <;>
    first
    | simp
    | linear_combination (1 - (r : ℝ)) * hR
    | linear_combination (-(r : ℝ)) * hR
    | linear_combination (r : ℝ) * hR
    | linear_combination hR

theorem det_mapGL_pos (γ : SL(2, ℤ)) :
    0 < ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.det_coe]
  norm_num

theorem det_upperRightHom_pos (x : ℝ) :
    0 < ((upperRightHom x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  simp [Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.det_fin_two]

/-- **One term of the twist under `W_{N r²}`.** -/
theorem slash_twist_term (f : Newform N 2) (hχ : f.χ = 1) (r : ℕ) [NeZero r]
    [NeZero (N * r * r)] (a b d₀ : ℤ) (h : (r : ℤ) * d₀ - N * a * b = 1) :
    (⇑f.toCuspForm ∣[(2 : ℤ)] (upperRightHom ((a : ℝ) / r) : GL (Fin 2) ℝ)) ∣[(2 : ℤ)]
        TauCeti.frickeGL ℝ (N * r * r) =
      f.frickeSign hχ • (⇑f.toCuspForm ∣[(2 : ℤ)] (upperRightHom ((b : ℝ) / r) : GL (Fin 2) ℝ)) := by
  rw [← SlashAction.slash_mul, upperRightHom_mul_frickeGL N r a b d₀ h, SlashAction.slash_mul,
    SlashAction.slash_mul, SlashAction.slash_mul, ModularForm.slash_scalar]
  rw [show ((2 : ℤ) - 2) = 0 by norm_num, zpow_zero, one_smul, slash_frickeGL_newform f hχ,
    ModularForm.smul_slash_of_det_pos _ (det_mapGL_pos _),
    slash_gamma0_newform f hχ _ (twistGamma_mem N r a b d₀ h),
    ModularForm.smul_slash_of_det_pos _ (det_upperRightHom_pos _)]

end Slash

/-! ## The twist is a Fricke eigenvector -/

section Eigen

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open Matrix.GeneralLinearGroup (upperRightHom)
open scoped MatrixGroups ModularForm

theorem sum_eq_sum_units {r : ℕ} {E : Type*} [AddCommMonoid E] (g : ZMod r → E)
    (hg : ∀ a, ¬ IsUnit a → g a = 0) [Fintype (ZMod r)] :
    ∑ a, g a = ∑ u : (ZMod r)ˣ, g u := by
  classical
  rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun a _ h => by_contra fun hu => h (hg a hu))]
  have : (Finset.univ.filter IsUnit : Finset (ZMod r)) =
      Finset.univ.map ⟨((↑) : (ZMod r)ˣ → ZMod r), Units.val_injective⟩ := by
    ext a; simp [IsUnit, eq_comm]
  rw [this, Finset.sum_map]
  rfl

variable {N : ℕ} [NeZero N]

/-- The involution `u ↦ −(N u)⁻¹` of `(ZMod r)ˣ`. -/
def twistInv {r : ℕ} (Nu : (ZMod r)ˣ) (u : (ZMod r)ˣ) : (ZMod r)ˣ := -(Nu * u)⁻¹

theorem twistInv_involutive {r : ℕ} (Nu : (ZMod r)ˣ) : Function.Involutive (twistInv Nu) := by
  intro u
  simp only [twistInv, mul_neg, inv_neg, neg_neg, _root_.mul_inv_rev, inv_inv]
  simp [mul_assoc]

/-- **One translate of the twist under `W_{N r²}`**, at a unit `u`. -/
theorem slash_twist_unit (f : Newform N 2) (hχ : f.χ = 1) (r : ℕ) [NeZero r]
    [NeZero (N * r * r)] (hcop : Nat.Coprime N r) (u : (ZMod r)ˣ) :
    (⇑f.toCuspForm ∣[(2 : ℤ)] (upperRightHom (((u : ZMod r).val : ℝ) / r) : GL (Fin 2) ℝ))
        ∣[(2 : ℤ)] TauCeti.frickeGL ℝ (N * r * r) =
      f.frickeSign hχ • (⇑f.toCuspForm ∣[(2 : ℤ)]
        (upperRightHom ((((twistInv (ZMod.unitOfCoprime N hcop) u : (ZMod r)ˣ) : ZMod r).val : ℝ)
          / r) : GL (Fin 2) ℝ)) := by
  set a := (u : ZMod r).val with ha
  have hca : Nat.Coprime (N * a) r := Nat.Coprime.mul_left hcop (ZMod.val_coe_unit_coprime u)
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hca
  have hdet : (r : ℤ) * y - N * (a : ℤ) * (-x) = 1 := by push_cast at hxy; linear_combination hxy
  have h1 := slash_twist_term f hχ r (a : ℤ) (-x) y hdet
  push_cast at h1
  rw [h1]
  congr 1
  -- `-x ≡ (twistInv u).val (mod r)`
  set v := ((twistInv (ZMod.unitOfCoprime N hcop) u : (ZMod r)ˣ) : ZMod r) with hv
  have hxv : ((-x : ℤ) : ZMod r) = v := by
    have hx1 : (x : ZMod r) * ((ZMod.unitOfCoprime N hcop * u : (ZMod r)ˣ) : ZMod r) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod r) hxy
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      rw [Units.val_mul, ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (u : ZMod r), ← ha]
      linear_combination this
    have hinv : (((ZMod.unitOfCoprime N hcop * u)⁻¹ : (ZMod r)ˣ) : ZMod r) = x := by
      rw [Units.inv_eq_of_mul_eq_one_left hx1]
    rw [hv, twistInv, Units.val_neg, hinv]; push_cast; ring
  obtain ⟨m, hm⟩ : (r : ℤ) ∣ (-x) - (v.val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [ZMod.natCast_zmod_val, ← hxv]; push_cast; ring
  have hr : (r : ℝ) ≠ 0 := NeZero.ne _
  have e : ((-x : ℤ) : ℝ) / r = (v.val : ℝ) / r + (m : ℤ) := by
    have : ((-x : ℤ) : ℝ) = (v.val : ℝ) + r * m := by exact_mod_cast (by linear_combination hm)
    rw [this]; field_simp
  push_cast at e
  rw [e, slash_upperRightHom_add_intCast f.toCuspForm]

omit [NeZero N] in
theorem dft_twistInv {D : ℤ} [NeZero D.natAbs] (hcop : Nat.Coprime N D.natAbs)
    (u : (ZMod D.natAbs)ˣ) :
    𝓕 (chiDMod D) u = (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) *
      𝓕 (chiDMod D) (twistInv (ZMod.unitOfCoprime N hcop) u : (ZMod D.natAbs)ˣ) := by
  rw [dft_chiDMod_unit u, dft_chiDMod_unit (twistInv (ZMod.unitOfCoprime N hcop) u), ← mul_assoc,
    ← chiDMod_intCast, ← chiDMod_mul]
  congr 1
  have e : ((-(N : ℤ) : ℤ) : ZMod D.natAbs) *
      ((twistInv (ZMod.unitOfCoprime N hcop) u : (ZMod D.natAbs)ˣ) : ZMod D.natAbs) =
      ((u⁻¹ : (ZMod D.natAbs)ˣ) : ZMod D.natAbs) := by
    have h1 : ((N : ℕ) : ZMod D.natAbs) = ((ZMod.unitOfCoprime N hcop : (ZMod D.natAbs)ˣ) :
        ZMod D.natAbs) := (ZMod.coe_unitOfCoprime N hcop).symm
    simp only [twistInv, Units.val_neg]
    push_cast
    rw [h1, neg_mul_neg, ← Units.val_mul, _root_.mul_inv_rev, ← mul_assoc, mul_comm _ u⁻¹,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [e, chiDMod_inv]

/-- **The twist `f ⊗ χ_D` is an eigenvector of `W_{N D²}` with eigenvalue `χ_D(−N) ε_N(f)`.** -/
theorem slash_frickeGL_twist (f : Newform N 2) (hχ : f.χ = 1) {D : ℤ} (hD : IsOddFundDisc D)
    (hcop : Nat.Coprime N D.natAbs) [NeZero D.natAbs] [NeZero (N * D.natAbs * D.natAbs)] :
    (⇑(CuspForm.twist (chiDMod D) (L := N * D.natAbs * D.natAbs) (dvd_mul_right _ _)
        ⟨N, by ring⟩ f.toCuspForm)) ∣[(2 : ℤ)] TauCeti.frickeGL ℝ (N * D.natAbs * D.natAbs) =
      ((jacobiSym (-(N : ℤ)) D.natAbs : ℂ) * f.frickeSign hχ) •
        ⇑(CuspForm.twist (chiDMod D) (L := N * D.natAbs * D.natAbs) (dvd_mul_right _ _)
          ⟨N, by ring⟩ f.toCuspForm) := by
  have hW : 0 < ((TauCeti.frickeGL ℝ (N * D.natAbs * D.natAbs) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
    have := TauCeti.val_det_frickeGL_pos (K := ℝ) (N := N * D.natAbs * D.natAbs)
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  set h : ZMod D.natAbs → (ℍ → ℂ) := fun a =>
    ⇑f.toCuspForm ∣[(2 : ℤ)] (upperRightHom ((a.val : ℝ) / D.natAbs) : GL (Fin 2) ℝ) with hh
  have hF : ⇑(CuspForm.twist (chiDMod D) (L := N * D.natAbs * D.natAbs) (dvd_mul_right _ _)
        ⟨N, by ring⟩ f.toCuspForm) =
      (D.natAbs : ℂ)⁻¹ • ∑ a : ZMod D.natAbs, 𝓕 (chiDMod D) a • h a := by
    funext τ
    simp only [CuspForm.twist_apply, hh, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      TauCeti.ModularForm.slash_upperRightHom_apply]
  set Nu := ZMod.unitOfCoprime N hcop with hNu
  set c : ℂ := (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) with hc
  set ε := f.frickeSign hχ with hε
  have hvan : ∀ (g : ZMod D.natAbs → ℍ → ℂ) (a : ZMod D.natAbs), ¬ IsUnit a →
      𝓕 (chiDMod D) a • g a = 0 := fun g a ha => by
    rw [dft_chiDMod_nonunit hD a ha, zero_smul]
  have hterm : ∀ u : (ZMod D.natAbs)ˣ, 𝓕 (chiDMod D) u • (h u ∣[(2 : ℤ)]
      TauCeti.frickeGL ℝ (N * D.natAbs * D.natAbs)) =
      (c * ε) • (𝓕 (chiDMod D) (twistInv Nu u : (ZMod D.natAbs)ˣ) • h (twistInv Nu u)) := by
    intro u
    rw [hh]
    simp only
    rw [slash_twist_unit f hχ D.natAbs hcop u, dft_twistInv hcop u, smul_smul, smul_smul]
    congr 1
    ring
  rw [hF, ModularForm.smul_slash_of_det_pos _ hW, SlashAction.sum_slash]
  simp_rw [ModularForm.smul_slash_of_det_pos _ hW]
  rw [sum_eq_sum_units _ (hvan _), sum_eq_sum_units _ (hvan h)]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), ← Finset.smul_sum]
  have hperm := Equiv.sum_comp (twistInv_involutive Nu).toPerm
    (fun u : (ZMod D.natAbs)ˣ => 𝓕 (chiDMod D) (u : ZMod D.natAbs) • h u)
  simp only [Function.Involutive.coe_toPerm] at hperm
  rw [hperm, smul_comm]

end Eigen

/-! ## The twisted functional equation -/

section FE

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- `completedL M G` is Tau Ceti's `frickeCompletedL F M` for a weight-2 cusp form `F` of level
`Γ₁(M)` and the entire continuation `G` of its L-series, on `Re s > 0`. -/
theorem completedL_eq_frickeCompletedL_cusp {M : ℕ} [NeZero M]
    (F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) {G : ℂ → ℂ}
    (hG : IsEntireCont (fun n => (UpperHalfPlane.qExpansion 1 F).coeff n) 2 G) {s : ℂ}
    (hs : 0 < s.re) :
    ZInQ.Literature.completedL M G s =
      CuspForm.frickeCompletedL F (M.toPNat (NeZero.pos M)) s := by
  have hk : (0 : ℤ) < 2 := by norm_num
  have hEq : G = ModularForm.L hk F := by
    have := CuspForm.eq_strictWidthInfty_cpow_mul_L F hk hG.1 (fun {s} hs => by
      simp only [strictWidthInfty_Gamma1]
      exact hG.2 s (by norm_num at hs; linarith))
    simpa [strictWidthInfty_Gamma1] using this
  rw [hEq, ZInQ.Literature.completedL,
    CuspForm.frickeCompletedL_eq_cpow_mul_Λ F _ hk s, ModularForm.L]
  have hMc : (((M.toPNat (NeZero.pos M) : ℕ+) : ℕ) : ℂ) = (M : ℂ) := rfl
  rw [hMc, Complex.Gammaℂ_def]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hπ : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast h.1)
  field_simp

/-- **The twisted functional equation, proved** (`TwistFunctionalEquation` is glue). -/
theorem twistFunctionalEquation : TwistFunctionalEquation := by
  intro N _ f hχ D hD hcop G hG s hs1 hs2
  have hD0 : D ≠ 0 := by rintro rfl; exact absurd hD.2.1 (by decide)
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  have : NeZero (N * D.natAbs * D.natAbs) :=
    ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne _)) (NeZero.ne _)⟩
  have hk : (0 : ℤ) < 2 := by norm_num
  set F := CuspForm.twist (chiDMod D) (L := N * D.natAbs * D.natAbs) (dvd_mul_right _ _)
    ⟨N, by ring⟩ f.toCuspForm with hFdef
  set c : ℂ := (jacobiSym (-(N : ℤ)) D.natAbs : ℂ) with hc
  have hεF : TauCeti.normalizedFrickeOperatorCusp (N := N * D.natAbs * D.natAbs) 2 F =
      (c * f.frickeSign hχ) • F := by
    apply DFunLike.coe_injective
    rw [TauCeti.coe_normalizedFrickeOperatorCusp, FunLike.coe_smul]
    have h1 : TauCeti.atkinLehnerNormalizer (N * D.natAbs * D.natAbs) 2 = 1 := by
      simp [TauCeti.atkinLehnerNormalizer]
    rw [h1, one_smul]
    exact slash_frickeGL_twist f hχ hD hcop.symm
  have hFE := CuspForm.frickeCompletedL_sub_eq_of_normalizedFrickeOperatorCusp_eq_smul F hk hεF s
  have e2 : ((2 : ℤ) : ℂ) = 2 := by norm_num
  rw [e2] at hFE
  -- `G` continues the L-series of `F`
  have hGF : IsEntireCont (fun n => (UpperHalfPlane.qExpansion 1 F).coeff n) 2 G := by
    refine isEntireCont_congr (fun n _ => ?_) hG
    rw [hFdef, CuspForm.qExpansion_twist_coeff, chiDMod_natCast]
    simp only [twistCoeff, coeff]
    ring
  have h2s : 0 < (2 - s).re := by simp only [Complex.sub_re]; norm_num; linarith
  rw [show N * D.natAbs ^ 2 = N * D.natAbs * D.natAbs by ring,
    completedL_eq_frickeCompletedL_cusp F hGF h2s, completedL_eq_frickeCompletedL_cusp F hGF hs1,
    hFE]
  simp only [rootNumber]
  ring

end FE

end ZInQ.GZFH

#print axioms ZInQ.GZFH.twistFunctionalEquation
