import ZInQKernel.Contrib.GZTheta.ALFricke

/-!
# atkin-li: quadratic twists of newforms are good eigenforms; strong multiplicity one

Task atkin-li. Toward `AtkinLiTwistNew` (gz-theta, `Split.lean`) in general.

* `NewformUniqueAcrossLevels`: two newforms of levels dividing `N`, whose nebentypes induce the
  same character modulo `N` and whose eigenvalues agree at every prime `p ∤ N`, have the same level
  and are the same function (strong multiplicity one across levels). Published: Miyake, *Modular
  forms*, Thm 4.6.19 and Cor. 4.6.20; Li, Math. Ann. 212 (1975); Diamond–Shurman Thm 5.8.3
  (UNVERIFIED locators). Proved in Tau Ceti's main (commit 4d91513e) as
  `HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq` (VERIFIED by reading), whose
  proof is not in the vendored commit-5a01f5fe modules.
* `exists_eigenformAway_twist`: for a newform `G` of level `L`, weight 2, trivial nebentypus, the
  twist `G ⊗ (·/r)` is a good Hecke eigenform of level `L r²` with trivial nebentypus.
* `newform_fricke_ne`: gz-theta's `newform_fricke`, with the Fricke constant nonzero.
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-- **Strong multiplicity one across levels** (glue-level restatement of a published theorem):
two newforms `g`, `g'` of levels `M`, `M'` dividing `N`, whose nebentypes induce the same
character `χ` modulo `N` and whose Hecke eigenvalues agree at every prime `p ∤ N`, have `M = M'`
and are the same function on `ℍ`. Miyake, *Modular forms*, Theorem 4.6.19 and Corollary 4.6.20;
W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975); Diamond–Shurman,
Theorem 5.8.3 (UNVERIFIED locators). It is Tau Ceti main's
`HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq` (commit 4d91513e) with the finite
exceptional set empty. -/
def NewformUniqueAcrossLevels : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (M M' : ℕ) [NeZero M] [NeZero M'] (χ : (ZMod N)ˣ →* ℂˣ)
    (g : Newform M k) (g' : Newform M' k) (hM : M ∣ N) (hM' : M' ∣ N),
    g.χ.comp (ZMod.unitsMap hM) = χ → g'.χ.comp (ZMod.unitsMap hM') = χ →
    (∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) =
        g'.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM')) →
    M = M' ∧ ⇑g.toCuspForm = ⇑g'.toCuspForm

/-! ### The Fricke constant of a newform is nonzero -/

theorem newform_fricke_ne {M : ℕ} [NeZero M] (g : Newform M 2) (hχ : g.χ = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M : ℂ) * z)).im),
      g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = c * z ^ 2 * g.toCuspForm ⟨z, hz⟩ := by
  have hfr := g.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ
  have hε : g.frickeSign hχ ≠ 0 := by
    rcases g.frickeSign_eq_one_or_neg_one hχ with h | h <;> rw [h] <;> norm_num
  set ε := g.frickeSign hχ
  have hnorm : TauCeti.atkinLehnerNormalizer M 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine ⟨ε * M, mul_ne_zero hε hM0, fun z hz hz' => ?_⟩
  have h := congrArg (fun F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 => (⇑F) ⟨z, hz⟩) hfr
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, hnorm, one_smul] at h
  rw [ModularForm.slash_apply] at h
  have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ M).det : ℝ) := TauCeti.val_det_frickeGL_pos
  have hσ : ∀ w : ℂ, σ (TauCeti.frickeGL ℝ M) w = w := fun w => by
    simp only [σ, if_pos hdet]; rfl
  have hpt : (TauCeti.frickeGL ℝ M • (⟨z, hz⟩ : ℍ)) = ⟨-1 / ((M : ℂ) * z), hz'⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom,
      TauCeti.coe_frickeGL]
    simp
  have hden : denom (TauCeti.frickeGL ℝ M) (⟨z, hz⟩ : ℍ) = (M : ℂ) * z := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL]
    simp
  have hdetv : |((TauCeti.frickeGL ℝ M).det : ℝ)| = M := by
    rw [TauCeti.val_det_frickeGL, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hσ, hpt, hden, hdetv, CuspForm.smul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  generalize g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = A at h ⊢
  generalize g.toCuspForm ⟨z, hz⟩ = B at h ⊢
  push_cast at h
  have hne : ((M : ℂ) * z) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hM0 hz0)
  simp only [zpow_one, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h

/-! ### The twist of a newform -/

/-- The twist `G ⊗ (·/r)` of a newform of level `L`, at level `L r²`. -/
def twistJ {L : ℕ} [NeZero L] (G : Newform L 2) (r : ℕ) [NeZero r] :
    CuspForm ((Gamma1 (L * r ^ 2)).map (mapGL ℝ)) 2 :=
  CuspForm.twist (jacobiChar r) (dvd_twist_left L r) (dvd_twist_right L r) G.toCuspForm

theorem qExpansion_twistJ_coeff {L : ℕ} [NeZero L] (G : Newform L 2) (r : ℕ) [NeZero r]
    (n : ℕ) : (qExpansion 1 (twistJ G r)).coeff n = (jacobiSym n r : ℂ) * coeff G n := by
  rw [twistJ, CuspForm.qExpansion_twist_coeff, jacobiChar_natCast]; rfl

theorem jacobiSym_sq_of_coprime {r p : ℕ} (h : Nat.Coprime p r) :
    (jacobiSym (p : ℤ) r : ℂ) ^ 2 = 1 := by
  have : jacobiSym (p : ℤ) r ^ 2 = 1 := jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact h)
  exact_mod_cast this

theorem twistChar_one (L r : ℕ) [NeZero L] [NeZero r] :
    ((1 : (ZMod L)ˣ →* ℂˣ).comp (ZMod.unitsMap (dvd_of_mul_right_dvd (dvd_twist_left L r))) *
        ((jacobiChar r).toUnitHom.comp
          (ZMod.unitsMap (dvd_of_mul_left_dvd (dvd_twist_right L r)))) ^ 2) = 1 := by
  ext u
  simp only [MonoidHom.mul_apply, MonoidHom.one_comp, MonoidHom.one_apply, one_mul,
    MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom,
    Units.val_one]
  exact jacobiChar_sq_unit r _

theorem twistJ_mem_charSpace {L : ℕ} [NeZero L] (G : Newform L 2) (hG : G.χ = 1) (r : ℕ)
    [NeZero r] : twistJ G r ∈ cuspFormCharSpace 2 (1 : (ZMod (L * r ^ 2))ˣ →* ℂˣ) := by
  have hm : G.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod L)ˣ →* ℂˣ) := hG ▸ G.mem_charSpace
  have h := CuspForm.twist_mem_cuspFormCharSpace (jacobiChar r) (dvd_twist_left L r)
    (dvd_twist_right L r) hm
  rw [twistChar_one] at h
  exact h

theorem twistJ_coeff_one {L : ℕ} [NeZero L] (G : Newform L 2) (r : ℕ) [NeZero r] :
    (qExpansion 1 (twistJ G r)).coeff 1 = 1 := by
  rw [qExpansion_twistJ_coeff, Nat.cast_one, jacobiSym.one_left, Int.cast_one, one_mul]
  exact G.isNorm

theorem twistJ_ne_zero {L : ℕ} [NeZero L] (G : Newform L 2) (r : ℕ) [NeZero r] :
    twistJ G r ≠ 0 := by
  intro h0
  have h1 := twistJ_coeff_one G r
  rw [h0] at h1
  simp [qExpansion_zero] at h1

/-- **The twist of a newform of trivial nebentypus by `(·/r)` is a good Hecke eigenform** of
level `L r²`, with trivial nebentypus. -/
theorem exists_eigenformAway_twist {L : ℕ} [NeZero L] (G : Newform L 2) (hG : G.χ = 1)
    (r : ℕ) [NeZero r] :
    ∃ E : EigenformAwayFromLevel (L * r ^ 2) 2, E.toCuspForm = twistJ G r ∧ E.χ = 1 := by
  obtain ⟨hmul, hpow⟩ := newform_mul_pow G hG
  refine EigenformAwayFromLevel.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two
    (twistJ_mem_charSpace G hG r) (twistJ_ne_zero G r) (fun u v huv => ?_)
    (fun p hp hpN j => ?_)
  · simp only [qExpansion_twistJ_coeff, hmul u v huv]
    push_cast
    rw [jacobiSym.mul_left]
    push_cast
    ring
  · simp only [qExpansion_twistJ_coeff]
    have hpL : ¬ p ∣ L := fun h => (Nat.Prime.coprime_iff_not_dvd hp).mp
      (hpN.coprime_dvd_right (Dvd.intro _ rfl)) h
    have hpr : Nat.Coprime p r := hpN.coprime_dvd_right ((dvd_pow_self r two_ne_zero).mul_left L)
    rw [hpow p hp j, if_neg hpL]
    simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    push_cast
    simp only [jacobiSym.mul_left, pow_succ, Int.cast_mul]
    have hsq := jacobiSym_sq_of_coprime hpr
    norm_num
    linear_combination (-(p : ℂ) * (jacobiSym ((p : ℤ) ^ j) r : ℂ) * coeff G (p ^ j)) * hsq

end ZInQ.GZTheta
