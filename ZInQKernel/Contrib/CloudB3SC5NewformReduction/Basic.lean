import ZInQKernel.Contrib.T25.Bridge

/-!
# Newform reduction preserving the original nebentypus

The original `PkgI4.IsNormalizedEigenform` coefficient identities produce a
bundled Tau Ceti newform of divisor level. Unlike the trace-only T25 interface,
this reduction also exposes the induced original nebentypus, and therefore the
character values occurring in the good-prime Hecke polynomials.

The proof uses the existing character-preserving decomposition theorem in
`ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Decomposition`
and the original-context bridges in `ZInQKernel.Contrib.T25.Bridge`.
No Galois representation existence theorem or new literature hypothesis is used.

The imported Tau Ceti proofs are Apache-2.0, copyright the Tau Ceti contributors;
their source revision and attribution notices remain in the imported modules.
-/

noncomputable section

namespace CloudB3SC5NewformReduction

open HeckeRing.GL2

/-- An induced unit character has the original Dirichlet character's values at
all integers coprime to the original level. -/
theorem induced_character_apply_of_coprime {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (ψ : (ZMod M)ˣ →* ℂˣ) (χ : DirichletCharacter ℂ N)
    (hψ : ψ.comp (ZMod.unitsMap hMN) = χ.toUnitHom)
    (n : ℕ) (hn : Nat.Coprime n N) :
    (MulChar.ofUnitHom ψ : DirichletCharacter ℂ M) (n : ZMod M) = χ (n : ZMod N) := by
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime n hn
  have hu : ((ZMod.unitsMap hMN u : (ZMod M)ˣ) : ZMod M) = (n : ZMod M) := by
    rw [ZMod.unitsMap_val]
    change ((ZMod.unitOfCoprime n hn : ZMod N).cast : ZMod M) = _
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hMN]
  calc
    (MulChar.ofUnitHom ψ : DirichletCharacter ℂ M) (n : ZMod M)
        = MulChar.ofUnitHom ψ ((ZMod.unitsMap hMN u : (ZMod M)ˣ) : ZMod M) := by rw [hu]
    _ = (ψ (ZMod.unitsMap hMN u) : ℂ) := MulChar.ofUnitHom_coe ψ _
    _ = (χ.toUnitHom u : ℂ) :=
      congrArg (fun ξ : (ZMod N)ˣ →* ℂˣ => (ξ u : ℂ)) hψ
    _ = χ (n : ZMod N) := by
      rw [MulChar.coe_toUnitHom]
      rfl

/-- A genuine bundled newform satisfies the original coefficient-form definition
of `PkgI4.IsNewform`, including normalization and nonmembership in the old space. -/
theorem newform_isNewform {M : ℕ} [NeZero M] {k : ℤ} (f : Newform M k) :
    PkgI4.IsNewform f.toCuspForm (MulChar.ofUnitHom f.χ) := by
  exact ⟨⟨T25.hasNebentypus_of_mem_cuspFormCharSpace f.mem_charSpace, f.isNorm,
    fun m n _ hn => T25.newform_coeff_mul f m n hn⟩,
    T25.not_mem_oldSpace f.isNew f.ne_zero⟩

/-- Every original-context normalized eigenform of positive level has a genuine
bundled newform of positive divisor level with the same good-prime q-coefficients
and nebentypus inducing the original character. The integer weight is unchanged;
no positivity assumption on the weight is needed by this closed reduction. -/
theorem exists_newform_preserving_nebentypus
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k)
    (hN : 0 < N) (hg : PkgI4.IsNormalizedEigenform g χ) :
    ∃ (M : ℕ) (_ : NeZero M) (hMN : M ∣ N) (f : Newform M k),
      0 < M ∧ PkgI4.IsNewform f.toCuspForm (MulChar.ofUnitHom f.χ) ∧
      f.χ.comp (ZMod.unitsMap hMN) = χ.toUnitHom ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        PkgI4.coeff f.toCuspForm p = PkgI4.coeff g p ∧
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ M) (p : ZMod M) = χ (p : ZMod N) := by
  have : NeZero N := ⟨hN.ne'⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 := hg.2.1
    simp only [PkgI4.coeff, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨M, hM, hMN, f, hχ, he⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      (T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1) hg0
      (a := fun p _ _ => PkgI4.coeff g p)
      (fun p hp hpN => T25.heckeTCuspNat_eq_coeff_smul hg hp hpN)
  have : NeZero M := hM
  refine ⟨M, hM, hMN, f, Nat.pos_of_ne_zero (NeZero.ne M), newform_isNewform f,
    hχ, fun p hp hpN => ?_⟩
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have hcoeff := f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm
    ⟨p, hp.pos⟩ (hcop.coprime_dvd_right hMN)
  change PkgI4.coeff f.toCuspForm p =
    f.eigenvalue ⟨p, hp.pos⟩ (hcop.coprime_dvd_right hMN) at hcoeff
  exact ⟨hcoeff.trans (he p hp hcop),
    induced_character_apply_of_coprime hMN f.χ χ hχ p hcop⟩

end CloudB3SC5NewformReduction
