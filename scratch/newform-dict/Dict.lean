import ZInQKernel.Contrib.T25.Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CharacterDecomp

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace NewformDict

open PkgI4 (CF coeff HasNebentypus IsNormalizedEigenform oldSpace IsNewform scaleH)

variable {N : ℕ} {k : ℤ}

/-- Tau Ceti's old subspace (span of level raises) lies in the leaf's `oldSpace`. -/
theorem map_cuspFormsOld_le_oldSpace [NeZero N] :
    (TauCeti.cuspFormsOld N k).map (T25.coeL N k) ≤ oldSpace N k := by
  rw [Submodule.map_le_iff_le_comap]
  refine TauCeti.cuspFormsOld_le ?_
  intro M d hdvd hM g
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h => by
    subst h; simp at hdvd; exact NeZero.ne N hdvd
  have hMN : M ∣ N := dvd_of_mul_left_dvd hdvd
  have hMlt : M < N := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_neZero N) hMN) hM
  rw [Submodule.mem_comap]
  refine Submodule.subset_span ⟨M, ⟨d, Nat.pos_of_neZero d⟩, g, hM0, hMN, hMlt, hdvd, ?_⟩
  funext τ
  simp only [T25.coeL, LinearMap.coe_mk, AddHom.coe_mk, TauCeti.CuspForm.levelRaise_apply]
  exact congrArg g (T25.scaleGL_smul_eq_scaleH ⟨d, Nat.pos_of_neZero d⟩ τ)

theorem ofUnitHom_toUnitHom (χ : DirichletCharacter ℂ N) :
    MulChar.ofUnitHom (MulChar.toUnitHom χ) = χ := by
  rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq, Equiv.symm_apply_apply]

/-- **The dictionary, converse direction.** -/
theorem exists_newform_of_isNewform [NeZero N] {f : CF N k} {χ : DirichletCharacter ℂ N}
    (hf : IsNewform f χ) :
    ∃ g : Newform N k, g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ := by
  obtain ⟨hg, hnot⟩ := hf
  have hχ := T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1
  have hT := fun (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) =>
    T25.heckeTCuspNat_eq_coeff_smul hg hp hpN
  by_contra hne
  apply hnot
  suffices hold : f ∈ TauCeti.cuspFormsOld N k from
    map_cuspFormsOld_le_oldSpace ⟨f, hold, rfl⟩
  set χ0 := MulChar.toUnitHom χ with hχ0
  have hmem : f ∈ TauCeti.cuspFormsOld N k ⊔
      ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ χ0), cuspFormCharSpace k ψ := by
    refine Submodule.span_le.mpr ?_
      (Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul
        (a := fun p _ _ => coeff f p) hT)
    rintro _ ⟨M, d, _, _, hdM, g, hgev, rfl⟩
    have hMN : M ∣ N := dvd_of_mul_left_dvd hdM
    by_cases hgχ : g.χ.comp (ZMod.unitsMap hMN) = χ0
    · refine Submodule.mem_sup_left (TauCeti.levelRaise_mem_cuspFormsOld hdM ?_ k _)
      rintro rfl
      obtain rfl : d = 1 :=
        (mul_left_eq_self₀.mp (Nat.dvd_antisymm hdM (dvd_mul_left _ _))).resolve_right
          (NeZero.ne _)
      rw [ZMod.unitsMap_self, MonoidHom.comp_id] at hgχ
      have hF := Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul g
        (F := f) (hgχ ▸ hχ) (fun p hp hpN => by rw [hT p hp hpN, hgev p hp hpN])
      have h1 : (qExpansion 1 f).coeff 1 = 1 := hg.2.1
      rw [h1, one_smul] at hF
      exact hne ⟨g, hF.symm, hgχ⟩
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace)))
  have hsplit : TauCeti.cuspFormsOld N k ≤
      (TauCeti.cuspFormsOld N k ⊓ cuspFormCharSpace k χ0) ⊔
        ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ χ0), cuspFormCharSpace k ψ := by
    conv_lhs => rw [← iSup_inf_cuspFormCharSpace_of_invariant k (TauCeti.cuspFormsOld N k)
      (fun d f hf => TauCeti.diamondOpCusp_mem_cuspFormsOld d hf)]
    refine iSup_le fun ψ => ?_
    by_cases h : ψ = χ0
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le ψ h inf_le_right)
  have hmem' := (sup_le (hsplit.trans le_rfl) le_sup_right) hmem
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hmem'
  have htχ : t ∈ cuspFormCharSpace k χ0 := by
    have : t = f - s := by rw [← hst]; abel
    rw [this]
    exact Submodule.sub_mem _ hχ (Submodule.mem_inf.mp hs).2
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ0)) t htχ ht
  rw [← hst, ht0, add_zero]
  exact (Submodule.mem_inf.mp hs).1

end NewformDict
