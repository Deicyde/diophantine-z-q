import ZInQKernel.Contrib.T25.Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CharacterDecomp
import ZInQKernel.OneProof.H.LPrefix
import ZInQKernel.OneProof.H.TailS
import ZInQKernel.Contrib.OneProof.R16Split

/-!
# newform-dict: the kernel's `IsNewform` is the printed newform

The kernel states several open hypotheses over a coefficient-level newform predicate `IsNewform`
(three textual copies with the same body: `_root_.PkgI4.IsNewform` in
`ZInQKernel/HDecomp/Conductor/LadicCond.lean`, `ZInQ.Contrib.G9.PkgI4.IsNewform` in
`ZInQKernel/Contrib/G9/I4Layer.lean`, `HDec.LeafModCurves.IsNewform` in `ZInQKernel/OneProof/H/LPrefix.lean`):

  `IsNewform f χ := IsNormalizedEigenform f χ ∧ ⇑f ∉ oldSpace N k`,

a cusp form on `Γ₁(N)` with slash nebentypus `χ`, `a₁ = 1`, the Hecke relations
`a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k-1} a_{mn/d²}` for all `m, n ≥ 1`, and **not in** the span of the
level raises `τ ↦ g(dτ)` from proper divisor levels.

The printed newform (Atkin–Lehner 1970; Li 1975; Diamond–Shurman Def. 5.8.1; Miyake's primitive form)
is a normalized Hecke eigenform **in the new subspace**, the Petersson orthogonal complement of the
old subspace. In Lean this is Tau Ceti's `HeckeRing.GL2.Newform N k` (vendored,
`ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Newform.lean`): `cuspFormsNew` is
`CuspForm.peterssonOrthogonal (cuspFormsOld N k)`.

`T25/Bridge.lean` proves that a Tau Ceti newform satisfies `IsNewform`. This file proves the
converse (`exists_newform_of_isNewform`), so the two notions agree (`isNewform_iff`, for each of the
three copies). The converse is strong multiplicity one; it is proved here from Tau Ceti's
eigenvalue-refined spanning theorem (Diamond–Shurman Thm 5.8.3), its multiplicity one on the whole
nebentypus space (`Newform.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul`,
DS Thm 5.8.2), the diamond stability of the old space and the independence of the nebentypus spaces.

§3 restates the three bundle fields that are stated over `IsNewform` (`r17`, `r16CoreY`,
`eigenformHTNew`) over the printed newform (`f : Newform N k` with `f.χ = MulChar.toUnitHom χ`),
and proves each field equivalent to its restatement.

No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2

open scoped MatrixGroups ModularForm

namespace NewformDict

/-! ## §1. The dictionary for `_root_.PkgI4.IsNewform` -/

section Dict

open PkgI4 (CF coeff HasNebentypus IsNormalizedEigenform oldSpace IsNewform scaleH)

variable {N : ℕ} {k : ℤ}

/-- Tau Ceti's old subspace (the span of the level raises `V_d` from proper divisor levels) lies
in the kernel's `oldSpace` (converse of `T25.oldSpace_le_map_cuspFormsOld`). -/
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

/-- **The dictionary, hard direction (strong multiplicity one).** A cusp form satisfying the
kernel's `IsNewform f χ` is (the underlying cusp form of) a Tau Ceti newform of level `N` whose
nebentypus is `χ`. -/
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
  -- `f` is a combination of level-raised newforms with its eigenvalues; those of level `N` and
  -- nebentypus `χ` would equal `f`, the others are old or in another nebentypus space
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
  -- the old space is diamond-stable, so it is the sum of its nebentypus parts
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
  -- the component outside `χ` lies in `S_k(N, χ)`, hence is `0`
  have htχ : t ∈ cuspFormCharSpace k χ0 := by
    have : t = f - s := by rw [← hst]; abel
    rw [this]
    exact Submodule.sub_mem _ hχ (Submodule.mem_inf.mp hs).2
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ0)) t htχ ht
  rw [← hst, ht0, add_zero]
  exact (Submodule.mem_inf.mp hs).1

/-- **The dictionary, easy direction** (`T25/Bridge.lean`, restated): a Tau Ceti newform satisfies
the kernel's `IsNewform` with its zero-extended nebentypus. -/
theorem isNewform_of_newform [NeZero N] (g : Newform N k) :
    IsNewform (g.toCuspForm : CF N k) (MulChar.ofUnitHom g.χ) :=
  ⟨⟨T25.hasNebentypus_of_mem_cuspFormCharSpace g.mem_charSpace, g.isNorm,
    fun m n _ hn => T25.newform_coeff_mul g m n hn⟩, T25.not_mem_oldSpace g.isNew g.ne_zero⟩

/-- **The dictionary** (`_root_.PkgI4.IsNewform`): for `N ≥ 1`, `IsNewform f χ` holds exactly when
`f` is a newform of level `N` and nebentypus `χ` in the sense of Atkin–Lehner / Li /
Diamond–Shurman Def. 5.8.1 (Tau Ceti's `Newform`). -/
theorem isNewform_iff (hN : 0 < N) {f : CF N k} {χ : DirichletCharacter ℂ N} :
    IsNewform f χ ↔
      ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ := by
  constructor
  · intro hf
    have : NeZero N := ⟨hN.ne'⟩
    obtain ⟨g, hg, hgχ⟩ := exists_newform_of_isNewform hf
    exact ⟨inferInstance, g, hg, hgχ⟩
  · rintro ⟨_, g, rfl, hgχ⟩
    have h := isNewform_of_newform g
    rwa [hgχ, ofUnitHom_toUnitHom] at h

end Dict

/-! ## §2. The other two copies of `IsNewform` -/

section Copies

variable {N : ℕ} {k : ℤ}

/-- `ZInQ.Contrib.G9.PkgI4.IsNewform` (I4Layer) has the same body as `_root_.PkgI4.IsNewform`. -/
theorem g9_isNewform_iff_pkgI4 {f : ZInQ.Contrib.G9.PkgI4.CF N k} {χ : DirichletCharacter ℂ N} :
    ZInQ.Contrib.G9.PkgI4.IsNewform f χ ↔ PkgI4.IsNewform (f : PkgI4.CF N k) χ :=
  Iff.rfl

/-- `HDec.LeafModCurves.IsNewform` (LPrefix) has the same body as `_root_.PkgI4.IsNewform`. -/
theorem leafModCurves_isNewform_iff_pkgI4 {f : HDec.LeafModCurves.CF N k}
    {χ : DirichletCharacter ℂ N} :
    HDec.LeafModCurves.IsNewform f χ ↔ PkgI4.IsNewform (f : PkgI4.CF N k) χ :=
  Iff.rfl

/-- **The dictionary** for `ZInQ.Contrib.G9.PkgI4.IsNewform`. -/
theorem g9_isNewform_iff (hN : 0 < N) {f : ZInQ.Contrib.G9.PkgI4.CF N k}
    {χ : DirichletCharacter ℂ N} :
    ZInQ.Contrib.G9.PkgI4.IsNewform f χ ↔
      ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ :=
  g9_isNewform_iff_pkgI4.trans (isNewform_iff hN)

/-- **The dictionary** for `HDec.LeafModCurves.IsNewform`. -/
theorem leafModCurves_isNewform_iff (hN : 0 < N) {f : HDec.LeafModCurves.CF N k}
    {χ : DirichletCharacter ℂ N} :
    HDec.LeafModCurves.IsNewform f χ ↔
      ∃ (_ : NeZero N) (g : Newform N k), g.toCuspForm = f ∧ g.χ = MulChar.toUnitHom χ :=
  leafModCurves_isNewform_iff_pkgI4.trans (isNewform_iff hN)

end Copies

/-! ## §3. A transport principle and the three bundle fields over the printed newform

Each field below is stated over `IsNewform`. Its restatement replaces the binder `(f : CF N k)` and
the hypotheses `0 < N → IsNewform f χ →` by `[NeZero N] (f : Newform N k)` and
`f.χ = MulChar.toUnitHom χ →` (a newform of level `N` with nebentypus `χ` in the printed sense), and
`f` by `f.toCuspForm`; nothing else changes. Each field is proved equivalent to its restatement. -/

section Transport

open PkgI4 (CF IsNewform)

/-- **Transport principle.** A statement about every kernel newform (`0 < N`, `IsNewform f χ`) is
the same statement about every printed newform (Tau Ceti's `Newform N k` with nebentypus `χ`). -/
theorem forall_isNewform_iff {k : ℤ} (P : (N : ℕ) → DirichletCharacter ℂ N → CF N k → Prop) :
    (∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N k), 0 < N → IsNewform f χ → P N χ f) ↔
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N k),
        f.χ = MulChar.toUnitHom χ → P N χ f.toCuspForm := by
  constructor
  · intro h N _ χ f hfχ
    exact h N χ f.toCuspForm (Nat.pos_of_neZero N)
      ((isNewform_iff (Nat.pos_of_neZero N)).mpr ⟨inferInstance, f, rfl, hfχ⟩)
  · intro h N χ f hN hf
    obtain ⟨_, g, rfl, hgχ⟩ := (isNewform_iff hN).mp hf
    exact h N χ g hgχ

end Transport

section R17

open PkgI4 LadicCond

/-- **`r17` over the printed newform** (`LadicCond.CarayolR17'` with `IsNewform f χ` replaced by a
Tau Ceti newform `f` of level `N` and nebentypus `χ`): Carayol 1986, Théorème (A), for a newform `f`
of weight 2 and level `N` in the sense of Atkin–Lehner / Li / Diamond–Shurman Def. 5.8.1, a
semisimple `ρ` attached to `f` and a prime `p ≠ ℓ`: the conductor exponent of `ρ|_{G_{ℚ_p}}` is
`v_p(N)`. Equivalent to the field (`carayolR17'_of_newform`, `newform_of_carayolR17'`). -/
def CarayolR17Newform : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N 2) (ρ : GaloisRep ℓ 2)
    (p : ℕ) [Fact p.Prime],
    f.χ = MulChar.toUnitHom χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL (f.toCuspForm : CF N 2) →
      p ≠ ℓ → condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

theorem carayolR17'_of_newform (h : CarayolR17Newform) : LadicCond.CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp
  obtain ⟨_, g, rfl, hgχ⟩ := (isNewform_iff hN).mp hf
  exact h ℓ ιC ιL N χ g ρ p hgχ hs ha hp

theorem newform_of_carayolR17' (h : LadicCond.CarayolR17') : CarayolR17Newform := by
  intro ℓ _ ιC ιL N _ χ f ρ p _ hfχ hs ha hp
  exact h ℓ ιC ιL N χ f.toCuspForm ρ p (Nat.pos_of_neZero N)
    ((isNewform_iff (Nat.pos_of_neZero N)).mpr ⟨inferInstance, f, rfl, hfχ⟩) hs ha hp

theorem carayolR17'_iff_newform : LadicCond.CarayolR17' ↔ CarayolR17Newform :=
  ⟨newform_of_carayolR17', carayolR17'_of_newform⟩

end R17

section R16

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)
open LeafModCurves
open WeierstrassCurve AlgebraicGeometry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open R16Split

/-- **`r16CoreY` over the printed newform** (`R16Split.R16CoreY` with `IsNewform f χ` replaced by a
Tau Ceti newform `f` of level `N` and nebentypus `χ`; sources as for `R16Split.R16CoreY`: Shimura
1973 Thm 1, Diamond–Shurman Thm 9.5.4 / Shimura 1971 Thm 7.11, numbers UNVERIFIED). Equivalent to the
field (`r16CoreY_of_newform`, `newform_of_r16CoreY`). -/
def R16CoreYNewform : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : Newform N 2) (J : AbVar ℚ),
    f.χ = MulChar.toUnitHom χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField (f.toCuspForm : CF N 2)) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField (f.toCuspForm : CF N 2) →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField (f.toCuspForm : CF N 2)) : ℕ) : WithBot ℕ∞) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField (f.toCuspForm : CF N 2) →+* PadicAlgCl ℓ),
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField (f.toCuspForm : CF N 2), (a : ℂ) = coeff (f.toCuspForm : CF N 2) p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField (f.toCuspForm : CF N 2), (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p)

theorem r16CoreY_of_newform (h : R16CoreYNewform) : R16Split.R16CoreY := by
  intro N χ f J hN hf hJ
  obtain ⟨_, g, rfl, hgχ⟩ := (isNewform_iff hN).mp hf
  exact h N χ g J hgχ hJ

theorem newform_of_r16CoreY (h : R16Split.R16CoreY) : R16CoreYNewform := by
  intro N _ χ f J hfχ hJ
  exact h N χ f.toCuspForm J (Nat.pos_of_neZero N)
    ((isNewform_iff (Nat.pos_of_neZero N)).mpr ⟨inferInstance, f, rfl, hfχ⟩) hJ

theorem r16CoreY_iff_newform : R16Split.R16CoreY ↔ R16CoreYNewform :=
  ⟨newform_of_r16CoreY, r16CoreY_of_newform⟩

end R16

section HT

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- **`eigenformHTNew` over the printed newform** (`ZInQ.Contrib.HodgeSplit.EigenformHTNew` with
`IsNewform f χ` replaced by a Tau Ceti newform `f` of level `N` and nebentypus `χ`; sources as for the
field: Kato 2004 9.2-9.4, transported to any semisimple attached `ρ` and dualized). Equivalent to the
field (`eigenformHTNew_of_newform`, `newform_of_eigenformHTNew`). -/
def EigenformHTNewNewform : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ)
    (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : Newform N k) (ρ : GaloisRep ℓ 2),
    2 ≤ k → f.χ = MulChar.toUnitHom χ → ρ.IsSemisimple →
    ρ.AttachedTo ιC ιL (f.toCuspForm : ZInQ.Contrib.G9.PkgI4.CF N k) →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

theorem eigenformHTNew_of_newform (h : EigenformHTNewNewform) :
    ZInQ.Contrib.HodgeSplit.EigenformHTNew := by
  intro ℓ _ ιC ιL N k χ f ρ hN hk hf hs ha
  obtain ⟨_, g, rfl, hgχ⟩ := (g9_isNewform_iff hN).mp hf
  exact h ℓ ιC ιL N k χ g ρ hk hgχ hs ha

theorem newform_of_eigenformHTNew (h : ZInQ.Contrib.HodgeSplit.EigenformHTNew) :
    EigenformHTNewNewform := by
  intro ℓ _ ιC ιL N _ k χ f ρ hk hfχ hs ha
  exact h ℓ ιC ιL N k χ f.toCuspForm ρ (Nat.pos_of_neZero N) hk
    ((g9_isNewform_iff (Nat.pos_of_neZero N)).mpr ⟨inferInstance, f, rfl, hfχ⟩) hs ha

theorem eigenformHTNew_iff_newform :
    ZInQ.Contrib.HodgeSplit.EigenformHTNew ↔ EigenformHTNewNewform :=
  ⟨newform_of_eigenformHTNew, eigenformHTNew_of_newform⟩

end HT

end NewformDict
