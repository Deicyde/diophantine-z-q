import ZInQKernel.Contrib.OneProof.DSThm966EV
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-! # Deligne–Serre in weight one: from the normalized form to the printed form (cluster C5)

Supporting bridge only. This file proves no open hypothesis and introduces no statement to be assumed.
It shows that the kernel's normalized-eigenform reading of Deligne–Serre,
`ZInQ.Contrib.HodgeSplit.DSThm966`, implies the printed reading `DSThm966EV.DSThm966Printed`. The printed
reading is for an eigenform away from the level, with no normalization `a₁ = 1` and the trace equal to the
`T_p`-eigenvalue. The converse, `DSThm966EV.dsThm966_of_printed`, is already in the tree, so the two
readings are equivalent.

Route. Let `F` be a nonzero eigenform of the good Hecke operators, of weight `1` and nebentypus `ε`. An
arbitrary `F` cannot be normalized by `a₁`, because an oldform may have `a₁ = 0`.

1. Tau Ceti's `Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul`
   (Diamond–Shurman Prop. 5.8.4) gives a level `M ∣ N` and a newform `g` of level `M`. The nebentypus of
   `g`, read at level `N`, is `F.χ`, and `g` has the eigenvalues of `F` at every prime `p ∤ N`.
2. The full eigenform of `g` (`Newform.toEigenform`) is normalized. By
   `DSCoeffExt.isNormalizedEigenform_of_DS` it is a normalized eigenform in the kernel's coefficient form,
   with character `ofUnitHom g.χ`.
3. Apply `DSThm966` at level `M`. Every `p ∤ N` also has `p ∤ M`. The trace `a_p(g)` is the eigenvalue of
   `g` at `p`, which is `F.eigenvalue p`. The determinant `(ofUnitHom g.χ)(p mod M)` is `ε(p mod N)`, read
   through `ZMod.unitsMap`.

Checked 2026-11-16 with Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` on fork main
`c1e4ed1b8`. The file compiles without warnings of its own, and every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3SC5DeligneSerre

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ZInQ.Contrib.G9.PkgI4 (Qbar GQ CF coeff IsNormalizedEigenform LiesOver IsArithFrob)

/-- If `ψ : (ZMod M)ˣ →* ℂˣ` induces `ε` at level `N` (`M ∣ N`), then for `p` prime to `N`,
`(ofUnitHom ψ)(p mod M) = ε(p mod N)`. -/
theorem ofUnitHom_natCast_eq_of_comp_unitsMap {N M : ℕ} (hM : M ∣ N) {ψ : (ZMod M)ˣ →* ℂˣ}
    {ε : DirichletCharacter ℂ N} (h : ψ.comp (ZMod.unitsMap hM) = MulChar.toUnitHom ε) {p : ℕ}
    (hp : Nat.Coprime p N) :
    (MulChar.ofUnitHom ψ : DirichletCharacter ℂ M) (p : ZMod M) = ε (p : ZMod N) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime p hp with hu_def
  have hu : ((ZMod.unitsMap hM u : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) := by
    rw [ZMod.unitsMap_val, hu_def, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hM]
  have h2 : ((ψ (ZMod.unitsMap hM u) : ℂˣ) : ℂ) = ((MulChar.toUnitHom ε u : ℂˣ) : ℂ) := by
    rw [← h]
    rfl
  rw [MulChar.coe_toUnitHom, hu_def, ZMod.coe_unitOfCoprime] at h2
  rw [← hu, MulChar.ofUnitHom_coe]
  exact h2

/-- `toUnitHom (ofUnitHom ψ) = ψ`. -/
theorem toUnitHom_ofUnitHom {M : ℕ} (ψ : (ZMod M)ˣ →* ℂˣ) :
    MulChar.toUnitHom (MulChar.ofUnitHom ψ : DirichletCharacter ℂ M) = ψ := by
  rw [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq]
  exact MulChar.equivToUnitHom.apply_symm_apply ψ

/-- A newform of weight `1` is a normalized eigenform in the kernel's coefficient form, with character
`ofUnitHom g.χ`. -/
theorem isNormalizedEigenform_newform {M : ℕ} [NeZero M] (g : Newform M 1) :
    IsNormalizedEigenform (g.toCuspForm : CF M 1) (MulChar.ofUnitHom g.χ) := by
  apply DSCoeffExt.isNormalizedEigenform_of_DS
  refine ⟨g.toEigenform, g.toEigenform_toCuspForm, ?_, g.isNorm⟩
  rw [g.toEigenform_χ, toUnitHom_ofUnitHom]

/-- The `q`-coefficient of a newform at a prime `p` prime to the level is its eigenvalue at `p`. -/
theorem newform_coeff_eq_eigenvalue {M : ℕ} [NeZero M] (g : Newform M 1) {p : ℕ} (hp : p.Prime)
    (hpM : Nat.Coprime p M) :
    coeff (g.toCuspForm : CF M 1) p = g.eigenvalue ⟨p, hp.pos⟩ hpM := by
  have h1 := g.toEigenform_eigenvalue_eq_qExpansion_coeff ⟨p, hp.pos⟩
  have h2 := g.toEigenform.toEigenformAwayFromLevel_eigenvalue ⟨p, hp.pos⟩ hpM
  rw [g.toEigenform_toEigenformAwayFromLevel] at h2
  rw [h2, h1]
  rfl

/-- **The normalized reading of Deligne–Serre implies the printed reading.** -/
theorem dsThm966Printed_of_dsThm966 (h : ZInQ.Contrib.HodgeSplit.DSThm966) :
    DSThm966EV.DSThm966Printed := by
  intro N _ ε F hFχ _hε
  obtain ⟨M, hMz, hM, g, hgχ, hgev⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      F.mem_charSpace F.ne_zero (a := fun p hp hpN => F.eigenvalue ⟨p, hp.pos⟩ hpN)
      (fun _ hp hpN => F.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  obtain ⟨ρ, hc, hfin, hρ⟩ :=
    h M (MulChar.ofUnitHom g.χ) g.toCuspForm (NeZero.pos M) (isNormalizedEigenform_newform g)
  refine ⟨ρ, hc, hfin, fun p hp hpN => ?_⟩
  have hpM : ¬ p ∣ M := fun hd => hpN (hd.trans hM)
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  obtain ⟨hin, hfr⟩ := hρ p hp hpM
  refine ⟨hin, fun v σ hv hσ => ?_⟩
  obtain ⟨htr, hdet⟩ := hfr v σ hv hσ
  refine ⟨?_, ?_⟩
  · rw [htr, newform_coeff_eq_eigenvalue g hp (hcop.coprime_dvd_right hM), hgev p hp hcop]
    rfl
  · rw [hdet]
    exact ofUnitHom_natCast_eq_of_comp_unitsMap hM (hgχ.trans hFχ) hcop

end ZInQ.Contrib.CloudB3SC5DeligneSerre
