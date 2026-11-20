import ZInQKernel.Contrib.OneProof.Y3ComplexQuotient
import ZInQKernel.Contrib.OneProof.Y3CMRationalDescent

/-! Period values for the three distinguished CM types on the complex quotient. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeafQM LeafQM.AV HDec
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodGlue
open HDec.HSyn.G0Split.FibreQM.PeriodMapH
open RayClassCFT ShimuraCFT Y3Fix HDec.QMSplit.Moduli
open scoped Matrix

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false

private theorem nrd_ne_zero_of_monic_quad {β : B} {p q : ℚ} (hq : q ≠ 0)
    (h : β * β + p • β + algebraMap ℚ B q = 0) : ShimuraGlue.nrdQ ℚ β ≠ 0 := by
  have he : β * (β + algebraMap ℚ B p) = -(algebraMap ℚ B q) := by
    rw [mul_add, ← Algebra.commutes p β, ← Algebra.smul_def]
    exact eq_neg_of_add_eq_zero_left h
  apply nrd_ne_zero_of_mul (y := (-q)⁻¹ • (β + algebraMap ℚ B p))
  rw [mul_smul_comm, he, ← map_neg, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ (neg_ne_zero.mpr hq), map_one]

/-- A period of an object with one of the distinguished CM endomorphisms takes
the corresponding value of the analytic Hauptmodul. -/
theorem cm_period_values {f : UpperHalfPlane → OnePoint ℂ}
    (hf : QMHauptmodulFn f) (hA : CMAnalytic) (Q : QML3 ℂ) (τ : UpperHalfPlane)
    (hτ : HasQMPeriod Q τ) :
    (HasCM4 Q.q → f τ = OnePoint.some 0) ∧
    (HasCM3 Q.q → f τ = OnePoint.infty) ∧
    (HasCM24 Q.q → f τ = OnePoint.some (-16 / 27)) := by
  obtain ⟨Φu, hu, hι⟩ := hτ
  obtain ⟨ρ, hρ⟩ := hA τ Q Φu hu hι
  have hO (a : com Q.q) : PkgI1.InO (ρ a) := (inO_iff _).mpr (hρ a).1
  have hfix (a : com Q.q) (hn : ShimuraGlue.nrdQ ℚ (ρ a) ≠ 0) :
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (ρ a) ∧ g • τ = τ := by
    obtain ⟨-, l, hl⟩ := hρ a
    let g := iotaGL (ρ a) hn
    have he := iotaGL_coe (ρ a) hn
    refine ⟨g, he, smul_eq_of_eig g τ (lam := l) ?_⟩
    rw [he]
    exact hl
  obtain ⟨-, -, -, -, h4, h3, h24⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨φ, hφ, he⟩
    let a : com Q.q := ⟨φ, hφ⟩
    have h := com_rel ρ hφ (P0 := 0) (Q0 := 1) (by simpa using eq_neg_iff_add_eq_zero.mp he)
    have h' : ρ a * ρ a + (1 : B) = 0 := by simpa [a] using h
    have hn : ShimuraGlue.nrdQ ℚ (ρ a) ≠ 0 := nrd_ne_zero_of_monic_quad
      (p := 0) (q := 1) (by norm_num) (by simpa using h')
    obtain ⟨g, hg, hgτ⟩ := hfix a hn
    exact h4 (ρ a) (hO a) (eq_neg_iff_add_eq_zero.mpr h') g hg τ hgτ
  · rintro ⟨φ, hφ, he⟩
    let a : com Q.q := ⟨φ, hφ⟩
    have h := com_rel ρ hφ (P0 := -1) (Q0 := 1) (by simpa [sub_eq_add_neg] using he)
    have h' : ρ a * ρ a - ρ a + (1 : B) = 0 := by simpa [a, sub_eq_add_neg] using h
    have hn : ShimuraGlue.nrdQ ℚ (ρ a) ≠ 0 := nrd_ne_zero_of_monic_quad
      (p := -1) (q := 1) (by norm_num) (by simpa [sub_eq_add_neg] using h')
    obtain ⟨g, hg, hgτ⟩ := hfix a hn
    exact h3 (ρ a) (hO a) h' g hg τ hgτ
  · rintro ⟨φ, hφ, he⟩
    let a : com Q.q := ⟨φ, hφ⟩
    have h := com_rel ρ hφ (P0 := 0) (Q0 := 6) (by simpa using eq_neg_iff_add_eq_zero.mp he)
    have h' : ρ a * ρ a + (6 : B) = 0 := by simpa [a] using h
    have hn : ShimuraGlue.nrdQ ℚ (ρ a) ≠ 0 := nrd_ne_zero_of_monic_quad
      (p := 0) (q := 6) (by norm_num) (by simpa using h')
    obtain ⟨g, hg, hgτ⟩ := hfix a hn
    exact h24 (ρ a) (hO a) (eq_neg_iff_add_eq_zero.mpr h') g hg τ hgτ

/-- The CM flags determine single twist classes, and these three fibres
descend to rational points of the quotient. -/
theorem exists_rational_CM_fibres_of_periods
    {Y Z : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (π : Y ⟶ Z)
    (hΦ : R1fpPropsAbP Y Φ)
    (hquot : ∀ (K : Type) [Field K] [Algebra ℚ K]
      (y y' : fieldPt K ⟶ Y) (P Q : QML3 K),
      Φ K y = M3.mk P → Φ K y' = M3.mk Q →
        (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hL : QMTwistLattice)
    (hA : CMAnalytic) (hf : PkgI1.QMHauptmodul)
    (hE : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) :
    ∃ x₄ x₃ x₂₄ : fieldPt ℚ ⟶ Z, x₄ ≠ x₃ ∧ x₄ ≠ x₂₄ ∧ x₃ ≠ x₂₄ ∧
      ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        (HasCM4 P.q ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x₄) ∧
        (HasCM3 P.q ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x₃) ∧
        (HasCM24 P.q ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x₂₄) := by
  obtain ⟨f, hf⟩ := qmHauptmodul_iff.mp hf
  obtain ⟨Ψ, hB, hU⟩ := Y3Hodge.deligneH_of_print hD Y Φ hΦ
  have hb := body_of_H hB
  have hu := units_of_H hU
  let lifted (P : QML3 Qbar) : fieldPt Qbar ⟶ Y := (Φ Qbar).symm (M3.mk P)
  have hlift (P : QML3 Qbar) : Φ Qbar (lifted P) = M3.mk P := (Φ Qbar).apply_symm_apply _
  have period (P : QML3 Qbar) :
      ∃ (τ : UpperHalfPlane) (Q : QML3 ℂ),
        Φ ℂ (fieldMap ιC ≫ lifted P) = M3.mk Q ∧ HasQMPeriod Q τ ∧
        (HasCM4 P.q → f τ = OnePoint.some 0) ∧
        (HasCM3 P.q → f τ = OnePoint.infty) ∧
        (HasCM24 P.q → f τ = OnePoint.some (-16 / 27)) := by
    obtain ⟨τ₀, g, hτg⟩ := hb.1 (fieldMap ιC ≫ lifted P)
    obtain ⟨γ, hγ, u, hu', hg⟩ := exists_pos_decomp classNumberOneB_proof g
    let τ := (iotaGL (binv γ) (nrd_binv_pos hγ).ne') • τ₀
    have hτu : Ψ τ u = fieldMap ιC ≫ lifted P :=
      ((hb.2.1 τ₀ g τ u).mpr (dcRel_of_decomp hγ τ₀ hg)).symm.trans hτg
    obtain ⟨Q, hQ, hun⟩ := hu u hu' τ
    have hQ' : Φ ℂ (fieldMap ιC ≫ lifted P) = M3.mk Q := hτu ▸ hQ
    obtain ⟨R, hR, hBC⟩ := hΦ.2.2.1 Qbar ℂ ιC (lifted P) P (hlift P)
    obtain ⟨e⟩ := Quotient.exact (hR.symm.trans hQ')
    let e' : QMIso R.q Q.q := ⟨e.φ, e.ψ, e.left, e.right, e.equivariant⟩
    obtain ⟨bc₄, bc₃, bc₂₄⟩ := cmBaseChange (ιC : Qbar →+* ℂ) P R hBC
    obtain ⟨v₄, v₃, v₂₄⟩ := cm_period_values hf hA Q τ hun
    exact ⟨τ, Q, hQ', hun, fun h => v₄ (HasCM4.of_iso e' (bc₄ h)),
      fun h => v₃ (HasCM3.of_iso e' (bc₃ h)), fun h => v₂₄ (HasCM24.of_iso e' (bc₂₄ h))⟩
  have same {P P' : QML3 Qbar} {τ τ' : UpperHalfPlane} {Q Q' : QML3 ℂ}
      (hP : Φ ℂ (fieldMap ιC ≫ lifted P) = M3.mk Q) (hτ : HasQMPeriod Q τ)
      (hP' : Φ ℂ (fieldMap ιC ≫ lifted P') = M3.mk Q') (hτ' : HasQMPeriod Q' τ')
      (hval : f τ = f τ') : ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) P'.q) := by
    have htw := (hL Q Q' τ τ' hτ hτ').mpr ((hf.2.2.1 τ τ').mp hval)
    have he := (hquot ℂ _ _ Q Q' hP hP').mpr htw
    rw [Category.assoc, Category.assoc] at he
    exact (hquot Qbar _ _ P P' (hlift P) (hlift P')).mp (fieldMap_ιC_inj he)
  have transitive (P P' : QML3 Qbar) :
      (HasCM4 P.q → HasCM4 P'.q → ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) P'.q)) ∧
      (HasCM3 P.q → HasCM3 P'.q → ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) P'.q)) ∧
      (HasCM24 P.q → HasCM24 P'.q → ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) P'.q)) := by
    obtain ⟨τ, Q, hP, hτ, v₄, v₃, v₂₄⟩ := period P
    obtain ⟨τ', Q', hP', hτ', v₄', v₃', v₂₄'⟩ := period P'
    exact ⟨fun a b => same hP hτ hP' hτ' ((v₄ a).trans (v₄' b).symm),
      fun a b => same hP hτ hP' hτ' ((v₃ a).trans (v₃' b).symm),
      fun a b => same hP hτ hP' hτ' ((v₂₄ a).trans (v₂₄' b).symm)⟩
  obtain ⟨r₄, hr₄⟩ := exists_rational_distinguished_fibre π hΦ (hquot Qbar)
    (fun P => HasCM4 P.q) hE.1 (fun P Q => (transitive P Q).1)
    (fun P _ α e h => HasCM4.of_iso e ((hasCM4_twist P.q α).mpr h))
    (fun σ P Q h => (hasCM_preserved_by_baseChange σ.toRingHom P Q h).1)
  obtain ⟨r₃, hr₃⟩ := exists_rational_distinguished_fibre π hΦ (hquot Qbar)
    (fun P => HasCM3 P.q) hE.2.1 (fun P Q => (transitive P Q).2.1)
    (fun P _ α e h => HasCM3.of_iso e ((hasCM3_twist P.q α).mpr h))
    (fun σ P Q h => (hasCM_preserved_by_baseChange σ.toRingHom P Q h).2.1)
  obtain ⟨r₂₄, hr₂₄⟩ := exists_rational_distinguished_fibre π hΦ (hquot Qbar)
    (fun P => HasCM24 P.q) hE.2.2 (fun P Q => (transitive P Q).2.2)
    (fun P _ α e h => HasCM24.of_iso e ((hasCM24_twist P.q α).mpr h))
    (fun σ P Q h => (hasCM_preserved_by_baseChange σ.toRingHom P Q h).2.2)
  refine ⟨r₄, r₃, r₂₄, ?_, ?_, ?_, fun y P h => ⟨hr₄ y P h, hr₃ y P h, hr₂₄ y P h⟩⟩
  · intro e
    obtain ⟨P, hP⟩ := hE.1
    have hv := (hr₄ (lifted P) P (hlift P)).mp hP
    rw [e] at hv
    have hc := (hr₃ (lifted P) P (hlift P)).mpr hv
    obtain ⟨τ, Q, -, -, v₄, v₃, -⟩ := period P
    exact OnePoint.coe_ne_infty _ ((v₄ hP).symm.trans (v₃ hc))
  · intro e
    obtain ⟨P, hP⟩ := hE.1
    have hv := (hr₄ (lifted P) P (hlift P)).mp hP
    rw [e] at hv
    have hc := (hr₂₄ (lifted P) P (hlift P)).mpr hv
    obtain ⟨τ, Q, -, -, v₄, -, v₂₄⟩ := period P
    have h := OnePoint.coe_injective ((v₄ hP).symm.trans (v₂₄ hc))
    norm_num at h
  · intro e
    obtain ⟨P, hP⟩ := hE.2.1
    have hv := (hr₃ (lifted P) P (hlift P)).mp hP
    rw [e] at hv
    have hc := (hr₂₄ (lifted P) P (hlift P)).mpr hv
    obtain ⟨τ, Q, -, -, -, v₃, v₂₄⟩ := period P
    exact OnePoint.infty_ne_coe _ ((v₃ hP).symm.trans (v₂₄ hc))

end Y3P1j

#print axioms Y3P1j.cm_period_values
#print axioms Y3P1j.exists_rational_CM_fibres_of_periods
