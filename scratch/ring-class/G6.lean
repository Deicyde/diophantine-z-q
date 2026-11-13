import ZInQKernel.Contrib.TYZGenus.RingClassGenus

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section ArtinPrime

open ZInQ.RouteK.Rank5b

variable (d : ℕ) [NeZero d]

instance : (Subgroup.zpowers (artin4 d (sigmaClass d))).Normal := Subgroup.normal_of_comm _

/-- **The Artin isomorphism for `H'_d`**: `Pic(O_{d,4})/⟨σ_{1+2ϖ}⟩ ≃* Gal(H'_d/K_d)` (`Cl'_d` of TYZ). -/
def artinPrime : Pic (O4 d) ⧸ Subgroup.zpowers (sigmaClass d) ≃* Gal(Hprime d/QNeg d) :=
  (QuotientGroup.congr (Subgroup.zpowers (sigmaClass d)) (Subgroup.zpowers (artin4 d (sigmaClass d)))
      (artin4 d) (by rw [MonoidHom.map_zpowers]; rfl)).trans
    ((IsGalois.normalAutEquivQuotient (Subgroup.zpowers (artin4 d (sigmaClass d)))).trans
      (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv _)))

/-- `artinPrime` is the restriction of the Artin symbol of `H_{d,4}`. -/
theorem artinPrime_mk_apply (c : Pic (O4 d)) (x : Hprime d) :
    ((artinPrime d (QuotientGroup.mk c) x : Hprime d) : SeparableClosure (QNeg d)) =
      ((artin4 d c ⟨x, Hprime_le_H4 d x.2⟩ : H4 d) : SeparableClosure (QNeg d)) := by
  have h := AlgEquiv.restrictNormal_commutes (artin4 d c)
    (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d))))
    ((IntermediateField.liftAlgEquiv
      (IntermediateField.fixedField (Subgroup.zpowers (artin4 d (sigmaClass d))))).symm ⟨x.1, x.2⟩)
  simp only [artinPrime, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    IsGalois.normalAutEquivQuotient_apply, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.restrictNormalHom_apply]
  exact congrArg Subtype.val h

instance : FiniteDimensional (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance

instance : IsGalois (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance

theorem card_artinPrime : Nat.card (Pic (O4 d) ⧸ Subgroup.zpowers (sigmaClass d)) =
    Module.finrank (QNeg d) (Hprime d) := by
  rw [Nat.card_congr (artinPrime d).toEquiv, IsGalois.card_aut_eq_finrank]

end ArtinPrime

end ZInQ.Contrib.TYZGenus.RingClass
