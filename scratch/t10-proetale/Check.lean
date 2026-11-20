import ZInQKernel.Contrib.OneProof.T10Proetale.ExtensionFibres
import ZInQKernel.Contrib.OneProof.T10Proetale.Tower
import ZInQKernel.Contrib.OneProof.T10Proetale.Transport

open ZInQ.Manuscript.T10Proetale

#print axioms injectivePresentation_shortExact
#print axioms extensionClass_surjective
#print axioms extensionClass_eq_zero_iff
#print axioms extensionClass_eq_iff
#print axioms local_sectionLifts
#print axioms exact_and_injective_on_sections
#print axioms sectionLifts_existsUnique_translate
#print axioms translate_restrict
#print axioms classOfSection_surjective
#print axioms classOfSection_eq_zero_iff

#print axioms residueStep_surjective_sections
#print axioms proTransition_surjective_H0
#print axioms difference_surjective
#print axioms proH0_difference_surjective
#print axioms continuous_toResidue
#print axioms proReduction_transition
#print axioms proReduction_transport

#print axioms galIso_inv_inv_eq_galAut
#print axioms graphPoint_galAut
#print axioms compose_transport_squares

open CategoryTheory AlgebraicGeometry

-- The forward construction applies to the actual integral coefficient sheaf.
example (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (x : X.EllAdicCohomology ℓ 1) :
    ∃ s, classOfSection (T10Etale.isTerminalProEt X) (T10Etale.F X ℓ) s = x ∧
      Presheaf.imageSieve (injectivePresentation (T10Etale.F X ℓ)).g.hom s ∈
        Scheme.ProEt.topology X (T10Etale.terminalProEt X) := by
  obtain ⟨s, hs⟩ := classOfSection_surjective (T10Etale.isTerminalProEt X) (T10Etale.F X ℓ) x
  exact ⟨s, hs, local_sectionLifts (injectivePresentation_shortExact _) s⟩
