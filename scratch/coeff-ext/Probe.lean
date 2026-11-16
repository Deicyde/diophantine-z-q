import ZInQKernel.Contrib.OneProof.DSThm965Weak
import ZInQKernel.Contrib.T25.Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector

open IsDedekindDomain
#check @HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
#check @HeightOneSpectrum.valuation_lt_one_iff_mem
#check @HeightOneSpectrum.valuation_of_algebraMap
#check @HeightOneSpectrum.intValuation_lt_one_iff_mem
#check @UniformSpace.Completion.extensionHom
#check @HeightOneSpectrum.adicCompletion.equiv
#check @HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion
#check @Valued.hasBasis_nhds_zero
#check @Matrix.charpoly_map
#check @PadicAlgCl.norm_extends
#check @FiniteDimensional.complete
#check @Units.continuous_map
#check @HeckeRing.GL2.coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
#check @SwanBridge.isIntegral_iff_norm_le_one
#check @NumberField.RingOfIntegers
#check @IntermediateField.adjoin.finiteDimensional
#check @UniformSpace.Completion.extension
#check @HeightOneSpectrum.adicCompletion.coe_toCompletion
#check @Polynomial.aeval_algHom_apply
#check @Matrix.aeval_map
example (ℓ : ℕ) [Fact ℓ.Prime] : NormedAlgebra ℚ_[ℓ] (PadicAlgCl ℓ) := inferInstance
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) : TopologicalSpace (GL (Fin 2) (v.adicCompletion K)) := inferInstance
