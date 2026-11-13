import ZInQKernel.Contrib.Different.Local
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Exponent
open NumberField IsDedekindDomain IsLocalRing
open scoped AdicCompletionExtension
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
#synth IsDiscreteValuationRing (v.adicCompletionIntegers ℚ)
#synth IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ)
#synth PerfectField (ResidueField (v.adicCompletionIntegers ℚ))
#synth Finite (ResidueField (v.adicCompletionIntegers ℚ))
#synth IsDiscreteValuationRing (w.adicCompletionIntegers L)
#synth Algebra (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)
#synth Module.Finite (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)
#synth Module.IsTorsionFree (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)
#synth CharZero (FractionRing (v.adicCompletionIntegers ℚ))
#synth Algebra.IsSeparable (FractionRing (v.adicCompletionIntegers ℚ)) (FractionRing (w.adicCompletionIntegers L))
#check @IsDedekindDomain.HeightOneSpectrum.multiplicity_map_adicCompletionIntegers
#check @IsDedekindDomain.HeightOneSpectrum.differentExponent_adicCompletion_eq_multiplicity_differentIdeal
