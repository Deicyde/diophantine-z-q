import Mathlib
open WithZero
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
example : T2Space K := inferInstance
example (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) : T2Space (v.adicCompletion ℚ) := inferInstance
