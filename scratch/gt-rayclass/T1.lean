import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
open IsDedekindDomain HeightOneSpectrum NumberField
set_option pp.explicit true in
example (v : HeightOneSpectrum (𝓞 ℚ)) (a : v.adicCompletion ℚ) : True := by
  obtain ⟨b, hb, hab⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  trace_state
  trivial
#check @coe_mem_adicCompletionIntegers
