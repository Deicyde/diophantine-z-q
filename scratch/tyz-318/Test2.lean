import ZInQKernel.Contrib.TYZGenus.RingClassBridge
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b NumberField
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

variable (d : ℕ) [NeZero d]

instance : FiniteDimensional (QNeg d) (Hprime d) := by rw [Hprime_eq_ringSubfield]; infer_instance
instance : IsGalois (QNeg d) (Hprime d) := by rw [Hprime_eq_ringSubfield]; infer_instance
instance : FiniteDimensional ℚ (Hprime d) := Module.Finite.trans (QNeg d) (Hprime d)
instance : NumberField (Hprime d) := ⟨⟩

#synth Algebra (𝓞 (QNeg d)) (𝓞 (Hprime d))
#synth MulSemiringAction Gal(Hprime d/QNeg d) (𝓞 (Hprime d))
#synth IsGaloisGroup Gal(Hprime d/QNeg d) (𝓞 (QNeg d)) (𝓞 (Hprime d))
#check @Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
#check @splitSet
#check @mem_splitSet_iff
