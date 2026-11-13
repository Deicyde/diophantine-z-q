import ZInQKernel.HDecomp.ModCurves.X1Belyi
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Inertia

open WeierstrassCurve IsDedekindDomain
#check @WeierstrassCurve.finite_torsionBy
#check @IntermediateField.adjoin_adjoin_coe_preimage
#check @IsIntegralClosure.isDedekindDomain
#check @IsIntegralClosure.isFractionRing_of_finite_extension
#check @IsIntegralClosure.MulSemiringAction
#check @IsGaloisGroup.of_isFractionRing
#check @Ideal.inertia
#check @Ideal.card_inertia_eq_ramificationIdxIn
#check @ValuationSubring.inertiaSubgroup
#check @ValuationSubring.decompositionSubgroup
#check @HeightOneSpectrum.valuation_of_algebraMap
#check @HeightOneSpectrum.intValuation_le_pow_iff_dvd
#check @HeightOneSpectrum.valuation_lt_one_iff_mem
#check @HeightOneSpectrum.valuation_le_one
#check @WeierstrassCurve.Affine.Point.xCoord
#check @WeierstrassCurve.Affine.Point.algEquiv_eq_one_of_adjoin_coords_eq_top
#check @WeierstrassCurve.inertiaSubgroup_eq_bot_of_adjoin_coords_eq_top
#check @WeierstrassCurve.Affine.Point.map
#check @IsLocalRing.exists_factor_valuationRing
#check @IntermediateField.normal_iff_forall_map_le
#check @ValuationSubring.primeSpectrumOrderEquiv
#check @Ideal.ramificationIdx
#check @IsDedekindDomain.flat_iff_torsion_eq_bot
example (k : Type) [Field k] : IsDedekindDomain (Polynomial k) := inferInstance
example (k : Type) [Field k] [CharZero k] (M : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))) : Algebra (Polynomial k) M := inferInstance
example (k : Type) [Field k] [CharZero k] (M : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))) : Algebra.IsSeparable (RatFunc k) M := inferInstance
example (k : Type) [Field k] [CharZero k] (M : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))) : IsScalarTower (Polynomial k) (RatFunc k) M := inferInstance
