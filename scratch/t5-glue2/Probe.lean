import ZInQKernel.Contrib.TYZGenus.ShimuraModFn
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormSubgroup
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory IsDedekindDomain
variable (K : Type) [Field K] [NumberField K]
example (v : HeightOneSpectrum (𝓞 K)) : CompactSpace (v.adicCompletionIntegers K) := inferInstance
#check @globalGroundEquiv
#check @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
#check @Submonoid.units_isCompact
#check @FiniteAdeleRing.isCompact_integralAdeles
#check @NormalLayer.LayerRefinement.quotientHom_abelianizationRestrict
#check @LayerRefinement.quotientHom_abelianizationRestrict
#check @ClassFormation.surjective_artinMap
#check @Continuous.units_map
#print ZInQ.RouteK.Rank5b.QNeg
example (m : ℕ) [NeZero m] : NumberField (ZInQ.RouteK.Rank5b.QNeg m) := inferInstance
#check @NumberField.IsTotallyComplex
