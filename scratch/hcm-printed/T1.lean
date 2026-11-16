import ZInQKernel.Contrib.OneProof.QMRecPrinted
open NumberField IsDedekindDomain TauCeti.GlobalNumberFields
#check (IsDedekindDomain.FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 ℚ) (K := ℚ))
#check @RayClassCFT.ZhatS
#check @ShimuraCFT.ZhatS
example (m : ℕ) [NeZero m] : NumberField (T5Glue.QNeg m) := inferInstance
example (m : ℕ) [NeZero m] : Algebra (FiniteAdeleRing (𝓞 ℚ) ℚ) (FiniteAdeleRing (𝓞 (T5Glue.QNeg m)) (T5Glue.QNeg m)) := inferInstance
#check @finiteAdeleBaseChangeAlgEquiv
#check @IsDedekindDomain.FiniteAdeleRing.closure_range_algebraMap
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L] : FiniteDimensional K L := inferInstance
example (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L] (Ks : Type) [Field Ks] [Algebra K Ks] (ι : L →ₐ[K] Ks) [IsAbelianGalois K L] : IsAbelianGalois K ι.fieldRange := inferInstance
#check @IsAbelianGalois.of_algEquiv
#check @ShimuraCFT.exists_iota
#check @ZInQ.Contrib.TYZGenus.CM.ιC
