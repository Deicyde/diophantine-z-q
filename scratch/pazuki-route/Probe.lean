import ZInQKernel.Contrib.OneProof.PazukiInputs

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

section
variable {k K : Type} [Field k] [Field K] [Algebra k K] {X : Scheme.{0}} [X.Over (Spec (.of k))]
set_option pp.explicit true in
example [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] :
    True := by
  have := Scheme.Modules.finrankH_pullback K M 0
  trace_state
  trivial
end
#check @bijective_appTop_of_isProper_of_geometricallyIntegral
#check @Scheme.Pic.mkIso
#check @Scheme.Modules.pullbackComp
#check @IsPullback.isoPullback_hom_fst
#check @Scheme.Modules.finrankH_pullback_of_isIso
#check @Scheme.Modules.finrankH_congr
example (X : Scheme.{0}) (L : X.Pic) : ((fromSkeleton X.Modules).obj L.val).IsQuasicoherent := inferInstance
#check @PicDict.picLocFinType_proof
#check @PicLFT.picLocFinType_proof
#check @PicDict.pushforwardUnitUniversal
#check @Functor.grpObjObj
