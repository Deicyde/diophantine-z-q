import ZInQKernel.Contrib.OneProof.NeronOggShafarevich
import ZInQKernel.Contrib.CloudR2NOS.NOSSepGlue.Lemmas

/-! H5 lane3 conditional adapter (2026-11-17, SOURCE-ONLY). It needs NO H5 converse source and is
buildable from main's suppliers and the owner's file alone: the glue turns the converse over `K̄` (at
universe 0) into the owner's `NOSProof.NOSConverseSep`, and elaboration checks that statement match by defeq. -/
example (hconv : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (w : ValuationSubring (AlgebraicClosure K)),
      w.comap (algebraMap K (AlgebraicClosure K)) = O →
      ∀ (A : CategoryTheory.Grp (CategoryTheory.Over (AlgebraicGeometry.Spec (.of K))))
        [PkgI2.IsAbelianVariety A],
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite →
        PkgI2.HasGoodReduction A O) :
    NOSProof.NOSConverseSep :=
  ZInQ.Contrib.CloudR2NOS.NOSSepGlue.nosConverseSep_of_converse hconv
