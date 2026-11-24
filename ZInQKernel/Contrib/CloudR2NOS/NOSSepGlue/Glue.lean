/-
H5 lane3: `nosConverseSep_proof` — the target `NOSProof.NOSConverseSep` (owner e9828e92,
`ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean` L332–337), body written out, at universe 0.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.
It instantiates the converse-only chain (`EndToEnd/ConverseOnly.lean`, universe u) at u := 0
(instantiation, not transfer) and applies the glue (`NOSSepGlue/Lemmas.lean`). SOURCE STATUS: it
depends on the stage chain and the open gates recorded in the V5/NOS plans.
-/
import ZInQKernel.Contrib.CloudR2NOS.NOSSepGlue.Lemmas
import ZInQKernel.Contrib.CloudR2NOS.EndToEnd.ConverseOnly

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.NOSSepGlue

/-- **The target leaf `NOSConverseSep`**, its statement written out (see
`NOSSepGlue/Adapter.lean` for the defeq check against the owner's definition). -/
theorem nosConverseSep_proof :
    ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (Ks : Type) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
      (w : ValuationSubring Ks), w.comap (algebraMap K Ks) = O →
      ∀ (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A],
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite →
        PkgI2.HasGoodReduction A O :=
  nosConverseSep_of_converse ZInQ.Contrib.CloudR2NOS.EndToEnd.originalInfiniteConverse_only.{0}

end ZInQ.Contrib.CloudR2NOS.NOSSepGlue
