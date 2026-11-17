/-
H5 lane3: `NOSSepGlue.MainLeafConditional`. Main's leaf `NOSSepDict.NeronOggShafarevichSep` from the converse over
`K̄ = AlgebraicClosure K` (at universe 0), taken as a hypothesis. It needs NO H5 converse source, so it can be
compile-probed NOW, from main's suppliers, the owner's file (wip/nos-proof e9828e92, staged byte-exact) and
`NOSSepGlue/Lemmas` alone. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe 0.
It follows the owner's `scratch/nos-proof/SepCompat.lean` (89472f6c), against the REAL main definition. CREDIT: the
forward directions are the owner's `NOSProof.inertiaTrivialOn_of_goodReduction_any` (at `Ω = Ks`) and
`NOSProof.infinite_natCast_isUnit`, imported from e9828e92.
-/
import ZInQKernel.Contrib.OneProof.NeronOggShafarevichSep
import ZInQKernel.Contrib.OneProof.NeronOggShafarevich
import ZInQKernel.Contrib.CloudR2NOS.NOSSepGlue.Lemmas

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.NOSSepGlue

/-- Main's leaf from the converse over `K̄`: the owner's forward lemmas plus the glue `nosConverseSep_of_converse`. -/
theorem neronOggShafarevichSep_of_converse
    (hconv : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (w : ValuationSubring (AlgebraicClosure K)),
      w.comap (algebraMap K (AlgebraicClosure K)) = O →
      ∀ (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A],
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite →
        PkgI2.HasGoodReduction A O) :
    NOSSepDict.NeronOggShafarevichSep := by
  intro K _ O _ Ks _ _ _ w hw A _
  have hca := nosConverseSep_of_converse hconv K O Ks w hw A
  have hab : PkgI2.HasGoodReduction A O →
      ∀ m : ℕ, 0 < m → IsUnit (m : O) → PkgI2.InertiaTrivialOn A w m :=
    fun hA m _ hu => NOSProof.inertiaTrivialOn_of_goodReduction_any O Ks w hw A hA m hu
  have hbc : (∀ m : ℕ, 0 < m → IsUnit (m : O) → PkgI2.InertiaTrivialOn A w m) →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite := by
    intro hb
    refine (NOSProof.infinite_natCast_isUnit O).mono ?_
    rintro m ⟨hm, hu⟩
    exact ⟨hm, hu, hb m hm hu⟩
  exact ⟨⟨hab, fun hb => hca (hbc hb)⟩, ⟨fun hA => hbc (hab hA), hca⟩⟩

end ZInQ.Contrib.CloudR2NOS.NOSSepGlue
