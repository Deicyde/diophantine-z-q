/-
H5 lane3: ROOT `NOSSepGlue.MainLeaf`. It discharges MAIN's open leaf `NOSSepDict.NeronOggShafarevichSep`
(`ZInQKernel/Contrib/OneProof/NeronOggShafarevichSep.lean`, main c0f3d085 = e1b31749, unchanged), both
directions over an arbitrary separable closure `Ks`, against the REAL definition. No copy of the definition.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe 0.

Modelled on the owner's `scratch/nos-proof/SepCompat.lean` (wip/nos-proof e9828e92, banked 89472f6c). That file proves
a copy of this leaf from `NOSProof.NOSConverseSep`. Here the converse is OUR `nosConverseSep_proof`
(`NOSSepGlue/Glue.lean`).

CREDIT. The forward directions are the owner's proved lemmas, imported, never copied, from
`ZInQKernel/Contrib/OneProof/NeronOggShafarevich.lean` on the owner's unmerged branch wip/nos-proof,
commit e9828e923c775b67e575fed6916fd55ae54950c3 (sha256 c42e27c9…), staged byte-exact:
* (a) ⇒ (b) over any field `Ω ⊇ K`: `NOSProof.inertiaTrivialOn_of_goodReduction_any`, at `Ω = Ks`;
* (b) ⇒ (c): `NOSProof.infinite_natCast_isUnit`.
The (c) ⇒ (a) direction over `Ks` is H5's: `ZInQ.Contrib.CloudR2NOS.NOSSepGlue.nosConverseSep_proof`.
-/
import ZInQKernel.Contrib.OneProof.NeronOggShafarevichSep
import ZInQKernel.Contrib.OneProof.NeronOggShafarevich
import ZInQKernel.Contrib.CloudR2NOS.NOSSepGlue.Glue

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.NOSSepGlue

/-- **Main's leaf `NOSSepDict.NeronOggShafarevichSep`** (Serre–Tate 1968, Thm 1, over a separable closure): the
owner's forward lemmas (e9828e92), plus H5's converse `nosConverseSep_proof`. -/
theorem neronOggShafarevichSep_proof : NOSSepDict.NeronOggShafarevichSep := by
  intro K _ O _ Ks _ _ _ w hw A _
  -- (c) ⇒ (a): H5's converse over `Ks`
  have hca := nosConverseSep_proof K O Ks w hw A
  -- (a) ⇒ (b): the owner's `inertiaTrivialOn_of_goodReduction_any` at `Ω = Ks`
  have hab : PkgI2.HasGoodReduction A O →
      ∀ m : ℕ, 0 < m → IsUnit (m : O) → PkgI2.InertiaTrivialOn A w m :=
    fun hA m _ hu => NOSProof.inertiaTrivialOn_of_goodReduction_any O Ks w hw A hA m hu
  -- (b) ⇒ (c): the owner's `infinite_natCast_isUnit`
  have hbc : (∀ m : ℕ, 0 < m → IsUnit (m : O) → PkgI2.InertiaTrivialOn A w m) →
      {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite := by
    intro hb
    refine (NOSProof.infinite_natCast_isUnit O).mono ?_
    rintro m ⟨hm, hu⟩
    exact ⟨hm, hu, hb m hm hu⟩
  exact ⟨⟨hab, fun hb => hca (hbc hb)⟩, ⟨fun hA => hbc (hab hA), hca⟩⟩

end ZInQ.Contrib.CloudR2NOS.NOSSepGlue
