import ZInQKernel.Contrib.OneProof.C8ConradB
import ZInQKernel.Contrib.OneProof.CartierSmooth
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.GroupSchemeEquidim
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Main

/-! # c8-conrad2: the C8 and Poincaré swaps (the Picard rows off consumers (i) and (ii))

* **(ii) Step E1-E2, Poincaré reducibility** (diophantine_zq.tex L865, paragraph "Transfer from a modular
  Jacobian": "Absolute simplicity and Poincaré reducibility give an `L'`-isogeny `A × Z → J`"; the manuscript cites
  nothing there). The chain reads Poincaré's theorem as the textbook field `poincareComplement :
  ZInQ.Contrib.AVB1.PoincareComplement` of `OpenTextbookLeaves13HF`, which the current top fills from the Picard rows
  (`PicZeroChar0.Poincare.poincareComplement_of_open0`, PicZeroCharZeroCopy L2218). Here the field is restored as a
  printed textbook leaf, classed ELLIOT (an uncited manuscript step): `openTextbookLeaves13HF_of_open16_P` builds the
  bundle with `poincareComplement := hP`, and `t8_of_poincareComplement` is the chain's own derivation of the
  consumer's `t8 : PkgI3.PoincareReducibility` (`AVGlue.poincareReducibility_of_published'`, TailP L1257) with its
  other inputs proved.
* **(i) Step C8** (L758-766): `C8Inputs` bundles the new inputs of `C8Conrad.c8TwistFinite_of_leaves` (C8CFT), and
  `g12DetPZ_of_inputs` is the term that replaces `g12Det_of_pz m.r14det m.detTate m.finIndex …` at
  `g8_g12_of_leaves3_hf_pz_eb` (EichlerBoundCopy L2485). -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

/-- The inputs of the C8 reroute that are not in the chain: the leaf `conradAppB` (Conrad App. B, pp. 32-33, base field
`ℚ_p`, the manuscript's citation: p. 32 and Prop. B.3; conrad-b3 replaced c8-conrad2's two leaves `conradAppBQp` and
`tateTwistInvariantsInertia` (Tate 1967 §3.3 Thm 2 over the completion of `K^{ur}`, a departure) by this one), the two
dictionary statements `inertiaAtPDecomp` and `minkowskiInertiaQ` (GLUE, proved in `C8Dicts`), and the glue
`twistCharHTWt0` (proved in `C8Twist`). `LocAlgExponentEqWeight` (`C8ConradB`) and `FiniteOfLocAlgTrivialQ`
(`C8CFT`) are proved from these. -/
structure C8Inputs : Prop where
  conradAppB : ConradAppB
  twistCharHTWt0 : TwistCharHTWt0
  inertiaAtPDecomp : InertiaAtPDecomp
  minkowskiInertiaQ : MinkowskiInertiaQ

/-- **C8's consumer from the C8 inputs** (the replacement term at `g8_g12_of_leaves3_hf_pz_eb`). -/
theorem g12DetPZ_of_inputs (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT) (c : C8Inputs)
    (h9 : G9GlueNoT23) (hdR : PkgI4.DeRhamComparison) : G12DetPZ :=
  g12DetPZ_of_twistFinite (c8TwistFinite_of_conradB hR hHT c.conradAppB c.twistCharHTWt0 c.inertiaAtPDecomp
    c.minkowskiInertiaQ) h9 hdR

end HDec.G0Galois.C8Conrad

namespace HDec.HSyn

/-- **T8 (Poincaré reducibility, the consumer's form) from Poincaré's complement theorem**, without the Picard rows:
the chain's own derivation (`AVGlue.poincareReducibility_of_published'`, as in `textbookLeaves6_of_open7_hf_pz`,
PicZeroCharZeroCopy L1640) with Cartier's theorem, Milne's quasi-inverse, `geomConnOfRationalPoint` and
`groupSchemeEquidim` proved. -/
theorem t8_of_poincareComplement (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) :
    _root_.PkgI3.PoincareReducibility :=
  _root_.AVGlue.poincareReducibility_of_published' _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof hP
    (isogenyQuasiInverseAG_lf7 _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof)
    _root_.geomConnOfRationalPoint_proof _root_.groupSchemeEquidim_proof

/-- **The textbook bundle `OpenTextbookLeaves13HF` with Poincaré's theorem as a leaf** (copy of
`openTextbookLeaves13HF_of_open16_22_pz`, PicZeroCharZeroCopy L2211, with `poincareComplement := hP` in place of
`poincareComplement_of_open0 l.picRepresentableAbVar l.picZeroAbVar …`; the added bundle is no longer read). -/
theorem openTextbookLeaves13HF_of_open16_P (t : OpenTextbookLeaves16)
    (h : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind)
    (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement) : OpenTextbookLeaves13HF where
  mumfordTorsionAlgClosed := t.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC _root_.uniformizationLeafAll_proof
    t.mumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed := t.charPolyIndepOfEllAlgClosed
  poincareComplement := hP
  gagaMorphism := t.gagaMorphism
  neronSchemeExtensionExists := _root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind h

end HDec.HSyn
