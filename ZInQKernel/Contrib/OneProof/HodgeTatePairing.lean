import ZInQKernel.Contrib.OneProof.HodgeTatePairingCore
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.TateTwistInvariants
import ZInQKernel.Contrib.OneProof.MilneIsogenyQuasiInverse
import ZInQKernel.Contrib.OneProof.PhiAmpleIsogeny
import ZInQKernel.OneProof.H.TailZ24

/-!
# `HodgeSplit.HodgeTateDecompAbVar` from a dimension-free printed leaf

Task hodgetate-from-dr (2026-11-16; report `docs/research/hodgetate-from-dr.md`).

The open field `hodgeTateDecompAbVar` (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`,
`ZInQKernel/OneProof/H/TailS.lean`) is the Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`; it was
rated GLUE because the coordinate form needs `dim t_A = dim t_{A'}^* = g`. Here it is proved from

* the new leaf `HodgeTateDecompExists` (Fontaine's decomposition with bases chosen, dimensions `a`, `b`
  unspecified: a specialization of the printed theorem with no other input), and
* open fields already in the bundles: T5 (`mumfordTorsionAlgClosed`, giving `T_p(A)` free of rank `2g`) and the
  four Picard leaves behind T9 (`picRepresentableAbVar`, `picZeroAbVar`, `mumfordKLFiniteSectionAC`,
  `mumfordPhiSurjectiveAC`, `weilPairingMumford`, giving a polarization and the Weil pairing),

with Tate's two theorems and the isogeny quasi-inverse supplied by their contributions. The proof: the Weil pairing
is a nondegenerate `G_F`-equivariant pairing on `V_p(A)` with multiplier the cyclotomic character, which forces
`a = b` (`eq_of_pairing`), and `a + b = dim V_p(A) = 2g`.
-/

namespace ZInQ.Contrib.HodgeTateFromPairing

/-- **`HodgeTateDecompAbVar` from the leaf `HodgeTateDecompExists` and open fields of the bundles**: T5
(`AvSplit.MumfordTorsionAlgClosed`) and the leaves of T9 (`T09Pic.t09SymmIsogenyExists_of_four` with
`PicFix.phiAmpleIsogeny_of_printed`). Tate's two theorems, Ax–Sen–Tate and the isogeny quasi-inverse are
theorems (contributions `TateTwistInvariants`, `AxSenTate`, `MilneIsogenyQuasiInverse`). -/
theorem hodgeTateDecompAbVar_of_printed (hHT : HodgeTateDecompExists)
    (hM : _root_.AvSplit.MumfordTorsionAlgClosed) (h1 : _root_.T09Pic.PicRepresentableAbVar)
    (h2 : _root_.T09Pic.PicZeroAbVar) (h3 : _root_.PicFix.MumfordKLFiniteSectionAC)
    (h4 : _root_.PicDict.MumfordPhiSurjectiveAC) (h5 : _root_.T09Pic.WeilPairingMumford) :
    ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar :=
  hodgeTateDecompAbVar_of_leaves hHT ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    ZInQ.Contrib.CloudB3W11.axSenTate_proof
    (_root_.T09Pic.t09SymmIsogenyExists_of_four h1 h2 (_root_.PicFix.phiAmpleIsogeny_of_printed h3 h4) h5)
    (HDec.HSyn.isogenyQuasiInverse_lf7 ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof)
    (_root_.AvSplit.Final.h25 hM)

end ZInQ.Contrib.HodgeTateFromPairing

#print axioms ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_printed
