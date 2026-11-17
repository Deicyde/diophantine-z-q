import ZInQKernel.OneProof.H.TailZ48
import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZero
-- copied from ZInQKernel/OneProof/H/TailZ45.lean:99 (OpenAddedLeaves19)
namespace HDec
namespace HSyn
/-- `OpenAddedLeaves18PZ` without `phiAmpleIsogeny`, `egaIV_8_10_5_xii`, with the leaves `mumfordKLFiniteSectionAC`, `mumfordPhiSurjectiveAC` (leaf-fold32-dict). -/
structure OpenAddedLeaves19PZ : Prop where
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L2, printed form: for every representation of `Pic_{A/K}`, its identity component with the induced
  group law is an abelian variety (`IsPicZero`; Mumford §13, Kleiman 9.5.1 and 9.5.3, SGA 3 VI_A 2.4; locators
  UNVERIFIED). -/
  picZeroAbVar : _root_.PicZeroChar0.PicZeroAbVar0
  /-- t09-pic, L4, printed form (single leaf): there is a pairing `A[n] × Pic⁰[n] → μ_n`, `n` invertible in `K`, with
  the values of Mumford's `ē_n` (`weilScalar`), perfect, Galois-equivariant, compatible in `n`, adjoint for the
  genuine dual `f^∨`, and trivial on `(x, λ_L x)` for ample `L` (Mumford §20 and §23; Milne 1986 §16; locators
  UNVERIFIED). -/
  weilPairingMumford : _root_.T09Pic.WeilPairingMumford
  /-- pic-fix: K(L) finite for L ample with a nonzero global section s (L = O(D), D = Z(s) effective) on an abelian variety over an algebraically closed field (Mumford, Abelian varieties, section 6 Application 1, (iv) => (ii), printed for L = O(D) with D effective; locator UNVERIFIED). -/
  mumfordKLFiniteSectionAC : _root_.PicZeroChar0.MumfordKLFiniteSectionAC0
  /-- pic-dict: for L ample every L' in Pic0(X) is t_x^*L (x) L^-1, X an abelian variety over an algebraically closed field (Mumford section 8 Thm 1; locator UNVERIFIED). -/
  mumfordPhiSurjectiveAC : _root_.PicDict.MumfordPhiSurjectiveAC
end HSyn
end HDec

-- copied from ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean:2078 (openTextbookLeaves13_of_OpenTextbookLeaves14_hf)
set_option linter.all false
set_option linter.all false
set_option linter.all false
set_option linter.all false
set_option linter.all false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
namespace HDec
namespace HSyn
/-- `OpenTextbookLeaves13HF` from `OpenTextbookLeaves14HF`: `poincareComplement` by the contributions. -/
theorem openTextbookLeaves13_of_OpenTextbookLeaves14_hf_pz (n : OpenTextbookLeaves14HF) (l : OpenAddedLeaves19PZ) : OpenTextbookLeaves13HF where
  mumfordTorsionAlgClosed := n.mumfordTorsionAlgClosed
  homFreeFiniteAlgClosed := _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC _root_.uniformizationLeafAll_proof n.mumfordTorsionAlgClosed
  charPolyIndepOfEllAlgClosed := n.charPolyIndepOfEllAlgClosed
  poincareComplement := _root_.PicZeroChar0.Poincare.poincareComplement_of_open0 l.picRepresentableAbVar l.picZeroAbVar (_root_.PicZeroChar0.phiAmpleIsogeny0_of_printed l.mumfordKLFiniteSectionAC l.mumfordPhiSurjectiveAC) _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof _root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
  gagaMorphism := n.gagaMorphism
  neronSchemeExtensionExists := n.neronSchemeExtensionExists
end HSyn
end HDec

