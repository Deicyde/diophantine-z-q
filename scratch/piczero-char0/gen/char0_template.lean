import ZInQKernel.Contrib.OneProof.PoincareComplement
import ZInQKernel.Contrib.OneProof.MumfordKLFinite
import ZInQKernel.Contrib.OneProof.PicZeroAbVar
import ZInQKernel.Contrib.OneProof.CartierSmooth

/-!
# `PicZeroAbVar` in characteristic `0`, from three LEAF statements and Cartier's theorem (piczero-char0)

The open field `picZeroAbVar : T09Pic.PicZeroAbVar` (the identity component of `Pic_{A/K}` is an abelian variety)
quantifies over every field `K`. In `ZInQ.OneProof.frozenTarget` it is used only at fields of characteristic `0`
(scratch/piczero-char0, docs/research/piczero-char0.md): through `t09SymmIsogenyExists` (read only by
`detTate_of_leaves4`, at number fields, and by T9, which reaches only the discarded antecedent of `G12Det`), through
`mumfordKLFiniteSectionAC` and `phiAmpleIsogeny` (which feed only those two), and through `poincareComplement`,
whose statement is already over fields of characteristic `0`.

This file gives the characteristic-`0` form of each of these statements and proves them:

* `PicZeroChar0.picZeroAbVar0_of_leaves : PicDict.PicLocFinType → PicDict.IdentityComponentLFT →
  PicFix.KleimanPicZeroProper → PicZeroAbVar0` (pic-smooth's argument, with Cartier's theorem supplied by
  `ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof`; no `PicZeroSmoothPosChar`);
* `mumfordKLFiniteSectionAC0_of_open`, `phiAmpleIsogeny0_of_printed`, `t09SymmIsogenyExists0_of_four`,
  `poincareComplement_of_open0`: the proofs of `PhiAmple.mumfordKLFiniteSectionAC_of_open`,
  `PicFix.phiAmpleIsogeny_of_printed`, `T09Pic.t09SymmIsogenyExists_of_four` and
  `PoincareComplement.poincareComplement_of_open`, copied verbatim with `[CharZero K]` added (each applies its
  hypotheses only at the field it is about, or at its algebraic closure, again of characteristic `0`).

The rerouted bundle chain that reads these is `PicZeroAbVarCharZeroReroute.lean` (generated).
-/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

set_option linter.style.haveILetI false

namespace PicZeroChar0

open T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

/-! ## §1. pic-smooth's statements at one field (copied from wip/pic-smooth,
`ZInQKernel/Contrib/OneProof/PicZeroSmoothCartier.lean`, lines 35-142, namespace changed) -/

@PS_BODY@

/-! ## §2. The characteristic-`0` statements -/

/-- **`T09Pic.PicZeroAbVar` over fields of characteristic `0`** (a consequence of it, never stronger). -/
def PicZeroAbVar0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : AbVar K) (j : B.X ⟶ P), IsPicZero rep B j

/-- **`PicFix.MumfordKLFiniteSectionAC` over algebraically closed fields of characteristic `0`.** -/
def MumfordKLFiniteSectionAC0 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : AbVar k) (c₀ : X.X.left.Pic), IsAmple X.X.left c₀ →
    (∃ s : 𝟙_ X.X.left.Modules ⟶ AC.modX c₀, s ≠ 0) →
    {x : AC.Kpt X | AC.phi c₀ x = 1}.Finite

/-- `PicDict.MumfordKLFiniteAC` over algebraically closed fields of characteristic `0`. -/
def MumfordKLFiniteAC0 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X : AbVar k) (c₀ : X.X.left.Pic), IsAmple X.X.left c₀ →
    {x : AC.Kpt X | AC.phi c₀ x = 1}.Finite

/-- `PicDict.MumfordKLFinite` over fields of characteristic `0`. -/
def MumfordKLFinite0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K) (c₀ : (AK A).Pic), IsAmple (AK A) c₀ →
    {x : A.Pt (AlgebraicClosure K) | phiPt c₀ x = 1}.Finite

/-- **`T09Pic.PhiAmpleIsogeny` over fields of characteristic `0`.** -/
def PhiAmpleIsogeny0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ L : A.X.left.Pic, IsAmple A.X.left L →
      ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam

/-- **`HDec.WeilPairing.T09_SymmIsogenyExists` over fields of characteristic `0`.** -/
def T09_SymmIsogenyExists0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K), Nonempty (HDec.WeilPairing.SymmIsogeny A)

/-- Each characteristic-`0` form is a consequence of the general one. -/
theorem picZeroAbVar0_of_picZeroAbVar (h : PicZeroAbVar) : PicZeroAbVar0 := fun K _ _ => h K
theorem phiAmpleIsogeny0_of_phiAmpleIsogeny (h : PhiAmpleIsogeny) : PhiAmpleIsogeny0 := fun K _ _ => h K
theorem mumfordKLFiniteSectionAC0_of (h : MumfordKLFiniteSectionAC) : MumfordKLFiniteSectionAC0 :=
  fun k _ _ _ => h k
theorem t09SymmIsogenyExists0_of (h : HDec.WeilPairing.T09_SymmIsogenyExists) : T09_SymmIsogenyExists0 :=
  fun K _ _ => h K

/-! ## §3. `PicZeroAbVar0` from three LEAF statements (no characteristic-`p` input) -/

/-- **Main result.** `Pic⁰_{A/K}` is an abelian variety at every field of characteristic `0`, from
`PicLocFinType` (Kleiman 9.4.8 / BLR 8.2 Thm 3), `IdentityComponentLFT` (SGA 3 VI_A 2.4) and
`KleimanPicZeroProper` (Kleiman 9.5.4), with Cartier's theorem proved (`cartierSmooth_proof`). -/
theorem picZeroAbVar0_of_leaves (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3 : KleimanPicZeroProper) :
    PicZeroAbVar0 := fun K _ _ =>
  picZeroAbVarAt_charZero_of_cartier ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof h1 h2 h3 K

/-! ## §4. The consumers in characteristic `0` -/

section KL

open PhiAmple

set_option backward.isDefEq.respectTransparency false in
/-- `PhiAmple.mumfordKLFiniteAC_of_open` (phi-ample, `MumfordKLFinite.lean`) verbatim, characteristic `0`. -/
theorem mumfordKLFiniteAC0_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar0) :
    MumfordKLFiniteAC0 := by
@KL_BODY@

/-- `PhiAmple.mumfordKLFiniteSectionAC_of_open`, characteristic `0`. -/
theorem mumfordKLFiniteSectionAC0_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar0) :
    MumfordKLFiniteSectionAC0 :=
  fun k _ _ _ X c₀ hc₀ _ => mumfordKLFiniteAC0_of_open h1 h2 k X c₀ hc₀

end KL

section Phi

set_option backward.isDefEq.respectTransparency false in
/-- `PicFix.mumfordKLFiniteAC_of_section` (pic-fix) verbatim, characteristic `0`. -/
theorem mumfordKLFiniteAC0_of_section (h : MumfordKLFiniteSectionAC0) : MumfordKLFiniteAC0 := by
@SEC_BODY@

set_option backward.isDefEq.respectTransparency false in
/-- `PicDict.mumfordKLFinite_of_ac` (pic-dict) verbatim, characteristic `0` (`AlgebraicClosure K` has
characteristic `0`). -/
theorem mumfordKLFinite0_of_ac (h : MumfordKLFiniteAC0) : MumfordKLFinite0 := by
@AC_BODY@

set_option backward.isDefEq.respectTransparency false in
/-- `PicDict.phiAmpleIsogeny_of_printed` (pic-dict) verbatim, characteristic `0`. -/
theorem phiAmpleIsogeny0_of_parts (hKL : MumfordKLFinite0) (h8 : MumfordPhiSurjective)
    (hamp : AmpleBaseChangeAlgClosure) (hsub : PicZeroPtsTranslInv) :
    PhiAmpleIsogeny0 := by
@PR_BODY@

/-- **`PicFix.phiAmpleIsogeny_of_printed`, characteristic `0`**: from `MumfordKLFiniteSectionAC0` and Mumford §8
Thm 1 (`MumfordPhiSurjectiveAC`, unchanged), through the same proved glue as pic-dict's `phiAmpleIsogeny_final`. -/
theorem phiAmpleIsogeny0_of_printed (hKL : MumfordKLFiniteSectionAC0) (h8 : MumfordPhiSurjectiveAC) :
    PhiAmpleIsogeny0 :=
  phiAmpleIsogeny0_of_parts (mumfordKLFinite0_of_ac (mumfordKLFiniteAC0_of_section hKL))
    (mumfordPhiSurjective_of_ac h8) ampleBaseChangeAlgClosure
    (picZeroPtsTranslInv_of_leaves pushforwardUnitUniversal geomIntegralProd)

end Phi

section T9

/-- `T09Pic.t09SymmIsogenyExists_of_leaves` (TailZ24) verbatim, characteristic `0`, with L3 and L4 in the form
`t09SymmIsogenyExists_of_mumford` supplies them. -/
theorem t09SymmIsogenyExists0_of_leaves (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar0)
    (h3 : ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
      (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
      IsPicZero rep B j → ∀ L : A.X.left.Pic, IsVeryAmple A L →
        ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam)
    (h4 : WeilPairingPicZero) :
    T09_SymmIsogenyExists0 := by
@T9L_BODY@

/-- **`T09Pic.t09SymmIsogenyExists_of_four`, characteristic `0`.** -/
theorem t09SymmIsogenyExists0_of_four (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar0)
    (h3 : PhiAmpleIsogeny0) (h4 : WeilPairingMumford) : T09_SymmIsogenyExists0 :=
  t09SymmIsogenyExists0_of_leaves h1 h2
    (fun K _ _ A P rep B j hj L hL lam hlam => h3 K A P rep B j hj L (veryAmpleIsAmple K A L hL) lam hlam)
    (weilPairingPicZero_of_printed veryAmpleIsAmple (weilPairingPicZeroPrinted_of_mumford h4))

end T9

end PicZeroChar0

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace PicZeroChar0.Poincare

open PkgI3 PkgI3.AbVar ZInQ.Contrib.OneProof.PoincareComplement

variable {k : Type} [Field k]

/-- `PoincareComplement.exists_psi` (poincare-proof) verbatim, characteristic `0`. -/
theorem exists_psi0 [CharZero k] (h1 : T09Pic.PicRepresentableAbVar) (h2 : PicZeroChar0.PicZeroAbVar0)
    (h3 : PicZeroChar0.PhiAmpleIsogeny0) (J B : AbVar k) (i : Hom B J)
    (hi : IsClosedImmersion i.hom.left) :
    ∃ (D : AbVar k) (ψ : Hom J D), IsIsogenyMor (i.hom ≫ ψ.hom) := by
@PSI_BODY@

/-- **`poincareComplement`, proved from the characteristic-`0` forms** (poincare-proof's
`poincareComplement_of_open` verbatim, with `PicZeroAbVar0` and `PhiAmpleIsogeny0`). -/
theorem poincareComplement_of_open0 (h1 : T09Pic.PicRepresentableAbVar) (h2 : PicZeroChar0.PicZeroAbVar0)
    (h3 : PicZeroChar0.PhiAmpleIsogeny0) (hQ : AvSplit.MilneIsogenyQuasiInverse)
    (hC : AVGlue.CartierSmooth) : ZInQ.Contrib.AVB1.PoincareComplement := by
  intro k _ _ J B i hi
  obtain ⟨D, ψ, hψ⟩ := exists_psi0 h1 h2 h3 J B i hi
  exact complement_of_psi hQ hC J B D i ψ hψ

end PicZeroChar0.Poincare
