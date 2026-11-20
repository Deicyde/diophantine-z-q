import ZInQKernel.Contrib.OneProof.RC.KatoP2.EvenBridgeChecked
import ZInQKernel.Contrib.OneProof.RC.KatoP2.RealSign

/-! Build a constituent for the checked Appendix E consumers with the real
sign proved from its actual Tate representation. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PrintsArith

/-- Supply a constituent to the existing consumers without a separate
real sign argument. The conductor parameter `d` retains the full odd
filter, so the transfer uses `D = d * 2^a`. -/
def KodaiConstituent.ofArithmetic {E : WeierstrassCurve ℚ} {c ds d : ℕ}
    {Z : RetainedZeta E c ds} (a : ℕ) (es : EulerSystemData ℤ_[2])
    (transfer : TwistTransfer Z d a es) (full : KodaiFullOpen (kodaiBase E d))
    (retainedIw : KodaiJStar) (finiteH2 : Module.Finite KatoLambda2 full.iw.H2)
    (tower : KodaiTower es (kodaiBase E d) full.iw) (class07 : tower.IsClass07)
    (H1compare : KatoH1Comparison es (kodaiBase E d) full.iw retainedIw.iw tower)
    (H2cone : KatoOddSupportCone full retainedIw) (charGalois : GalQ →* ℤˣ)
    (char_eq : ∀ [NeZero (primitiveD d a)] {ζ : Qbar}
      (hζ : IsPrimitiveRoot ζ (primitiveD d a)) (g : GalQ),
        ((charGalois g : ℤ) : ℤ_[2]) = (transfer.χ (hζ.autToPow ℚ g) : ℤ_[2]))
    (nonzeroClass : GenericNonzero full.iw) : KodaiConstituent Z d := by
  letI := Z.elliptic
  exact
    { a := a
      es := es
      transfer := transfer
      full := full
      retainedIw := retainedIw
      finiteH2 := finiteH2
      tower := tower
      class07 := class07
      H1compare := H1compare
      H2cone := H2cone
      charGalois := charGalois
      char_eq := char_eq
      realSign := (rationalTwist_realSigns E charGalois).1
      nonzeroClass := nonzeroClass }

end ZInQ.Manuscript.RC.KatoP2.Checked
