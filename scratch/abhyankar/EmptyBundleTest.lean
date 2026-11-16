import ZInQKernel.Contrib.OneProof.Abhyankar
/-! Check that the empty bundle autofold generates (`OpenGlue9`) parses, and the discharge term typechecks
against the field type `SGRDirect.NVLocalInertia` of sgr-fold's `OpenGlue8`. -/
namespace AbhTest
structure OpenGlue9 : Prop where

/-- doc -/
theorem t (_n : OpenGlue9) : SGRDirect.NVLocalInertia := _root_.Abhyankar.nvLocalInertia
example : OpenGlue9 := ⟨⟩
end AbhTest
