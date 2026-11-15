import ZInQKernel.Contrib.OneProof.CMStab
set_option linter.ambiguousOpen false
open LeafQM LeafQM.AV GapGlue.CMStab

theorem uij_val : (((LeafQM.AV.Pin.NormO.ui * LeafQM.AV.Pin.NormO.uj : Bˣ)) : B) = ⟨0, 0, 0, 1⟩ := by
  rw [Units.val_mul]
  ext <;> simp [LeafQM.AV.Pin.NormO.ui, LeafQM.AV.Pin.NormO.uj, LeafQM.AV.Pin.NormO.ei,
    LeafQM.AV.Pin.NormO.ej, ofInt]

theorem rep3_eq_αK : HDec.LeafQM.AV.Pin.Exact.rep 3 = αK := by
  apply RingEquiv.ext; intro a
  apply Subtype.ext
  rw [αK_coe]
  show ((LeafQM.AV.Pin.NormO.ui * LeafQM.AV.Pin.NormO.uj : Bˣ) : B) * a *
    (((LeafQM.AV.Pin.NormO.ui * LeafQM.AV.Pin.NormO.uj)⁻¹ : Bˣ) : B) = _
  have h : ((LeafQM.AV.Pin.NormO.ui * LeafQM.AV.Pin.NormO.uj : Bˣ) : B) * (a : B) =
      cK (a : B) * ((LeafQM.AV.Pin.NormO.ui * LeafQM.AV.Pin.NormO.uj : Bˣ) : B) := by
    rw [uij_val]; generalize (a : B) = y; ext <;> simp [cK] <;> ring
  rw [h, mul_assoc, Units.mul_inv, mul_one]
