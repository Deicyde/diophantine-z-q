import ZInQKernel.OneProof.H.TailZ22
/-! triage2 probe B: `babaGranathRationalAb` from Elkies' (derived) statement plus the existence of the three CM
pairs. The T1 glue step of task 3, attempted in full. -/
open CategoryTheory AlgebraicGeometry

namespace HDec.QMSplit.Moduli
open LeafQM LeafQM.AV

/-- Existence of QM pairs over `ℚ̄` with CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (the only content of the reverse
directions of Baba–Granath that the chain reads, through `CMExists`). -/
def CMPairsExistT2 : Prop :=
  (∃ P : QMPair Qbar, HasCM4 P.q) ∧ (∃ P : QMPair Qbar, HasCM3 P.q) ∧ (∃ P : QMPair Qbar, HasCM24 P.q)

theorem babaGranathRationalAb_of_elkiesT2 (hE : ElkiesEquationsX6Ab) (hC : CMPairsExistT2) :
    BabaGranathRationalAb := by
  classical
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hF, -⟩ := hE
  obtain ⟨⟨P4, c4⟩, ⟨P3, c3⟩, ⟨P2, c2⟩⟩ := hC
  have hx : ∀ P0 : QMPair Qbar, Ψ (Ψ.symm (Quotient.mk _ P0)) = Quotient.mk _ P0 :=
    fun P0 => Ψ.apply_symm_apply _
  refine ⟨Y, Φ, X, Ψ, fY, t, (OnePoint.some (1 : ℚ)), OnePoint.infty, (OnePoint.some (0 : ℚ)), h1, h6,
    by simp, by simp, by simp, ?_⟩
  intro x x' P Q hP hQ
  refine ⟨(hF x x' P Q hP hQ).1, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · simpa using (hF x x P P hP hP).2.2.1 h
  · have h' : t.val (K := Qbar) x.left = OnePoint.some 1 := by simpa using h
    obtain ⟨α, ⟨g⟩⟩ := ((hF _ x P4 P (hx P4) hP).1).1
      (((hF _ _ P4 P4 (hx P4) (hx P4)).2.2.1 c4).trans h'.symm)
    exact HasCM4.of_iso g ((hasCM4_twist P4.q α).2 c4)
  · simpa using (hF x x P P hP hP).2.2.2 h
  · have h' : t.val (K := Qbar) x.left = OnePoint.infty := by simpa using h
    obtain ⟨α, ⟨g⟩⟩ := ((hF _ x P3 P (hx P3) hP).1).1
      (((hF _ _ P3 P3 (hx P3) (hx P3)).2.2.2 c3).trans h'.symm)
    exact HasCM3.of_iso g ((hasCM3_twist P3.q α).2 c3)
  · simpa using (hF x x P P hP hP).2.1 h
  · have h' : t.val (K := Qbar) x.left = OnePoint.some 0 := by simpa using h
    obtain ⟨α, ⟨g⟩⟩ := ((hF _ x P2 P (hx P2) hP).1).1
      (((hF _ _ P2 P2 (hx P2) (hx P2)).2.1 c2).trans h'.symm)
    exact HasCM24.of_iso g ((hasCM24_twist P2.q α).2 c2)

end HDec.QMSplit.Moduli

-- declarations the CMPairsExist plan needs
#check @RayClassCFT.ModuliAtUnits
#check @RayClassCFT.ShimuraMainThmIDeligneY3AbU
#check @RayClassCFT.OhatQ_one
#check @HDec.QMSplit.Moduli.ElkiesEquationsX6Ab
#check @HDec.QMSplit.Moduli.BabaGranathRationalAb
#check @LeafQM.AV.CMExists
#check @LeafQM.AV.cm_of_val
#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.descend_main
