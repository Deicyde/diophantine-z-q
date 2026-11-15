import ZInQKernel.OneProof.Main
/-! triage2 probe D (task 3): the complex half of `CMPairsExistT2` from fields already on the chain
(`shimuraMainThmIDeligneY3AbU`, `uniformizationLeafAll`, `gagaMorphism`) and proved theorems. -/
open CategoryTheory AlgebraicGeometry
open HDec.HSyn.G0Split.FibreQM

theorem cmComplexT2 (hU : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (HL : BPAnalytic.Uniformization.UniformizationLeafAll) (HG : ZInQ.HomLattice.GAGAMorphism) :
    (∃ Q : LeafQM.AV.QML3 ℂ, LeafQM.AV.HasCM4 Q.q) ∧ (∃ Q : LeafQM.AV.QML3 ℂ, LeafQM.AV.HasCM3 Q.q) ∧
      (∃ Q : LeafQM.AV.QML3 ℂ, LeafQM.AV.HasCM24 Q.q) := by
  have hCF := PeriodMapH.cmFixedHasCM_of
    (PeriodGlue.t11aRiemannEnd_of_hom (HDec.HSyn.t11aRiemannHom_of_corr4 (AvSplit.Final.h69 HL HG)))
  obtain ⟨Y, Φ, -, Ψ, ⟨-, -, -, ⟨hmod, -⟩, -⟩, -⟩ := hU
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hsq, g, hg, τ, hτ⟩ := PeriodMap.cm4_exists
    obtain ⟨Q, -, hQ⟩ := hmod τ
    exact ⟨Q, (hCF Q τ hQ x g hx hg hτ).1 hsq⟩
  · obtain ⟨x, hx, hsq, g, hg, τ, hτ⟩ := PeriodMap.cm3_exists
    obtain ⟨Q, -, hQ⟩ := hmod τ
    exact ⟨Q, (hCF Q τ hQ x g hx hg hτ).2.1 hsq⟩
  · obtain ⟨x, hx, hsq, g, hg, τ, hτ⟩ := PeriodMap.cm24_exists
    obtain ⟨Q, -, hQ⟩ := hmod τ
    exact ⟨Q, (hCF Q τ hQ x g hx hg hτ).2.2 hsq⟩

-- descent (the remaining step): declarations to copy from
#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.descend_main
#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_of
#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM
#check @HDec.QMSplit.Moduli.ElkiesX6Star.elkiesEquationsX6Ab_of_printed

namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck
open LeafQM.AV

/-- The first lines of `descend_main` (TailO:1181-1191), without `TorsionDescends` and `R1R2fpRep`:
a `ℚ̄`-pair whose endomorphisms receive those of `Q` compatibly with `ι`. -/
theorem pairOfT2 (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (Q : QML3 ℂ)
    (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (P : QMPair Qbar) (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      ∀ a, κ (Q.q.iota a) = P.q.iota a := by
  obtain ⟨ιe, A₀, e, e', h1, h2⟩ := hST Q.A Q.q Q.surface hcm
  let β := RingEquiv.ofBijective (endBCe ιe A₀) (endBCe_bijective ιe A₀ hR)
  let κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End A₀ := β.symm.toRingHom.comp (conjE e e' h1 h2)
  have κinj : Function.Injective κ := β.symm.injective.comp (conjE_injective e e' h1 h2)
  let q₀ : QMStr A₀ := ⟨κ.comp Q.q.iota, κinj.comp Q.q.injective⟩
  have hdim : A₀.dim = 2 := by
    have := dim_eq_of_iso e e' h1 h2
    rw [← Q.surface, ← this]
    exact (@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).symm
  exact ⟨⟨A₀, hdim, q₀⟩, κ, fun a => rfl⟩

theorem com_ofT2 (Q : QML3 ℂ) (P : QMPair Qbar) (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A)
    (hκ : ∀ a, κ (Q.q.iota a) = P.q.iota a) : ∀ φ ∈ com Q.q, κ φ ∈ com P.q := by
  intro φ hφ
  rw [com, Subring.mem_centralizer_iff] at hφ ⊢
  rintro _ ⟨a, rfl⟩
  rw [← hκ, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]

/-- **`CMPairsExistT2` from fields already on the chain** (task 3's remaining statement). -/
theorem cmPairsExistT2_of (hU : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (HL : BPAnalytic.Uniformization.UniformizationLeafAll) (HG : ZInQ.HomLattice.GAGAMorphism)
    (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) :
    (∃ P : QMPair Qbar, HasCM4 P.q) ∧ (∃ P : QMPair Qbar, HasCM3 P.q) ∧ (∃ P : QMPair Qbar, HasCM24 P.q) := by
  obtain ⟨⟨Q4, c4⟩, ⟨Q3, c3⟩, ⟨Q2, c2⟩⟩ := cmComplexT2 hU HL HG
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨P, κ, hκ⟩ := pairOfT2 hST hR Q4 (Or.inl c4)
    obtain ⟨φ, hφ, hφ2⟩ := c4
    exact ⟨P, κ φ, com_ofT2 Q4 P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_one]⟩
  · obtain ⟨P, κ, hκ⟩ := pairOfT2 hST hR Q3 (Or.inr (Or.inl c3))
    obtain ⟨φ, hφ, hφ2⟩ := c3
    exact ⟨P, κ φ, com_ofT2 Q3 P κ hκ φ hφ, by
      rw [← map_mul, ← map_sub, ← map_one κ, ← map_add, hφ2, map_zero]⟩
  · obtain ⟨P, κ, hκ⟩ := pairOfT2 hST hR Q2 (Or.inr (Or.inr c2))
    obtain ⟨φ, hφ, hφ2⟩ := c2
    exact ⟨P, κ φ, com_ofT2 Q2 P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_ofNat]⟩

end HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

#check @HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.stqm_of
#check @HDec.HSyn.t11b_of_exists5
#check @HDec.HSyn.t11bExists_lf8
#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmPairsExistT2_of
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

/-- **End-to-end (task 3): the field `babaGranathRationalAb` from the top bundles' other fields.** -/
theorem babaGranathRationalAb_of_open28T2 (n : HDec.HSyn.OpenResearchLeaves21) (t : HDec.HSyn.OpenTextbookLeaves11)
    (l : HDec.HSyn.OpenAddedLeaves17) : HDec.QMSplit.Moduli.BabaGranathRationalAb :=
  HDec.QMSplit.Moduli.babaGranathRationalAb_of_elkiesT2
    (HDec.QMSplit.Moduli.ElkiesX6Star.elkiesEquationsX6Ab_of_printed n.elkiesX6StarPrinted)
    (HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.cmPairsExistT2_of n.shimuraMainThmIDeligneY3AbU
      t.uniformizationLeafAll t.gagaMorphism
      (HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.stqm_of l.shimuraTaniyamaQbar)
      (HDec.HSyn.t11b_of_exists5 HDec.HSyn.t11bExists_lf8))
#print axioms babaGranathRationalAb_of_open28T2
