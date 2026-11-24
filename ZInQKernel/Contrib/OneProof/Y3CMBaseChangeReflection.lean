import ZInQKernel.Contrib.OneProof.STQM

/-! # The three CM conditions are reflected by extension to the complex numbers -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- For a geometric base-change witness, the canonical abelian base change identifies
both quaternion actions. -/
private theorem qmIso_baseChange (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q : QML3 ℂ)
    (hBC : IsBaseChangeOf ιe P Q) :
    ∃ q : QMStr (bcC ιe P.A), (∀ a, endBCe ιe P.A (P.q.iota a) = q.iota a) ∧
      Nonempty (QMIso Q.q q) := by
  obtain ⟨g, hg, hi, hl⟩ := hBC
  let θ : Q.A.X ⟶ (bcC ιe P.A).X :=
    Over.homMk ((bc_isPullback ιe P.A).lift g Q.A.X.hom hg.w)
      ((bc_isPullback ιe P.A).lift_snd _ _ _)
  let θ' : (bcC ιe P.A).X ⟶ Q.A.X :=
    Over.homMk (hg.lift (fstC ιe P.A) (bcC ιe P.A).X.hom (bc_isPullback ιe P.A).w)
      (hg.lift_snd _ _ _)
  have hθ : θ.left ≫ fstC ιe P.A = g := (bc_isPullback ιe P.A).lift_fst _ _ _
  have hθ' : θ'.left ≫ g = fstC ιe P.A := hg.lift_fst _ _ _
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    ext1
    exact hg.hom_ext (by rw [Over.comp_left, Category.assoc, hθ', hθ]; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ', Over.w θ]; simp)
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    ext1
    exact (bc_isPullback ιe P.A).hom_ext (by rw [Over.comp_left, Category.assoc, hθ, hθ']; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ, Over.w θ']; simp)
  have hη : η[Q.A.X] ≫ θ = η[(bcC ιe P.A).X] := by
    ext1
    refine (bc_isPullback ιe P.A).hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, hθ, HDec.HSyn.G0Split.FibreQM.PeriodGlue.eta_comp hl,
        eta_bc_fst]
    · rw [Over.comp_left, Category.assoc, Over.w θ, Over.w η[Q.A.X], Over.w η[(bcC ιe P.A).X]]
  have hη' : η[(bcC ιe P.A).X] ≫ θ' = η[Q.A.X] := by
    rw [← hη, Category.assoc, hθθ', Category.comp_id]
  haveI : IsMonHom θ :=
    HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q.A.X (bcC ιe P.A).X θ hη
  haveI : IsMonHom θ' :=
    HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral (bcC ιe P.A).X Q.A.X θ' hη'
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  let q : QMStr (bcC ιe P.A) :=
    ⟨(endBCe ιe P.A).comp P.q.iota,
      (HDec.G0ModField.KernelField.endBC_injective P.A ℂ).comp P.q.injective⟩
  refine ⟨q, fun _ => rfl, ⟨⟨PkgI3.AbVar.Hom.mk' θ, PkgI3.AbVar.Hom.mk' θ', hθθ', hθ'θ, ?_⟩⟩⟩
  intro a
  simp only [PkgI3.AbVar.Hom.hom_mk']
  ext1
  refine (bc_isPullback ιe P.A).hom_ext ?_ ?_
  · change ((Q.q.iota a).hom.left ≫ θ.left) ≫ fstC ιe P.A =
      (θ.left ≫ (endBCe ιe P.A (P.q.iota a)).hom.left) ≫ fstC ιe P.A
    rw [Category.assoc, hθ, hi, Category.assoc, endBCe_fst, ← Category.assoc, hθ]
  · simp [Over.w]

/-- Any one of the distinguished CM endomorphisms of a base change descends
by full faithfulness on endomorphisms. -/
theorem cm_reflect_of_baseChange (hR : ZInQ.LeafPush2.T11b_Rigidity)
    (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q : QML3 ℂ) (hBC : IsBaseChangeOf ιe P Q) :
    (HasCM4 Q.q → HasCM4 P.q) ∧ (HasCM3 Q.q → HasCM3 P.q) ∧ (HasCM24 Q.q → HasCM24 P.q) := by
  obtain ⟨q, hi, ⟨i⟩⟩ := qmIso_baseChange ιe P Q hBC
  let e := RingEquiv.ofBijective (endBCe ιe P.A) (endBCe_bijective ιe P.A hR)
  let κ := e.symm.toRingHom.comp (conjHom i)
  have hκ (a : O) : κ (Q.q.iota a) = P.q.iota a := by
    change e.symm (conjHom i (Q.q.iota a)) = P.q.iota a
    rw [conjHom_iota, ← hi]
    exact e.symm_apply_apply _
  have hκc (φ : PkgI3.AbVar.End Q.A) (hφ : φ ∈ com Q.q) : κ φ ∈ com P.q := by
    rw [com, Subring.mem_centralizer_iff] at hφ ⊢
    rintro _ ⟨a, rfl⟩
    rw [← hκ, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨φ, hφ, h⟩
    exact ⟨κ φ, hκc φ hφ, by rw [← map_mul, h, map_neg, map_one]⟩
  · rintro ⟨φ, hφ, h⟩
    exact ⟨κ φ, hκc φ hφ, by rw [← map_mul, ← map_sub, ← map_one κ, ← map_add, h, map_zero]⟩
  · rintro ⟨φ, hφ, h⟩
    exact ⟨κ φ, hκc φ hφ, by rw [← map_mul, h, map_neg, map_ofNat]⟩

end Y3P1j

#print axioms Y3P1j.cm_reflect_of_baseChange
