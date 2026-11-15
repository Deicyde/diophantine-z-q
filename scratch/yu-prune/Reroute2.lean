import ZInQKernel.OneProof.H.TailZ26
import ZInQKernel.Contrib.OneProof.QMLattice

/-! yu-prune test (copy of scratch/gt-qm/Reroute.lean, inline IsAlgebraic instance): the four live applications of `PkgI3.QMDichotomyYu` rerouted to `HDec.QMLattice.YuB6Alg`
(each is the chain's proof with the one application line replaced; checks that a fold can drop `yuThm11`).
Not part of the contribution. -/

set_option linter.all false
noncomputable section

namespace HDec
namespace FS5NoCM
open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3
open scoped Quaternion TensorProduct

theorem comIntOrQuadOrder_of_yuB6 (hYu : HDec.QMLattice.YuB6Alg) (t6 : PkgI3.HomFreeFinite)
    (hCM : ComOfMatrixEnd0) : ComIntOrQuadOrder := by
  intro P
  rcases hYu Qbar P.A P.surface P.q with
    he | ⟨d, hd, hM⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (com_int_of_end0_quat t6 P.q e)
  · exact Or.inr (hCM P.A P.q d hd hM)

end FS5NoCM

namespace G0FibreSimple
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn HSyn.G0Split
open scoped Quaternion TensorProduct

theorem fibreSimple_of_pieces_yuB6 (hYu : HDec.QMLattice.YuB6Alg) (h1 : EndDivisionDescent)
    (h2 : EndDivisionOfSchemeIso) (h3 : EndDivisionOfEnd0Division)
    (h4 : CentralizerOfMatrixEnd0) (h5 : FibreComTrivial) : FibreSimple := by
  intro Y Φ π hR1 hR2 u hu K A hF
  obtain ⟨emb, y, P, hP, hval, hiso⟩ := hF
  let _ : Algebra K.K LeafQM.AV.Qbar := emb.toAlgebra
  -- G5 (T27 at `B = (2,-3)`): `End⁰(P.A) ≅ B` or `≅ M₂(ℚ(√d))`.
  have hY := hYu LeafQM.AV.Qbar P.A P.surface P.q
  -- G6 (NoCM): the second case is excluded.
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ := h4 LeafQM.AV.Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := h5 Y Φ π hR1 hR2 u hu y P hP hval φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  have hPdiv : PkgI3.EndDivision P.A := h3 LeafQM.AV.Qbar P.A (division_of_algEquiv e B6_isUnit)
  have hAbar : PkgI3.EndDivision (LeafAdopt.abVarEquiv LeafQM.AV.Qbar (A.baseChange LeafQM.AV.Qbar)) :=
    h2 LeafQM.AV.Qbar _ P.A hiso hPdiv
  exact h1 K.K LeafQM.AV.Qbar A hAbar

end G0FibreSimple

namespace G0ModField.KernelField
open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Quaternion
open LeafQM.AV

theorem endEqOFibre_of_yuB6 (hYu : HDec.QMLattice.YuB6Alg) (hHF : PkgI3.HomFreeFinite)
    (hmax : OMaximal) : EndEqOFibre := by
  intro P hcom f
  have hY := hYu Qbar P.A P.surface P.q
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ :=
        G0FibreSimple.centralizerOfMatrixEnd0_of_homFree hHF Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := hcom φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  let φ : LeafQM.B →ₐ[ℚ] PkgI3.AbVar.End0 P.A := (G0FibreSimple.qmBasis P.q).liftHom
  haveI : Nontrivial (PkgI3.AbVar.End0 P.A) := e.toEquiv.nontrivial
  have hinj : Function.Injective φ := φ.toRingHom.injective
  haveI : FiniteDimensional ℚ (PkgI3.AbVar.End0 P.A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hrank : Module.finrank ℚ LeafQM.B = Module.finrank ℚ (PkgI3.AbVar.End0 P.A) :=
    e.toLinearEquiv.finrank_eq.symm
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).mp hinj
  let j : PkgI3.AbVar.End P.A →ₐ[ℤ] PkgI3.AbVar.End0 P.A := Algebra.TensorProduct.includeRight
  have hfree : Module.Free ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).1
  haveI : Module.Finite ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).2.1
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End P.A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End P.A) (S := ℚ))
  have hjinj : Function.Injective j := by
    intro x y hxy
    have hm : (1 : ℚ) ⊗ₜ[ℤ] (x - y) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s'))
  -- `φ` agrees with `j ∘ ι` on `𝒪`
  have hagree : ∀ a : LeafQM.O, φ (a : LeafQM.B) = j (P.q.iota a) := by
    let ψ1 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := φ.toRingHom.comp (Subring.subtype _)
    let ψ2 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := j.toRingHom.comp P.q.iota
    have hi : ψ1 G0FibreSimple.oi = ψ2 G0FibreSimple.oi := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oi : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oi, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    have hj : ψ1 G0FibreSimple.oj = ψ2 G0FibreSimple.oj := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oj : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oj, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    intro a
    obtain ⟨n, hn⟩ := a.2
    have h2 : (2 : LeafQM.O) * a = ((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
        ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * G0FibreSimple.oi +
        ((n 2 : ℤ) : LeafQM.O) * G0FibreSimple.oj +
        ((n 3 : ℤ) : LeafQM.O) * (G0FibreSimple.oi * G0FibreSimple.oj) := by
      apply Subtype.ext
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
      rw [show ((2 : LeafQM.O) : LeafQM.B) = 2 from rfl, hn]
      ext <;> simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat,
        QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;>
        ring
    have key : ∀ ψ : LeafQM.O →+* PkgI3.AbVar.End0 P.A, ψ ((2 : LeafQM.O) * a) =
        ((2 * n 0 + n 2 : ℤ) : PkgI3.AbVar.End0 P.A) +
        ((2 * n 1 + n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oi +
        ((n 2 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oj +
        ((n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * (ψ G0FibreSimple.oi * ψ G0FibreSimple.oj) := by
      intro ψ
      rw [h2]; simp only [map_add, map_mul, map_intCast]
    have e1 : (2 : PkgI3.AbVar.End0 P.A) * ψ1 a = (2 : PkgI3.AbVar.End0 P.A) * ψ2 a := by
      have := key ψ1
      rw [map_mul, map_ofNat] at this
      rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
    have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
      rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e1
    exact smul_right_injective (PkgI3.AbVar.End0 P.A) (two_ne_zero : (2 : ℚ) ≠ 0) e2
  -- the order `R = φ⁻¹(End)`
  let R : Subring LeafQM.B := (j.toRingHom.range).comap φ.toRingHom
  have hOR : LeafQM.O ≤ R := fun x hx => ⟨P.q.iota ⟨x, hx⟩, (hagree ⟨x, hx⟩).symm⟩
  have hint : ∀ x ∈ R, IsIntegral ℤ x := by
    rintro x ⟨g, hg⟩
    have h1 : IsIntegral ℤ g := Algebra.IsIntegral.isIntegral g
    have h2 : IsIntegral ℤ (φ x) := by
      have := h1.map j
      rwa [show j g = φ x from hg] at this
    exact (isIntegral_algHom_iff (φ.restrictScalars ℤ) hinj).mp h2
  obtain ⟨x, hx⟩ := hsurj (j f)
  have hxO : x ∈ LeafQM.O := hmax R hOR hint ⟨f, hx.symm⟩
  refine ⟨⟨x, hxO⟩, hjinj ?_⟩
  rw [← hagree, ← hx]

end G0ModField.KernelField

namespace LTGoodRed.QM
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField LeafQM
open scoped Quaternion TensorProduct
open LeafQM.AV LeafQM.AV.Pin _root_.ZInQ ZInQ ZInQ.JHeight PkgI3

theorem qmEndRank_of_yuB6 (hM1 : PkgI3.HomFreeFinite) (hYu : HDec.QMLattice.YuB6Alg)
    (hS : QMSplitCaseRank) : HSyn.LinkedTate.QMEndRank := by
  intro K L L' _ hKL hLL' PK hdiv
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  set A' : PkgI3.AbVar L' := @PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL') with hA'
  let φ : O →+* PkgI3.AbVar.End A' :=
    (HSyn.LinkedTate.endBC (PK.A.baseChange L) L').comp
      ((HSyn.LinkedTate.endBC PK.A L).comp PK.q.iota)
  have hφ : Function.Injective φ :=
    (HSyn.LinkedTate.endBC_injective _ L').comp
      ((HSyn.LinkedTate.endBC_injective _ L).comp PK.q.injective)
  have hdimA' : A'.dim = 2 := by
    rw [hA', G0Dim.pkgI3_dim_baseChange, G0Dim.pkgI3_dim_baseChange]
    exact PK.surface
  refine le_antisymm ?_ (four_le_finrank hM1 A' φ hφ)
  -- the geometric endomorphism algebra
  let Ω := AlgebraicClosure L'
  let A'' : PkgI3.AbVar Ω := A'.baseChange Ω
  have hdimA'' : A''.dim = 2 := by
    show (A'.baseChange Ω).dim = 2
    rw [G0Dim.pkgI3_dim_baseChange]; exact hdimA'
  let φ'' : O →+* PkgI3.AbVar.End A'' := (HSyn.LinkedTate.endBC A' Ω).comp φ
  haveI : Algebra.IsAlgebraic ℚ Ω := by
    haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
    exact Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  rcases hYu Ω A'' hdimA'' ⟨φ'', (HSyn.LinkedTate.endBC_injective A' Ω).comp hφ⟩ with he | ⟨d, hd, he⟩
  · obtain ⟨e⟩ := he
    calc Module.finrank ℤ (PkgI3.AbVar.End A')
        ≤ Module.finrank ℤ (PkgI3.AbVar.End A'') := finrank_le_baseChange hM1 A' Ω
      _ = Module.finrank ℚ (PkgI3.AbVar.End0 A'') := (finrank_end0 hM1 A'').symm
      _ = Module.finrank ℚ ℍ[ℚ, 2, -3] := e.toLinearEquiv.finrank_eq
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  · exact hS L' A' Ω φ hφ hdimA' hdiv d hd he

end LTGoodRed.QM
end HDec

#print axioms HDec.FS5NoCM.comIntOrQuadOrder_of_yuB6
#print axioms HDec.G0FibreSimple.fibreSimple_of_pieces_yuB6
#print axioms HDec.G0ModField.KernelField.endEqOFibre_of_yuB6
#print axioms HDec.LTGoodRed.QM.qmEndRank_of_yuB6
