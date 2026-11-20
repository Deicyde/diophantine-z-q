import ZInQKernel.Contrib.OneProof.CMBranch.Localize
import ZInQKernel.Contrib.OneProof.H.TailF

/-! # cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex L581-586) reduced

Step 1 (this file): the reduction `cmFibreSplit_of` of the glue `CMFibreSplit` to
* `CMHomFieldModel` (A8's Hom field at a fibre, L540-561, without the conjugacy maps),
* `CMMatrixUnitSplit` (L582-586: matrix units of `End⁰(A_ℚ̄) = M₂(k)` over `L`),
with the case `End⁰(P.A) ≅ M₂(ℚ(√d))` read off from Yu's dichotomy (the chain's leaf `YuB6Alg`).
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace HDec
namespace CMBranch
namespace FibreSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch
open scoped Quaternion TensorProduct

/-- `ℚ(√d)`, as in the chain's form of Yu's dichotomy (`QMLattice.YuB6Alg`). -/
abbrev Kd (d : ℚ) : Type := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)

/-- **Glue (manuscript L540-561, A8, the Hom field; no conjugacy maps).** At every fibre context
(moduli data with R1-R2's clauses, `u ∉ 𝒞`, a `ℚ̄`-point carrying `P` over `J(u)`) there is a number
field `L ⊆ ℚ̄` with `[L:ℚ] ≤ D` and a model `A/L` of `P.A` (an isomorphism of abelian varieties
`A_ℚ̄ ≅ P.A`) over which every geometric endomorphism is defined (`End(A) → End(A_ℚ̄)` onto):
`L = EK`, `E` the kernel field of `G_ℚ` on the endomorphism lattice of `W₀ = Res_{K/ℚ} A`. -/
def CMHomFieldModel : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 LeafQM.AV.Qbar), G0ModField.FibreCtx Y Φ π u P →
    ∃ (L : G0ModField.IF) (_ : FiniteDimensional ℚ L), Module.finrank ℚ L ≤ heightD ∧
      ∃ (A : PkgI3.AbVar L) (θ : PkgI3.AbVar.Hom (A.baseChange LeafQM.AV.Qbar) P.A)
        (θ' : PkgI3.AbVar.Hom P.A (A.baseChange LeafQM.AV.Qbar)),
        θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
        Function.Surjective (G0ModField.KernelField.endBC A LeafQM.AV.Qbar)

/-- **Glue (manuscript L582-586: matrix units).** An abelian surface `A` over a number field `L`
all of whose geometric endomorphisms are defined over `L` (`End(A) → End(A_Ω)` onto, `Ω` an
algebraic closure), with `End⁰(A_Ω) ≅ M₂(ℚ(√d))`, `d < 0`: multiples of matrix units give an
elliptic curve `E/L` (the image of a multiple of `e₁₁`) whose geometric endomorphism ring is an order
`R` of an imaginary quadratic field `k`, the product `E² = E × E`, and an `L`-isogeny `E² → A`
(`(x, y) ↦ x + m e₂₁ y`). -/
def CMMatrixUnitSplit : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : PkgI3.AbVar L), A.dim = 2 →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω],
      Function.Surjective (G0ModField.KernelField.endBC A Ω) →
      ∀ d : ℚ, d < 0 →
        Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) →
        ∃ (E Pr : ZInQ.DefFaltings.AbVar L) (k : Type) (_ : Field k) (_ : NumberField k)
          (R : Subring k),
          E.dim = 1 ∧ Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧
          (∃ φ : Pr.X ⟶ ((LeafAdopt.abVarEquiv L).symm A).X, IsIsogeny φ) ∧
          IsImagQuadOrder k R ∧ IsCMBy E k R


/-! ## 1. The CM case of Yu's dichotomy -/

/-- **`End⁰ ≅ B` forces `End = ι(𝒪)`** (the chain's `G0ModField.KernelField.endEqOFibre_of_hf`, lines
after its case analysis copied verbatim: `B → End⁰` is onto by dimension, `End` is an order of
`ι(B)` containing the maximal order `ι(𝒪)`). -/
theorem end_eq_iota_of_B (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (P : QML3 LeafQM.AV.Qbar) (hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]))
    (f : PkgI3.AbVar.End P.A) : ∃ a : LeafQM.O, f = P.q.iota a := by
  have hmax := G0ModField.KernelField.oMaximal
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
  have hfree : Module.Free ℤ (PkgI3.AbVar.End P.A) := (hHF LeafQM.AV.Qbar _root_.HFReroute.sigmaQbar P.A P.A).1
  haveI : Module.Finite ℤ (PkgI3.AbVar.End P.A) := (hHF LeafQM.AV.Qbar _root_.HFReroute.sigmaQbar P.A P.A).2.1
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

/-- The centre of `𝒪` is `ℤ`: an element commuting with `i` and `j` is an integer. -/
theorem central_O (a : LeafQM.O) (hi : a * G0FibreSimple.oi = G0FibreSimple.oi * a)
    (hj : a * G0FibreSimple.oj = G0FibreSimple.oj * a) : ∃ n : ℤ, a = n := by
  obtain ⟨v, hv⟩ := a.2
  have hi' := congrArg Subtype.val hi
  have hj' := congrArg Subtype.val hj
  simp only [Subring.coe_mul] at hi' hj'
  rw [hv] at hi' hj'
  have e1 := congrArg QuaternionAlgebra.imJ hi'
  have e2 := congrArg QuaternionAlgebra.imK hi'
  have e3 := congrArg QuaternionAlgebra.imI hj'
  have e4 := congrArg QuaternionAlgebra.imK hj'
  simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt] at e1 e2 e3 e4
  refine ⟨v 0, Subtype.ext ?_⟩
  rw [hv]
  have h2 : (v 2 : ℚ) = 0 := by linarith
  have h3 : (v 3 : ℚ) = 0 := by linarith
  have h1 : (v 1 : ℚ) = 0 := by linarith
  ext <;> simp [LeafQM.ofInt, h1, h2, h3]

/-- **The CM case (manuscript L572-581, through Yu's dichotomy).** If the `𝒪`-centralizer of a QM
surface over `ℚ̄` contains a non-integer, then `End⁰ ≅ M₂(ℚ(√d))` with `d < 0`. -/
theorem end0Matrix_of_noncentral (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (P : QML3 LeafQM.AV.Qbar)
    (φ : PkgI3.AbVar.End P.A) (hφ : φ ∈ com P.q) (hne : ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End P.A)) :
    ∃ d : ℚ, d < 0 ∧ Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (Kd d)) := by
  rcases hYu LeafQM.AV.Qbar P.A P.surface P.q with hB | h
  · exfalso
    obtain ⟨a, ha⟩ := end_eq_iota_of_B hHF P hB φ
    have hc : ∀ b : LeafQM.O, a * b = b * a := by
      intro b
      apply P.q.injective
      have := hφ (P.q.iota b) ⟨b, rfl⟩
      rw [map_mul, map_mul, ← ha]
      exact this.symm
    obtain ⟨n, hn⟩ := central_O a (hc _) (hc _)
    apply hne n
    rw [ha, hn, map_intCast]
  · exact h

/-! ## 2. Transport of `End` along an isomorphism of abelian varieties -/

/-- `End A ≅ End B` for inverse homomorphisms `θ : A → B`, `θ' : B → A`. -/
def endEquivOfIso {K : Type} [Field K] {A B : PkgI3.AbVar K} (θ : PkgI3.AbVar.Hom A B)
    (θ' : PkgI3.AbVar.Hom B A) (h1 : θ.hom ≫ θ'.hom = 𝟙 _) (h2 : θ'.hom ≫ θ.hom = 𝟙 _) :
    PkgI3.AbVar.End A ≃+* PkgI3.AbVar.End B where
  toFun f := PkgI3.AbVar.Hom.mk' (θ'.hom ≫ f.hom ≫ θ.hom)
  invFun g := PkgI3.AbVar.Hom.mk' (θ.hom ≫ g.hom ≫ θ'.hom)
  left_inv f := PkgI3.AbVar.Hom.ext' (by
    simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h1, h1, Category.comp_id])
  right_inv g := PkgI3.AbVar.Hom.ext' (by
    simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h2, h2, Category.comp_id])
  map_mul' f g := PkgI3.AbVar.Hom.ext' (by
    change θ'.hom ≫ (g.hom ≫ f.hom) ≫ θ.hom =
      (θ'.hom ≫ g.hom ≫ θ.hom) ≫ θ'.hom ≫ f.hom ≫ θ.hom
    simp only [Category.assoc]
    rw [reassoc_of% h1])
  map_add' f g := PkgI3.AbVar.Hom.ext' (by
    change θ'.hom ≫ (f.hom * g.hom) ≫ θ.hom =
      (θ'.hom ≫ f.hom ≫ θ.hom) * (θ'.hom ≫ g.hom ≫ θ.hom)
    simp only [MonObj.mul_comp, MonObj.comp_mul, Category.assoc])

/-- `End⁰ A ≅ End⁰ B` as `ℚ`-algebras, for inverse homomorphisms. -/
def end0EquivOfIso {K : Type} [Field K] {A B : PkgI3.AbVar K} (θ : PkgI3.AbVar.Hom A B)
    (θ' : PkgI3.AbVar.Hom B A) (h1 : θ.hom ≫ θ'.hom = 𝟙 _) (h2 : θ'.hom ≫ θ.hom = 𝟙 _) :
    PkgI3.AbVar.End0 A ≃ₐ[ℚ] PkgI3.AbVar.End0 B :=
  Algebra.TensorProduct.congr AlgEquiv.refl (endEquivOfIso θ θ' h1 h2).toIntAlgEquiv

/-! ## 4. A8's Hom field without NoCM: `CMHomFieldModel` from the chain's proved pieces -/

section HomField

open TwistDescentXC TwistDescentHFD G0ModField G0ModField.KernelField

/-- **The pasting isomorphism** `(B_L)_ℚ̄ ≅ B ×_{K} ℚ̄` (the conjugate of `B` at `K ⊆ ℚ̄`), as
inverse homomorphisms (rigidity), compatible with the comparison `B_ℚ̄ → B_L`. -/
theorem paste_iso {K : IF} (B : PkgI3.AbVar K) {L : IF} (hKL : K ≤ L) :
    letI : Algebra K L := incAlg hKL
    ∃ (h₁ : sp ((K.val : K →ₐ[ℚ] LeafQM.AV.Qbar) : K →+* LeafQM.AV.Qbar) = sp (algebraMap L LeafQM.AV.Qbar) ≫ sp (algebraMap K L))
      (θ : PkgI3.AbVar.Hom ((B.baseChange L).baseChange LeafQM.AV.Qbar) ((G4WeilRes.conjData K B).A K.val))
      (θ' : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A K.val) ((B.baseChange L).baseChange LeafQM.AV.Qbar)),
      θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
      θ.hom.left ≫ xc B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁ =
        pullback.fst (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar)) := by
  letI : Algebra K L := incAlg hKL
  have h₁ : sp ((K.val : K →ₐ[ℚ] LeafQM.AV.Qbar) : K →+* LeafQM.AV.Qbar) = sp (algebraMap L LeafQM.AV.Qbar) ≫ sp (algebraMap K L) :=
    sp_eq _ _ _ fun x => rfl
  let C : PkgI3.AbVar LeafQM.AV.Qbar := (G4WeilRes.conjData K B).A K.val
  let A' : PkgI3.AbVar LeafQM.AV.Qbar := (B.baseChange L).baseChange LeafQM.AV.Qbar
  have hP := xc_isPullback B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁
  have hP0 : IsPullback (pullback.fst (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar)))
      (pullback.snd (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar)))
      (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar)) :=
    IsPullback.of_hasPullback _ _
  let ιso := hP0.isoIsPullback _ _ hP
  have hιfst : ιso.hom ≫ xc B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁ = pullback.fst _ _ :=
    hP0.isoIsPullback_hom_fst _ _ hP
  have hιsnd : ιso.hom ≫ pullback.snd B.X.hom (sp ((K.val : K →ₐ[ℚ] LeafQM.AV.Qbar) : K →+* LeafQM.AV.Qbar)) =
      pullback.snd _ _ := hP0.isoIsPullback_hom_snd _ _ hP
  let t : A'.X ⟶ C.X := Over.homMk ιso.hom hιsnd
  let t' : C.X ⟶ A'.X := Over.homMk ιso.inv ((Iso.inv_comp_eq ιso).mpr hιsnd.symm)
  have htt : t ≫ t' = 𝟙 _ := by apply Over.OverMorphism.ext; exact ιso.hom_inv_id
  have ht't : t' ≫ t = 𝟙 _ := by apply Over.OverMorphism.ext; exact ιso.inv_hom_id
  let ηA : Spec (CommRingCat.of LeafQM.AV.Qbar) ⟶
      pullback (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar)) :=
    η[A'.X].left
  let ηC : Spec (CommRingCat.of LeafQM.AV.Qbar) ⟶
      pullback B.X.hom (sp ((K.val : K →ₐ[ℚ] LeafQM.AV.Qbar) : K →+* LeafQM.AV.Qbar)) := η[C.X].left
  have hηl : ηA ≫ ιso.hom = ηC := by
    apply hP.hom_ext
    · rw [Category.assoc, hιfst]
      exact (G4Conj.one_left_fst (sp (algebraMap L LeafQM.AV.Qbar)) (B.baseChange L).X).trans
        (xc_one B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁).symm
    · rw [Category.assoc, hιsnd]
      exact (Over.w η[A'.X]).trans (Over.w η[C.X]).symm
  have hη : η[A'.X] ≫ t = η[C.X] := Over.OverMorphism.ext hηl
  have hη' : η[C.X] ≫ t' = η[A'.X] := by rw [← hη, Category.assoc, htt, Category.comp_id]
  haveI : IsMonHom t := G0FibreSimple.rigidityHom LeafQM.AV.Qbar A' C t hη
  haveI : IsMonHom t' := G0FibreSimple.rigidityHom LeafQM.AV.Qbar C A' t' hη'
  exact ⟨h₁, PkgI3.AbVar.Hom.mk' t, PkgI3.AbVar.Hom.mk' t', htt, ht't, hιfst⟩

/-- **Every endomorphism of `(B_L)_ℚ̄` is defined over `L`** when `L ⊇ K` is a Hom field of `B`
(`G_L` acts trivially on the Hom lattice of the conjugates; manuscript L560-561 "It defines every
geometric endomorphism"): `td_hom_inv` (`G_L`-invariance), `hfd` (descent), rigidity. -/
theorem endBC_surjective_of_homField {K : IF} [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (B : PkgI3.AbVar K) {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1) :
    Function.Surjective (@endBC L _ (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)) LeafQM.AV.Qbar _ _) := by
  letI : Algebra K L := incAlg hKL
  obtain ⟨h₁, θ, θ', hθθ', hθ'θ, hθx⟩ := paste_iso B hKL
  intro f
  let f₀ : PkgI3.AbVar.End ((G4WeilRes.conjData K B).A K.val) :=
    PkgI3.AbVar.Hom.mk' (θ'.hom ≫ f.hom ≫ θ.hom)
  let e₀ : K →ₐ[ℚ] LeafQM.AV.Qbar := K.val
  let e₁L : K →+* L := algebraMap K L
  have he₁ : ∀ x, (e₁L x : LeafQM.AV.Qbar) = (e₀ : K →+* LeafQM.AV.Qbar) x := fun x => rfl
  let φ₀ : pullback B.X.hom (sp (e₀ : K →+* LeafQM.AV.Qbar)) ⟶
      pullback B.X.hom (sp (e₀ : K →+* LeafQM.AV.Qbar)) := f₀.hom.left
  have hφs : φ₀ ≫ pullback.snd B.X.hom (sp (e₀ : K →+* LeafQM.AV.Qbar)) =
      pullback.snd B.X.hom (sp (e₀ : K →+* LeafQM.AV.Qbar)) := Over.w f₀.hom
  obtain ⟨φL, hφL⟩ := hfd B.X B.X e₁L e₁L _ _ h₁ h₁ he₁ he₁ φ₀ hφs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₀ e₀ f₀ k hk k₁ k₂)
  have ep₁ := xc_epi B.X e₁L _ h₁
  have hφLs : φL ≫ pullback.snd B.X.hom (sp e₁L) = pullback.snd B.X.hom (sp e₁L) := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, xc_snd, ← Category.assoc, hφs]
  haveI := specQbar_epi L
  have o1 := xc_one B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁
  have o3 : η[((G4WeilRes.conjData K B).A e₀).X].left ≫ f₀.hom.left =
      η[((G4WeilRes.conjData K B).A e₀).X].left := by
    show (η[((G4WeilRes.conjData K B).A e₀).X] ≫ f₀.hom).left = _
    rw [IsMonHom.one_hom]
  let ηL : Spec (CommRingCat.of L) ⟶ pullback B.X.hom (sp e₁L) := η[(B.baseChange L).X].left
  let ηQ : Spec (CommRingCat.of LeafQM.AV.Qbar) ⟶ pullback B.X.hom (sp (e₀ : K →+* LeafQM.AV.Qbar)) :=
    η[((G4WeilRes.conjData K B).A e₀).X].left
  have o1' : ηQ ≫ xc B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁ = sp (algebraMap L LeafQM.AV.Qbar) ≫ ηL := o1
  have o3' : ηQ ≫ φ₀ = ηQ := o3
  have hηL : ηL ≫ φL = ηL := by
    apply (cancel_epi (sp (algebraMap L LeafQM.AV.Qbar))).mp
    rw [← Category.assoc, ← o1', Category.assoc, hφL, ← Category.assoc, o3']
  let g' : (B.baseChange L).X ⟶ (B.baseChange L).X := Over.homMk φL hφLs
  have hη : η[(B.baseChange L).X] ≫ g' = η[(B.baseChange L).X] := Over.OverMorphism.ext hηL
  haveI : IsMonHom g' := G0FibreSimple.rigidityHom L _ _ g' hη
  have hf : f.hom.left ≫ θ.hom.left = θ.hom.left ≫ f₀.hom.left := by
    have h : θ.hom.left ≫ θ'.hom.left = 𝟙 _ := by rw [← Over.comp_left, hθθ', Over.id_left]
    show _ = θ.hom.left ≫ (θ'.hom.left ≫ f.hom.left ≫ θ.hom.left)
    rw [reassoc_of% h]
  refine ⟨PkgI3.AbVar.Hom.mk' g', PkgI3.AbVar.Hom.ext' (Over.OverMorphism.ext ?_)⟩
  apply pullback.hom_ext
  · change ((Over.pullback (sp (algebraMap L LeafQM.AV.Qbar))).map g').left ≫ _ = _
    simp only [Over.pullback_map_left, pullback.lift_fst]
    let P2 := pullback (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar))
    let fL : P2 ⟶ P2 := f.hom.left
    let θL : P2 ⟶ pullback B.X.hom (sp (e₀ : K →+* LeafQM.AV.Qbar)) := θ.hom.left
    have hθx' : θL ≫ xc B.X (sp (algebraMap L LeafQM.AV.Qbar)) h₁ = pullback.fst _ _ := hθx
    have hf' : fL ≫ θL = θL ≫ φ₀ := hf
    show pullback.fst (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar)) ≫ φL =
      fL ≫ pullback.fst (pullback.snd B.X.hom (sp (algebraMap K L))) (sp (algebraMap L LeafQM.AV.Qbar))
    rw [← hθx', Category.assoc, hφL, reassoc_of% hf']
  · change ((Over.pullback (sp (algebraMap L LeafQM.AV.Qbar))).map g').left ≫ _ = _
    simp only [Over.pullback_map_left, pullback.lift_snd]
    exact (Over.w f.hom).symm

/-- **`CMHomFieldModel` proved** from G2 (`FibreCoverExists`, the chain's
`fibreCoverExists_of_propTSAll'`) and the leaves of the chain's A8 (T6 `HomFreeFiniteC`,
Néron–Ogg–Shafarevich, Raynaud, torsion structure): the rational fibre `PK/K` (G2), the kernel field
`E` of `G_ℚ` on the Hom lattice of the conjugates of `PK.A` (`kernelField_of_model_hf`: the
manuscript's `W₀ = Res_{K/ℚ} A`, L544-555), `L = E ⊔ K` with `[L:ℚ] ≤ F₀·3^{r²} ≤ D`
(`a8_field`, L551-555), `A = (PK.A)_L`; `A_ℚ̄ ≅ P.A` (R1's naturality, `bc_transport`, the pasting
isomorphism); every endomorphism of `A_ℚ̄` is defined over `L` (`endBC_surjective_of_homField`,
L560-561). No NoCM and no conjugacy maps. -/
theorem cmHomFieldModel_of (hCover : G0ModField.FibreCoverExists)
    (hHFF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterionNF.{0})
    (hTors : PkgI2.TorsionStructure.{0}) : CMHomFieldModel := by
  intro Y Φ π u P hctx
  obtain ⟨K, hfK, hgK, hKF, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model_hf hHFF hNOS K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3 hNOS hRay hTors K PK (T u) (three_mem_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hKF hE hr
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  obtain ⟨hR1, -, -, -⟩ := hctx
  obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 K LeafQM.AV.Qbar K.val yK PK hyK
  have hQP : M3.mk Q = M3.mk P := hQ.symm.trans hyKP
  obtain ⟨e⟩ := Quotient.exact hQP
  obtain ⟨θ₁, θ₁', h11, h12, -⟩ := bc_transport G0FibreSimple.rigidityHom PK K.val Q hbc
  obtain ⟨-, θ₀, θ₀', h01, h02, -⟩ := paste_iso PK.A (le_sup_right : K ≤ E ⊔ K)
  refine ⟨E ⊔ K, inferInstance, hdeg, @PkgI3.AbVar.baseChange K _ PK.A ↥(E ⊔ K) _ (incAlg le_sup_right),
    PkgI3.AbVar.Hom.mk' (θ₀.hom ≫ θ₁.hom ≫ e.φ.hom), PkgI3.AbVar.Hom.mk' (e.ψ.hom ≫ θ₁'.hom ≫ θ₀'.hom),
    ?_, ?_, endBC_surjective_of_homField PK.A le_sup_right hfix⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% e.left, reassoc_of% h11, h01]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h02, reassoc_of% h12, e.right]

end HomField

/-! ## 3. The reduction of `CMFibreSplit` -/

/-- **`CMFibreSplit` from A8's Hom field and the matrix units** (with the chain's leaves T27 = Yu,
`YuB6Alg`, and T6, `HomFreeFiniteC`). A fibre with CM has a `ℚ̄`-point `P` whose `𝒪`-centralizer
contains a non-integer; then `End⁰(P.A) ≅ M₂(ℚ(√d))` (Yu, `end0Matrix_of_noncentral`), A8 gives
`A/L` with `[L:ℚ] ≤ D`, `A_ℚ̄ ≅ P.A` and every geometric endomorphism defined over `L`, and the
matrix units give `E`, `E²`, the isogeny and the order. -/
theorem cmFibreSplit_of (hYu : QMLattice.YuB6Alg)
    (hHF : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC)
    (hA8 : CMHomFieldModel) (hMU : CMMatrixUnitSplit) : CMFibreSplit := by
  intro Y Φ π hR1 hR2 u hu hCM
  simp only [NoCMAt, not_forall, not_exists] at hCM
  obtain ⟨y, P, hP, hπ, φ, hφ, hne⟩ := hCM
  obtain ⟨L, hfin, hdeg, A, θ, θ', h1, h2, hsurj⟩ := hA8 Y Φ π u P ⟨hR1, hR2, hu, y, hP, hπ⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := end0Matrix_of_noncentral hYu hHF P φ hφ hne
  letI : NumberField L := G0ModField.numberField_of_fd L
  have hiso : letI : Algebra L LeafQM.AV.Qbar := (algebraMap L LeafQM.AV.Qbar).toAlgebra;
      Nonempty ((((LeafAdopt.abVarEquiv L).symm A).baseChange LeafQM.AV.Qbar).X ≅ P.A.X) :=
    ⟨⟨θ.hom, θ'.hom, h1, h2⟩⟩
  have hA2 : A.dim = 2 :=
    G0Split.model_dim G0Split.dimBaseChange (algebraMap L LeafQM.AV.Qbar) ((LeafAdopt.abVarEquiv L).symm A)
      P.A hiso P.surface
  haveI : Algebra.IsAlgebraic L LeafQM.AV.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  obtain ⟨E, Pr, k, i1, i2, R, hE, hPr, hprod, hisog, hR, hcm⟩ :=
    hMU L A hA2 LeafQM.AV.Qbar hsurj d hd ⟨(end0EquivOfIso θ θ' h1 h2).trans e⟩
  exact ⟨⟨L⟩, (LeafAdopt.abVarEquiv L).symm A, E, Pr, k, i1, i2, R,
    ⟨algebraMap L LeafQM.AV.Qbar, y, P, hP, hπ, hiso⟩, hdeg, hE, hPr, hprod, hisog, hR, hcm⟩

end FibreSplit
end CMBranch
end HDec
