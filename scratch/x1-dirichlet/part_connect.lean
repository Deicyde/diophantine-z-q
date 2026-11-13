
/-! ## x1-dirichlet: the two glue targets discharged in g0-mod-newform's statements -/

noncomputable section

namespace X1DirichletConnect

open PkgI4 (Qbar GQ GaloisRep GaloisChar)
open PkgI3 LeafModCurves G0ModNewform

/-- g0-mod-newform's `DirichletOfFinite` is the Prop proved in §X1Dirichlet (same body). -/
theorem dirichletOfFinite_iff : G0ModNewform.DirichletOfFinite ↔ X1Dirichlet.DirichletOfFinite :=
  Iff.rfl

/-- **`DirichletOfFinite` (GLUE, proved from T17 `KroneckerWeberCyclic`, bundle field `t17`).** -/
theorem g0_dirichletOfFinite (hKW : TSkolemKW.KW.KroneckerWeberCyclic) :
    G0ModNewform.DirichletOfFinite :=
  X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic hKW

/-- **`X1ModelExists` (GLUE, proved by x1-belyi from T36, T38, T39, T40, bundle field `x1`).**
The `X1ModelExists` of g0-mod-newform is `LeafModCurves.X1ModelExists`. -/
theorem g0_x1ModelExists (x1 : X1Belyi.X1Leaves) : X1ModelExists :=
  (X1Belyi.x1ModelExists_and_belyiX1 x1).1

/-- `panOutput_of_G12Out` with `DirichletOfFinite` discharged by T17. -/
theorem panOutput_of_G12Out_kw (hKW : TSkolemKW.KW.KroneckerWeberCyclic) (r : GaloisRep 5 2)
    (h : GalG12Out r) :
    ∃ (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl 5), PanOutput ιC ιL r :=
  panOutput_of_G12Out (g0_dirichletOfFinite hKW) r h

/-- `g12Spec_of_galois` with `DirichletOfFinite` discharged by T17. -/
theorem g12Spec_of_galois_kw (hKW : TSkolemKW.KW.KroneckerWeberCyclic) {K : Type} [Field K]
    [NumberField K] (A : PkgI3.AbVar K) (ρ5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (ρ3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (Vb A 3)) (r5 : GaloisRep 5 2)
    (r3 : GaloisRep 3 2) (h5 : GalG8Out A 5 ρ5 r5) (h3 : GalG8Out A 3 ρ3 r3)
    (h12 : GalG12Out r5) :
    ∃ (i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) (ιC : Qbar →ₐ[ℚ] ℂ)
      (ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5),
      ∀ ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3, G12Spec (⟨i, ιC, ι5, ι3, r5, r3⟩ : ModData K A) :=
  g12Spec_of_galois (g0_dirichletOfFinite hKW) A ρ5 ρ3 r5 r3 h5 h3 h12

/-- `g16Out_with_J1` with `X1ModelExists` discharged by the x1-belyi leaves. -/
theorem g16Out_with_J1_leaves (hJac : JacobianExists ℚ) (x1 : X1Belyi.X1Leaves)
    {L : Type} [Field L] [NumberField L] {A : AbVar L} (u : ℚ) (h : G16Out A u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) :=
  g16Out_with_J1 hJac (g0_x1ModelExists x1) u h

/-- `modularConstituent_tail` with `X1ModelExists` discharged by the x1-belyi leaves. -/
theorem modularConstituent_tail_leaves (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (x1 : X1Belyi.X1Leaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15Ram D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) :=
  modularConstituent_tail lv hJac (g0_x1ModelExists x1) hSw hL8 hAd A u h

/-- **G13-G16, final form, with `X1ModelExists` discharged (GLUE, proved).**
`modularConstituent_tail_G` of g0-mod-newform with `hX` replaced by the x1-belyi leaves
(`X1Belyi.X1Leaves`, the bundle field `x1` of `TextbookLeaves`). -/
theorem modularConstituent_tail_G_leaves (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (x1 : X1Belyi.X1Leaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) :=
  modularConstituent_tail_G lv hJac (g0_x1ModelExists x1) hSw hL8 hAd A u h

end X1DirichletConnect

end

#print axioms X1Dirichlet.cycChar_frob
#print axioms X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic
#print axioms X1DirichletConnect.dirichletOfFinite_iff
#print axioms X1DirichletConnect.g0_dirichletOfFinite
#print axioms X1DirichletConnect.g0_x1ModelExists
#print axioms X1DirichletConnect.panOutput_of_G12Out_kw
#print axioms X1DirichletConnect.g12Spec_of_galois_kw
#print axioms X1DirichletConnect.g16Out_with_J1_leaves
#print axioms X1DirichletConnect.modularConstituent_tail_leaves
#print axioms X1DirichletConnect.modularConstituent_tail_G_leaves
