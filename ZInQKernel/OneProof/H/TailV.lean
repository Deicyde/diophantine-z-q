import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailT

/-! # OneProof H, leaf-fold7 part V: hodge-split's rows transported to the chain's copies

hodge-split (`TailS`, `TailT`) proves its five rows over the kernel's pkg-I4 layer `ZInQ.Contrib.G9.PkgI4`
(`ZInQKernel/Contrib/G9/I4Layer.lean`). The chain states the same rows over its own copies: the structures
`_root_.PkgI4.GaloisRep`, `_root_.PkgI4.GaloisChar` (`HDecomp/Conductor/LadicCond.lean`, aliased in `HDec.PkgI4`) and
`HDec.PkgI4.I3.AbVar`, and the definitions of `HDec.PkgI4` (`htMult`, `HasHTWeightsAtSelf`, `IsDeRham`,
`IsDeRhamOver`, `htMultOver`, ...), all verbatim copies of pkg-I4. The transports below send a chain object to the
G9 object with the same fields; the predicates then agree by unfolding (the copies have the same text over Mathlib). -/

namespace HDec

set_option maxHeartbeats 1000000

namespace HSyn

namespace HodgeLF7

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- A chain Galois representation as a G9 one (same fields). -/
def toG9Rep {p n : ℕ} [Fact p.Prime] (ρ : _root_.PkgI4.GaloisRep p n) : ZInQ.Contrib.G9.PkgI4.GaloisRep p n :=
  ⟨ρ.toHom, ρ.continuous_toHom⟩

/-- A G9 Galois representation as a chain one (same fields). -/
def ofG9Rep {p n : ℕ} [Fact p.Prime] (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep p n) : _root_.PkgI4.GaloisRep p n :=
  ⟨ρ.toHom, ρ.continuous_toHom⟩

/-- A chain Galois character as a G9 one (same fields). -/
def toG9Char {p : ℕ} [Fact p.Prime] (ψ : _root_.PkgI4.GaloisChar p) : ZInQ.Contrib.G9.PkgI4.GaloisChar p :=
  ⟨ψ.toHom, ψ.continuous_toHom⟩

/-- A chain abelian variety (pkg-I4's I3 layer) as a G9 one (same fields). -/
def toG9AbVar {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : ZInQ.Contrib.G9.PkgI4.I3.AbVar F :=
  { X := A.X, grp := A.grp, proper := A.proper, smooth := A.smooth, geomInt := A.geomInt }

/-- **H-52** on the chain's copy. -/
theorem finiteImageHT (h : _root_.ZInQ.Contrib.HodgeSplit.G0Galois.FiniteImageHT) : G0Galois.FiniteImageHT := by
  intro p _ n ρ hfin
  exact h p n (toG9Rep ρ) hfin

/-- **H-51** on the chain's copy. -/
theorem senTwist (h : _root_.ZInQ.Contrib.HodgeSplit.G0Galois.SenTwist) : G0Galois.SenTwist := by
  intro p _ n ρ ρ' ψ S S' htw hS hS' h1 h2
  exact h p n (toG9Rep ρ) (toG9Rep ρ') (toG9Char ψ) S S' htw hS hS' h1 h2

/-- **H-22** on the chain's copy. -/
theorem r14Det (h : _root_.ZInQ.Contrib.HodgeSplit.G0Galois.R14Det) : G0Galois.R14Det := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, h1, h2, ε, h3, h4⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨ofG9Rep ρ, h1, h2, ε, h3, h4⟩

/-- **H-32** on the chain's copy. -/
theorem t23 (h : ∀ (p : ℕ) [Fact p.Prime], ZInQ.Contrib.G9.PkgI4.T23_FontaineClosure p) :
    ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p :=
  fun p _ => h p

/-! ### H-8: the representation `V_p(A)` moved along the identity -/

set_option linter.unusedSectionVars false

section Inv
variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  {V W : Type} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
  (ρ' : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) (e : V ≃ₗ[ℚ_[p]] W)
  (he : ∀ σ v, e (ρ σ v) = ρ' σ (e v))

include he in
/-- `D_dR` is invariant under an isomorphism of representations. -/
theorem ddr_equiv : Nonempty (ZInQ.Contrib.G9.PkgI4.ddrSpaceOver p ρ' ≃ₗ[ℚ_[p]]
    ZInQ.Contrib.G9.PkgI4.ddrSpaceOver p ρ) := by
  refine ⟨LinearEquiv.ofLinearMap
    { toFun := fun φ => ⟨φ.1 ∘ₗ e.toLinearMap, fun σ v => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he]
        exact φ.2 σ (e v)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    { toFun := fun φ => ⟨φ.1 ∘ₗ e.symm.toLinearMap, fun σ w => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        have : e.symm (ρ' σ w) = ρ σ (e.symm w) := by
          apply e.injective; rw [he]; simp
        rw [this]
        exact φ.2 σ (e.symm w)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ?_ ?_⟩
  · ext φ v; simp
  · ext φ w; simp

include he in
theorem isDeRhamOver_congr :
    ZInQ.Contrib.G9.PkgI4.IsDeRhamOver p ρ ↔ ZInQ.Contrib.G9.PkgI4.IsDeRhamOver p ρ' := by
  obtain ⟨d⟩ := ddr_equiv p ρ ρ' e he
  unfold ZInQ.Contrib.G9.PkgI4.IsDeRhamOver
  rw [← d.finrank_eq, e.finrank_eq]

include he in
theorem ht_equiv (i : ℤ) : Nonempty (ZInQ.Contrib.G9.PkgI4.htSpaceOver p ρ' i ≃ₗ[ℚ_[p]]
    ZInQ.Contrib.G9.PkgI4.htSpaceOver p ρ i) := by
  refine ⟨LinearEquiv.ofLinearMap
    { toFun := fun φ => ⟨φ.1 ∘ₗ e.toLinearMap, fun σ v => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he]
        exact φ.2 σ (e v)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    { toFun := fun φ => ⟨φ.1 ∘ₗ e.symm.toLinearMap, fun σ w => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        have : e.symm (ρ' σ w) = ρ σ (e.symm w) := by
          apply e.injective; rw [he]; simp
        rw [this]
        exact φ.2 σ (e.symm w)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ?_ ?_⟩
  · ext φ v; simp
  · ext φ w; simp

include he in
theorem htMultOver_congr (w : ℤ) :
    ZInQ.Contrib.G9.PkgI4.htMultOver p ρ w = ZInQ.Contrib.G9.PkgI4.htMultOver p ρ' w := by
  obtain ⟨d⟩ := ht_equiv p ρ ρ' e he (-w)
  unfold ZInQ.Contrib.G9.PkgI4.htMultOver
  rw [← d.finrank_eq]

end Inv


section AV
variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F]

theorem galT_eq (A : PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F) (x : A.T p) :
    ((toG9AbVar A).galT (ℓ := p) σ x : A.T p) = A.galT (ℓ := p) σ x := by
  apply Subtype.ext; funext n; rfl

/-- The identity of `V_p(A)`, from G9's instances to the chain's (the two Tate modules are the same sequences). -/
noncomputable def vEquiv (A : PkgI4.I3.AbVar F) : (toG9AbVar A).V p ≃ₗ[ℚ_[p]] A.V p := LinearEquiv.refl ℚ_[p] (A.V p)

theorem vEquiv_galRep (A : PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F) (v : (toG9AbVar A).V p) :
    vEquiv p A ((toG9AbVar A).galRep p σ v) = A.galRep p σ (vEquiv p A v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    change c ⊗ₜ[ℤ_[p]] ((toG9AbVar A).galT (ℓ := p) σ x) = c ⊗ₜ[ℤ_[p]] (A.galT (ℓ := p) σ x)
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

end AV

/-- **H-8** on the chain's copy: the G9 statement at `toG9AbVar A`, moved to `A` along `vEquiv` (the identity of
`V_p(A)`; the two `galRep`s agree on pure tensors), with `IsDeRhamOver`/`htMultOver` invariant under isomorphisms of
representations (`isDeRhamOver_congr`, `htMultOver_congr`) and equal to the chain's copies for one representation
(by unfolding). -/
theorem r10 (h : ZInQ.Contrib.R10.DeRhamComparisonHT) : PkgI4.DeRhamComparisonHT := by
  intro p _ F _ _ _ A
  obtain ⟨h1, h2⟩ := h p F (toG9AbVar A)
  have hR := isDeRhamOver_congr p ((toG9AbVar A).galRep p) (A.galRep p) (vEquiv p A) (vEquiv_galRep p A)
  have hM := htMultOver_congr p ((toG9AbVar A).galRep p) (A.galRep p) (vEquiv p A) (vEquiv_galRep p A)
  refine ⟨fun g hg => ?_, fun w hw0 hw1 => ?_⟩
  · obtain ⟨a, b, c⟩ := h1 g hg
    exact ⟨hR.1 a, (hM 0).symm.trans b, (hM (-1)).symm.trans c⟩
  · exact (hM w).symm.trans (h2 w hw0 hw1)

end HodgeLF7

end HSyn

end HDec
