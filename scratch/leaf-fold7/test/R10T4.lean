import ZInQKernel.OneProof.H.TailO
import ZInQKernel.OneProof.H.TailT

namespace HDec.HSyn.HodgeT
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

def toG9AbVar {F : Type} [Field F] (A : PkgI4.I3.AbVar F) : ZInQ.Contrib.G9.PkgI4.I3.AbVar F :=
  { X := A.X, grp := A.grp, proper := A.proper, smooth := A.smooth, geomInt := A.geomInt }

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
def vEquiv (A : PkgI4.I3.AbVar F) : (toG9AbVar A).V p ≃ₗ[ℚ_[p]] A.V p := LinearEquiv.refl ℚ_[p] (A.V p)

theorem vEquiv_galRep (A : PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F) (v : (toG9AbVar A).V p) :
    vEquiv p A ((toG9AbVar A).galRep p σ v) = A.galRep p σ (vEquiv p A v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    change c ⊗ₜ[ℤ_[p]] ((toG9AbVar A).galT (ℓ := p) σ x) = c ⊗ₜ[ℤ_[p]] (A.galT (ℓ := p) σ x)
    congr 1
  | add x y hx hy => simp only [map_add, hx, hy]

end AV

theorem r10 (h : ZInQ.Contrib.R10.DeRhamComparisonHT) : PkgI4.DeRhamComparisonHT := by
  intro p _ F _ _ _ A
  obtain ⟨h1, h2⟩ := h p F (toG9AbVar A)
  have hR := isDeRhamOver_congr p ((toG9AbVar A).galRep p) (A.galRep p) (vEquiv p A) (vEquiv_galRep p A)
  have hM := htMultOver_congr p ((toG9AbVar A).galRep p) (A.galRep p) (vEquiv p A) (vEquiv_galRep p A)
  refine ⟨fun g hg => ?_, fun w hw0 hw1 => ?_⟩
  · obtain ⟨a, b, c⟩ := h1 g hg
    exact ⟨hR.1 a, (hM 0).symm.trans b, (hM (-1)).symm.trans c⟩
  · exact (hM w).symm.trans (h2 w hw0 hw1)

#print axioms r10
end HDec.HSyn.HodgeT
