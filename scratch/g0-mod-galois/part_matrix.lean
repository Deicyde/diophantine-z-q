
/-! ### G8's linear-algebra remainder, reduced to Burnside's theorem -/

section G0GaloisMatrixSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep)

/-- **Burnside's theorem, absolutely irreducible form (textbook leaf; Lang, *Algebra*, XVII §3,
Cor. 3.4, and Curtis–Reiner §27 (Burnside, Frobenius–Schur); locators UNVERIFIED).** If a
finite-dimensional representation `ρ` of a monoid over a field `F` stays irreducible after every
field extension, then the matrices `ρ(g)` (in any basis) generate `M_n(F)` as an `F`-algebra.
Mathlib has the Jacobson density theorem (`jacobson_density`), from which it follows. -/
def BurnsideAbsIrred : Prop :=
  ∀ (F : Type) [Field F] (G : Type) [Monoid G] (W : Type) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (n : ℕ) (b : Module.Basis (Fin n) F W) (ρ : Representation F G W),
    (∀ (F' : Type) [Field F'] [Algebra F F'], (GlueI3.repBaseChange F' ρ).IsIrreducible) →
    Algebra.adjoin F (Set.range fun g => LinearMap.toMatrix b b (ρ g)) = ⊤

/-- **`G8Matrix` from Burnside (proved).** A basis of `W = e₀₀ V` (`dim W = 2`) turns `ρ|_W` into
a continuous `r : G_ℚ → GL₂(ℚ̄_ℓ)` (continuity from the weak continuity of `ρ`, through the
functionals `b.coord i ∘ e₀₀`); `splitEquiv` composed with the basis intertwines `ρ` with
`r ⊕ r`; Burnside gives the generation of `M₂(ℚ̄_ℓ)` by `r(G_K)`. -/
theorem g8Matrix_of_burnside (hB : BurnsideAbsIrred) : G8Matrix := by
  intro K _ _ A ℓ _ ρ u hc h4 hcont hirr
  haveI : FiniteDimensional (PadicAlgCl ℓ) (Vb A ℓ) :=
    Module.finite_of_finrank_pos (by rw [h4]; norm_num)
  have hW2 : Module.finrank (PadicAlgCl ℓ) u.W = 2 := u.finrank_W h4
  let b : Module.Basis (Fin 2) (PadicAlgCl ℓ) u.W :=
    Module.finBasisOfFinrankEq (PadicAlgCl ℓ) u.W hW2
  let rW := restrictRep ρ u.W (fun g _ hw => u.mapsTo_W ρ hc g hw)
  let m : PkgI4.GQ →* Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp rW
  have hm : ∀ g, m g = LinearMap.toMatrix b b (rW g) := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply]
    exact LinearMap.toMatrixAlgEquiv_apply b (rW g) i j
  have hcm : Continuous fun g => m g := by
    refine continuous_matrix fun i j => ?_
    let f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ) :=
      (b.coord i).comp ((u.e 0 0).codRestrict u.W (fun v => u.mem_W_of_e0 0 v))
    refine (hcont f (b j : Vb A ℓ)).congr fun g => ?_
    rw [hm, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
    change b.coord i _ = b.coord i _
    congr 1
    exact Subtype.ext (u.e00_of_mem (u.mapsTo_W ρ hc g (b j).2))
  let toHom : PkgI4.GQ →* GL (Fin 2) (PadicAlgCl ℓ) := m.toHomUnits
  have hcont' : Continuous toHom := by
    rw [Units.continuous_iff]
    refine ⟨hcm, ?_⟩
    have hinv : (fun g => (((toHom g)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) :
        Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))) = fun g => m g⁻¹ := by
      funext g
      rw [← map_inv]
      rfl
    rw [hinv]
    exact hcm.comp continuous_inv
  let r : GaloisRep ℓ 2 := ⟨toHom, hcont'⟩
  have hrmat : ∀ g, r.mat g = LinearMap.toMatrix b b (rW g) := hm
  let e := u.splitEquiv.trans (b.equivFun.prodCongr b.equivFun)
  refine ⟨r, e, ?_, ?_⟩
  · intro g v
    have h1 := u.splitEquiv_intertwines ρ hc g v
    simp only [e, LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply,
      Module.Basis.equivFun_apply, hrmat]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [LinearMap.toMatrix_mulVec_repr]
      rfl
    · dsimp only
      rw [LinearMap.toMatrix_mulVec_repr]
      rfl
  · have hfun : (fun σ => r.mat (resQ K σ)) =
        fun σ => LinearMap.toMatrix b b ((rW.comp (resQ K)) σ) :=
      funext fun σ => hrmat _
    rw [hfun]
    exact hB (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) u.W 2 b (rW.comp (resQ K)) hirr

end G0Galois

end

end G0GaloisMatrixSec
