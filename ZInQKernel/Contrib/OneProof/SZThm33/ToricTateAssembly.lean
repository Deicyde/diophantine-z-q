import ZInQKernel.Contrib.OneProof.SZThm33.ToricTateMap

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace SZRaynaud

variable {S : Scheme.{0}} {P U G : Over S} [GrpObj U] [GrpObj G] [IsCommMonObj G]
    {T : Type*} [CommGroup T] {ℓ : ℕ} [Fact ℓ.Prime]

/-- The integral Tate map induced by the points of a subgroup of a group scheme. -/
def integralTatePointMap (i : U ⟶ G) [IsMonHom i] (e : T →* (P ⟶ U)) :
    PkgI3.Tate.T ℓ (Additive T) →ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ (Additive (P ⟶ G)) :=
  PkgI3.Tate.map ((mapGroupPoint (P := P) i).comp e).toAdditive

theorem integralTatePointMap_baseChange (i : U ⟶ G) [IsMonHom i] (e : T →* (P ⟶ U)) :
    (integralTatePointMap (ℓ := ℓ) i e).baseChange ℚ_[ℓ] = rationalTatePointMap i e :=
  rfl

section Rank

variable {k : Type} [Field k] [IsAlgClosed k]

/-- The toric Tate lattice has rank equal to the number of split factors. -/
theorem splitTorus_tate_equiv (r : ℕ) (hℓ : (ℓ : k) ≠ 0) :
    Nonempty (PkgI3.Tate.T ℓ (Additive (Fin r → kˣ)) ≃ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ])) :=
  T5Torsion.TateFree.tate_linearEquiv _ (fun n => card_torsion_splitTorus r n hℓ)

variable {D : Type*} [AddCommGroup D] [Module ℤ_[ℓ] D]

/-- The toric Tate rank is unchanged by any subsequent rationally injective
specialization of the target Tate lattice. -/
theorem finrank_range_toricTatePointMap (i : U ⟶ G) [IsMonHom i] [Mono i.left]
    (r : ℕ) (hℓ : (ℓ : k) ≠ 0) (e : (Fin r → kˣ) →* (P ⟶ U))
    (he : Function.Injective e) (f : PkgI3.Tate.T ℓ (Additive (P ⟶ G)) →ₗ[ℤ_[ℓ]] D)
    (hf : Function.Injective (f.baseChange ℚ_[ℓ])) :
    Module.finrank ℚ_[ℓ] ((f.comp (integralTatePointMap i e)).baseChange ℚ_[ℓ]).range = r := by
  rw [LinearMap.baseChange_comp, integralTatePointMap_baseChange]
  obtain ⟨E⟩ := splitTorus_tate_equiv (ℓ := ℓ) r hℓ
  have : Module.Free ℤ_[ℓ] (PkgI3.Tate.T ℓ (Additive (Fin r → kˣ))) :=
    Module.Free.of_equiv E.symm
  let m := (f.baseChange ℚ_[ℓ]).comp (rationalTatePointMap i e)
  have hm : Function.Injective m := hf.comp (rationalTatePointMap_injective i e he)
  change Module.finrank ℚ_[ℓ] m.range = r
  rw [LinearMap.finrank_range_of_inj hm, Module.finrank_baseChange, E.finrank_eq,
    Module.finrank_fin_fun]

end Rank
end SZRaynaud
