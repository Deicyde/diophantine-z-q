import LPrefix
namespace HDec
variable {k G V W : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
#check @Representation.asModuleEquiv
theorem equivariant_of_asModule' (ρ : Representation k G V) (σ : Representation k G W)
    (φ : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  refine ⟨{ toFun := fun v => σ.asModuleEquiv (φ (ρ.asModuleEquiv.symm v))
            invFun := fun w => ρ.asModuleEquiv (φ.symm (σ.asModuleEquiv.symm w))
            map_add' := fun v w => by simp only [map_add]
            map_smul' := fun c v => by
              rw [ρ.asModuleEquiv_symm_map_smul, φ.map_smul,
                Representation.asModuleEquiv_map_smul, AlgHom.commutes, Module.algebraMap_end_apply]
              rfl
            left_inv := fun v => by
              dsimp only
              rw [σ.asModuleEquiv.symm_apply_apply, φ.symm_apply_apply, ρ.asModuleEquiv.apply_symm_apply]
            right_inv := fun w => by
              dsimp only
              rw [ρ.asModuleEquiv.symm_apply_apply, φ.apply_symm_apply, σ.asModuleEquiv.apply_symm_apply] }, fun g v => ?_⟩
  simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ρ.asModuleEquiv_symm_map_rho, φ.map_smul, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_of]
end HDec
