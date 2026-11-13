import ZInQKernel.Contrib.G9.Speiser

/-!
# G9: finite Galois descent for spaces of equivariant maps

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

A group `G` acts `K`-linearly on a `K`-algebra `B` (`act`) and on a `K`-space `V` (`ρ`). For
`S ⊆ G`, `Dsp act ρ S` is the space of `K`-linear maps `φ : V → B` with `φ(ρ(g) v) = act(g)(φ v)`
for `g ∈ S`. (pkg-I4's `ddrSpace`, `ddrSpaceOver`, `htSpace`, `htSpaceOver` are all of this
form: `B = B_dR` or `B = ℂ_p` with the twisted action `χ(g)^i · g`.)

**Descent (`descent_finrank`).** Let `L/K` be finite Galois, `γ : G → Gal(L/K)` a surjective
homomorphism, and `ι : L → B` a `K`-algebra map with `act(g)(ι(x) b) = ι(γ(g) x) · act(g)(b)`.
Then `dim_K Dsp(ker γ) = [L:K] · dim_K Dsp(G)`. Proof: `Dsp(ker γ)` is an `L`-space through `ι`,
with a semilinear action of `Gal(L/K) = G/ker γ`, whose invariants are `Dsp(G)`; apply Speiser's
lemma (`speiser_finrank`). This is the finite-descent paragraph of N5's Lemma
`lem:de-rham-descent` (`D_K = D_{F}^{Gal(F/K)}`, `F ⊗_K D_K ≅ D_F`).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct

section Dsp

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  {V : Type*} [AddCommGroup V] [Module K V]

/-- `S`-equivariant `K`-linear maps `V → B`. -/
def Dsp (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) :
    Submodule K (V →ₗ[K] B) where
  carrier := {φ | ∀ g ∈ S, ∀ v, φ (ρ g v) = act g (φ v)}
  zero_mem' := by intro g _ v; simp
  add_mem' := by
    intro φ ψ hφ hψ g hg v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ g hg v, hψ g hg v, map_add]
  smul_mem' := by
    intro c φ hφ g hg v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ g hg v, map_smul]

theorem mem_Dsp {act : G → B →ₗ[K] B} {ρ : G → V →ₗ[K] V} {S : Set G} {φ : V →ₗ[K] B} :
    φ ∈ Dsp act ρ S ↔ ∀ g ∈ S, ∀ v, φ (ρ g v) = act g (φ v) := Iff.rfl

end Dsp

section Descent

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [CommRing B] [Algebra K B]
  {V : Type*} [AddCommGroup V] [Module K V]
  (act : G →* (B →ₗ[K] B)) (ρ : G →* (V →ₗ[K] V))
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (ι : L →ₐ[K] B) (γ : G →* (L ≃ₐ[K] L))

theorem act_inv_act (g : G) (b : B) : act g (act g⁻¹ b) = b := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_rho (g : G) (v : V) : ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- `g · φ = act(g) ∘ φ ∘ ρ(g)⁻¹`, on `Hom_K(V, B)`. -/
def twist (g : G) : (V →ₗ[K] B) →ₗ[K] (V →ₗ[K] B) where
  toFun φ := act g ∘ₗ φ ∘ₗ ρ g⁻¹
  map_add' φ ψ := by ext v; simp
  map_smul' c φ := by ext v; simp

theorem twist_apply (g : G) (φ : V →ₗ[K] B) (v : V) :
    twist act ρ g φ v = act g (φ (ρ g⁻¹ v)) := rfl

theorem twist_mul (g h : G) (φ : V →ₗ[K] B) :
    twist act ρ (g * h) φ = twist act ρ g (twist act ρ h φ) := by
  ext v
  simp only [twist_apply, map_mul, mul_inv_rev, Module.End.mul_apply]

theorem twist_mem (g : G) {φ : V →ₗ[K] B} (hφ : φ ∈ Dsp act ρ (γ.ker : Set G)) :
    twist act ρ g φ ∈ Dsp act ρ (γ.ker : Set G) := by
  intro h hh v
  have hh' : γ h = 1 := hh
  have hk : g⁻¹ * h * g ∈ γ.ker := by
    show γ (g⁻¹ * h * g) = 1
    simp [hh']
  have e1 : ρ g⁻¹ (ρ h v) = ρ (g⁻¹ * h * g) (ρ g⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    group
  rw [twist_apply, twist_apply, e1, hφ _ hk]
  rw [← Module.End.mul_apply (act g), ← map_mul, ← Module.End.mul_apply (act h), ← map_mul]
  congr 2
  group

theorem twist_eq_self_of_mem_ker {h : G} (hh : h ∈ γ.ker) {φ : V →ₗ[K] B}
    (hφ : φ ∈ Dsp act ρ (γ.ker : Set G)) : twist act ρ h φ = φ := by
  ext v
  have hh' : h⁻¹ ∈ γ.ker := γ.ker.inv_mem hh
  rw [twist_apply, hφ _ hh', act_inv_act]

theorem twist_eq_self_of_mem_univ (g : G) {φ : V →ₗ[K] B}
    (hφ : φ ∈ Dsp act ρ Set.univ) : twist act ρ g φ = φ := by
  ext v
  rw [twist_apply, hφ _ (Set.mem_univ _), act_inv_act]

theorem mem_univ_of_twist (φ : V →ₗ[K] B) (h : ∀ g, twist act ρ g φ = φ) :
    φ ∈ Dsp act ρ Set.univ := by
  intro g _ v
  have := LinearMap.congr_fun (h g) (ρ g v)
  rw [twist_apply, rho_inv_rho] at this
  exact this.symm

variable (hγ : Function.Surjective γ)
  (hsemi : ∀ g x b, act g (ι x * b) = ι (γ g x) * act g b)

include hsemi in
theorem twist_smul (g : G) (x : L) (φ : V →ₗ[K] B) :
    twist act ρ g (ι x • φ) = ι (γ g x) • twist act ρ g φ := by
  ext v
  simp only [twist_apply, LinearMap.smul_apply, smul_eq_mul, hsemi]

include hγ hsemi in
/-- **Finite Galois descent for `Dsp`.** `dim_K Dsp(ker γ) = [L:K] · dim_K Dsp(G)`. -/
theorem descent_finrank :
    finrank K (Dsp act ρ (γ.ker : Set G)) = finrank K L * finrank K (Dsp act ρ Set.univ) := by
  classical
  -- `B` as an `L`-algebra through `ι`
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  -- the `L`-subspace `Dsp(ker γ)`
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ (γ.ker : Set G)}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ h hh v
        simp only [Set.mem_ofPred_eq] at hφ
        have hx : γ h x = x := by
          rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh
          rw [hh]; rfl
        simp only [LinearMap.smul_apply, hLsmul, hφ h hh v, hsemi, hx] }
  have hDL : DL.restrictScalars K = Dsp act ρ (γ.ker : Set G) := Submodule.ext fun _ => Iff.rfl
  -- the action of `g ∈ G` on `DL`
  let Tg : G → DL →+ DL := fun g =>
    { toFun := fun φ => ⟨twist act ρ g φ, twist_mem act ρ γ g φ.2⟩
      map_zero' := by ext1; simp
      map_add' := by intro φ ψ; ext1; simp }
  have Tg_val : ∀ g (φ : DL), ((Tg g φ : DL) : V →ₗ[K] B) = twist act ρ g φ := fun _ _ => rfl
  let s : (L ≃ₐ[K] L) → G := Function.surjInv hγ
  have hs : ∀ τ, γ (s τ) = τ := Function.surjInv_eq hγ
  have hker : ∀ g, (s (γ g))⁻¹ * g ∈ γ.ker := by
    intro g; rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  let T : (L ≃ₐ[K] L) → DL →+ DL := fun τ => Tg (s τ)
  have hT_eq : ∀ g (φ : DL), Tg g φ = T (γ g) φ := by
    intro g φ
    apply Subtype.ext
    have hg : g = s (γ g) * ((s (γ g))⁻¹ * g) := by group
    change twist act ρ g φ = twist act ρ (s (γ g)) φ
    conv_lhs => rw [hg]
    rw [twist_mul, twist_eq_self_of_mem_ker act ρ γ (hker g) φ.2]
  have hsmul : ∀ τ (c : L) (φ : DL), T τ (c • φ) = τ c • T τ φ := by
    intro τ c φ
    apply Subtype.ext
    change twist act ρ (s τ) (ι c • (φ : V →ₗ[K] B)) = ι (τ c) • twist act ρ (s τ) φ
    rw [twist_smul act ρ ι γ hsemi, hs]
  have hone : ∀ φ, T 1 φ = φ := by
    intro φ
    apply Subtype.ext
    change twist act ρ (s 1) φ = φ
    have : s 1 ∈ γ.ker := by rw [MonoidHom.mem_ker, hs]
    exact twist_eq_self_of_mem_ker act ρ γ this φ.2
  have hmul : ∀ τ σ φ, T (τ * σ) φ = T τ (T σ φ) := by
    intro τ σ φ
    have h1 : T (τ * σ) φ = Tg (s τ * s σ) φ := by
      rw [hT_eq (s τ * s σ), map_mul, hs, hs]
    rw [h1]
    apply Subtype.ext
    change twist act ρ (s τ * s σ) φ = twist act ρ (s τ) (twist act ρ (s σ) φ)
    rw [twist_mul]
  have hsp := speiser_finrank (K := K) (L := L) (M := DL) T hsmul hone hmul
  -- the fixed points are `Dsp(G)`
  have hfix : Submodule.map (DL.subtype.restrictScalars K) (fixedK (K := K) (L := L) (M := DL) T hsmul)
      = Dsp act ρ Set.univ := by
    ext φ
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      apply mem_univ_of_twist
      intro g
      have := congrArg Subtype.val ((hT_eq g ψ).trans (hψ (γ g)))
      exact this
    · intro hφ
      refine ⟨⟨φ, fun g hg v => hφ g (Set.mem_univ _) v⟩, ?_, rfl⟩
      intro τ
      apply Subtype.ext
      exact twist_eq_self_of_mem_univ act ρ (s τ) hφ
  have e1 : finrank K (fixedK (K := K) (L := L) (M := DL) T hsmul) = finrank K (Dsp act ρ Set.univ) := by
    rw [← hfix]
    exact (Submodule.equivMapOfInjective (DL.subtype.restrictScalars K)
      (Submodule.injective_subtype DL) _).finrank_eq
  have e2 : finrank K DL = finrank K (Dsp act ρ (γ.ker : Set G)) := by
    rw [← hDL]
    rfl
  rw [← e2, hsp, e1]

end Descent

end ZInQ.Contrib.G9
