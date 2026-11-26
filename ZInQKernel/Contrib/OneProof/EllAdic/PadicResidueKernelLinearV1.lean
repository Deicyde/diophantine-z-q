import ZInQKernel.Contrib.OneProof.EllAdic.PadicResidueKernelModuleV1

set_option autoImplicit false

namespace RC53.EllAdic

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {A : ℕ → Type u} [∀ n, AddCommGroup (A n)]

/-- The pointwise residue action on the literal additive kernel. -/
@[instance_reducible]
noncomputable def padicResidueKernelModule
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (d : ∀ n, A (n + 1) →+ A n)
    (δ : (∀ n, A n) →+ (∀ n, A n))
    (hδ : ∀ x n, δ x n = x n - d n (x (n + 1))) : Module ℤ_[p] ↥δ.ker := by
  letI : ∀ n, Module ℤ_[p] (A n) := padicResidueDepthModule (p := p) kill
  let K := padicResidueKernelSubmodule (p := p) kill d δ hδ
  let hk : K.toAddSubgroup = δ.ker := padicResidueKernelSubmodule_toAddSubgroup kill d δ hδ
  letI : SMul ℤ_[p] ↥δ.ker := ⟨fun a x => ⟨a • x.val, by
    have hx : x.val ∈ K.toAddSubgroup := hk.symm ▸ x.property
    have hz : a • x.val ∈ K.toAddSubgroup := K.smul_mem a hx
    rw [hk] at hz
    exact hz⟩⟩
  exact (Subtype.val_injective : Function.Injective δ.ker.subtype).module ℤ_[p] δ.ker.subtype (fun _ _ => rfl)

/-- The action uses the specified residue scalar at every coordinate. -/
theorem padicResidueKernelModule_smul_coordinate
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (d : ∀ n, A (n + 1) →+ A n)
    (δ : (∀ n, A n) →+ (∀ n, A n))
    (hδ : ∀ x n, δ x n = x n - d n (x (n + 1)))
    (a : ℤ_[p]) (x : ↥δ.ker) (n : ℕ) :
    letI := padicResidueKernelModule (p := p) kill d δ hδ
    letI := padicResidueDepthModule (p := p) kill n
    (a • x).val n = a • x.val n := rfl

variable {M : Type v} [AddCommGroup M] [Module ℤ_[p] M]

/-- An additive equivalence into this exact kernel upgrades without changing
its values or imposing a continuity hypothesis. -/
noncomputable def padicResidueKernelLinearEquiv
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (d : ∀ n, A (n + 1) →+ A n)
    (δ : (∀ n, A n) →+ (∀ n, A n))
    (hδ : ∀ x n, δ x n = x n - d n (x (n + 1))) (e : M ≃+ ↥δ.ker) :
    letI := padicResidueKernelModule (p := p) kill d δ hδ
    M ≃ₗ[ℤ_[p]] ↥δ.ker := by
  letI := padicResidueKernelModule (p := p) kill d δ hδ
  let π (n : ℕ) : ↥δ.ker →+ A n :=
    { toFun := fun x => x.val n, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact linearEquiv_of_addEquiv_residue_projections e π
    (fun h => Subtype.ext (funext h)) kill

theorem padicResidueKernelLinearEquiv_apply
    (kill : ∀ n (x : A n), (p ^ n : ℕ) • x = 0)
    (d : ∀ n, A (n + 1) →+ A n)
    (δ : (∀ n, A n) →+ (∀ n, A n))
    (hδ : ∀ x n, δ x n = x n - d n (x (n + 1))) (e : M ≃+ ↥δ.ker) (x : M) :
    padicResidueKernelLinearEquiv kill d δ hδ e x = e x := rfl

end RC53.EllAdic
