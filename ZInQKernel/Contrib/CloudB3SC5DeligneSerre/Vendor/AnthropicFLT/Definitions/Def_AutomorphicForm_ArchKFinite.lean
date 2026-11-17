/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_ArchKFinite (git blob de33cc7543ccad02788a053b7bf2afb5dfd33f47, sha256 e35e5c0ff708a6563a35d46d2b2fff802fd75ae4ec9c15608288ea6a3b24e6b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section Generic

variable {G : Type*} [Group G]

def RightTranslatesSpanFinite (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ s : Finset (G → ℂ),
    ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))

theorem rightTranslatesSpanFinite_const (K : Subgroup G) (c : ℂ) :
    RightTranslatesSpanFinite K (fun _ : G => c) := by
  refine ⟨{fun _ => c}, fun k _hk => ?_⟩
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

theorem rightTranslatesSpanFinite_bot (f : G → ℂ) :
    RightTranslatesSpanFinite (⊥ : Subgroup G) f := by
  refine ⟨{f}, fun k hk => ?_⟩
  rw [Subgroup.mem_bot] at hk; subst hk
  have h1 : (fun x : G => f (x * 1)) = f := by funext x; rw [mul_one]
  rw [h1]
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

end Generic

section Arch

variable (F : Type) [Field F] [NumberField F]

def archRowIsometrySubgroup (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup w.Completion).map (adelicArchGLInclAt F w)

def IsArchKFiniteAt (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  RightTranslatesSpanFinite (archRowIsometrySubgroup F w) φ

def IsArchKFinite (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, IsArchKFiniteAt F w φ

theorem isArchKFinite_const (c : ℂ) : IsArchKFinite F (fun _ => c) :=
  fun w => rightTranslatesSpanFinite_const (archRowIsometrySubgroup F w) c

theorem isArchKFinite_zero : IsArchKFinite F (fun _ => (0 : ℂ)) := isArchKFinite_const F 0

theorem isArchKFinite_of_hasArchType
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : HasArchType F χ φ) :
    IsArchKFinite F φ := by
  intro w
  refine ⟨{φ}, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hχ : (fun x => φ (x * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)))
      = ((χ w ⟨k, hk⟩ : ℂˣ) : ℂ) • φ := by
    funext x
    exact hφ w ⟨k, hk⟩ x
  rw [hχ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _)))

end Arch

end AutomorphicForm
