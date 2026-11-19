/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_AdelicLsXi (git blob e9fd0babd98c898e33ffb630f7cb8699431d7b57, sha256 0f03f01460b9aae22162f8e5cb0d284b128d59d243162565e13bb09004660a15).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

def globalPoints : Matrix.GeneralLinearGroup (Fin 2) K →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

def centralScalar : (AdeleRing R K)ˣ →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

def IsIdeleClassChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ u : Kˣ, χ (Units.map (algebraMap K (AdeleRing R K)) u) = 1

def IsUnitaryChar (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AdeleRing R K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def SquaresToXi (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)
    (χ : (AdeleRing R K)ˣ →* ℂˣ) : Prop :=
  ∀ z : Z, χ (z : (AdeleRing R K)ˣ) ^ 2 = ξ z

variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)

structure IsLsXiFunction (φ : AdelicGL2 R K → ℂ) : Prop where
  left_invariant : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 R K),
    φ (globalPoints R K γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 R K),
    φ (centralScalar R K (z : (AdeleRing R K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g

theorem isLsXiFunction_zero : IsLsXiFunction R K Z ξ (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ => rfl, fun _ _ => by simp⟩

variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))

structure LsXiMember (φ : AdelicGL2 R K → ℂ) : Prop extends IsLsXiFunction R K Z ξ φ where
  memLp_two : MemLp φ 2 ((volume : Measure (AdelicGL2 R K)).restrict D)

theorem lsXiMember_zero : LsXiMember R K Z ξ D (fun _ => (0 : ℂ)) :=
  ⟨isLsXiFunction_zero R K Z ξ, MemLp.zero'⟩

def chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K → ℂ :=
  fun g => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

end AutomorphicForm

end
